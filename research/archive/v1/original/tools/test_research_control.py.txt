"""Contract-level tests for durable accounting; no network or repository writes."""
import hashlib
import json
import os
import tempfile
import unittest
from datetime import datetime, timezone
from pathlib import Path

from research_control import SECTIONS, audit

NOW = datetime(2026, 11, 3, 12, 0, tzinfo=timezone.utc)


def programme(key="R001"):
    return dict(schema=1, id=key, programme=key, lane="core", status="ready",
                revision=1, parallel_limit=2,
                grants=[dict(id=1, slots=4, by="Super-Critic", kind="installer",
                             decision="research/decisions/install.md")],
                claims=[], review_requested=None)


def claim(n, state="finished", old=False, grant=1, root="R001"):
    stamp = "2026-11-03T09:00:00Z" if old else "2026-11-03T11:30:00Z"
    return dict(id=f"agent{n}:run-{n}:{root}", agent=f"agent{n}", run_id=f"run-{n}",
                claimed_at=stamp, registered_at=stamp, grant=grant, task_issue=root,
                task=f"Distinct scientific task {n}", role="investigate", state=state,
                evidence=[], handoff="Current evidence and next exact step.")


class Contracts(unittest.TestCase):
    def setUp(self):
        base = Path(os.environ.get("BB6_RESEARCH_TEST_TMP", tempfile.gettempdir())).resolve()
        self.temp = tempfile.TemporaryDirectory(dir=base)
        self.root = Path(self.temp.name).resolve()
        self.root.relative_to(base)  # Verify cleanup remains inside the selected fixture directory.
        (self.root / "research/issues").mkdir(parents=True)
        (self.root / "research/decisions").mkdir()
        (self.root / "research/decisions/install.md").write_text("Authority", encoding="utf-8")
        self.addCleanup(self.temp.cleanup)

    def save(self, record):
        fence = chr(96) * 3
        body = f"# {record['id']}\n\n{fence}json\n{json.dumps(record)}\n{fence}\n"
        body += "".join(f"\n## {section}\nConcrete record.\n" for section in SECTIONS)
        (self.root / "research/issues" / (record["id"] + ".md")).write_text(body, encoding="utf-8")

    def result(self):
        return audit(self.root, NOW)

    def test_ready_programme_has_four_slots_and_no_review(self):
        self.save(programme())
        result = self.result()
        self.assertEqual(result["errors"], [])
        self.assertEqual(result["programmes"][0]["remaining"], 4)
        self.assertEqual(result["queue"], [])

    def test_full_grant_queues_review_and_fifth_claim_is_rejected(self):
        record = programme()
        record["claims"] = [claim(n) for n in range(1, 5)]
        self.save(record)
        result = self.result()
        self.assertEqual(result["errors"], [])
        self.assertEqual(result["queue"][0]["id"], "R001")
        record["claims"].append(claim(5))
        self.save(record)
        self.assertTrue(any("over capacity" in e for e in self.result()["errors"]))

    def test_crash_does_not_refund_slot_or_keep_execution_lock(self):
        record = programme()
        record["claims"] = [claim(1, "active", old=True)]
        self.save(record)
        row = self.result()["programmes"][0]
        self.assertEqual((row["remaining"], row["active"], row["stale"]), (3, 0, 1))
        record["claims"][0]["state"] = "interrupted"
        self.save(record)
        self.assertEqual(self.result()["programmes"][0]["remaining"], 3)

    def test_parallel_limit_and_duplicate_exact_tasks(self):
        record = programme()
        record["claims"] = [claim(n, "active") for n in range(1, 4)]
        self.save(record)
        self.assertTrue(any("parallel limit" in e for e in self.result()["errors"]))
        record["claims"] = record["claims"][:2]
        record["claims"][1]["task"] = record["claims"][0]["task"]
        self.save(record)
        self.assertTrue(any("duplicate active" in e for e in self.result()["errors"]))

    def test_same_incarnation_cannot_reset_budget_in_new_claim(self):
        record = programme()
        record["claims"] = [claim(1), claim(1)]
        record["claims"][1]["id"] = "different-filename"
        self.save(record)
        self.assertTrue(any("duplicate incarnation" in e for e in self.result()["errors"]))

    def test_child_uses_root_budget_and_cannot_have_own_grant(self):
        record = programme()
        child = dict(schema=1, id="R-child", programme="R001", lane="core",
                     status="ready", revision=1)
        record["claims"] = [claim(1)]
        record["claims"][0]["task_issue"] = "R-child"
        self.save(record)
        self.save(child)
        self.assertEqual(self.result()["errors"], [])
        self.assertEqual(self.result()["total_slots"], 1)
        child["grants"] = []
        self.save(child)
        self.assertTrue(any("child tasks" in e for e in self.result()["errors"]))

    def test_independent_peer_can_renew_without_critic(self):
        record = programme()
        record["claims"] = [claim(n) for n in range(1, 5)]
        record["grants"].append(dict(id=2, slots=4, by="agent9", kind="peer",
                                    decision="research/decisions/install.md"))
        self.save(record)
        self.assertEqual(self.result()["errors"], [])
        self.assertEqual(self.result()["programmes"][0]["remaining"], 4)
        record["grants"][-1]["by"] = "agent1"
        self.save(record)
        self.assertTrue(any("reviewer authored" in e for e in self.result()["errors"]))

    def test_new_grant_cannot_be_repeated_self_pilot(self):
        record = programme()
        record["grants"][0].update(kind="self-pilot", slots=2, by="agent1")
        self.save(record)
        self.assertEqual(self.result()["errors"], [])
        record["grants"].append(dict(id=2, slots=2, by="agent1", kind="self-pilot",
                                    decision="research/decisions/install.md"))
        self.save(record)
        self.assertTrue(any("self-pilot" in e for e in self.result()["errors"]))

    def test_dispute_precedes_older_routine_review(self):
        one, two = programme(), programme("R002")
        one["review_requested"] = dict(at="2026-11-03T09:00:00Z", reason="renewal", target="peer")
        two["status"] = "disputed"
        two["review_requested"] = dict(at="2026-11-03T11:00:00Z", reason="counterexample", target="critic")
        self.save(one)
        self.save(two)
        self.assertEqual([r["id"] for r in self.result()["queue"]], ["R002", "R001"])

    def test_malformed_record_reports_errors_without_crashing(self):
        record = programme()
        record["programme"] = []
        record["lane"] = {}
        self.save(record)
        self.assertTrue(self.result()["errors"])

    def test_missing_root_and_outside_decision_are_rejected(self):
        record = programme()
        record["grants"][0]["decision"] = "../outside.md"
        self.save(record)
        child = dict(schema=1, id="R-orphan", programme="R-missing", lane="core",
                     status="ready", revision=1)
        self.save(child)
        errors = self.result()["errors"]
        self.assertTrue(any("existing root" in e for e in errors))
        self.assertTrue(any("decision must link" in e for e in errors))

    def test_checker_is_read_only(self):
        record = programme()
        record["claims"] = [claim(1, "active", old=True)]
        self.save(record)
        def hashes():
            return {str(p): hashlib.sha256(p.read_bytes()).hexdigest()
                    for p in self.root.rglob("*") if p.is_file()}
        before = hashes()
        self.result()
        self.assertEqual(before, hashes())


if __name__ == "__main__":
    unittest.main()
