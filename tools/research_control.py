#!/usr/bin/env python3
"""Read-only research-record checks and board. No network, writes or lease edits."""
import argparse
import json
import re
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path

LANES = {"core", "frontier", "validation", "exploration"}
STATES = {"ready", "active", "review", "shelved", "completed", "disputed"}
ROLES = {"investigate", "falsify", "integrate", "validate"}
SECTIONS = ("Question and scope", "Baseline and evidence",
            "Approach and discriminating tests", "Outcomes and renewal",
            "Compute", "Next action and handoff")
BLOCK = re.compile(r"^" + chr(96) * 3 + r"json[ \t]*\n(.*?)\n" + chr(96) * 3,
                   re.MULTILINE | re.DOTALL)


def utc(value):
    if not isinstance(value, str):
        raise ValueError("timestamp must be an ISO UTC string")
    stamp = datetime.fromisoformat(value.replace("Z", "+00:00"))
    if stamp.tzinfo is None or stamp.utcoffset().total_seconds() != 0:
        raise ValueError("timestamp must explicitly be UTC")
    return stamp


def positive(value):
    return type(value) is int and value > 0


def local_reference(root, value):
    if not isinstance(value, str) or not value or "\\" in value or ":" in value:
        return False
    path = Path(value)
    if path.is_absolute() or ".." in path.parts:
        return False
    resolved = (root / path).resolve()
    try:
        resolved.relative_to(root.resolve())
    except ValueError:
        return False
    return resolved.is_file()


def audit(root, now=None):
    root = Path(root)
    now = now or datetime.now(timezone.utc)
    report = {"errors": [], "warnings": [], "programmes": [], "queue": [],
              "lanes": Counter(), "total_slots": 0}
    errors, warnings = report["errors"], report["warnings"]
    policy = {"default_grant_slots": 4, "pilot_slots": 2, "adoption_review_after_slots": 12,
              "lane_targets": {"core": 40, "frontier": 30, "validation": 20, "exploration": 10}}
    config_path = root / "research" / "policy.json"
    if config_path.exists():
        try:
            configured = json.loads(config_path.read_text(encoding="utf-8"))
            if not isinstance(configured, dict):
                raise ValueError("policy must be an object")
            for field in ("default_grant_slots", "pilot_slots", "adoption_review_after_slots"):
                if not positive(configured.get(field)):
                    raise ValueError(f"invalid {field}")
            policy.update(configured)
        except (OSError, ValueError) as exc:
            errors.append(f"policy.json: {exc}")
    report["policy"] = policy
    records = {}
    directory = root / "research" / "issues"
    paths = sorted(directory.glob("*.md"))
    if not paths:
        errors.append("No research/issues/*.md records found.")
    for path in paths:
        try:
            body = path.read_text(encoding="utf-8")
            block = BLOCK.search(body)
            if not block:
                raise ValueError("missing fenced json metadata")
            meta = json.loads(block.group(1))
            if not isinstance(meta, dict):
                raise ValueError("metadata must be an object")
        except (OSError, ValueError) as exc:
            errors.append(f"{path.name}: {exc}")
            continue
        key = meta.get("id")
        if not isinstance(key, str) or not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_-]*", key):
            errors.append(f"{path.name}: invalid id")
            continue
        if key != path.stem:
            errors.append(f"{path.name}: filename must match id {key}")
        if key in records:
            errors.append(f"{key}: duplicate issue id")
            continue
        prior_errors = len(errors)
        if meta.get("schema") != 1 or type(meta.get("schema")) is not int:
            errors.append(f"{key}: schema must be 1")
        if not positive(meta.get("revision")):
            errors.append(f"{key}: revision must be a positive integer")
        if not isinstance(meta.get("lane"), str) or meta["lane"] not in LANES:
            errors.append(f"{key}: unknown lane")
        if not isinstance(meta.get("status"), str) or meta["status"] not in STATES:
            errors.append(f"{key}: unknown status")
        if not isinstance(meta.get("programme"), str):
            errors.append(f"{key}: missing programme id")
        for section in SECTIONS:
            if f"## {section}" not in body:
                errors.append(f"{key}: missing section {section}")
        if len(errors) > prior_errors:
            continue
        records[key] = meta

    for key, meta in records.items():
        parent = records.get(meta.get("programme"))
        if parent is None or parent.get("programme") != parent.get("id"):
            errors.append(f"{key}: programme must name an existing root")
        if meta.get("programme") != key and ("grants" in meta or "claims" in meta):
            errors.append(f"{key}: child tasks cannot carry grants or claims")
        if parent and meta.get("lane") != parent.get("lane"):
            errors.append(f"{key}: child lane must match root")

    for key, meta in records.items():
        if meta.get("programme") != key:
            continue
        grants, claims = meta.get("grants"), meta.get("claims")
        limit = meta.get("parallel_limit")
        if not positive(limit):
            errors.append(f"{key}: parallel_limit must be positive")
            limit = 2
        if not isinstance(grants, list) or not isinstance(claims, list):
            errors.append(f"{key}: root grants/claims must be arrays")
            continue
        by_grant, ordered = {}, []
        for grant in grants:
            if not isinstance(grant, dict):
                errors.append(f"{key}: malformed grant")
                continue
            gid = grant.get("id")
            if not positive(gid) or gid in by_grant or (ordered and gid <= ordered[-1]):
                errors.append(f"{key}: grant ids must be unique increasing positive integers")
                continue
            if not positive(grant.get("slots")):
                errors.append(f"{key}: grant {gid} slots must be positive")
                continue
            kind = grant.get("kind")
            if not isinstance(kind, str) or kind not in {"installer", "self-pilot", "peer", "critic"}:
                errors.append(f"{key}: grant {gid} has unknown authorization kind")
            if not isinstance(grant.get("by"), str) or not grant["by"].strip():
                errors.append(f"{key}: grant {gid} needs a named reviewer/authority")
            if not local_reference(root, grant.get("decision")):
                errors.append(f"{key}: grant {gid} decision must link an existing local record")
            if kind == "self-pilot" and (ordered or grant["slots"] > policy["pilot_slots"]):
                errors.append(f"{key}: self-pilot is only a first grant within the pilot allowance")
            if kind == "peer" and grant["slots"] > policy["default_grant_slots"]:
                errors.append(f"{key}: larger peer grants require a critic decision")
            if kind == "installer" and ordered:
                errors.append(f"{key}: installer authorization cannot renew a programme")
            by_grant[gid] = grant
            ordered.append(gid)

        used, seen_ids, seen_runs = Counter(), set(), set()
        agents_by_grant, active_tasks = {}, set()
        active = stale = 0
        for claim in claims:
            if not isinstance(claim, dict):
                errors.append(f"{key}: malformed claim")
                continue
            cid, agent, run = claim.get("id"), claim.get("agent"), claim.get("run_id")
            if not isinstance(cid, str) or not cid or cid in seen_ids:
                errors.append(f"{key}: invalid/duplicate claim id")
            else:
                seen_ids.add(cid)
            if not isinstance(agent, str) or not re.fullmatch(r"agent([1-9]|[1-4][0-9]|50)", agent):
                errors.append(f"{key}: claim agent must be agent1 through agent50")
            if not isinstance(run, str) or not run:
                errors.append(f"{key}: claim needs original run_id")
            pair = (str(agent), str(run))
            if pair in seen_runs:
                errors.append(f"{key}: duplicate incarnation claim {pair}")
            seen_runs.add(pair)
            gid = claim.get("grant")
            if type(gid) is not int or gid not in by_grant:
                errors.append(f"{key}: claim refers to missing grant")
            else:
                used[gid] += 1
                agents_by_grant.setdefault(gid, set()).add(str(agent))
            task_id = claim.get("task_issue")
            target = records.get(task_id) if isinstance(task_id, str) else None
            if not target or target.get("programme") != key:
                errors.append(f"{key}: claim task must belong to this root")
            if not isinstance(claim.get("task"), str) or not claim["task"].strip():
                errors.append(f"{key}: claim needs an explicit task")
            if not isinstance(claim.get("role"), str) or claim["role"] not in ROLES:
                errors.append(f"{key}: unknown claim role")
            state = claim.get("state")
            if not isinstance(state, str) or state not in {"active", "finished", "interrupted"}:
                errors.append(f"{key}: unknown claim state")
            if not isinstance(claim.get("evidence"), list) or not isinstance(claim.get("handoff"), str):
                errors.append(f"{key}: claim needs evidence array and handoff")
            try:
                start = utc(claim.get("claimed_at"))
                registered = utc(claim.get("registered_at"))
                if registered < start:
                    errors.append(f"{key}: registration predates original claim")
                age = (now - start).total_seconds()
                if age < 0 or registered > now:
                    warnings.append(f"{key}: future timestamp; check real clock")
                is_stale = age > 100 * 60
                if state == "interrupted" and not is_stale:
                    errors.append(f"{key}: abandoned claim interrupted before 100-minute threshold")
                if state == "active":
                    if is_stale:
                        stale += 1
                        warnings.append(f"{key}: stale claim {cid}; preserve cost and reconcile handoff")
                    else:
                        active += 1
                        task_key = (str(task_id), " ".join(str(claim.get("task")).lower().split()))
                        if task_key in active_tasks:
                            errors.append(f"{key}: duplicate active exact task")
                        active_tasks.add(task_key)
            except (ValueError, TypeError, OverflowError) as exc:
                errors.append(f"{key}: invalid claim timestamps: {exc}")

        for gid, grant in by_grant.items():
            if used[gid] > grant["slots"]:
                errors.append(f"{key}: grant {gid} over capacity ({used[gid]}/{grant['slots']})")
        for pos, gid in enumerate(ordered):
            grant = by_grant[gid]
            if (pos and grant.get("kind") == "peer" and isinstance(grant.get("by"), str)
                    and grant["by"] in agents_by_grant.get(ordered[pos-1], set())):
                errors.append(f"{key}: peer renewal reviewer authored preceding grant work")
        if active > limit:
            errors.append(f"{key}: {active} active investigators exceed parallel limit {limit}")
        current = by_grant[ordered[-1]] if ordered else None
        remaining = current["slots"] - used[current["id"]] if current else 0
        request = meta.get("review_requested")
        requested_at = ""
        if request is not None:
            if not isinstance(request, dict):
                errors.append(f"{key}: review_requested must be null or an object")
            else:
                try:
                    requested_at = utc(request.get("at")).isoformat()
                except (ValueError, TypeError, OverflowError):
                    errors.append(f"{key}: review request needs UTC timestamp")
                if (not isinstance(request.get("target"), str) or request["target"] not in {"peer", "critic"}
                        or not isinstance(request.get("reason"), str) or not request["reason"].strip()):
                    errors.append(f"{key}: review request needs target and reason")
        needs_review = (request is not None or meta.get("status") in {"review", "disputed"}
                        or (remaining <= 0 and meta.get("status") in {"ready", "active"}))
        if needs_review:
            if request is None:
                warnings.append(f"{key}: review due; record a timestamped request")
            report["queue"].append(dict(id=key, at=requested_at,
                target=request.get("target", "peer") if isinstance(request, dict) else "peer",
                reason=request.get("reason", "grant exhausted or review status") if isinstance(request, dict)
                       else "grant exhausted or review status",
                disputed=meta.get("status") == "disputed"))
        count = len(claims)
        lane = meta.get("lane", "unknown")
        report["lanes"][lane] += count
        report["total_slots"] += count
        report["programmes"].append(dict(id=key, lane=lane, status=meta.get("status"),
            grant=current["id"] if current else None, remaining=max(0, remaining),
            active=active, stale=stale, total=count, review=needs_review))
    report["queue"].sort(key=lambda item: (not item["disputed"], item["at"] or "9999", item["id"]))
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["check", "board"])
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--now", type=utc, help="explicit UTC timestamp for reproducible diagnostics")
    args = parser.parse_args()
    result = audit(args.root, args.now)
    for error in result["errors"]:
        print("ERROR:", error)
    for warning in result["warnings"]:
        print("WARN:", warning)
    if args.command == "board":
        print("Issue | lane | state | current grant | remaining | active | stale | all slots")
        for row in result["programmes"]:
            print(" | ".join(str(row[k]) for k in
                  ("id", "lane", "status", "grant", "remaining", "active", "stale", "total")))
        print("\nReview queue (correctness disputes first; then timestamp):")
        for item in result["queue"]:
            print(f"{item['id']} [{item['target']}] {item['at'] or 'timestamp needed'}: {item['reason']}")
        if not result["queue"]:
            print("No reviews currently queued.")
        print("\nRecorded slots:", result["total_slots"], dict(result["lanes"]))
        print("Effort guides:", result["policy"]["lane_targets"])
        if result["total_slots"] >= result["policy"]["adoption_review_after_slots"]:
            print("Adoption-review threshold reached: successor critic should inspect policy consequences.")
    print(f"{len(result['errors'])} error(s), {len(result['warnings'])} warning(s). "
          "Read-only structural check; not mathematical or lease authentication.")
    return 1 if result["errors"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
