#!/usr/bin/env python3
"""Fail-fast advisory preflight for the *accepted Canonical39* BB(6) roster.

Prevents re-launching expensive global-consumer CI for raw representatives
already removed on the accepted lineage. This is NOT a Lean theorem, a
machine-decision certificate, or a proof of source/roster correspondence.
The underlying canonical40 JSON is explicitly a reconstructed manifest.
The Canonical39 decrement is separately source-accepted (run 46129131784).

Use before writing or dispatching a consumer, then verify exact table identity,
membership/removal and all transitive axioms in the actual Lean consumer.

  python3 tools/preflight_canonical39_raw.py --accepted Canonical39 47 112
  python3 tools/preflight_canonical39_raw.py --accepted Canonical39 83 85 106 79
  python3 tools/preflight_canonical39_raw.py --accepted Canonical39 47 \
    --table '1RB---_1RC---_0RD---_1LD0RC_------_------'

Exit 0: all requested raw IDs retained (with optional table match).
Exit 2: at least one absent or mismatched (do not launch consumer as written).
Exit 3: the pinned snapshot assumptions changed or input was invalid.

This snapshot must be updated or superseded when a NEW accepted global
successor replaces Canonical39. It does not infer acceptance from proposals.
"""
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "im-results/agent50-raw47-canonical41/canonical40-raw-index-audit.json"
ACCEPTED_CONSUMERS = {"Canonical39": "46129131784", "Canonical38": "46150267242"}
RAW112_TABLE = "1RB---_1RC---_0RD---_1LD1RE_---1LC_------"


def load_snapshot(stage):
    if stage not in ACCEPTED_CONSUMERS:
        raise ValueError("unknown accepted stage")
    data = json.loads(MANIFEST.read_text(encoding="utf-8"))
    if data.get("status") != "manifest-reconstructed; not kernel-certified roster identity":
        raise ValueError("reconstruction status changed; re-audit before preflight")
    entries = data.get("canonical40", [])
    if len(entries) != 40:
        raise ValueError("expected 40 canonical40 rows")
    raw_map = {row["raw"]: row["table"] for row in entries}
    if len(raw_map) != 40 or 39 not in raw_map or 112 not in raw_map:
        raise ValueError("canonical40 rows changed or necessary parent absent")
    if not data.get("history") or data["history"][-1].get("stage") != "Canonical40":
        raise ValueError("expected canonical40 to be last recorded base stage")
    if data["history"][-1].get("remaining") != 40:
        raise ValueError("canonical40 historical count changed")
    if normalized_table(raw_map[112]) != normalized_table(RAW112_TABLE):
        raise ValueError("Raw112 literal table differs from source-accepted parent")
    after39 = {r: t for r, t in raw_map.items() if r != 39}
    if len(after39) != 39:
        raise ValueError("canonical39 reconstructed complement count != 39")
    retained = (after39 if stage == "Canonical39"
                else {r: t for r, t in after39.items() if r != 112})
    if len(retained) != (39 if stage == "Canonical39" else 38):
        raise ValueError("selected reconstructed complement count is wrong")
    removed_at = {
        raw: item["stage"]
        for item in data["history"]
        for raw in item["removed"]
    }
    removed_at[39] = "Canonical39"
    if stage == "Canonical38":
        removed_at[112] = "Canonical38"
    return retained, removed_at

def normalized_table(value):
    compact = "".join(value.upper().split()).replace("_", "")
    if len(compact) != 36 or any(
        compact[i:i+3] != "---"
        and not (
            compact[i] in "01"
            and compact[i+1] in "LR"
            and compact[i+2] in "ABCDEF"
        ) for i in range(0, 36, 3)
    ):
        raise ValueError("table must encode exactly 12 three-character transitions")
    return compact


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--accepted", required=True, choices=["Canonical39", "Canonical38"],
                        help="explicit source-accepted roster snapshot (not a live query)")
    parser.add_argument("--table", help="exact 12-transition table; requires one raw ID")
    parser.add_argument("raw_ids", type=int, nargs="+", metavar="RAW")
    args = parser.parse_args(argv)
    if args.table and len(args.raw_ids) != 1:
        parser.error("--table requires exactly one raw ID")
    try:
        retained, removed_at = load_snapshot(args.accepted)
        exact_table = normalized_table(args.table) if args.table else None
    except (OSError, ValueError, KeyError, json.JSONDecodeError) as err:
        print(f"PREFLIGHT INDETERMINATE: {err}", file=sys.stderr)
        return 3

    print(f"Advisory snapshot {args.accepted} (source consumer {ACCEPTED_CONSUMERS[args.accepted]}); "
          "not a proof and not an automatic latest-roster check.")
    failed = False
    for raw in args.raw_ids:
        if raw not in retained:
            stage = removed_at.get(raw)
            reason = f"already removed by {stage}" if stage else "not in this reconstructed roster"
            print(f"Raw{raw}: REJECT — {reason}")
            failed = True
        elif exact_table and normalized_table(retained[raw]) != exact_table:
            print(f"Raw{raw}: REJECT — raw ID matches but exact transition table differs")
            failed = True
        else:
            print(f"Raw{raw}: RETAINED — {retained[raw]}")
    if failed:
        print("Do not dispatch the proposed global removal unchanged; check the accepted "
              "Lean roster and revise the parent target.")
        return 2
    print("Preflight passes. Still prove source-checked exact membership and successor.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
