#!/usr/bin/env python3
"""Check that the depth-four exporter contains the two exact authentic-root leaves."""

from __future__ import annotations

import json
import sys
from pathlib import Path

GROUP = "S5_fix_A_x_LR_reflection"
MASS = 25**8

def tr(write: int, direction: str, next_state: str) -> dict:
    return {
        "halt": False,
        "write": write,
        "direction": direction,
        "next_state": next_state,
    }

def branch(slot: str, write: int, direction: str, next_state: str) -> dict:
    return {"slot": slot, "transition": tr(write, direction, next_state)}

EXPECTED = {
    "Machine C": {
        "path": [
            branch("A/0", 1, "R", "B"),
            branch("B/0", 1, "L", "C"),
            branch("C/1", 0, "L", "B"),
            branch("C/0", 1, "L", "A"),
        ],
        "free_slots": ["A/1", "B/1", "D/0", "D/1", "E/0", "E/1", "F/0", "F/1"],
        "probe_slot": "B/1",
        "endpoint": {"state": "B", "head": -2, "one_cells": [-3, -2, -1, 1]},
        "table": [
            tr(1, "R", "B"), None, tr(1, "L", "C"), None,
            tr(1, "L", "A"), tr(0, "L", "B"), None, None,
            None, None, None, None,
        ],
        "canonical_key": "00:M101;10:M112;20:M110;21:M011",
        "orbit_size": 40,
        "stabilizer_size": 6,
    },
    "#623": {
        "path": [
            branch("A/0", 1, "R", "B"),
            branch("B/0", 0, "R", "C"),
            branch("C/0", 0, "R", "D"),
            branch("D/0", 1, "L", "D"),
        ],
        "free_slots": ["A/1", "B/1", "C/1", "D/1", "E/0", "E/1", "F/0", "F/1"],
        "probe_slot": "D/1",
        "endpoint": {"state": "D", "head": 0, "one_cells": [1, 2, 3, 0]},
        "table": [
            tr(1, "R", "B"), None, tr(0, "R", "C"), None,
            tr(0, "R", "D"), None, tr(1, "L", "D"), None,
            None, None, None, None,
        ],
        "canonical_key": "00:M101;10:M002;20:M003;30:M113",
        "orbit_size": 120,
        "stabilizer_size": 2,
    },
}

def check(record: dict, name: str, expected: dict) -> None:
    assert record["terminal_status"] == "open", (name, "status")
    assert record["frontier_stop"] == "tree-depth-exhausted", (name, "stop")
    assert record["branch_depth"] == 4, (name, "depth")
    assert record["branch_path"] == expected["path"], (name, "ordered path")
    assert record["partial_table_A0_A1_B0_B1_C0_C1_D0_D1_E0_E1_F0_F1"] == expected["table"], (name, "partial table")
    assert record["free_slots"] == expected["free_slots"], (name, "free slots")
    assert record["compatible_raw_completions"] == MASS, (name, "completion mass")

    outcomes = record["oracle_outcomes"]
    assert outcomes == {
        "accepted_by_source_oracle": False,
        "finiteDecision": False,
        "finiteLasso": False,
        "finiteEntryMacroBi": False,
    }, (name, "oracle outcomes")

    probe = record["physical_scan_probe"]
    assert probe == {
        "kind": "next_unassigned_physical_input",
        "successful_moves_before_stop": 6,
        "endpoint": expected["endpoint"],
        "next_unassigned_slot": expected["probe_slot"],
        "exact_halt_score": None,
        "source_theorem": "physicalScanProbe_unknown_is_raw_prefix",
    }, (name, "physical probe")

    action = record["next_action"]
    assert action["status"] == "extend_the_authenticated_physical_frontier", (name, "next action")
    assert action["first_branch_slot"] == expected["probe_slot"], (name, "next slot")
    assert action["after_successful_blank_root_moves"] == 6, (name, "next move index")
    assert action["required_branch"] == "all 25 transition outcomes at this previously unassigned slot", (name, "branch obligation")
    assert action["leaf_certificate_type"] == "Cover (DecidedBelow B) partialTable", (name, "certificate contract")

    contract = record["required_global_discharge_contract"]
    assert contract["type"] == "Cover (DecidedBelow B) partialTable", (name, "global contract")
    assert "NeverHalts m OR exists n" in contract["pointwise_predicate"], (name, "pointwise predicate")
    assert "does not establish a global BB(6) bound" in contract["bound_status"], (name, "bound disclaimer")

    symmetry = record["root_preserving_symmetry"]
    assert symmetry["group"] == GROUP and symmetry["group_order"] == 240, (name, "symmetry group")
    assert symmetry["canonical_key"] == expected["canonical_key"], (name, "canonical key")
    assert symmetry["orbit_size"] == expected["orbit_size"], (name, "orbit size")
    assert symmetry["stabilizer_size"] == expected["stabilizer_size"], (name, "stabilizer")
    assert symmetry["canonicalizing_transform"] == {
        "old_to_new_state_labels": list("ABCDEF"),
        "left_right_reflection": True,
    }, (name, "canonicalizing transform")

def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: verify_export.py depth4-residual-frontier.jsonl")
    path = Path(sys.argv[1])
    matches = {name: [] for name in EXPECTED}
    with path.open() as source:
        for line_no, line in enumerate(source, 1):
            if not line.strip():
                continue
            record = json.loads(line)
            for name, expected in EXPECTED.items():
                if record.get("branch_path") == expected["path"]:
                    matches[name].append((line_no, record))
    for name, found in matches.items():
        if len(found) != 1:
            raise SystemExit(f"{name}: expected exactly one matching terminal, found {len(found)}")
        check(found[0][1], name, EXPECTED[name])
        print(f"verified {name}: JSONL line {found[0][0]}, mass={MASS}, next={EXPECTED[name]['probe_slot']}")
    print("verified both authentic-root terminal records and their exact symmetry/probe fields")

if __name__ == "__main__":
    main()
