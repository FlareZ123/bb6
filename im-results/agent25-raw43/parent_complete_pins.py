#!/usr/bin/env python3
"""Emit the authenticated-input array for Raw43ParentComplete.

The eighteen immutable source-accepted inputs are pinned here.  Supply the five
remaining run ids once their source gates succeed; merge_parent.py revalidates
every run, artifact manifest, theorem, bound, source revision, Lean binary, and
module identity before composing the parent.
"""
from __future__ import annotations

import argparse
import json

STATIC = [
    {"run_id": 45806858894, "artifact": "raw43-child-proof"},
    {"run_id": 45921443774, "artifact": "raw43-0rd-proof"},
    {"run_id": 45922723471, "artifact": "raw43-1rd-proof"},
    {"run_id": 45923417036, "artifact": "raw43-extra-proof"},  # 0RE
    {"run_id": 45923820055, "artifact": "raw43-extra-proof"},  # 1LB
    {"run_id": 45924128359, "artifact": "raw43-extra-proof"},  # 1RE
    {"run_id": 45924242489, "artifact": "raw43-extra-proof"},  # 0RC
    {"run_id": 45924433029, "artifact": "raw43-extra-proof"},  # 0RF
    {"run_id": 45924494093, "artifact": "raw43-extra-proof"},  # 1LA
    {"run_id": 45924542932, "artifact": "raw43-extra-proof"},  # 1LE
    {"run_id": 45924672806, "artifact": "raw43-extra-proof"},  # 1RF
    {"run_id": 45934715974, "artifact": "raw43-b1rc-complete-proof"},
    {"run_id": 45937283185, "artifact": "raw43-b0rc-complete-proof"},
    {"run_id": 45953249331, "artifact": "raw43-b0ra-complete-proof"},
    {"run_id": 45955232997, "artifact": "raw43-b0la-complete-proof"},
    {"run_id": 46136565063, "artifact": "raw43-b1ra-complete-proof"},
    {"run_id": 46137497179, "artifact": "raw43-b1lb-complete-proof"},
    {"run_id": 46151063756, "artifact": "raw43-b1re-complete-proof"},
]

PENDING_ARTIFACTS = {
    "0lf": "raw43-extra-proof",
    "1lf": "raw43-extra-proof",
    "b1la": "raw43-b1la-complete-proof",
    "b1le": "raw43-b1le-complete-proof",
    "b0le": "raw43-b0le-complete-proof",
}


def run_id(value: str) -> int:
    n = int(value)
    if n <= 0:
        raise argparse.ArgumentTypeError("run id must be positive")
    return n


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    for key in PENDING_ARTIFACTS:
        ap.add_argument("--" + key, required=True, type=run_id)
    args = ap.parse_args()

    pins = list(STATIC)
    for key, artifact in PENDING_ARTIFACTS.items():
        pins.append({"run_id": getattr(args, key), "artifact": artifact})

    assert len(pins) == 23
    assert len({(p["run_id"], p["artifact"]) for p in pins}) == 23
    print(json.dumps(pins, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
