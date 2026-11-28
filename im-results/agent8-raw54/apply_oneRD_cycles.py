#!/usr/bin/env python3
"""Apply exact side-cycle discovery candidates to a Raw54 E1=1RD tree.

This is deliberately an untrusted transformation.  It only substitutes
`["cycle", entry, period, direction, boundary]` for source open leaves whose
literal table code matches the lasso ledger.  The transformed tree is then
fed to generate_oneRD_bank_cut.py, whose Lean `bankCheck` replays every cycle.
All non-cycle entries remain explicit `open` residuals.
"""
from __future__ import annotations

import argparse
import ast
import json
from pathlib import Path


def read_lasso(path: Path) -> dict[str, list]:
    out: dict[str, list] = {}
    for lineno, raw in enumerate(path.read_text().splitlines(), 1):
        if not raw.strip():
            continue
        try:
            code, payload = raw.split("\t", 1)
        except ValueError as e:
            raise ValueError(f"{path}:{lineno}: expected TAB") from e
        item = ast.literal_eval(payload)
        if not isinstance(item, list) or not item:
            raise ValueError(f"{path}:{lineno}: malformed payload")
        if code in out:
            raise ValueError(f"{path}:{lineno}: duplicate code {code}")
        out[code] = item
    return out


def transform(t, ledger: dict[str, list], source_seen: list[str],
              residual_seen: list[str], cycle_seen: list[str]):
    kind = t[0]
    if kind == "open":
        code = t[1]
        source_seen.append(code)
        item = ledger.get(code, ["open"])
        if item[0] == "cycle":
            if len(item) != 5:
                raise ValueError((code, item))
            entry, period, right, boundary = item[1:]
            if not (isinstance(entry, int) and isinstance(period, int)
                    and period > 0 and isinstance(right, bool)
                    and isinstance(boundary, int)):
                raise ValueError((code, item))
            cycle_seen.append(code)
            return ["cycle", entry, period, right, boundary]
        residual_seen.append(code)
        return t
    if kind == "split":
        return [t[0], t[1], t[2],
                [transform(x, ledger, source_seen, residual_seen, cycle_seen)
                 for x in t[3]]]
    return t


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("tree", type=Path)
    ap.add_argument("open", type=Path)
    ap.add_argument("lasso", type=Path)
    ap.add_argument("out", type=Path)
    a = ap.parse_args()
    a.out.mkdir(parents=True, exist_ok=True)

    tree = json.loads(a.tree.read_text())
    original = a.open.read_text().splitlines()
    ledger = read_lasso(a.lasso)
    source_seen: list[str] = []
    residual_seen: list[str] = []
    cycle_seen: list[str] = []
    transformed = transform(tree, ledger, source_seen, residual_seen, cycle_seen)

    assert source_seen == original, (len(source_seen), len(original))
    assert len(source_seen) == 671, len(source_seen)
    unknown = sorted(set(ledger) - set(source_seen))
    assert not unknown, unknown[:10]

    (a.out / "tree.json").write_text(
        json.dumps(transformed, separators=(",", ":")) + "\n")
    (a.out / "open.txt").write_text(
        "".join(code + "\n" for code in residual_seen))
    summary = {
        "source_open_count": len(source_seen),
        "cycle_candidate_count": len(cycle_seen),
        "residual_open_count": len(residual_seen),
        "cycle_codes": cycle_seen,
    }
    (a.out / "cycle-transform-summary.json").write_text(
        json.dumps(summary, indent=2) + "\n")
    print(json.dumps({k: v for k, v in summary.items() if k != "cycle_codes"},
                     sort_keys=True))


if __name__ == "__main__":
    main()
