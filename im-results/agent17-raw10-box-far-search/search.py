#!/usr/bin/env python3
"""Try BlockFAR on singleton projections of the 34 exact raw10 complement boxes.

Run from repository root:
  python im-results/agent17-raw10-box-far-search/search.py
  python im-results/agent17-raw10-box-far-search/search.py --generate --min-fixed 6
  python im-results/agent17-raw10-box-far-search/search.py --generate --compile --min-fixed 6

The box decomposition is reconstructed from Raw10Encoded.lean using the same
first-mismatch subtraction as BB6.Agent49Box.subtractMany. No 25**10 completion
enumeration is performed.
"""
from __future__ import annotations

import argparse
import contextlib
import importlib.util
import io
import json
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
ENCODED = ROOT / "im-results/agent49-box-complement/Raw10Encoded.lean"
GENERATOR = ROOT / "im-results/agent13-block-far/generate.py"
COMPILER = ROOT / "tools/lean_compile_closure.py"
EXPECTED_BOXES = 34
EXPECTED_MASS = 90_890_091_604_975


def parse_rows() -> list[tuple[int, ...]]:
    source = ENCODED.read_text(encoding="utf-8")
    start = source.index("def rows :")
    end = source.index("def slots :", start)
    block = source[start:end]
    rows = []
    for match in re.finditer(r"\[([0-9,\s]+)\]", block):
        row = tuple(int(x.strip()) for x in match.group(1).split(","))
        if len(row) == 12:
            rows.append(row)
    if len(rows) != 66:
        raise RuntimeError(f"expected 66 encoded cylinders, found {len(rows)}")
    return rows


def live(box: list[list[int]]) -> bool:
    return all(domain for domain in box)


def possible(box: list[list[int]], cube: list[tuple[int, int]]) -> bool:
    return all(value in box[slot] for slot, value in cube)


def pieces(box: list[list[int]], cube: list[tuple[int, int]]) -> list[list[list[int]]]:
    """Exact first-mismatch pieces used by BB6.Agent49Box.pieces."""
    current = [domain[:] for domain in box]
    out: list[list[list[int]]] = []
    for slot, value in cube:
        rejected = [domain[:] for domain in current]
        rejected[slot] = [x for x in rejected[slot] if x != value]
        if live(rejected):
            out.append(rejected)
        current = [domain[:] for domain in current]
        current[slot] = [x for x in current[slot] if x == value]
        if not live(current):
            break
    return out


def subtract(box: list[list[int]], cube: list[tuple[int, int]]) -> list[list[list[int]]]:
    if not possible(box, cube):
        return [[domain[:] for domain in box]]
    return [piece for piece in pieces(box, cube) if live(piece)]


def reconstruct_boxes(rows: list[tuple[int, ...]]) -> list[list[list[int]]]:
    base = [
        [8] if slot == 0 else [11] if slot == 2 else list(range(25))
        for slot in range(12)
    ]
    boxes = [base]
    for row in rows:
        cube = [(slot, value) for slot, value in enumerate(row) if value != 0]
        next_boxes = []
        for box in boxes:
            next_boxes.extend(subtract(box, cube))
        boxes = next_boxes
    return boxes


def code_to_move(code: int) -> str:
    """Fin 25 encoding: 0 is wildcard/halt; 1..24 are q,w,dir ordered."""
    if code == 0:
        return "---"
    i = code - 1
    state = i // 4
    write = (i % 4) // 2
    right = i % 2
    return f"{write}{'R' if right else 'L'}{chr(ord('A') + state)}"


def singleton_projection(box: list[list[int]]) -> tuple[str, list[int]]:
    # Slot order is A0,A1,B0,B1,...,F0,F1.
    # A singleton halt is deliberately left undefined too: the projection is
    # weaker than the box, so every box completion still extends it.
    codes = [
        domain[0] if len(domain) == 1 and domain[0] != 0 else 0
        for domain in box
    ]
    table = "_".join(
        code_to_move(codes[2 * q]) + code_to_move(codes[2 * q + 1])
        for q in range(6)
    )
    fixed_slots = [i for i, code in enumerate(codes) if code != 0]
    return table, fixed_slots


def load_generator():
    spec = importlib.util.spec_from_file_location("agent13_blockfar_generator", GENERATOR)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load generator at {GENERATOR}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--generate", action="store_true",
                        help="run Agent13's existing BlockFAR generator for each projection")
    parser.add_argument("--compile", action="store_true",
                        help="compile every generated certificate with lean_compile_closure.py")
    parser.add_argument("--min-fixed", type=int, default=2,
                        help="skip boxes with fewer singleton ordinary moves")
    parser.add_argument("--max-boxes", type=int, default=EXPECTED_BOXES,
                        help="limit the number of boxes for a quick pilot")
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--compile-timeout", type=int, default=900)
    parser.add_argument("--output", type=Path,
                        default=Path("/tmp/agent17-raw10-box-far"))
    args = parser.parse_args()
    if args.compile:
        args.generate = True

    rows = parse_rows()
    boxes = reconstruct_boxes(rows)
    if len(boxes) != EXPECTED_BOXES:
        raise RuntimeError(f"expected {EXPECTED_BOXES} boxes, found {len(boxes)}")
    total_mass = sum(__import__("math").prod(map(len, box)) for box in boxes)
    if total_mass != EXPECTED_MASS:
        raise RuntimeError(f"box mass mismatch: {total_mass} != {EXPECTED_MASS}")

    args.output.mkdir(parents=True, exist_ok=True)
    generator = load_generator() if args.generate else None
    results = []
    for i, box in enumerate(boxes[:args.max_boxes]):
        table, fixed_slots = singleton_projection(box)
        mass = __import__("math").prod(map(len, box))
        item = {
            "box": i,
            "mass": mass,
            "domain_sizes": [len(domain) for domain in box],
            "singleton_ordinary_slots": fixed_slots,
            "fixed_count": len(fixed_slots),
            "table": table,
            "generator": "not-run",
            "compiled": None,
        }
        if args.generate and len(fixed_slots) >= args.min_fixed:
            outdir = args.output / f"box_{i:02d}"
            log = io.StringIO()
            try:
                with contextlib.redirect_stdout(log):
                    generator.generate(table, outdir)
                item["generator"] = "success"
                item["generator_log"] = log.getvalue()
                if args.compile:
                    proof = outdir / "HeldBlockProof.lean"
                    workdir = Path("/tmp") / f"agent17-raw10-box-{i:02d}"
                    env = os.environ.copy()
                    search = str(ROOT / "im-results/agent13-block-far")
                    env["LEAN_PATH"] = os.pathsep.join(
                        p for p in (search, env.get("LEAN_PATH", "")) if p
                    )
                    command = [
                        sys.executable, str(COMPILER),
                        "--workdir", str(workdir),
                        "--jobs", str(args.jobs),
                        str(proof),
                    ]
                    run = subprocess.run(
                        command, cwd=ROOT, env=env, text=True,
                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                        timeout=args.compile_timeout,
                    )
                    item["compile_returncode"] = run.returncode
                    item["compile_log"] = run.stdout[-12000:]
                    item["compiled"] = (
                        run.returncode == 0
                        and not re.search(r"sorryAx|native_decide", run.stdout)
                    )
            except Exception as exc:  # a failed projection is an open box, not a crash
                item["generator"] = "no-certificate"
                item["error"] = f"{type(exc).__name__}: {exc}"
                item["generator_log"] = log.getvalue()[-6000:]
        results.append(item)
        print(
            f"box={i:02d} fixed={len(fixed_slots):2d} mass={mass} "
            f"generator={item['generator']} compiled={item['compiled']} table={table}"
        )

    summary = {
        "encoded_cylinders": len(rows),
        "box_count": len(boxes),
        "total_box_mass": total_mass,
        "tested_boxes": len(results),
        "min_fixed": args.min_fixed,
        "generated": sum(x["generator"] == "success" for x in results),
        "compiled": sum(x["compiled"] is True for x in results),
        "results": results,
    }
    (args.output / "summary.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8"
    )
    print(
        f"summary: boxes={len(boxes)} mass={total_mass} "
        f"tested={len(results)} generated={summary['generated']} "
        f"compiled={summary['compiled']}"
    )


if __name__ == "__main__":
    main()
