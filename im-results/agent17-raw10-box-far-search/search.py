#!/usr/bin/env python3
"""Try BlockFAR on singleton projections of exact raw10 complement boxes.

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
EXPECTED_PARTITIONS = {
    (False, False): (34, 90_890_091_604_975),
    (True, False): (40, 90_890_091_604_350),
    (False, True): (35, 90_737_503_714_350),
    (True, True): (41, 90_737_503_713_725),
}
RAW10_BOX8_CYCLE_ROW = (8, 14, 11, 0, 17, 4, 9, 2, 23, 15, 10, 0)
# 25 is an experiment-only sentinel for a forced halt; 0 remains wildcard.
RAW10_BOX0_HALT_ROW = (8, 25, 11, 0, 0, 25, 0, 0, 0, 0, 0, 0)


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


def decode_row_value(value: int) -> int:
    # The encoded source rows reserve 0 for wildcard. Extra halt rows use 25
    # as a sentinel for the actual Fin 25 halt value 0.
    return 0 if value == 25 else value


def possible(box: list[list[int]], cube: list[tuple[int, int]]) -> bool:
    return all(decode_row_value(value) in box[slot] for slot, value in cube)


def pieces(box: list[list[int]], cube: list[tuple[int, int]]) -> list[list[list[int]]]:
    """Exact first-mismatch pieces used by BB6.Agent49Box.pieces."""
    current = [domain[:] for domain in box]
    out: list[list[list[int]]] = []
    for slot, raw_value in cube:
        value = decode_row_value(raw_value)
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
    parser.add_argument("--include-cycle", action="store_true",
                        help="subtract Agent50's 625-completion cycle table (use only after CI acceptance)")
    parser.add_argument("--include-halt", action="store_true",
                        help="subtract Agent50's 25^8 halt table (use only after CI acceptance)")
    parser.add_argument("--min-fixed", type=int, default=2,
                        help="skip boxes with fewer singleton ordinary moves")
    parser.add_argument("--max-boxes", type=int, default=41,
                        help="limit the number of boxes for a quick pilot")
    parser.add_argument("--rank-promising", action="store_true",
                        help="try boxes with more singleton ordinary moves and smaller mass first")
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--compile-timeout", type=int, default=900)
    parser.add_argument("--output", type=Path,
                        default=ROOT / ".tmp/agent17-raw10-box-far")
    args = parser.parse_args()
    if args.compile:
        args.generate = True

    rows = parse_rows()
    held_table = "_".join(
        code_to_move(rows[-1][2 * q]) + code_to_move(rows[-1][2 * q + 1])
        for q in range(6)
    )
    expected_held = "1RB0RD_1LC1LB_0LE1RA_0LC0RA_1LF1LD_1RD---"
    if held_table != expected_held:
        raise RuntimeError(f"Fin 25 move-code mapping mismatch: {held_table}")

    extra_rows = []
    if args.include_cycle:
        extra_rows.append(RAW10_BOX8_CYCLE_ROW)
    if args.include_halt:
        extra_rows.append(RAW10_BOX0_HALT_ROW)
    all_rows = rows + extra_rows
    boxes = reconstruct_boxes(all_rows)
    expected_boxes, expected_mass = EXPECTED_PARTITIONS[
        (args.include_cycle, args.include_halt)
    ]
    if len(boxes) != expected_boxes:
        raise RuntimeError(f"expected {expected_boxes} boxes, found {len(boxes)}")
    total_mass = sum(__import__("math").prod(map(len, box)) for box in boxes)
    if total_mass != expected_mass:
        raise RuntimeError(f"box mass mismatch: {total_mass} != {expected_mass}")

    args.output.mkdir(parents=True, exist_ok=True)
    generator = load_generator() if args.generate else None
    results = []
    indexed_boxes = list(enumerate(boxes))
    if args.rank_promising:
        indexed_boxes.sort(
            key=lambda item: (
                -len(singleton_projection(item[1])[1]),
                __import__("math").prod(map(len, item[1])),
                item[0],
            )
        )
    selected_boxes = indexed_boxes[:args.max_boxes]
    for i, box in selected_boxes:
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
            except (Exception, SystemExit) as exc:
                item["generator"] = "no-certificate"
                item["error"] = f"{type(exc).__name__}: {exc}"
                item["generator_log"] = log.getvalue()[-6000:]

            if args.compile and item["generator"] == "success":
                proof = outdir / "HeldBlockProof.lean"
                workdir = Path("/tmp") / f"agent17-raw10-box-{i:02d}"
                env = os.environ.copy()
                search_paths = [
                    str(outdir),
                    str(ROOT / "im-results/agent13-block-far"),
                    env.get("LEAN_PATH", ""),
                ]
                env["LEAN_PATH"] = os.pathsep.join(p for p in search_paths if p)
                command = [
                    sys.executable, str(COMPILER),
                    "--workdir", str(workdir),
                    "--jobs", str(args.jobs),
                    str(proof),
                ]
                try:
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
                except subprocess.TimeoutExpired as exc:
                    item["compiled"] = False
                    item["compile_error"] = f"timeout after {args.compile_timeout}s"
                except Exception as exc:
                    item["compiled"] = False
                    item["compile_error"] = f"{type(exc).__name__}: {exc}"
        results.append(item)
        reason = item.get("error", "")
        generator_tail = item.get("generator_log", "").strip().replace("\n", " | ")[-240:]
        print(
            f"box={i:02d} fixed={len(fixed_slots):2d} mass={mass} "
            f"generator={item['generator']} compiled={item['compiled']} table={table} "
            f"error={reason!r} tail={generator_tail!r}"
        )

    summary = {
        "encoded_cylinders": len(rows),
        "included_cycle": args.include_cycle,
        "included_halt": args.include_halt,
        "box_count": len(boxes),
        "total_box_mass": total_mass,
        "tested_boxes": len(results),
        "min_fixed": args.min_fixed,
        "rank_promising": args.rank_promising,
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
