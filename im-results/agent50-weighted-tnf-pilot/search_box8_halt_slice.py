#!/usr/bin/env python3
"""Explore the 24 F1=halt completions of raw10 base box 8.

The other 576 completions of this 600-element box have all 12 transitions
defined and are therefore nonhalting by convention. Three of the 24 halt
quickly; F0=0RC has a short exact cycle. The remaining 20 are sent to the
existing BlockFAR generator as individual complete tables.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import time

ROOT = Path(__file__).resolve().parents[2]
GENERATOR_PATH = ROOT / "im-results/agent13-block-far/generate.py"
BASE_ROWS = "1RB0RD_1LC1LB_0LE1RA_0LC0RA_1LF1LD".split("_")
MASK = (1 << 64) - 1
HALTING_CODES = {12, 22, 24}
CYCLE_CODE = 10


def move_label(code: int) -> str:
    if code == 0:
        return "---"
    i = code - 1
    write = (i % 4) // 2
    direction = "R" if i % 2 else "L"
    state = chr(ord("A") + i // 4)
    return f"{write}{direction}{state}"


def move_from_code(code: int):
    if code == 0:
        return None
    i = code - 1
    return ((i % 4) // 2, i % 2 == 1, i // 4)


def table_for(f0_code: int) -> str:
    return "_".join(BASE_ROWS + [move_label(f0_code) + "---"])


def parse_table(table: str):
    tokens = [table.split("_")[q][i:i + 3] for q in range(6) for i in (0, 3)]
    moves = []
    for token in tokens:
        if token == "---":
            moves.append(None)
        else:
            moves.append((int(token[0]), token[1] == "R", ord(token[2]) - ord("A")))
    return moves


def splitmix64(x: int) -> int:
    x = (x + 0x9e3779b97f4a7c15) & MASK
    z = x
    z = ((z ^ (z >> 30)) * 0xbf58476d1ce4e5b9) & MASK
    z = ((z ^ (z >> 27)) * 0x94d049bb133111eb) & MASK
    return z ^ (z >> 31)


def zpos(position: int) -> int:
    return splitmix64(position & MASK)


def configuration_at(moves, count: int):
    ones = set()
    state = 0
    head = 0
    for _ in range(count):
        move = moves[2 * state + (1 if head in ones else 0)]
        if move is None:
            return None
        write, right, next_state = move
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += 1 if right else -1
        state = next_state
    return state, head, frozenset(ones)


def simulate(moves, limit: int):
    ones = set()
    tape_hash = 0
    state = 0
    head = 0
    steps = 0
    max_abs_head = 0
    seen = {(state, head, tape_hash): 0}
    while True:
        move = moves[2 * state + (1 if head in ones else 0)]
        if move is None:
            return {
                "status": "halt",
                "steps": steps,
                "max_abs_head": max_abs_head,
                "ones": len(ones),
            }
        if steps == limit:
            return {
                "status": "survive",
                "steps": steps,
                "max_abs_head": max_abs_head,
                "ones": len(ones),
            }
        write, right, next_state = move
        old = 1 if head in ones else 0
        if write != old:
            tape_hash ^= zpos(head)
            if write:
                ones.add(head)
            else:
                ones.remove(head)
        head += 1 if right else -1
        state = next_state
        steps += 1
        max_abs_head = max(max_abs_head, abs(head))
        key = (state, head, tape_hash)
        if key in seen:
            start = seen[key]
            replay = configuration_at(moves, start)
            if replay == (state, head, frozenset(ones)):
                return {
                    "status": "cycle",
                    "steps": steps,
                    "cycle_start": start,
                    "cycle_length": steps - start,
                    "max_abs_head": max_abs_head,
                    "ones": len(ones),
                }
        else:
            seen[key] = steps


def load_generator():
    spec = importlib.util.spec_from_file_location("agent13_blockfar_generate", GENERATOR_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load generator: {GENERATOR_PATH}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def generate_unique(generator, table: str, out_dir: Path, f0_code: int):
    generator.generate(table, out_dir)
    tag = f"Box8F0{f0_code:02d}"
    packed = out_dir / "HeldBlockPacked.lean"
    proof = out_dir / "HeldBlockProof.lean"
    packed_text = packed.read_text(encoding="utf8")
    proof_text = proof.read_text(encoding="utf8")
    packed_text = packed_text.replace("BB6BlockFAR.Held", f"BB6BlockFAR.{tag}")
    proof_text = proof_text.replace("HeldBlockPacked", f"{tag}Packed")
    proof_text = proof_text.replace("BB6BlockFAR.Held", f"BB6BlockFAR.{tag}")
    packed_name = out_dir / f"{tag}Packed.lean"
    proof_name = out_dir / f"{tag}Proof.lean"
    packed_name.write_text(packed_text, encoding="utf8")
    proof_name.write_text(proof_text, encoding="utf8")
    packed.unlink()
    proof.unlink()
    return [packed_name.name, proof_name.name]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path(".tmp/agent50-box8-halt-slice"))
    parser.add_argument("--simulation-limit", type=int, default=1_000_000)
    parser.add_argument("--limit", type=int, default=0, help="limit number of F0 codes tested; 0 means all")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    generator = load_generator()
    codes = [c for c in range(1, 25) if c not in HALTING_CODES and c != CYCLE_CODE]
    if args.limit:
        codes = codes[:args.limit]
    results = []
    started = time.time()
    for code in codes:
        table = table_for(code)
        simulation = simulate(parse_table(table), args.simulation_limit)
        entry = {
            "f0_code": code,
            "f0_move": move_label(code),
            "table": table,
            "simulation": simulation,
        }
        try:
            modules = generate_unique(generator, table, args.output / f"f0_{code:02d}", code)
            entry["generator"] = "success"
            entry["modules"] = modules
        except Exception as exc:
            entry["generator"] = "failed"
            entry["error"] = f"{type(exc).__name__}: {exc}"
        results.append(entry)
        print(json.dumps(entry, sort_keys=True), flush=True)

    summary = {
        "box_index": 8,
        "box_table": "1RB0RD_1LC1LB_0LE1RA_0LC0RA_1LF1LD_------",
        "box_domain_sizes": [1] * 10 + [24, 25],
        "box_mass": 600,
        "fully_defined_completions": 576,
        "f1_halt_completions": 24,
        "known_halting_f0_codes": sorted(HALTING_CODES),
        "known_cycle_f0_code": CYCLE_CODE,
        "generator_tested_f0_codes": codes,
        "simulation_limit": args.simulation_limit,
        "elapsed_seconds": time.time() - started,
        "results": results,
    }
    (args.output / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf8")
    print(json.dumps({k: v for k, v in summary.items() if k != "results"}, sort_keys=True))


if __name__ == "__main__":
    main()
