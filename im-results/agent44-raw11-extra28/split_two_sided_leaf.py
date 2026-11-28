#!/usr/bin/env python3
"""Split one frozen PhaseTree automata leaf into row-checked TwoSidedAutomata modules.

Input is an already-generated Lean module whose checked Tree is exactly one
`.automata <Cert>` leaf.  The rewrite preserves the literal PartialMachine and
literal certificate data, but places the two stacks and twelve trie rows in
separate modules and checks the twelve state/symbol rows independently.

The original target module is replaced by a tiny same-table wrapper exporting
the same `parent` and `safe` names expected by its importers.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path


PAIRS = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}
CLOSERS = {v: k for k, v in PAIRS.items()}


def balanced_expr(text: str, start: int) -> tuple[str, int]:
    while start < len(text) and text[start].isspace():
        start += 1
    if start >= len(text) or text[start] not in PAIRS:
        raise ValueError(f"expected balanced expression at offset {start}")
    stack: list[str] = []
    for i in range(start, len(text)):
        ch = text[i]
        if ch in PAIRS:
            stack.append(ch)
        elif ch in CLOSERS:
            if not stack or stack[-1] != CLOSERS[ch]:
                raise ValueError(f"unbalanced delimiter {ch!r} at offset {i}")
            stack.pop()
            if not stack:
                return text[start:i + 1], i + 1
    raise ValueError("unterminated balanced expression")


def split_top_level(text: str) -> list[str]:
    out: list[str] = []
    stack: list[str] = []
    start = 0
    for i, ch in enumerate(text):
        if ch in PAIRS:
            stack.append(ch)
        elif ch in CLOSERS:
            if not stack or stack[-1] != CLOSERS[ch]:
                raise ValueError(f"unbalanced delimiter {ch!r} in component")
            stack.pop()
        elif ch == "," and not stack:
            out.append(text[start:i].strip())
            start = i + 1
    if stack:
        raise ValueError("unterminated component")
    out.append(text[start:].strip())
    return out


def extract_parent_expr(source: str) -> str:
    marker = "def parent : PartialMachine :="
    pos = source.index(marker) + len(marker)
    return balanced_expr(source, pos)[0]


def extract_single_automata_cert(source: str) -> str:
    marker = "(.automata "
    starts = [m.start() for m in re.finditer(re.escape(marker), source)]
    if len(starts) != 1:
        raise ValueError(f"expected exactly one automata literal, found {len(starts)}")
    pos = starts[0] + len(marker)
    cert, end = balanced_expr(source, pos)
    tail = source[end:].lstrip()
    if not tail.startswith(")"):
        raise ValueError("automata literal is not closed immediately after certificate")
    return cert


def parse_cert(cert: str) -> tuple[str, str, list[str]]:
    if not (cert.startswith("⟨") and cert.endswith("⟩")):
        raise ValueError("certificate is not a Cert constructor")
    parts = split_top_level(cert[1:-1])
    if len(parts) != 3:
        raise ValueError(f"expected three Cert fields, got {len(parts)}")
    left, right, rows = parts
    if not (rows.startswith("#[") and rows.endswith("]")):
        raise ValueError("certificate states field is not an Array literal")
    row_parts = split_top_level(rows[2:-1])
    if len(row_parts) != 12:
        raise ValueError(f"expected twelve state/symbol rows, got {len(row_parts)}")
    return left, right, row_parts


def write_module(out: Path, name: str, imports: list[str], namespace: str, body: str) -> None:
    out.joinpath(name + ".lean").write_text(
        "".join(f"import {dep}\n" for dep in imports)
        + "set_option maxRecDepth 100000\n"
        + "set_option maxHeartbeats 0\n"
        + "set_option Elab.async false\n"
        + f"namespace {namespace}\n"
        + body.rstrip()
        + f"\nend {namespace}\n",
        encoding="utf-8",
    )


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: split_two_sided_leaf.py <target-module.lean>")
    target = Path(sys.argv[1]).resolve()
    source = target.read_text(encoding="utf-8")
    module = target.stem

    ns_match = re.search(r"^namespace\s+(BB6\.[A-Za-z0-9_]+)\s*$", source, re.M)
    if not ns_match:
        raise ValueError("target namespace not found")
    target_ns = ns_match.group(1)

    bounds = {int(x) for x in re.findall(r"WeightedBound\s+(\d+)", source)}
    if len(bounds) != 1:
        raise ValueError(f"expected one literal WeightedBound, found {sorted(bounds)}")
    bound = next(iter(bounds))

    parent_expr = extract_parent_expr(source)
    cert_expr = extract_single_automata_cert(source)

    # Ensure the checked Tree really is just the one automata leaf.  Replacing
    # a larger tree by the leaf theorem would be unsound.
    if not re.search(
        r"def\s+cert\w*\s*:\s*Tree\s*:=\s*\(\.automata\s+",
        source,
        re.S,
    ):
        raise ValueError("target automata literal is not the root of a checked Tree certificate")

    left, right, rows = parse_cert(cert_expr)
    out = target.parent
    companion = Path(__file__).resolve().with_name("TwoSidedAutomataRows.lean")
    if not companion.is_file():
        raise FileNotFoundError(companion)
    out.joinpath("TwoSidedAutomataRows.lean").write_bytes(companion.read_bytes())
    prefix = "Agent44Extra132Giant"
    proof_ns = "BB6.Agent44Extra132Giant"

    write_module(
        out, prefix + "Left", ["TwoSidedAutomata"],
        proof_ns,
        "def left : BB6.Agent4Automata.Stack := " + left,
    )
    write_module(
        out, prefix + "Right", ["TwoSidedAutomata"],
        proof_ns,
        "def right : BB6.Agent4Automata.Stack := " + right,
    )

    row_mods: list[str] = []
    for j, row in enumerate(rows):
        name = prefix + f"RowData{j:02}"
        row_mods.append(name)
        write_module(
            out, name, ["TwoSidedAutomata"],
            proof_ns,
            f"def row{j:02} : BB6.Agent1NGram.Trie := {row}",
        )

    data_name = prefix + "Data"
    imports = [prefix + "Left", prefix + "Right", *row_mods]
    data_body = (
        "open BB6.Agent4Automata\n"
        f"def table : PartialMachine := {parent_expr}\n"
        "def cert : BB6.Agent4Automata.Cert := "
        "⟨left,right,#["
        + ",".join(f"row{j:02}" for j in range(12))
        + "]⟩"
    )
    write_module(out, data_name, imports, proof_ns, data_body)

    checked_mods: list[str] = []
    for j in range(12):
        q = j // 2
        a = "true" if j % 2 else "false"
        name = prefix + f"RowCheck{j:02}"
        checked_mods.append(name)
        body = f"""open BB6.Agent4Automata
theorem row{j:02}_checked :
    (row cert ({q} : Fin 6) {a}).all
      (fun i => stateStepOK table cert ({q} : Fin 6) {a}
        (i/cert.right.edges.size) (i%cert.right.edges.size)) = true := by
  decide +kernel
#print axioms row{j:02}_checked
"""
        write_module(out, name, [data_name], proof_ns, body)

    proof_name = prefix + "Proof"
    rows_cases = "\n".join(f"  · exact row{j:02}_checked" for j in range(12))
    proof_body = f"""open BB6Coverage BB6.Agent13BlankDelay BB6.Agent4Automata
theorem allRows (q : Fin 6) (a : Bool) :
    (row cert q a).all
      (fun i => stateStepOK table cert q a
        (i/cert.right.edges.size) (i%cert.right.edges.size)) = true := by
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases a
{rows_cases}

theorem checked : check table cert = true :=
  BB6.Agent44TwoSidedRows.check_of_rows
    (by decide) (by decide) (by decide) (by decide) (by decide) allRows

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent4Automata.never table cert checked m hm

theorem weighted (B : Nat) : Cover (WeightedBound B) table :=
  .leaf _ fun m hm => weighted_never B m (never m hm)

#print axioms checked
#print axioms never
#print axioms weighted
"""
    write_module(
        out, proof_name,
        ["TwoSidedAutomataRows", data_name, *checked_mods],
        proof_ns, proof_body,
    )

    # Preserve the exact module/namespace/export interface expected by the rest
    # of the frozen Extra132 repair DAG.
    target.write_text(
        f"""import PhaseTree
import PhaseFrontier
import {proof_name}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace {target_ns}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree

def parent : PartialMachine := {parent_expr}

theorem safe : ∀ m, compatible parent m → WeightedBound {bound} m := by
  intro m hm
  have hEq : parent = BB6.Agent44Extra132Giant.table :=
    BB6.Agent47PhaseFrontier.sameTable_sound (by decide +kernel)
  rw [hEq] at hm
  exact Cover.sound (BB6.Agent44Extra132Giant.weighted {bound}) m hm

#print axioms safe
end {target_ns}
""",
        encoding="utf-8",
    )

    print(
        f"row-split {module}: bound={bound}, "
        f"left={len(left.encode())}, right={len(right.encode())}, "
        f"rows={[len(x.encode()) for x in rows]}, support={2+12+1+12+1}",
        flush=True,
    )


if __name__ == "__main__":
    main()
