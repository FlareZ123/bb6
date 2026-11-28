#!/usr/bin/env python3
"""Factor the largest singleton TwoSidedAutomata leaf inside a frozen PhaseTree module.

The target may contain many leaf proofs.  This script selects the largest
`.automata <Cert>` literal, requires that its enclosing `def cert... : Tree`
is exactly that one automata leaf, and replaces only that cert/checked/safe
triple by a same-table theorem backed by row-split checking of the identical
literal certificate.  Sibling declarations stay untouched.

Usage:
  split_two_sided_leaf.py TARGET.lean TABLE
where TABLE is the exact 12-slot transition string for the selected cert.
"""
from __future__ import annotations

import os
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


def table_expr(table: str) -> str:
    t = table.replace("_", "")
    if len(t) != 36:
        raise ValueError(f"expected 12 three-character slots, got {len(t)} chars")
    toks = [t[i:i + 3] for i in range(0, 36, 3)]
    lines = ["def table : PartialMachine := fun s => match s.1.val, s.2 with"]
    for j, tok in enumerate(toks):
        if tok == "---":
            continue
        if not re.fullmatch(r"[01][LR][A-F]", tok):
            raise ValueError(f"bad table token {tok!r}")
        q, b = divmod(j, 2)
        write = "true" if tok[0] == "1" else "false"
        right = "true" if tok[1] == "R" else "false"
        nxt = ord(tok[2]) - ord("A")
        lines.append(
            f"  | {q},{str(bool(b)).lower()} => "
            f"some (some ⟨{write},{right},{nxt}⟩)"
        )
    lines.append("  | _,_ => none")
    return "\n".join(lines)


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
    if len(sys.argv) != 3:
        raise SystemExit("usage: split_two_sided_leaf.py TARGET.lean TABLE")
    target = Path(sys.argv[1]).resolve()
    literal_table = sys.argv[2]
    source = target.read_text(encoding="utf-8")

    # Select the exact largest automata literal.
    autos: list[tuple[int, int, int, str]] = []
    marker = "(.automata "
    for m in re.finditer(re.escape(marker), source):
        cert, end = balanced_expr(source, m.end())
        tail = source[end:].lstrip()
        if not tail.startswith(")"):
            raise ValueError("automata literal not closed after Cert")
        autos.append((len(cert.encode()), m.start(), end, cert))
    if not autos:
        raise ValueError("no automata literal found")
    autos.sort(reverse=True)
    cert_bytes, auto_start, cert_end, cert_expr = autos[0]
    min_cert_bytes = int(os.environ.get("TWOSIDED_SPLIT_MIN_CERT_BYTES", "1000000"))
    if cert_bytes < min_cert_bytes:
        raise ValueError(
            f"largest automata certificate unexpectedly small: {cert_bytes} < {min_cert_bytes}"
        )

    # Find the exact cert declaration whose Tree expression contains the giant.
    defs = list(re.finditer(r"^\s*def\s+(cert[A-Za-z0-9_]*)\s*:\s*Tree\s*:=\s*", source, re.M))
    candidates = [m for m in defs if m.start() < auto_start]
    if not candidates:
        raise ValueError("enclosing cert declaration not found")
    d = candidates[-1]
    cert_name = d.group(1)
    tree_expr, tree_end = balanced_expr(source, d.end())
    expected = "(.automata " + cert_expr + ")"
    compact = lambda s: re.sub(r"\s+", "", s)
    if compact(tree_expr) != compact(expected):
        raise ValueError(
            f"giant cert is not a singleton Tree leaf in {cert_name}; "
            "regenerate with RAW11_REPAIR_CERT_THRESHOLD=1"
        )

    suffix = cert_name[len("cert"):]
    checked_name = "checked" + suffix
    safe_name = "safe" + suffix

    checked = re.search(
        rf"^\s*theorem\s+{re.escape(checked_name)}\b", source[tree_end:], re.M
    )
    if not checked:
        raise ValueError(f"{checked_name} not found after {cert_name}")
    checked_start = tree_end + checked.start()

    safe = re.search(
        rf"^\s*theorem\s+{re.escape(safe_name)}\s*:\s*∀\s+m,\s*compatible\s+"
        rf"([A-Za-z0-9_]+)\s+m\s*→\s*WeightedBound\s+(\d+)\s+m\s*:=\s*",
        source[checked_start:],
        re.M,
    )
    if not safe:
        raise ValueError(f"{safe_name} header not found")
    safe_start = checked_start + safe.start()
    p_name = safe.group(1)
    bound = int(safe.group(2))

    # End the replaced block at the next declaration after the safe header.
    after_header = checked_start + safe.end()
    next_decl = re.search(r"^\s*(?:def|theorem|#print|end)\b", source[after_header:], re.M)
    block_end = len(source) if not next_decl else after_header + next_decl.start()

    left, right, rows = parse_cert(cert_expr)
    out = target.parent
    companion = Path(__file__).resolve().with_name("TwoSidedAutomataRows.lean")
    if not companion.is_file():
        raise FileNotFoundError(companion)
    out.joinpath("TwoSidedAutomataRows.lean").write_bytes(companion.read_bytes())

    prefix = os.environ.get("TWOSIDED_SPLIT_PREFIX", "Agent44Extra132Giant")
    proof_ns = os.environ.get("TWOSIDED_SPLIT_NAMESPACE", "BB6.Agent44Extra132Giant")

    write_module(out, prefix + "Left", ["TwoSidedAutomata"], proof_ns,
                 "def left : BB6.Agent4Automata.Stack := " + left + "\n#print axioms left")
    write_module(out, prefix + "Right", ["TwoSidedAutomata"], proof_ns,
                 "def right : BB6.Agent4Automata.Stack := " + right + "\n#print axioms right")

    row_mods: list[str] = []
    for j, row in enumerate(rows):
        name = prefix + f"RowData{j:02}"
        row_mods.append(name)
        write_module(out, name, ["TwoSidedAutomata"], proof_ns,
                     f"def row{j:02} : BB6.Agent1NGram.Trie := {row}\n#print axioms row{j:02}")

    data_name = prefix + "Data"
    write_module(
        out, data_name, ["PhaseTree", prefix + "Left", prefix + "Right", *row_mods], proof_ns,
        "open BB6.Agent4Automata BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree\n"
        f"{table_expr(literal_table)}\n"
        "def cert : BB6.Agent4Automata.Cert := ⟨left,right,#["
        + ",".join(f"row{j:02}" for j in range(12)) + "]⟩\n#print axioms cert",
    )

    checked_mods: list[str] = []
    for j in range(12):
        q, abit = divmod(j, 2)
        a = "true" if abit else "false"
        name = prefix + f"RowCheck{j:02}"
        checked_mods.append(name)
        write_module(
            out, name, [data_name], proof_ns,
            f"""open BB6.Agent4Automata
theorem row{j:02}_checked :
    (row cert ({q} : Fin 6) {a}).all
      (fun i => stateStepOK table cert ({q} : Fin 6) {a}
        (i/cert.right.edges.size) (i%cert.right.edges.size)) = true := by
  decide +kernel
#print axioms row{j:02}_checked
""",
        )

    proof_name = prefix + "Proof"
    row_cases = "\n".join(f"  · exact row{j:02}_checked" for j in range(12))
    write_module(
        out, proof_name, ["TwoSidedAutomataRows", data_name, *checked_mods],
        proof_ns,
        f"""open BB6Coverage BB6.Agent13BlankDelay BB6.Agent4Automata
theorem allRows (q : Fin 6) (a : Bool) :
    (row cert q a).all
      (fun i => stateStepOK table cert q a
        (i/cert.right.edges.size) (i%cert.right.edges.size)) = true := by
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases a
{row_cases}

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
""",
    )

    replacement = f"""theorem {safe_name} : ∀ m, compatible {p_name} m → WeightedBound {bound} m := by
  intro m hm
  have hEq : {p_name} = {proof_ns}.table :=
    BB6.Agent47PhaseFrontier.sameTable_sound (by decide +kernel)
  rw [hEq] at hm
  exact Cover.sound ({proof_ns}.weighted {bound}) m hm

"""
    patched = source[:d.start()] + replacement + source[block_end:]
    if not re.search(rf"^import\s+{re.escape(proof_name)}\s*$", patched, re.M):
        patched = f"import {proof_name}\n" + patched
    target.write_text(patched, encoding="utf-8")

    print(
        f"row-split {target.name}: cert={cert_name} safe={safe_name} "
        f"machine={p_name} bound={bound} cert_bytes={cert_bytes} "
        f"left={len(left.encode())} right={len(right.encode())} "
        f"rows={[len(x.encode()) for x in rows]} "
        f"remaining_automata={patched.count('(.automata ')}",
        flush=True,
    )


if __name__ == "__main__":
    main()
