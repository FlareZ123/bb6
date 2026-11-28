#!/usr/bin/env python3
"""Split the automata leaves of one generated PhaseTree aggregate into modules.

This is a proof-granularity transformation only.  Each companion repeats the
exact literal parent/child table and original certificate, checks it with the
same kernel checker, and exports the same safety statement.  The aggregate
reimports those safety theorems through sameTable_sound.  No certificate,
bound, or covered machine is changed.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

PAIRS = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}
CLOSERS = {v: k for k, v in PAIRS.items()}


def balanced(text: str, start: int) -> tuple[str, int]:
    while start < len(text) and text[start].isspace():
        start += 1
    if start >= len(text) or text[start] not in PAIRS:
        raise ValueError(f"expected balanced expression at {start}")
    stack: list[str] = []
    for i in range(start, len(text)):
        ch = text[i]
        if ch in PAIRS:
            stack.append(ch)
        elif ch in CLOSERS:
            if not stack or stack[-1] != CLOSERS[ch]:
                raise ValueError(f"unbalanced {ch!r} at {i}")
            stack.pop()
            if not stack:
                return text[start:i + 1], i + 1
    raise ValueError("unterminated balanced expression")


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: split_phase_automata_leaves.py TARGET.lean")
    target = Path(sys.argv[1]).resolve()
    text = target.read_text(encoding="utf-8")

    ns_match = re.search(r"^namespace\s+BB6\.([A-Za-z0-9_]+)\s*$", text, re.M)
    if not ns_match:
        raise ValueError("namespace not found")
    target_ns = ns_match.group(1)

    parent_match = re.search(
        r"^def parent\s*:\s*PartialMachine\s*:=\s*", text, re.M
    )
    if not parent_match:
        raise ValueError("parent definition missing")
    parent_expr, _ = balanced(text, parent_match.end())
    parent_def = f"def parent : PartialMachine := {parent_expr}\n"

    rows = []
    pattern = re.compile(
        r"^def\s+(cert([A-Za-z0-9_]+))\s*:\s*Tree\s*:=\s*\(\.automata\s*",
        re.M,
    )
    for match in pattern.finditer(text):
        cert_expr, cert_end = balanced(text, match.end())
        close = cert_end
        while close < len(text) and text[close].isspace() and text[close] != "\n":
            close += 1
        if close >= len(text) or text[close] != ")":
            raise ValueError(f"automata close missing for {match.group(1)}")
        tree_end = close + 1
        tree_start = text.rfind("(", match.start(), match.end())
        tree_expr = text[tree_start:tree_end]

        suffix = match.group(2)
        p_name = "p" + suffix
        checked_name = "checked" + suffix
        safe_name = "safe" + suffix

        p_matches = list(
            re.finditer(
                rf"^def\s+{re.escape(p_name)}\s*:=\s*(.+)$",
                text[:match.start()],
                re.M,
            )
        )
        if not p_matches:
            raise ValueError(f"{p_name} missing")
        p_expr = p_matches[-1].group(1).strip()

        checked_match = re.search(
            rf"^\s*theorem\s+{re.escape(checked_name)}\b[^\n]*$",
            text[tree_end:],
            re.M,
        )
        safe_match = re.search(
            rf"^\s*theorem\s+{re.escape(safe_name)}\b[^\n]*$",
            text[tree_end:],
            re.M,
        )
        if not checked_match or not safe_match:
            raise ValueError(f"checked/safe theorem missing for {suffix}")

        checked_start = tree_end + checked_match.start()
        checked_end = tree_end + checked_match.end()
        safe_start = tree_end + safe_match.start()
        safe_end = tree_end + safe_match.end()
        if safe_start < checked_start:
            raise ValueError(f"safe theorem precedes checked theorem for {suffix}")

        block_end = safe_end
        if block_end < len(text) and text[block_end] == "\n":
            block_end += 1
        safe_line = text[safe_start:safe_end].strip()
        signature = safe_line.split(":=", 1)[0].rstrip()

        rows.append(
            (
                match.start(),
                block_end,
                suffix,
                p_name,
                p_expr,
                match.group(1),
                tree_expr,
                text[checked_start:checked_end].strip(),
                safe_name,
                safe_line,
                signature,
                len(cert_expr.encode()),
            )
        )

    if not rows:
        raise ValueError("no automata leaves found")

    imports: list[str] = []
    replacements: list[tuple[int, int, str]] = []
    for index, row in enumerate(rows):
        (
            block_start,
            block_end,
            suffix,
            p_name,
            p_expr,
            cert_name,
            tree_expr,
            checked_line,
            safe_name,
            safe_line,
            signature,
            cert_bytes,
        ) = row
        module = f"Agent44Split{target_ns}Leaf{index:02d}"
        imports.append(module)

        companion = (
            "import PhaseTree\n"
            "import PhaseFrontier\n"
            "set_option maxHeartbeats 0\n"
            "set_option maxRecDepth 100000\n"
            f"namespace BB6.{module}\n"
            "open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree\n\n"
            f"{parent_def}\n"
            f"def {p_name} := {p_expr}\n\n"
            f"def {cert_name} : Tree := {tree_expr}\n"
            f"{checked_line}\n"
            f"{safe_line}\n"
            f"#print axioms {safe_name}\n"
            f"end BB6.{module}\n"
        )
        target.with_name(module + ".lean").write_text(companion, encoding="utf-8")

        replacement = (
            f"{signature} := by\n"
            "  intro m hm\n"
            f"  have hEq : {p_name} = BB6.{module}.{p_name} :=\n"
            "    BB6.Agent47PhaseFrontier.sameTable_sound (by decide +kernel)\n"
            "  rw [hEq] at hm\n"
            f"  exact BB6.{module}.{safe_name} m hm\n"
        )
        replacements.append((block_start, block_end, replacement))
        print(
            f"split {cert_name}: cert_bytes={cert_bytes} -> {module}",
            flush=True,
        )

    patched = text
    for start, end, replacement in reversed(replacements):
        patched = patched[:start] + replacement + patched[end:]
    patched = "".join(f"import {module}\n" for module in imports) + patched

    if "(.automata " in patched:
        raise ValueError("unexpected unsplit automata leaf remains")
    target.write_text(patched, encoding="utf-8")
    print(
        f"split_module={target.name} automata={len(rows)} "
        f"companions={len(imports)} bytes_before={len(text.encode())} "
        f"bytes_after={len(patched.encode())}",
        flush=True,
    )


if __name__ == "__main__":
    main()
