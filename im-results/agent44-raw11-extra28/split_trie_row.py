#!/usr/bin/env python3
"""Split one generated TwoSidedAutomata row into proof-sized trie chunks.

The input is a generated ...RowDataNN.lean module containing one literal
BB6.Agent1NGram.Trie definition.  The script preserves that exact trie by
rewriting the row as a shallow skeleton of literal chunk definitions, proves
each chunk's stateStepOK obligation independently with `decide +kernel`, and
replaces the corresponding ...RowCheckNN.lean with a wrapper around the
recomposed theorem.

This is a proof-granularity transformation.  It does not change the finite
automaton certificate, machine table, row membership, or weighted bound.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path


def parse_trie(text: str, start: int = 0) -> dict:
    while start < len(text) and text[start].isspace():
        start += 1
    if text.startswith(".empty", start):
        return {"s": start, "e": start + 6, "kind": "empty"}
    if text.startswith(".leaf", start):
        return {"s": start, "e": start + 5, "kind": "leaf"}
    if text.startswith("(.branch", start):
        left = parse_trie(text, start + len("(.branch"))
        right = parse_trie(text, left["e"])
        end = right["e"]
        while end < len(text) and text[end].isspace():
            end += 1
        if end >= len(text) or text[end] != ")":
            raise ValueError(f"unterminated branch at offset {start}")
        return {
            "s": start,
            "e": end + 1,
            "kind": "branch",
            "left": left,
            "right": right,
        }
    raise ValueError(f"unrecognized trie at offset {start}: {text[start:start+40]!r}")


def path_index_expr(bits: list[int]) -> str:
    # Low-bit trie: first branch bit is the least-significant bit.  Writing the
    # index in the exact nested form makes the final all_branch composition
    # definitionally match, avoiding expensive arithmetic normalization.
    expr = "i"
    for bit in reversed(bits):
        expr = f"(2*({expr})+{bit})"
    return expr


def main() -> None:
    if len(sys.argv) not in (2, 3):
        raise SystemExit("usage: split_trie_row.py ROWDATANN.lean [DEPTH]")
    target = Path(sys.argv[1]).resolve()
    depth_limit = int(sys.argv[2]) if len(sys.argv) == 3 else 3
    if depth_limit < 1 or depth_limit > 8:
        raise ValueError("depth must be between 1 and 8")

    source = target.read_text(encoding="utf-8")
    module = target.stem
    m = re.fullmatch(r"(.+)RowData(\d\d)", module)
    if not m:
        raise ValueError(f"unexpected row-data module name: {module}")
    root_module = m.group(1)
    row_index = int(m.group(2))
    row_name = f"row{row_index:02d}"
    q, abit = divmod(row_index, 2)
    a = "true" if abit else "false"

    ns_match = re.search(r"^namespace\s+(BB6\.[A-Za-z0-9_]+)\s*$", source, re.M)
    if not ns_match:
        raise ValueError("namespace not found")
    cert_ns = ns_match.group(1)

    row_match = re.search(
        rf"^def\s+{re.escape(row_name)}\s*:\s*BB6\.Agent1NGram\.Trie\s*:=\s*",
        source,
        re.M,
    )
    if not row_match:
        raise ValueError(f"{row_name} literal definition not found")
    literal_start = row_match.end()
    literal_line_end = source.find("\n", literal_start)
    if literal_line_end < 0:
        literal_line_end = len(source)
    literal = source[literal_start:literal_line_end].strip()
    root = parse_trie(literal)
    if root["e"] != len(literal):
        raise ValueError("row literal contains trailing data")

    out = target.parent
    split_prefix = f"{root_module}Row{row_index:02d}Split"
    split_ns = f"BB6.{split_prefix}"
    chunks: list[tuple[list[int], dict]] = []

    def collect(node: dict, depth: int, bits: list[int]) -> str:
        if depth == depth_limit or node["kind"] != "branch":
            idx = len(chunks)
            chunks.append((bits, node))
            return f"{split_ns}.chunk{idx:02d}"
        left = collect(node["left"], depth + 1, bits + [0])
        right = collect(node["right"], depth + 1, bits + [1])
        return f"(BB6.Agent1NGram.Trie.branch {left} {right})"

    skeleton = collect(root, 0, [])
    if len(chunks) < 2:
        raise ValueError("requested split produced fewer than two chunks")

    chunk_data_modules: list[str] = []
    chunk_check_modules: list[str] = []

    for idx, (bits, node) in enumerate(chunks):
        data_module = f"{split_prefix}Data{idx:02d}"
        check_module = f"{split_prefix}Check{idx:02d}"
        chunk_data_modules.append(data_module)
        chunk_check_modules.append(check_module)
        body = literal[node["s"]:node["e"]]

        out.joinpath(data_module + ".lean").write_text(
            "import TwoSidedAutomata\n"
            f"namespace {split_ns}\n"
            f"def chunk{idx:02d} : BB6.Agent1NGram.Trie := {body}\n"
            f"#print axioms chunk{idx:02d}\n"
            f"end {split_ns}\n",
            encoding="utf-8",
        )

        iexpr = path_index_expr(bits)
        out.joinpath(check_module + ".lean").write_text(
            f"import {root_module}Data\n"
            f"namespace {split_ns}\n"
            "open BB6.Agent4Automata\n"
            f"theorem checked{idx:02d} : chunk{idx:02d}.all "
            "(fun i => stateStepOK "
            f"{cert_ns}.table {cert_ns}.cert ({q} : Fin 6) {a} "
            f"(({iexpr})/{cert_ns}.cert.right.edges.size) "
            f"(({iexpr})%{cert_ns}.cert.right.edges.size)) = true := by\n"
            "  decide +kernel\n"
            f"#print axioms checked{idx:02d}\n"
            f"end {split_ns}\n",
            encoding="utf-8",
        )

    # Preserve the exact row by a shallow skeleton of opaque literal chunks.
    target.write_text(
        "".join(f"import {name}\n" for name in chunk_data_modules)
        + f"namespace {cert_ns}\n"
        + f"def {row_name} : BB6.Agent1NGram.Trie := {skeleton}\n"
        + f"#print axioms {row_name}\n"
        + f"end {cert_ns}\n",
        encoding="utf-8",
    )

    def proof_term(node: dict, depth: int, cursor: list[int]) -> str:
        if depth == depth_limit or node["kind"] != "branch":
            idx = cursor[0]
            cursor[0] += 1
            return f"{split_ns}.checked{idx:02d}"
        left = proof_term(node["left"], depth + 1, cursor)
        right = proof_term(node["right"], depth + 1, cursor)
        return f"(all_branch {left} {right})"

    term = proof_term(root, 0, [0])
    split_check_module = f"{split_prefix}Assembled"
    out.joinpath(split_check_module + ".lean").write_text(
        "".join(f"import {name}\n" for name in chunk_check_modules)
        + f"import {root_module}Data\n"
        + "set_option maxRecDepth 100000\n"
        + "set_option maxHeartbeats 0\n"
        + f"namespace {split_ns}\n"
        + "open BB6.Agent4Automata\n"
        + "theorem all_branch {e o : BB6.Agent1NGram.Trie} {f : Nat → Bool}\n"
        + "    (he : e.all (fun i => f (2*i)) = true)\n"
        + "    (ho : o.all (fun i => f (2*i+1)) = true) :\n"
        + "    (BB6.Agent1NGram.Trie.branch e o).all f = true := by\n"
        + "  simp only [BB6.Agent1NGram.Trie.all, Bool.and_eq_true]\n"
        + "  exact ⟨he,ho⟩\n\n"
        + f"theorem {row_name}_checked :\n"
        + f"    (BB6.Agent4Automata.row {cert_ns}.cert ({q} : Fin 6) {a}).all\n"
        + f"      (fun i => stateStepOK {cert_ns}.table {cert_ns}.cert ({q} : Fin 6) {a}\n"
        + f"        (i/{cert_ns}.cert.right.edges.size) "
        + f"(i%{cert_ns}.cert.right.edges.size)) = true := by\n"
        + f"  change {cert_ns}.{row_name}.all _ = true\n"
        + f"  change ({skeleton}).all _ = true\n"
        + f"  exact {term}\n"
        + f"#print axioms {row_name}_checked\n"
        + f"end {split_ns}\n",
        encoding="utf-8",
    )

    # Keep the module name expected by the parent Proof source.
    original_check_module = f"{root_module}RowCheck{row_index:02d}"
    out.joinpath(original_check_module + ".lean").write_text(
        f"import {split_check_module}\n"
        f"namespace {cert_ns}\n"
        "open BB6.Agent4Automata\n"
        + f"theorem {row_name}_checked :\n"
        + f"    (row cert ({q} : Fin 6) {a}).all\n"
        + f"      (fun i => stateStepOK table cert ({q} : Fin 6) {a}\n"
        + "        (i/cert.right.edges.size) (i%cert.right.edges.size)) = true :=\n"
        + f"  {split_ns}.{row_name}_checked\n"
        + f"#print axioms {row_name}_checked\n"
        + f"end {cert_ns}\n",
        encoding="utf-8",
    )

    print(
        f"trie-split {module}: row={row_index} depth={depth_limit} "
        f"chunks={len(chunks)} original_bytes={len(literal.encode())} "
        f"chunk_bytes={[node['e']-node['s'] for _, node in chunks]}",
        flush=True,
    )


if __name__ == "__main__":
    main()
