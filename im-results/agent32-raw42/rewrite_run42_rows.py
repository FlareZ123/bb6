#!/usr/bin/env python3
"""Rewrite one frozen Raw42 list-BiDFA Run witness into row-split FastBiDFA modules.

The certificate is converted by the existing exact list->trie converter.  This
changes only representation/proof granularity: the same transition table and
the same finite state/edge sets are checked, with the 12 state/symbol rows
kernel-reduced independently.
"""
import re
import sys
from pathlib import Path

from convert_bidfa import convert


root = Path(sys.argv[1])
branch = sys.argv[2]
leaf = int(sys.argv[3])
stem = f"Raw42{branch}Run{leaf}"
path = root / f"{stem}.lean"
fast = convert(path.read_text())

outer_m = re.search(r"^namespace ([^\n]+)$", fast, re.M)
leaf_m = re.search(r"^namespace Leaf(\d+)$", fast, re.M)
open_m = re.search(r"^open ([^\n]+)$", fast, re.M)
assert outer_m and leaf_m and open_m
assert int(leaf_m.group(1)) == leaf
outer = outer_m.group(1)
leaf_ns = f"Leaf{leaf}"
opens = open_m.group(1)

data_start = fast.index("-- ", leaf_m.end())
checked_start = fast.index("theorem checked", data_start)
definitions = fast[data_start:checked_start].rstrip()
assert "def table : PartialMachine" in definitions
assert "def cert : FastCert" in definitions

def write(name, imports, body):
    root.joinpath(name + ".lean").write_text(
        "".join(f"import {dep}\n" for dep in imports)
        + "set_option maxRecDepth 100000\n"
        + "set_option maxHeartbeats 0\n"
        + "set_option Elab.async false\n"
        + f"namespace {outer}\n"
        + f"open {opens}\n"
        + f"namespace {leaf_ns}\n"
        + body.rstrip()
        + f"\nend {leaf_ns}\nend {outer}\n"
    )

data_mod = stem + "Data"
write(data_mod, ["FastBiDFARows"], definitions)

rows = []
for j in range(12):
    q = j // 2
    a = str(bool(j % 2)).lower()
    row_mod = stem + f"Row{j:02}"
    rows.append(row_mod)
    write(
        row_mod,
        [data_mod],
        (
            f"theorem row{j:02}_checked : (row cert ({q} : Fin 6) {a}).all "
            f"(fun i => stateStepOK table cert ({q} : Fin 6) {a} "
            f"(i/cert.nr) (i%cert.nr)) = true := by decide"
        ),
    )

body = """theorem allRows (q : Fin 6) (a : Bool) :
    (row cert q a).all
      (fun i => stateStepOK table cert q a (i/cert.nr) (i%cert.nr)) = true := by
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases a
""" + "\n".join(f"  · exact row{j:02}_checked" for j in range(12)) + """
theorem checked : check table cert = true :=
  BB6.Agent32Raw42FastBiDFA.check_of_rows (by decide) (by decide) (by decide) allRows
theorem live (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never table cert checked m hm
#print axioms live
"""
write(stem, rows, body)
print(f"row-split {stem}: Data + {len(rows)} rows + final")
