"""Emit a row-split version of one Raw42 asymmetric N-gram certificate.

The mathematical certificate is identical to emit_ngram42.py: the only change is
proof/module granularity.  Keeping each state/symbol row in its own module lets
Lean kernel-check very large certificates without one monolithic reduction.
"""
from emit_ngram42 import saturate


def emit(root, branch, leaf, table, left_width, right_width):
    edges, rows = saturate(table, left_width, right_width)
    mod = f"Raw42{branch}NGram{leaf}"
    ns = f"BB6.Agent32Raw42{branch}.NGram"
    leaf_ns = f"Leaf{leaf}"

    def write(name, imports, body):
        root.joinpath(name + ".lean").write_text(
            "".join(f"import {dep}\n" for dep in imports)
            + "set_option maxRecDepth 100000\n"
            + "set_option maxHeartbeats 0\n"
            + "set_option Elab.async false\n"
            + f"namespace {ns}\n"
            + "open BB6Coverage BB6.Agent1NGram BB6.Agent32AsymNGram\n"
            + f"namespace {leaf_ns}\n"
            + "\n".join(body)
            + f"\nend {leaf_ns}\nend {ns}\n"
        )

    nodes = {}
    defs = []

    def trie(values):
        values = sorted(set(values))
        if not values:
            return ".empty"
        if values == [0]:
            return ".leaf"
        lo = trie([x // 2 for x in values if x % 2 == 0])
        hi = trie([x // 2 for x in values if x % 2 == 1])
        key = (lo, hi)
        if key not in nodes:
            name = f"t{len(defs)}"
            nodes[key] = name
            defs.append(f"def {name} : Trie := .branch {lo} {hi}")
        return nodes[key]

    left = trie(edges[0])
    right = trie(edges[1])
    state_rows = [trie(row) for row in rows]

    compact = table.replace("_", "")
    moves = ["def table : PartialMachine := fun s => match s.1.val,s.2 with"]
    for j in range(12):
        tr = compact[3 * j:3 * j + 3]
        if tr == "---":
            value = "none"
        else:
            value = (
                "some (some ⟨"
                + str(tr[0] == "1").lower()
                + ","
                + str(tr[1] == "R").lower()
                + ","
                + str(ord(tr[2]) - ord("A"))
                + "⟩)"
            )
        moves.append(f"  | {j // 2},{str(bool(j % 2)).lower()} => {value}")
    moves.append("  | _,_ => none")

    data = mod + "Data"
    write(
        data,
        ["AsymNGram"],
        [
            *defs,
            *moves,
            (
                "def cert : BB6.Agent32AsymNGram.Cert := "
                f"⟨{left_width - 1},{right_width - 1},{left},{right},"
                f"#[{','.join(state_rows)}]⟩"
            ),
        ],
    )

    row_modules = []
    for j in range(12):
        row_mod = mod + f"Row{j:02}"
        row_modules.append(row_mod)
        q = j // 2
        a = str(bool(j % 2)).lower()
        write(
            row_mod,
            [data],
            [
                (
                    f"theorem row{j:02}_checked : "
                    f"(row cert {q} {a}).all (fun i =>\n"
                    f"    stateStepOK table cert {q} {a} "
                    "(i/2^(cert.nR+1)) (i%2^(cert.nR+1))) = true := by decide"
                )
            ],
        )

    final = [
        "theorem allRows (q : Fin 6) (a : Bool) :",
        "    (row cert q a).all (fun i =>",
        "      stateStepOK table cert q a (i/2^(cert.nR+1)) (i%2^(cert.nR+1))) = true := by",
        "  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega",
        "  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl",
        "  all_goals cases a",
        *(f"  · exact row{j:02}_checked" for j in range(12)),
        "theorem checked : check table cert = true :=",
        "  check_of_rows (by decide) (by decide) (by decide) allRows",
        "theorem live (m : Machine) (hm : compatible table m) : NeverHalts m :=",
        "  never table cert checked m hm",
        "#print axioms live",
    ]
    write(mod, row_modules, final)
    return mod
