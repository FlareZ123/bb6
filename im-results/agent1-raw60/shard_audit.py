"""Memory-bounded emission of exhaustive TNF audit trees.

Every chunk uses the existing zipCheck; splitting only changes proof
organization. No candidate is dropped and no new Lean axiom is introduced.
"""
from itertools import product

def emit_shards(node, p_expr, kname, cname, mod, *, B, bname, build, emit, stats, slot, move, moves, threshold=300):
    def size(node):
        return 1 + sum(map(size, node[3])) if node[0] == "split" else 1

    def leaf(n, p, kn, cn):
        return f"\ndef {kn} (h : Exceptions) : Audit := {build(n)}\ntheorem {cn} (h : Exceptions) : zipCheck {B} ({p}) ({kn} h) = true := by rfl\n"

    def go(node, p_expr, kname, cname, mod):
        if size(node) <= threshold or node[0] != "split":
            emit(mod, [bname], leaf(node, p_expr, kname, cname))
            return [mod]
        stats["split"] += 1
        _, nn, ss, children = node
        assert len(children) == 24
        names, checknames, depmods, files, small = [], [], [], [], []
        chunk = 0

        def flush():
            nonlocal small, chunk
            if not small:
                return
            name = mod + f"Chunk{chunk:02}"
            chunk += 1
            emit(name, [bname], "\n".join(small))
            files.append(name)
            depmods.append(name)
            small = []

        for j, ch in enumerate(children):
            kn, cn = kname + f"_{j:02}", cname + f"_{j:02}"
            names.append(kn)
            checknames.append(cn)
            p = f"refine ({p_expr}) {slot(ss)} (some {move(moves[j])})"
            if size(ch) > threshold and ch[0] == "split":
                flush()
                sub = mod + f"Sub{j:02}"
                files += go(ch, p, kn, cn, sub)
                depmods.append(sub)
            else:
                body = leaf(ch, p, kn, cn)
                if sum(map(len, small)) + len(body) > 10000:
                    flush()
                small.append(body)
        flush()
        kids = kname + "Kids"
        cs = "\n".join(f"  · exact {checknames[12*w+6*r+q]} h" for q,w,r in product(range(6),range(2),range(2)))
        emit(mod, depmods, f"""
def {kids} (h : Exceptions) : Move → Audit := byMove [{','.join(kn+' h' for kn in names)}]
def {kname} (h : Exceptions) : Audit := .split {nn} {slot(ss)} ({kids} h)
theorem {cname}_kids (h : Exceptions) (mv : Move) : zipCheck {B} (refine ({p_expr}) {slot(ss)} (some mv)) ({kids} h mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cs}
theorem {cname} (h : Exceptions) : zipCheck {B} ({p_expr}) ({kname} h) = true := by
  change (zipQueryOK {B} ({p_expr}) {nn} {slot(ss)} && allMoves (fun mv => zipCheck {B} (refine ({p_expr}) {slot(ss)} (some mv)) ({kids} h mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨by decide, allMoves_of _ ({cname}_kids h)⟩
""")
        return files + [mod]

    return go(node, p_expr, kname, cname, mod)
