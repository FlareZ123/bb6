"""Generate an original-source Lean proof for P1 critical index 130 mod 65536.

The deterministic affine tree comes from Agent 4's original conservative
scanner. This generator only emits proof terms; Lean verifies every claim.
"""
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'agent4-p1-cone2398'))
from uniform_scan import Aff, check_residue, all_positive_g_ancestors

R = 130
assert check_residue(R)[0]
root = (Aff(131072, 131056 - 2*R), Aff(0, 3))
stack = [root]
nodes = []
while stack:
    b, d = stack.pop()
    i = len(nodes)
    branches = []
    for k, u in all_positive_g_ancestors(b, d):
        x, y = k*2 - 4, u + 4
        typ = 'power' if y.residue(2) == 0 else ('mod' if x.residue(4) == 2 else 'child')
        branches.append((k, u, x, y, typ))
        if typ == 'child':
            stack.append((x, y))
    D = d + b.divide_exact(2) + 3
    def v2(z):
        return (z & -z).bit_length() - 1
    nodes.append((i, b, d, D, v2(D.c), branches))
assert len(nodes) == 7

out = []
def add(s=''):
    out.append(s)
def ex(a):
    return f'({a.a}*tt q+{a.c})' if a.a else str(a.c)

add('import ConeReflect')
add('import NatAffineWrappers')
add('set_option maxRecDepth 16384')
add('set_option maxHeartbeats 2000000')
add('namespace BB6.Agent44.Case130')
add('open BB6.Agent44')
add('open BB6.Agent4Cone')
add('def tt (q : Nat) : Nat := 7*2^(65536*q+130-16)-(q+1)')
add('theorem tt_ge (q:Nat) : 223≤tt q := by')
add('  have h := BB6.Agent44.universal_strong_growth q 130 (by decide)')
add('  dsimp [tt]')
add('  omega')
for i, b, d, D, m, branches in nodes:
    add(f'def b{i} (q:Nat):Nat := {ex(b)}')
    add(f'def d{i} (q:Nat):Nat := {ex(d)}')
for i, b, d, D, m, branches in reversed(nodes):
    add(f'/-- Source-connected blocked cone node {i}, 2-adic depth {m}. -/')
    add(f'theorem blocked_{i} (q:Nat) : Blocked (b{i} q) (d{i} q) := by')
    add('  have ht := tt_ge q')
    add(f'  have hD : d{i} q + b{i} q/2 + 3 = {D.a}*tt q+{D.c} := by')
    add(f'    dsimp [b{i},d{i}]')
    add('    omega')
    add(f'  have hno : ∀ k, ¬BB6.P1Reduction.GAncestor (b{i} q) (d{i} q) k 1 := by')
    add(f'    apply nat_no_one_ancestor q 130 (b{i} q) (d{i} q) {D.a} {D.c} (by decide) (by decide)')
    add('    exact hD')
    add(f'  refine blocked_from_val_cert (b{i} q) (d{i} q) {D.a} {D.c} (tt q) {m} (by dsimp [b{i}]; omega) (by dsimp [b{i}]; omega) (by dsimp [d{i}]; omega) hno hD (by decide) (by decide) ?_')
    add('  intro n hn hv')
    add('  have hcases : '+' ∨ '.join(f'n={j}' for j in range(m+1))+' := by omega')
    if m > 0:
        add('  rcases hcases with '+' | '.join(['rfl']*(m+1)))
    else:
        add('  rcases hcases with rfl')
    for j, (k, u, x, y, typ) in enumerate(branches):
        assert j <= m
        add(f'  · have hcoords : invAt (b{i} q) (d{i} q) {j} = ({ex(k)}, {ex(u)}) := by')
        add(f'      simp only [invAt,b{i},d{i}]')
        add('      apply Prod.ext <;> dsimp <;> omega')
        add('    simp only [hcoords] at hv ⊢')
        if typ == 'mod':
            add('    exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)')
        elif typ == 'power':
            P = x+12
            add('    refine Blocked.powerLeaf _ _ (by omega) (by omega) (by omega) ?_')
            add(f'    apply nat_power_leaf q 130 (2*{ex(k)}-4) {P.a} {P.c} (by decide) (by decide) (by decide) (by decide) (by decide)')
            add(f'    change (2*{ex(k)}-4)+12={P.a}*tt q+{P.c}')
            add('    omega')
        else:
            tgt = next(t for t, bt, dt, *_ in nodes if (bt,dt)==(x,y))
            add(f'    have hx : 2*{ex(k)}-4=b{tgt} q := by dsimp [b{tgt}] <;> omega')
            add(f'    have hy : {ex(u)}+4=d{tgt} q := by dsimp [d{tgt}] <;> omega')
            add('    rw [hx,hy]')
            add(f'    exact blocked_{tgt} q')
add('theorem root_not_reached (q:Nat) : ¬BB6.Agent1.Reach (b0 q) (d0 q) :=')
add('  BB6.Agent4Cone.blocked_no_reach (b0 q) (d0 q) (blocked_0 q)')
add('#print axioms BB6.Agent44.Case130.root_not_reached')
add('end BB6.Agent44.Case130')

source = '\n'.join(out) + '\n'
path = Path(__file__).with_name('P1Case130.lean')
path.write_text(source)
print('generated Lean proof:', path, 'lines:', len(out), 'bytes:', len(source))
