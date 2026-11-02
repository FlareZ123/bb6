"""Generate an original-source Lean proof for P1 critical residue classes.

The deterministic affine tree comes from Agent 4's original conservative
scanner. This generator only emits proof terms; Lean verifies every claim.
"""
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'agent4-p1-cone2398'))
from uniform_scan import Aff, check_residue, all_positive_g_ancestors

R = int(sys.argv[1]) if len(sys.argv) > 1 else 130
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
assert len(nodes) == check_residue(R)[2]

out = []
def add(s=''):
    out.append(s)
def ex(a):
    return (f'({a.a}*tt q+{a.c})' if a.c >= 0 else f'({a.a}*tt q-{abs(a.c)})') if a.a else str(a.c)

add('import ConeReflect')
add('import NatAffineWrappers')
add('import P1Gate')
add('set_option maxRecDepth 16384')
add('set_option maxHeartbeats 2000000')
add(f'namespace BB6.Agent44.Case{R}')
add('open BB6.Agent44')
add('open BB6.Agent4Cone')
add(f'def tt (q : Nat) : Nat := 7*2^(65536*q+{R}-16)-(q+1)')
add('theorem tt_ge (q:Nat) : 223≤tt q := by')
add(f'  have h := BB6.Agent44.universal_strong_growth q {R} (by decide)')
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
    add(f'    apply nat_no_one_ancestor q {R} (b{i} q) (d{i} q) {D.a} {D.c} (by decide) (by decide)')
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
            add(f'    apply nat_power_leaf q {R} (2*{ex(k)}-4) {P.a} {P.c} (by decide) (by decide) (by decide) (by decide) (by decide)')
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
add(f'def critical (q:Nat):Nat := 14*2^(65536*q+{R})-2*(65536*q+{R})-10')
add('theorem critical_eq_root_plus_six (q:Nat) : critical q = b0 q + 6 := by')
add(f'  let n : Nat := 65536*q+{R}')
add('  let X : Nat := 2^(n-16)')
add(f'  have hX := BB6.Agent44.universal_strong_growth q {R} (by decide)')
add('  have hn : n=(n-16)+16 := by dsimp [n]; omega')
add('  have hp : 2^n=65536*X := by')
add('    rw [hn, Nat.pow_add]')
add('    have h16 : (2:Nat)^16=65536 := by decide')
add('    rw [h16]')
add('    dsimp [X]')
add('    omega')
add('  have ht : tt q+(q+1)=7*X := by')
add('    have hsub : q+1≤7*X := by dsimp [X,n]; omega')
add('    exact Nat.sub_add_cancel hsub')
add('  dsimp [critical,b0]')
add(f'  change 14*2^n-2*n-10=131072*tt q+{131056-2*R}+6')
add('  rw [hp]')
add('  omega')
add(f'theorem blank_no_critical_{R}_mod65536 (q:Nat) :')
add('    ¬BB6.Agent1.Reach 2 (critical q) := by')
add('  intro hr')
add('  have heq := critical_eq_root_plus_six q')
add('  have hge : 10≤critical q := by rw [heq]; dsimp [b0]; omega')
add('  have hmod : (critical q)%4=2 := by rw [heq]; dsimp [b0]; omega')
add('  have h := BB6.Agent50P1.critical_target_implies_three')
add('    (critical q) hge hmod hr')
add('  have hroot : BB6.Agent1.Reach (b0 q) 3 := by')
add('    have hv : critical q-6=b0 q := by omega')
add('    rw [hv] at h')
add('    exact h')
add('  exact root_not_reached q hroot')
add(f'#print axioms BB6.Agent44.Case{R}.blank_no_critical_{R}_mod65536')
add(f'#print axioms BB6.Agent44.Case{R}.root_not_reached')
add(f'end BB6.Agent44.Case{R}')

source = '\n'.join(out) + '\n'
path = Path(__file__).with_name(f'P1Case{R}.lean')
path.write_text(source)
print('generated Lean proof:', path, 'lines:', len(out), 'bytes:', len(source))
