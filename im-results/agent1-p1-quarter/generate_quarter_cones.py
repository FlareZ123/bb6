"""Reconstruct the exact source-certified eight-cone P1 n=2/50 mod64 proof.

The emitted file is proof source, not an oracle: the unmodified original Lean
kernel checks every inverse branch and each all-natural arithmetic obligation.
The generated QuarterCone.lean SHA256 is
c7b09fa15b003cabd29dd3f04ae84a1f226ced37b6350d2d0251def20295ac28.
"""
from pathlib import Path
from tempfile import NamedTemporaryFile
import fcntl
import os

R = [1, 13, 17, 29]


def add(p, q):
    return (p[0] + q[0], p[1] + q[1])


def mul(p, k):
    return (p[0] * k, p[1] * k)


def divexact(p, k):
    assert all(x % k == 0 for x in p), p
    return (p[0] // k, p[1] // k)


def divfloor(p, k):
    assert p[0] % k == 0, p
    return (p[0] // k, p[1] // k)


def s(p):
    a, b = p
    if b >= 0:
        return f'{a}*w+{b}'
    return f'{a}*w-{abs(b)}'


def inverse(b, d):
    k = add(divexact(b, 4), (0, -1))
    c = add(d, divexact(b, 2))
    v = []
    while True:
        x = add(mul(k, 2), (0, -4))
        y = add(c, (0, 4))
        v.append((k, c, x, y))
        assert c[0] % 2 == 0
        if c[1] % 2 == 0:
            break
        cc = divfloor(add(c, (0, -3)), 2)
        k = add(add(k, divfloor(cc, 2)), (0, 1))
        c = cc
    return v


def graph(r, lab):
    b, d = (
        ((128, 4*r-4), (128, 4*r+9))
        if lab == 'L0'
        else ((192, 6*r-2), (64, 2*r+5))
    )
    nodes = {}
    todo = [(lab, b, d)]
    while todo:
        path, b, d = todo.pop()
        if path in nodes:
            continue
        desc = []
        for t, (k, c, x, y) in enumerate(inverse(b, d)):
            if x[0] % 4 == 0 and x[1] % 4 == 2:
                term = 'M'
            elif x[0] % 4 == 0 and x[1] % 4 == 0 and y[0] % 2 == 0 and y[1] % 2 == 0:
                term = 'P'
                assert 35 <= (8*x[0]) // 32 <= 61
            elif x[0] % 4 == 0 and x[1] % 4 == 0 and y[1] % 2 == 1:
                term = 'N'
                todo.append((path + str(t), x, y))
            else:
                raise AssertionError((r, path, t, x, y))
            desc.append((k, c, x, y, term))
        nodes[path] = (b, d, desc)
    return nodes


def theorem_name(r, path):
    return f'cone_{r}_{path.lower()}'


def emit_node(r, path, nodes):
    b, d, desc = nodes[path]
    m = len(desc)-1
    lines = [
        f'private theorem {theorem_name(r,path)} (q u w : Nat) (hq:1≤q) (hw:1≤w)',
        '    (hu:u=32*w+' + str(r) + ') (hform:u+4*q+3=7*2^(16*q)) :',
        f'    Blocked ({s(b)}) ({s(d)}) := by'
    ]
    for t, (k, c, x, y, kind) in enumerate(desc):
        lines.append(
            f'  have h{t} : inverseAt ({s(b)}) ({s(d)}) {t} = some ({s(k)}, {s(c)}) := by'
        )
        if t == 0:
            lines.extend(['    simp [inverseAt]', '    omega'])
        else:
            prevc = desc[t-1][1]
            lines.extend([
                f'    rw [inverseAt, h{t-1}]',
                f'    have hc : 3 ≤ {s(prevc)} ∧ ({s(prevc)})%2=1 := by omega',
                '    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]',
                '    constructor <;> omega'
            ])
    lines.append(f'  have hn : (({s(d)})+({s(b)})/2+3)%2^({m}+1)≠0 := by')
    lines.append('    omega')
    lines.extend([
        '  apply Blocked.feeder', '  · omega', '  · omega', '  · omega',
        '  · intro k hk',
        f'    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod ({s(b)}) ({s(d)}) k 1 {m} hk hn',
        '    have hcases : ' + ' ∨ '.join(f't={t}' for t in range(m+1)) + ' := by omega',
        '    rcases hcases with ' + ' | '.join('h' + str(t) for t in range(m+1))
    ])
    for t, (k, c, x, y, kind) in enumerate(desc):
        lines.extend([
            f'    · subst t', f'      rw [h{t}] at hval',
            f'      have hp : (k,1)=({s(k)}, {s(c)}) := (Option.some.inj hval).symm',
            '      have hc := (Prod.mk.inj hp).2',
            '      omega'
        ])
    lines.extend([
        '  · intro k c h hc',
        f'    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod ({s(b)}) ({s(d)}) k c {m} h hn',
        '    have hcases : ' + ' ∨ '.join(f't={t}' for t in range(m+1)) + ' := by omega',
        '    rcases hcases with ' + ' | '.join('h' + str(t) for t in range(m+1))
    ])
    for t, (k, c0, x, y, kind) in enumerate(desc):
        lines.extend([
            f'    · subst t', f'      rw [h{t}] at hval',
            f'      have hp : (k,c)=({s(k)}, {s(c0)}) := (Option.some.inj hval).symm',
            '      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp',
            f'      have hx : 2*k-4 = {s(x)} := by omega',
            f'      have hy : c+4 = {s(y)} := by omega',
            '      rw [hx,hy]'
        ])
        if kind == 'M':
            lines.append(
                '      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)'
            )
        elif kind == 'P':
            lines.extend([
                '      apply Blocked.powerLeaf',
                '      · omega', '      · omega', '      · omega',
                f'      · exact window_not_power q u ({s(x)}) hq hform (by omega) (by omega)'
            ])
        else:
            lines.append('      exact ' + theorem_name(r, path + str(t)) + ' q u w hq hw hu hform')
    return '\n'.join(lines) + '\n\n'


def main():
    lines = [
        'import P1InverseFixed', 'import ConeKernel', 'import QuarterGap',
        'set_option maxRecDepth 8192',
        'set_option maxHeartbeats 5000000',
        'namespace BB6.Agent1Quarter', 'open BB6.Agent4Cone',
        'open BB6.Agent47P1', 'open BB6.P1Reduction', ''
    ]
    for r in R:
        for lab in ('L0', 'L1'):
            nodes = graph(r, lab)
            for p in sorted(nodes, key=lambda p: (-len(p), p)):
                lines.append(emit_node(r, p, nodes))
    for r in R:
        for lab in ('L0', 'L1'):
            lines.append(f'theorem {theorem_name(r,lab)}_final (q u w:Nat) (hq:1≤q) (hw:1≤w)')
            lines.append('    (hu:u=32*w+' + str(r) + ') (hform:u+4*q+3=7*2^(16*q)) :')
            b, d = graph(r, lab)[lab][:2]
            lines.append(
                f'    Blocked ({s(b)}) ({s(d)}) := {theorem_name(r,lab)} q u w hq hw hu hform\n'
            )
    for r in R:
        for lab in ('L0', 'L1'):
            lines.append(f'#print axioms BB6.Agent1Quarter.{theorem_name(r,lab)}_final')
    lines.append('end BB6.Agent1Quarter')
    out = Path(__file__).resolve().with_name('QuarterCone.lean')
    with open(out.with_suffix('.lock'), 'w') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        with NamedTemporaryFile('w', dir=out.parent, delete=False) as f:
            f.write('\n'.join(lines) + '\n')
            tmp = f.name
        os.replace(tmp, out)
    print('Wrote', out, 'SHA256 should equal c7b09fa15b003cabd29dd3f04ae84a1f226ced37b6350d2d0251def20295ac28')


if __name__ == '__main__':
    main()
