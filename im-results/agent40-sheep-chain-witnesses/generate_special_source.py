"""Generate full authenticated algebraic inverse classifications for two Sheep cones."""
from pathlib import Path
from tempfile import NamedTemporaryFile
from filelock import FileLock
from reflected_branches import CONES, PARENTS
import os
import sys

def generate():
    lines = [
        'import SheepEvenInverseAlgebra',
        'import ReflectedGeneric',
        'import SpecialCases',
        'import HCases',
        'import SheepSpecialNormalize',
        'set_option maxRecDepth 16384',
        'set_option maxHeartbeats 0',
        'namespace SheepFullSourceCases',
        '',
    ]
    for r, nodes in CONES.items():
        for ix, (s, b, d, limits) in enumerate(nodes):
            H = len(limits)
            c = -b
            ns = r + s
            lines.extend([
                f'theorem no_special_r{r}_n{ix} (k x y : Nat)',
                '    (edge : SheepEvenInverseAlgebra.SpecialEdge x y)',
                f'    (hy : {d}*y+{c}=2^({ns}+4860*k)) : False := by',
                '  obtain ⟨a,h,u,ha,hu,hx,hform,heq⟩ :=',
                f'    SheepEvenInverseAlgebra.special_inverse_negative x y {d} {c} ({ns}+4860*k) edge hy',
                f'  have hh : h<{H} := SheepHBound.h_bounded y {d} {c} ({ns}+4860*k) {H} h u hy hform (by',
                f'    simpa using SheepHCases.hstop_r{r}_n{ix} k)',
                '  have hc : ' + '∨'.join(f'h={h}' for h in range(H)) + ' := by omega',
                '  rcases hc with ' + '|'.join(f'h{h}' for h in range(H)),
            ])
            for h in range(H):
                D = d * 3**h
                A = 3 * D
                C = 2*D + 2**h*(d+c)
                base = ns+h
                lines.extend([
                    '  · subst h',
                    f'    have heqRow : {A}*2^a+{D}*a+{C}=2^({base}+4860*k) := by',
                    f'      have hexp : {ns}+4860*k+{h}={base}+4860*k := by omega',
                    '      rw [hexp] at heq',
                    f'      have hnorm := SheepSpecialNormalize.normalize {d} {c} {h} a ({base}+4860*k) heq',
                    '      simpa only [Nat.reducePow,Nat.reduceMul,Nat.reduceAdd,Nat.mul_one,Nat.one_mul,Nat.add_zero] using hnorm',
                    f'    exact (SheepSpecialCases.special_r{r}_n{ix}_h{h} k a) heqRow',
                ])
            lines.append('')
    for r, nodes in CONES.items():
        for ix, (s, b, d, limits) in enumerate(nodes):
            c = -b
            ns = r+s
            if (r,ix) in PARENTS:
                m,C,z = PARENTS[(r,ix)]
                conclusion = f'{m}*x+{C}={z}*2^({r}+4860*k)'
            else:
                conclusion = 'False'
            lines.extend([
                f'theorem complete_r{r}_n{ix} (k x y : Nat)',
                '    (edge : SheepEvenInverseAlgebra.Edge x y)',
                f'    (hy : {d}*y+{c}=2^({ns}+4860*k)) : {conclusion} := by',
                '  rcases edge with hg|hs',
                f'  · exact SheepReflectedGeneric.generic_r{r}_n{ix} k x y hg hy',
                f'  · exact False.elim (no_special_r{r}_n{ix} k x y hs hy)',
                '',
            ])
    lines.extend([
        '#print axioms complete_r402_n0',
        '#print axioms complete_r402_n2',
        '#print axioms complete_r1738_n1',
        '#print axioms complete_r1738_n2',
        'end SheepFullSourceCases',
    ])
    return '\n'.join(lines)+'\n'

def main(path):
    target = Path(path)
    with FileLock(str(target)+'.lock'):
        with NamedTemporaryFile(mode='w', encoding='utf-8', dir=target.parent, delete=False) as handle:
            handle.write(generate())
            handle.flush()
            os.fsync(handle.fileno())
            temp = handle.name
        os.replace(temp, target)
    print('Generated all six source-shaped inverse classifiers:', target)

if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv)>1 else 'SpecialSourceCases.lean')
