"""Generate all-k Lean certificates for 56 excluded small valuations of Sheep E gate 648.

Requires the existing exact seven_cones.py module (same directory in repository).
Uses multiprecision integer arithmetic and complete verified multiplicative orders.
Writes generated Lean source atomically under a cross-platform lock.
"""
from __future__ import annotations
from hashlib import sha256
from math import gcd
from os import fsync, fdopen, replace, unlink
from pathlib import Path
from tempfile import mkstemp
from filelock import FileLock
from seven_cones import CASES, order_two, v3


def create_source() -> tuple[str, int, int]:
    J, P, nodes, edges = CASES[-1]
    assert J == 648 and P == 122472
    assert len(nodes) == 2 and len(edges) == 1
    lines = [
        'import Sheep648Period',
        'set_option maxRecDepth 32768',
        'set_option maxHeartbeats 0',
        'set_option exponentiation.threshold 100000',
        '',
        'namespace Sheep648LowResidues',
        '',
    ]
    count = reps = 0
    for i, (s, b, d) in enumerate(nodes):
        Y = ((1 << (J + s)) + b) // d
        H = v3(Y - 1) + 1
        for h in range(H):
            D = d * 3**h
            C = D + 2**h * (b - d)
            A = 1
            while not (1 < D*(2*A - 1)-2*C < (1 << A) and (1 << A) >= 2*D):
                A += 1
            for a in range(1, A):
                if (i, h, a) == (0, 5, 2):
                    continue  # One genuine predecessor; formalize separately.
                m = D * (2**(a+1) + 1)
                period = order_two(m)
                q = period // gcd(period, P)
                R = J + s + h + 1
                K = D * (2*a - 1) - 2*C
                B = (-K) % m
                assert pow(2, P*q, m) == 1
                assert all((pow(2, R+P*t, m) + B) % m != 0 for t in range(q))
                name = f'exclude_{i}_{h}_{a}'
                lines += [
                    f'/-- Complete all-k inverse congruence: target node {i}, h={h}, a={a}. -/',
                    f'theorem {name} (k : Nat) :',
                    f'    (2^({R}+{P}*k)+{B})%{m} ≠ 0 := by',
                    f'  apply Sheep648Period.no_mod_zero_from_period {m} {period} {R} {P} {q} {B}',
                    '  · decide',
                    '  · decide',
                    '  · decide',
                    '  · decide',
                    '  · intro t ht',
                ]
                lines.append('    have hcases : ' + ' ∨ '.join(f't={z}' for z in range(q)) + ' := by omega')
                if q == 1:
                    lines.append('    subst t')
                else:
                    lines.append('    rcases hcases with ' + ' | '.join(f'h{z}' for z in range(q)))
                for t in range(q):
                    EX = R + P*t
                    reduced = (EX - 1) % period + 1
                    w = (EX - reduced) // period
                    indent = '    ' if q == 1 else '      '
                    if q > 1:
                        lines.append('    · subst t')
                    lines += [
                        f'{indent}have he : 2^({R}+{P}*{t})%{m} = 2^{reduced}%{m} := by',
                        f'{indent}  simpa only [show {reduced}+{period}*{w}={R}+{P}*{t} by decide] using',
                        f'{indent}    (Sheep648Period.pow_mod_period {m} {period} {reduced} {w}',
                        f'{indent}      (by decide) (by decide))',
                        f'{indent}have hc : (2^({R}+{P}*{t})+{B})%{m}=(2^{reduced}+{B})%{m} := by',
                        f'{indent}  rw [Nat.add_mod, he, ← Nat.add_mod]',
                        f'{indent}rw [hc]',
                        f'{indent}decide',
                    ]
                lines.append('')
                count += 1
                reps += q
    assert count == 56 and reps == 193, (count, reps)
    lines += [f'#print axioms exclude_{i}_{h}_{a}' for i, (s, b, d) in enumerate(nodes)
              for h in range(v3(((1 << (J+s))+b)//d - 1)+1)
              for a in range(1, next(a for a in range(1,50)
                if 1 < (d*3**h)*(2*a-1)-2*((d*3**h)+2**h*(b-d)) < 2**a
                and 2**a >= 2*(d*3**h))) if (i, h, a)!=(0,5,2)]
    lines += ['', 'end Sheep648LowResidues', '']
    return '\n'.join(lines), count, reps


def main() -> None:
    source, count, reps = create_source()
    target = Path(__file__).with_name('Sheep648LowResidues.lean')
    with FileLock(str(target) + '.lock'):
        fd, temp = mkstemp(prefix='.Sheep648LowResidues.', suffix='.lean.tmp', dir=target.parent)
        try:
            with fdopen(fd, 'w', encoding='utf-8', newline='\n') as stream:
                stream.write(source)
                stream.flush()
                fsync(stream.fileno())
            replace(temp, target)
        finally:
            if Path(temp).exists():
                unlink(temp)
    print('generated', count, 'theorems', reps, 'complete period representatives',
          len(source), 'bytes sha256', sha256(source.encode()).hexdigest())


if __name__ == '__main__':
    main()
