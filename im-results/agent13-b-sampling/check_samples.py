"""Independent exact-integer reproduction of finite Machine B scalar tests."""
from collections import defaultdict


def g(z: int) -> int:
    return 3 * (z // 2) + 4 + 5 * (z % 2)


def run(n: int, z: int = 0) -> int:
    for _ in range(n):
        z = g(z)
    return z


# Source-connected reduction's first two genuine recursively sampled indices.
assert run(3) == 19
assert run(25) == 227091
assert run(25) % 2 == 1
# Third sample is a finite prefix only; no all-time BB(6) claim.
third = run(227097)
assert third % 16 == 11
assert third.bit_length() == 132847
print('third_sample_index=227097; parity=1; mod16=11; bits=132847')

# Test scalar-orbit payloads, not the nested blank-reset subsequence.
samples = [run(t) for t in range(27)]
targets = {v + 6: v for v in samples}
y = 0
parities = {}
for t in range(max(targets) + 1):
    if t in targets:
        parities[targets[t]] = y & 1
    y = g(y)

assert (19 % 8, parities[19], parities[91]) == (3, 1, 0)
assert (505 % 64, 100921 % 64, parities[505], parities[100921]) == (57, 57, 1, 0)
assert (58 % 16, 10 % 16, parities[58], parities[10]) == (10, 10, 0, 1)
print('synthetic_mod8: v=19,91; parity=1,0')
print('true_scalar_orbit_mod64: t=10,23; v=505,100921; parity=1,0')
print('even_scalar_mod16: t=2,5; v=10,58; parity=1,0')

for k in [4, 8, 16, 32, 64]:
    groups = defaultdict(list)
    for t, v in enumerate(samples):
        groups[v % k].append((t, v, parities[v]))
    opposites = [(r, group) for r, group in groups.items() if len({a[2] for a in group}) == 2]
    print(f'modulus={k}; opposites={len(opposites)}')

print('PASS; finite exact-integer regressions, no root verdict')
