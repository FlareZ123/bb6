"""Finite exact-integer P1 odd-cone probe; output is computational evidence only."""
from argparse import ArgumentParser


def predecessors(b, d):
    k, c, t = b // 4 - 1, d + b // 2, 0
    while True:
        yield t, 2 * k - 4, c + 4, c
        if c < 3 or c % 2 == 0:
            break
        v = (c - 3) // 2
        k, c, t = k + v // 2 + 1, v, t + 1


def scan(q, limit):
    p = 2 ** (16 * q)
    u = 7 * p - 4 * q - 3
    pending = [(4 * u - 4, 4 * u + 9, 5), (6 * u - 2, 2 * u + 5, 3)]
    visited = set()
    even_leaves = 0
    max_m = 0
    max_t = 0
    exceptions = []
    while pending and len(visited) < limit:
        b, d, e = pending.pop()
        key = b, d, e
        if key in visited:
            continue
        visited.add(key)
        if b < 8 or b % 4 != 0 or d % 2 != 1:
            exceptions.append(('unexpected hub', e, b, d))
            break
        mass = 8 * u + e - b - d
        if mass < 0 or mass % 2 != 0:
            exceptions.append(('mass mismatch', e, b, d))
            break
        m = mass // 2
        max_m = max(max_m, m)
        if m <= 7 * p and b == 4 * m + 64 * q + (12 if e == 5 else 16):
            exceptions.append(('affine gateway met', q, e, m, b))
            break
        s = d + b // 2 + 3
        if s >= 4 and s & (s - 1) == 0:
            exceptions.append(('exceptional c=1 power', q, e, m, b))
            break
        for t, x, y, c in predecessors(b, d):
            max_t = max(max_t, t)
            if x <= 2:
                exceptions.append(('small predecessor', q, e, m, t, x))
                break
            if x % 4 == 0 and y % 2 == 0:
                even_leaves += 1
                if not (28 * p < x + 12 < 56 * p):
                    exceptions.append(('strict power gap violated', q, e, m, t, x))
                    break
                if (x + 12) % 14 == 0 and ((x + 12) // 14).bit_count() == 1:
                    exceptions.append(('power leaf', q, e, m, t, x))
                    break
            elif x % 4 == 0 and y % 2 == 1:
                pending.append((x, y, e))
            elif x % 4 != 2:
                exceptions.append(('unclassified predecessor', q, e, m, t, x, y))
                break
        if exceptions:
            break
    return dict(q=q, visited_odd_hubs=len(visited), pending=len(pending), even_leaves=even_leaves,
                max_inverse_cost=max_m, max_single_depth=max_t,
                exceptions=exceptions, exhaustive=(len(pending) == 0 and not exceptions))


def main():
    parser = ArgumentParser()
    parser.add_argument('q', type=int, nargs='+')
    parser.add_argument('--cap', type=int, default=500_000)
    args = parser.parse_args()
    for q in args.q:
        if q < 1:
            raise ValueError('q must be positive')
        print(scan(q, args.cap), flush=True)


if __name__ == '__main__':
    main()
