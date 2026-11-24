"""Exact finite extension of Agent3's D max-plus certificate.
Run from any directory; imports the original rank abstraction unchanged.
"""
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'agent3-d-density-drift'))
from certificate import N, CLASSES, RULES, pop, push, exit_rows, check_exit, e_rows


def height_edges(X, q, c):
    """(q',c',weight) constraints H(q,c) >= weight+H(q',c')."""
    ins = RULES[2*q + (c & 1)]
    if ins is None or ins[1] < 0:
        return
    b, _, r = ins
    for j, g1 in pop(c):
        yield r, j, 1+g1
        for (r2, k), g2 in X[r][j].items():
            l, g3 = push(b, k)
            yield r2, l, g1+g2+g3


def main():
    X, rounds = exit_rows()
    check_exit(X)
    e_rows(X)
    assert max(g for row in X for d in row for g in d.values()) == 2
    assert all(push(b,c)[1] <= 3 for b in (0,1) for c in CLASSES)
    edges = [[tuple(height_edges(X,q,c)) for c in CLASSES] for q in range(6)]
    H = [[0]*N for _ in range(6)]
    # Generator: only the subsequently checked inequalities are trusted.
    for sweep in range(100):
        changed = False
        for q in range(6):
            for c in CLASSES:
                v = max((g + H[r][j] for r,j,g in edges[q][c]), default=0)
                if v > H[q][c]:
                    H[q][c] = v
                    changed = True
        if not changed:
            break
    assert all(0 <= H[q][c] <= 4 for q in range(6) for c in CLASSES)
    assert all(H[q][c] >= g+H[r][j] for q in range(6) for c in CLASSES
               for r,j,g in edges[q][c])
    print(f'X closure rounds: {rounds}; height closure sweeps: {sweep+1}; max H: {max(map(max,H))}')
    anchors = [(123501,9),(196699,0),(276715,0),(277451,0)]
    L = [5*n-23 for n,R in anchors]
    U = [5*(n+R)+27 for n,R in anchors]
    assert all(8*(L[i+1]-U[i]) > 384 for i in range(3))
    assert 64*L[0] > 24*U[-1]+1152
    print('Enlarged terminal bands are strictly separated for all phases.')


if __name__ == '__main__':
    main()
