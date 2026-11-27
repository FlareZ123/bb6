#!/usr/bin/env python3
"""Shrink a BiDFA list certificate by relation-labelled DFA quotienting.

This is untrusted certificate discovery only. The emitted certificate must
pass the original Lean checker (or FastBiDFA's proved checker).
"""
import ast
import re
import sys
from pathlib import Path

PATTERN = re.compile(r'def cert : Cert := ⟨(\[[^\]]*\]),\s*(\[[^\]]*\]),\s*(\[[^\]]*\]),\s*(\[[^\]]*\]),\s*(\[[^\]]*\])⟩')


def parse(source):
    m = PATTERN.search(source)
    if m is None:
        raise ValueError('unsupported BiDFA list certificate syntax')
    dl, dr = map(ast.literal_eval, m.groups()[:2])
    el, er, states = [ast.literal_eval(x.replace('⟨', '(').replace('⟩', ')')
                       .replace('true', '1').replace('false', '0')) for x in m.groups()[2:]]
    return m, dl, dr, el, er, states


def partition(delta, signatures):
    """Moore refinement: preserve relation labels and both DFA transitions."""
    n = len(delta) // 2
    assert len(delta) == 2*n and n > 0 and all(0 <= v < n for v in delta)
    assert len(signatures) == n

    def classify(labels):
        classes = {}
        return [classes.setdefault(label, len(classes)) for label in labels]

    cls = classify(signatures)
    while True:
        nxt = classify((cls[i], cls[delta[2*i]], cls[delta[2*i+1]]) for i in range(n))
        if nxt == cls:
            break
        cls = nxt
    assert cls[0] == 0  # blank summary stays zero
    out = [0] * (2*(max(cls)+1))
    for i in range(n):
        out[2*cls[i]:2*cls[i]+2] = [cls[delta[2*i]], cls[delta[2*i+1]]]
    return out, cls


def literal_rows(xs):
    return '[' + ','.join('⟨' + ','.join(('true' if v else 'false') if i == 1 else str(v)
                                         for i, v in enumerate(row)) + '⟩' for row in xs) + ']'


def minimize(source):
    m, dl, dr, el, er, states = parse(source)
    nl, nr = len(dl)//2, len(dr)//2
    left = [set() for _ in range(nl)]
    right = [set() for _ in range(nr)]
    for q, a, l, r in states:
        left[l].add((q,a,r))
        right[r].add((q,a,l))
    DL, L = partition(dl, list(map(frozenset,left)))
    DR, R = partition(dr, list(map(frozenset,right)))
    EL = sorted({(L[d], b, L[t]) for d,b,t in el})
    ER = sorted({(R[d], b, R[t]) for d,b,t in er})
    S = sorted({(q,a,L[l],R[r]) for q,a,l,r in states})
    cert = 'def cert : Cert := ⟨' + ','.join((str(DL),str(DR),literal_rows(EL),literal_rows(ER),literal_rows(S))) + '⟩'
    before = (nl, nr, len(states))
    after = (len(DL)//2, len(DR)//2, len(S))
    return source[:m.start()] + cert + source[m.end():], before, after


if __name__ == '__main__':
    for name in sys.argv[1:]:
        p = Path(name)
        new, before, after = minimize(p.read_text())
        print(p.name, before, '->', after)
        p.write_text(new)
