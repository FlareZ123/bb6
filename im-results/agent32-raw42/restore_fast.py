"""Decode the exact FastBiDFA representation for quotient discovery.
The output is untrusted and must be checked again after conversion.
"""
import ast
import re

FAST = re.compile(r'def cert : FastCert := ⟨(\[[^\]]*\]),\s*(\[[^\]]*\]),\s*#\[(.*?)\],\s*#\[(.*?)\],\s*(\d+),\s*#\[(.*?)\]⟩', re.S)


def decode_rows(source):
    tokens = re.findall(r'\.(?:empty|leaf|branch)', source)
    if re.sub(r'\.(?:empty|leaf|branch)|[\s(),]', '', source):
        raise ValueError('unexpected FastBiDFA trie syntax')
    it = iter(tokens)

    def decode(tok):
        if tok == '.empty':
            return set()
        if tok == '.leaf':
            return {0}
        if tok != '.branch':
            raise ValueError('invalid FastBiDFA trie token')
        even, odd = decode(next(it)), decode(next(it))
        return {2*x for x in even} | {2*x+1 for x in odd}

    rows = []
    try:
        for tok in it:
            rows.append(decode(tok))
    except StopIteration as e:
        raise ValueError('truncated FastBiDFA trie') from e
    return rows


def restore_fast(source):
    """Return a list-certificate module, preserving all decoded entries."""
    m = FAST.search(source)
    if m is None:
        raise ValueError('unsupported FastBiDFA certificate syntax')
    dl, dr = map(ast.literal_eval, m.groups()[:2])
    el, er = (decode_rows(x) for x in m.groups()[2:4])
    width = int(m[5])
    rows = decode_rows(m[6])
    nl, nr = len(dl)//2, len(dr)//2
    if not (0 < width <= nr and len(rows) == 12 and len(el) <= nl and len(er) <= nr):
        raise ValueError('inconsistent FastBiDFA dimensions')
    EL = [(d, x%2, x//2) for d,row in enumerate(el) for x in sorted(row)]
    ER = [(d, x%2, x//2) for d,row in enumerate(er) for x in sorted(row)]
    S = [(i//2, i%2, x//width, x%width) for i,row in enumerate(rows) for x in sorted(row)]
    if (any(t >= nl for _,_,t in EL) or any(t >= nr for _,_,t in ER)
            or any(l >= nl or r >= nr for _,_,l,r in S)):
        raise ValueError('out-of-range FastBiDFA relation entry')
    def literal_rows(xs):
        return '[' + ','.join('⟨' + ','.join(('true' if v else 'false') if i == 1 else str(v)
                                             for i,v in enumerate(row)) + '⟩' for row in xs) + ']'
    cert = 'def cert : Cert := ⟨' + ','.join((str(dl),str(dr),literal_rows(EL),literal_rows(ER),literal_rows(S))) + '⟩'
    return (source[:m.start()] + cert + source[m.end():]).replace('import FastBiDFA','import BiDFA').replace(
        'open BB6Coverage BB6.Agent32FastBiDFA','open BB6Coverage BB6Coverage.Agent16BiDFA')
