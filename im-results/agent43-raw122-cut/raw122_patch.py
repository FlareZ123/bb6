#!/usr/bin/env python3
"""Patch 0LC/04 by literal table identity, without changing any other leaf."""
from pathlib import Path
from itertools import product
import re,sys
MOVES=[''.join(x) for x in product('01','LR','ABCDEF')]
PARENT='1RB---_1RC---_0RD---_1LD1RE_---0LF_------'
PATCH={
 '1RB0RB_1RC---_0RD0LE_1LD1RE_1RA0LF_1RB0LC':3905,
 '1RB0RC_1RC---_0RD0LE_1LD1RE_1RA0LF_1RB0LC':3906,
 '1RB1LD_1RC---_0RD0LE_1LD1RE_1RA0LF_1RB0LC':3908,
}
def leaf(s):
    stack=[];pairs={')':'(',']':'[','⟩':'⟨'}
    for i,c in enumerate(s):
        if c in '([⟨':stack.append(c)
        elif c in pairs:
            if not stack:return s[:i].rstrip(', ')
            assert stack.pop()==pairs[c]
        elif c==',' and not stack:return s[:i]
    assert not stack
    return s.rstrip(', ')
def patch(root):
    f=root/'Raw122Kid02_04.lean'
    head,body=f.read_text().split(' : PartialAudit := ',1)
    expr,tail=body.split('\ntheorem',1)
    lines=iter(expr.strip().splitlines())
    p=PARENT.replace('_','');p=[p[i:i+3] for i in range(0,36,3)]
    p[11]=MOVES[2];p[5]=MOVES[4];seen=[]
    def read(p,partial=True,first=None):
        s=next(lines).strip() if first is None else first
        if partial and s.startswith('.closed ('):
            return read(p,False,s[len('.closed ('):])
        m=re.match(r'\.split (\d+) \((\d+),(true|false)\) \(by(Partial)?Move \[',s)
        if m:
            n,q,b,part=m.groups();assert partial==bool(part)
            sl=2*int(q)+(b=='true');assert p[sl]=='---'
            kids=[]
            for a in MOVES:
                c=p.copy();c[sl]=a;kids.append(read(c,partial))
            return f'.split {n} ({q},{b}) (byMove [\n'+',\n'.join(kids)+'])'
        table='_'.join(''.join(p[i:i+2]) for i in range(0,12,2))
        if table in PATCH:
            i=PATCH[table];seen.append(i);ns=f'BB6Coverage.Agent31Pump.Raw122TailGrowth.M{i}'
            return f'.proven {ns}.table {ns}.never'
        assert not partial and re.match(r'\.(?:last|cycle|far|proven) ',s),s
        return leaf(s)
    result=read(p);assert next(lines,None) is None
    assert sorted(seen)==[3905,3906,3908],seen
    assert 'Raw122Symbol3905' not in result
    head=head.replace('import Raw122Symbol3905\n','import Raw122TailGrowth\n')
    f.write_text(head+' : PartialAudit := .closed ('+result+')\ntheorem'+tail)
    print('patched exact 0LC/04 leaves',seen,flush=True)
if __name__=='__main__':patch(Path(sys.argv[1]))
