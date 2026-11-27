"""Authentic fixed Box28 cuts, preserving old D0=14 artifact names."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parent
OLD={14:(3,4,17,18,19,20),16:(1,3,4,5,7,8,17,18,19,20)}
OTHER={int(d):tuple(v for v in vs if int(d)>=17 or v<=20)
       for d,vs in json.loads((HERE/'first-hole-residual.json').read_text())['residuals'].items()}
TODO={**OLD,**OTHER}

def second_index(d0):
    return 7 if d0 in OLD else 3 if d0<17 else 8

def fixed_for(d0,v):
    assert d0 in TODO and v in TODO[d0], (d0,v)
    fixed=[8,-1,11,-1,11,13,d0,-1,-1,-1,-1,-1]
    fixed[second_index(d0)]=v
    return fixed

def targets_for(d0):
    return tuple(i for i in range(12) if i not in (0,2,4,5,6,second_index(d0)))

def stem(d0,v):
    return f'Box28D{v}' if d0==14 else f'Box28D{d0}V{v}'


def carry_rectangle(row):
    """Exact subset of the two source-certified carry rectangles, gates free."""
    return len(row)==12 and row[1] in (20,24) and all(row[i]==v for i,v in {0:8,2:11,4:11,5:13,6:18,7:15,9:24,10:4,11:12}.items())
