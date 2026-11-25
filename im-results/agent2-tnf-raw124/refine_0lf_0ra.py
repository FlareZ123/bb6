"""Refine expensive top-level audit shards into smaller theorem modules.
Run after shard_0lf_1rb.py; independent subproofs avoid large decide terms.
"""
from pathlib import Path
import re, sys
root=Path(sys.argv[1])
header=(root/'Raw124ZeroLF0RAKid00.lean').read_text().split('\ndef kid00')[0]
footer='\nend BB6.Agent2Raw124ZeroLF0RA\n'
base='Raw124ZeroLF0RABase'
B=430

def parse(s):
    m=re.match(r'\.split (\d+) (\(\d+,(?:true|false)\)) \(byMove \[\s*',s)
    if not m:return s
    start=m.end(); depth=0; pieces=[]; a=start
    for i in range(start,len(s)):
        c=s[i]
        if c in '[({⟨':depth+=1
        elif c in '])}⟩':
            if depth==0:
                pieces.append(s[a:i].strip());break
            depth-=1
        elif c==',' and depth==0:
            pieces.append(s[a:i].strip());a=i+1
    assert len(pieces)==24,(len(pieces),s[:100])
    return int(m[1]),m[2],[parse(p) for p in pieces]

def show(t):
    if isinstance(t,str):return t
    n,s,children=t
    return f'.split {n} {s} (byMove [\n'+',\n'.join(map(show,children))+'])'

def mv(i):return f'⟨{str(i>=12).lower()},{str(i%12>=6).lower()},{i%6}⟩'

def emit(t,p,name,mod):
    # One relatively small decide proof per module. Large internal nodes use
    # checked child theorems rather than reduction of the full subtree.
    text=show(t)
    if isinstance(t,str) or (len(text)<1600 and text.count('.split')<=1):
        body=f'def kid{name} : Audit := {text}\ntheorem check{name} : fastCheck {B} {p} kid{name} = true := by decide\n'
        imports=[]
    else:
        n,s,children=t
        imports=[]; names=[]
        for i,c in enumerate(children):
            nn=f'{name}_{i:02}'; mm=f'{mod}_{i:02}'
            emit(c,f'(refine {p} {s} (some {mv(i)}))',nn,mm)
            names.append(nn);imports.append(mm)
        body=f'def kids{name} : Move → Audit := byMove ['+','.join('kid'+nn for nn in names)+']\n'
        body+=f'theorem checks{name} (mv : Move) : fastCheck {B} (refine {p} {s} (some mv)) (kids{name} mv) = true := by\n'
        body+='  rcases mv with ⟨w,r,q⟩\n  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega\n  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl\n  all_goals cases w <;> cases r\n'
        for q in range(6):
            for i in [q,q+6,q+12,q+18]:body+='  · exact check'+names[i]+'\n'
        body+=f'def kid{name} : Audit := .split {n} {s} kids{name}\n'
        body+=f'theorem check{name} : fastCheck {B} {p} kid{name} = true := by\n  change (fastQuery {B} {p} {n} {s} && allMoves (fun mv => fastCheck {B} (refine {p} {s} (some mv)) (kids{name} mv))) = true\n  simp only [Bool.and_eq_true]\n  exact ⟨by decide,allMoves_of _ checks{name}⟩\n'
    (root/(mod+'.lean')).write_text(''.join(f'import {m}\n' for m in imports)+header+'\n'+body+footer)
    print(mod)

for i in map(int,sys.argv[2:]):
    mod=f'Raw124ZeroLF0RAKid{i:02}'; name=f'{i:02}'
    txt=(root/(mod+'.lean')).read_text()
    t=parse(txt.split(f'def kid{name} : Audit := ',1)[1].split('\ntheorem check',1)[0])
    emit(t,f'(refine pChild (2,true) (some {mv(i)}))',name,mod)
