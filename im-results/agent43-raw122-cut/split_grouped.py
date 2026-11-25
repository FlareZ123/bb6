#!/usr/bin/env python3
"""Decompose a generated closed raw122 shard into checked subtrees.
Usage: split_closed.py INPUT WORK [MAX_CHARS]
All emitted checkers use the existing partialPrefix_eq or zipCheck.eq_5.
No decision procedure is trusted outside Lean. The caller compiles files in
printed order, then the original module name, which preserves the exported
kidNN_NN and kidNN_NN_checked declarations.
"""
import re,sys
from pathlib import Path

src=Path(sys.argv[1]); out=Path(sys.argv[2]); out.mkdir(exist_ok=True,parents=True)
limit=int(sys.argv[3]) if len(sys.argv)>3 else 3000
s=src.read_text(); header=s[:s.index('\ndef kid')]; footer='\nend BB6.Agent43Raw122\n'
m=re.search(r'def (kid\d+_\d+) : PartialAudit := \.closed \((.*)\)\ntheorem \1_checked : partialCheck 7014 (.*?) \1 = true := by',s,re.S)
assert m,src
kid,audit,root=m.groups(); modules=[]; records=[]; counter=0

def split_args(s):
    depth=0; start=0; result=[]
    for j,c in enumerate(s):
        if c in '([{⟨': depth+=1
        elif c in ')]}⟩': depth-=1
        elif c==',' and depth==0:
            result.append(s[start:j].strip());start=j+1
        assert depth>=0
    assert depth==0
    result.append(s[start:].strip())
    assert len(result)==24,len(result)
    return result

def move(i):return f'⟨{str(i>=12).lower()},{str(i%12>=6).lower()},{i%6}⟩'
def emit(name, deps, body):
    records.append((name,deps,body))

def build(a,p):
    global counter
    idx=counter;counter+=1
    name=f'{src.stem}Split{idx:04}'; decl=f'{kid}_s{idx:04}'
    m=re.fullmatch(r'\.split (\d+) (\([^)]*\)) \(byMove \[\s*(.*)\s*\]\)',a,re.S)
    if len(a)<=limit or not m:
        emit(name,[],f'''def {decl} : Audit := {a}
theorem {decl}_checked : zipCheck 7014 {p} {decl} = true := by
  rw [← partialCheck.eq_2, ← BB6.Agent47Raw111.partialPrefix_eq]
  decide
''')
    else:
        n,slot,children=m.groups(); children=split_args(children)
        kids=[build(c,f'(refine {p} {slot} (some {move(i)}))') for i,c in enumerate(children)]
        ks=decl+'_kids'; cases='\n'.join('  · exact '+kids[12*w+6*r+q][1]+'_checked' for q in range(6) for w in range(2) for r in range(2))
        emit(name,[k[0] for k in kids],f'''def {ks} : Move → Audit := byMove [{','.join(k[1] for k in kids)}]
theorem {ks}_checked (mv : Move) : zipCheck 7014 (refine {p} {slot} (some mv)) ({ks} mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
def {decl} : Audit := .split {n} {slot} {ks}
theorem {decl}_checked : zipCheck 7014 {p} {decl} = true := by
  rw [{decl},zipCheck.eq_5]
  simp only [Bool.and_eq_true]
  exact ⟨by decide, allMoves_of _ {ks}_checked⟩
''')
    return name,decl

name,decl=build(audit,root)
emit(src.stem,[name],f'''def {kid} : PartialAudit := .closed {decl}
theorem {kid}_checked : partialCheck 7014 {root} {kid} = true := by
  exact {decl}_checked
#print axioms {kid}_checked
''')
# Topological packing keeps each kernel reduction small, while amortizing
# the import overhead of the original source closure across several checks.
owner={}
pending=[]
def flush():
    if not pending:return
    name=src.stem+'Pack'+str(len(modules)).zfill(3)
    here={r[0] for r in pending}
    deps=sorted({owner[d] for _,ds,_ in pending for d in ds if d not in here})
    (out/(name+'.lean')).write_text(''.join(f'import {d}\n' for d in deps)+header+'\n'+'\n'.join(r[2] for r in pending)+footer)
    modules.append(name)
    owner.update((r[0],name) for r in pending)
    pending.clear()
for r in records[:-1]:
    if pending and (len(pending)>=12 or sum(len(x[2]) for x in pending)+len(r[2])>24000):flush()
    pending.append(r)
flush()
name,ds,body=records[-1]
(out/(name+'.lean')).write_text(''.join(f'import {owner[d]}\n' for d in ds)+header+'\n'+body+footer)
modules.append(name)
print('\n'.join(modules))
