"""Deterministic physical sparse DFS and Lean certificate batches.

Four assigned, actually encountered instruction rows. The only finite-loop
leaves retained are those that physically read 1. The 20-step cutoff is only
for finite lasso discovery. Per-batch original-source Lean checks are the
proof of all-time nonhalting, not the Python search.
"""
import fcntl
import hashlib
import os
from pathlib import Path
import sys
import tempfile

MOVES = [(w, d, state) for w in range(2) for d in (-1,1) for state in range(6)]
patterns = []
rules = {}
seen = {}

def advance(state, head, ones, step, move):
    cfg = (state, head, frozenset(ones))
    seen[cfg] = step
    write, d, q = move
    was = head in ones
    if write: ones.add(head)
    else: ones.discard(head)
    search(q, head+d, ones, step+1)
    if was: ones.add(head)
    else: ones.discard(head)
    del seen[cfg]

def search(state, head, ones, step):
    cfg = (state, head, frozenset(ones))
    if cfg in seen:
        if len(rules)==4 and any(bit for _,bit in rules):
            patterns.append((tuple(rules.items()),seen[cfg],step-seen[cfg]))
        return
    if step>=20: return
    slot=(state,int(head in ones))
    if slot in rules:
        advance(state,head,ones,step,rules[slot])
    elif len(rules)<4:
        for move in MOVES:
            rules[slot]=move
            advance(state,head,ones,step,move)
            del rules[slot]

search(0,0,set(),0)
assert len(patterns)==4510 and len(set(patterns))==4510

def row(x):
    (state,bit),(write,d,q)=x
    return f'(({state},{"true" if bit else "false"}), ⟨{"true" if write else "false"},{"true" if d>0 else "false"},{q}⟩)'

def code_for(batch_no,batch):
    name=f'Batch{batch_no:02d}'
    header=f'''import Agent3FiniteLasso
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.{name}

structure Witness where
  a : Slot × Move
  b : Slot × Move
  c : Slot × Move
  d : Slot × Move
  entry : Nat
  period : Nat

def witnesses : Array Witness := #[
'''
    entries=[]
    for r,entry,period in batch:
        entries.append('  { a := '+row(r[0])+', b := '+row(r[1])+', c := '+row(r[2])+
                       ', d := '+row(r[3])+f', entry := {entry}, period := {period}'+' }')
    footer='''
]

def witness (i : Fin witnesses.size) : Witness := witnesses[i]

def sparseTable (w : Witness) : PartialMachine := fun slot =>
  if slot = w.a.1 then some (some w.a.2)
  else if slot = w.b.1 then some (some w.b.2)
  else if slot = w.c.1 then some (some w.c.2)
  else if slot = w.d.1 then some (some w.d.2)
  else none

theorem checked (i : Fin witnesses.size) :
    finiteLassoCheck (sparseTable (witness i)) (witness i).entry (witness i).period = true := by
  revert i
  decide

theorem period_positive (i : Fin witnesses.size) : 0 < (witness i).period := by
  revert i
  decide

theorem cover (i : Fin witnesses.size) (bound : Nat) :
    Cover (DecidedBelow bound) (sparseTable (witness i)) :=
  finiteLassoCheck_sound _ _ _ _ (period_positive i) (checked i)

theorem mass (i : Fin witnesses.size) :
    cylinderMass (sparseTable (witness i)) = 25^8 := by
  revert i
  decide

#print axioms checked
#print axioms cover
#print axioms mass
end BB6Coverage.'''+name+'\n'
    return header+',\n'.join(entries)+footer

outdir=Path(sys.argv[1] if len(sys.argv)>1 else 'im-results/agent3-finite-lasso')
outdir.mkdir(parents=True,exist_ok=True)
lock=outdir/'.lasso4510.lock'
source_paths=[]
with lock.open('w') as lk:
    fcntl.flock(lk,fcntl.LOCK_EX)
    for batch_no,start in enumerate(range(0,len(patterns),100)):
        path=outdir/f'Agent3Lasso4510Batch{batch_no:02d}.lean'
        source=code_for(batch_no,patterns[start:start+100])
        fd,tmp=tempfile.mkstemp(dir=outdir,prefix='.lasso4510-')
        try:
            with os.fdopen(fd,'w',encoding='utf8') as f:
                f.write(source)
                f.flush()
                os.fsync(f.fileno())
            os.replace(tmp,path)
        finally:
            if os.path.exists(tmp): os.unlink(tmp)
        source_paths.append(path)
print('witnesses',len(patterns),'batches',len(source_paths))
h=hashlib.sha256()
for path in source_paths: h.update(path.read_bytes())
print('concatenated_sha256',h.hexdigest())
