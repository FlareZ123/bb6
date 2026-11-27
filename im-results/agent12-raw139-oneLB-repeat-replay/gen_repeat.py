#!/usr/bin/env python3
"""Generate exact kernel-checked replay blocks from an untrusted trace compressor."""
import sys
from pathlib import Path
sys.set_int_max_str_digits(0)
TABLES={209:[7,20,11,1,14,9,17,16,6,11,0,24],892:[7,23,11,13,14,21,24,16,6,11,3,0]}
def val(w):return int(w[::-1],2) if w else 0
def cat(w,u):return val(w)+(u<<len(w))
def strip(w,u):
    assert u%(1<<len(w))==val(w),(w,u%16)
    return u>>len(w)
def rep(a,w,k):
    b=1<<len(w);s=b**k
    return cat(a,val(w)*(s-1)//(b-1)),(1<<len(a))*s

def striprep(a,w,k,u):
    v,s=rep(a,w,k); assert u%s==v,(a,w,k,u%s,v)
    return u//s

def putrep(a,w,k,u):
    v,s=rep(a,w,k);return v+s*u

def step(t,s):
    q,l,r=s;c=t[2*q+r%2];assert c!=24
    w=c//2%2
    return (c//4,w+2*l,r//2) if c%2 else (c//4,l//2,l%2+2*w+4*(r//2))
def replay(t,rules,cmd,s):
    i,k=cmd
    if i<0:
        for _ in range(k):s=step(t,s)
        return s,k
    q,p,d,l,r,a,b=rules[i];assert s[0]==q
    if d:
        left=strip(l,s[1]);right=striprep(r,a,k,s[2])
        return (q,putrep(l,b,k,left),cat(r,right)),p*k
    else:
        left=striprep(l,a,k,s[1]);right=strip(r,s[2])
        return (q,cat(l,left),putrep(r,b,k,right)),p*k

def parse(path):
    a=Path(path).read_text().splitlines();n,q,b,nr,nc=map(int,a[0].split());rules=[]
    for l in a[1:1+nr]:
        q1,p,d,l,r,c,s=l.split();rules.append((int(q1),int(p),bool(int(d)),l.replace('-',''),r.replace('-',''),c,s))
    cmds=[tuple(map(int,l.split())) for l in a[1+nr:]];assert len(cmds)==nc
    return n,q,b,rules,cmds

def word(w):return '['+','.join('true' if c=='1' else 'false' for c in w)+']'
def lean_rule(a):
    q,p,d,*ws=a
    return '⟨'+','.join([str(q),str(p),str(d).lower()]+[word(w) for w in ws])+'⟩'
def lean_cmd(c):return f'.raw {c[1]}' if c[0]<0 else f'.repeated {c[0]} {c[1]}'
def lean_state(s):return '⟨'+','.join(map(str,s))+'⟩'
def emit(index,path,out,blocksize=128):
    t=TABLES[index];n,q,b,rules,cmds=parse(path);s=(0,0,0);time=0
    # The final unread endpoint may differ from the repeated trace's next-cycle bit.
    # In that case drop the last repetition into exact primitive replay.
    fixed=[]; preview=s; total=0
    for c in cmds:
        try:
            preview,k=replay(t,rules,c,preview);fixed.append(c);total+=k
        except AssertionError:
            i,k=c; assert i>=0 and k>=2
            for cc in [(i,k-1),(-1,rules[i][1])]:
                preview,kk=replay(t,rules,cc,preview);fixed.append(cc);total+=kk
    assert total==n and preview[0]==q and preview[2]%2==b
    cmds=fixed
    f=Path(out).open('w');f.write(f'''import RepeatReplay
namespace BB6.Agent12RepeatReplay.R{index}
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def parent : PartialMachine := fromCodes {t}
def rules : List Rule := [{','.join(map(lean_rule,rules))}]
theorem valid : validate parent rules = true := by decide +kernel
theorem reached0 : BB6.Agent12RepeatReplay.run parent 0 start.view = some start.view := rfl
''')
    blocks=0
    for j in range(0,len(cmds),blocksize):
        block=cmds[j:j+blocksize];a=time
        for c in block:
            s,k=replay(t,rules,c,s);time+=k
        blocks+=1;prev='start' if blocks==1 else f's{blocks-1}'
        f.write(f'''def s{blocks} : Packed := {lean_state(s)}
def c{blocks} : List Command := [{','.join(map(lean_cmd,block))}]
theorem check{blocks} : execute parent rules c{blocks} {prev} {a} = some (s{blocks},{time}) := by decide +kernel
theorem reached{blocks} : BB6.Agent12RepeatReplay.run parent {time} start.view = some s{blocks}.view := by
  have h := (execute_sound parent rules c{blocks} {prev} s{blocks} {a} {time} valid check{blocks}).1
  rw [show {time} = {a} + ({time}-{a}) by decide +kernel]
  rw [BB6.Agent12RepeatReplay.run_add,reached{blocks-1},Option.bind_some,h]
''')
    assert time==n and s[0]==q and s[2]%2==b and t[2*q+b]==24
    hole=f'({q},{str(bool(b)).lower()})'
    f.write(f'''theorem other : ∀ s : Slot, s≠{hole} → ∃ mv, parent s=some (some mv) := by
  intro s hs
  rcases s with ⟨q,b⟩
  have hcases : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by
    have hlt := q.isLt
    simp only [Fin.ext_iff]
    omega
  rcases hcases with h | h | h | h | h | h <;> subst q <;> cases b <;> first | (exact ⟨_,rfl⟩) | contradiction
theorem query : (s{blocks}.q,s{blocks}.read)={hole} := by decide +kernel
theorem all_completions_weighted (B : Nat) (hb : {n+6}≤B) : ∀ m, compatible parent m → WeightedBound B m :=
  weighted_last parent {n} B {hole} s{blocks} hb other query reached{blocks}
#print axioms reached{blocks}
#print axioms all_completions_weighted
end BB6.Agent12RepeatReplay.R{index}
''');f.close(); print(f'{index}: {n} moves, {len(cmds)} commands, {len(rules)} rules, {blocks} blocks, {q}:{b}, {Path(out).stat().st_size} bytes')
if __name__=='__main__':emit(int(sys.argv[1]),sys.argv[2],sys.argv[3],int(sys.argv[4]) if len(sys.argv)>4 else 128)
