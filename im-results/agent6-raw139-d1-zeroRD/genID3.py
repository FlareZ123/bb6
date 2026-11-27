#!/usr/bin/env python3
"""Untrusted witness generator; all local rule and replay equalities checked by Lean."""
from pathlib import Path
from collections import OrderedDict
import sys
P=[7,19,11,0,14,23,2,13,9,16,5,24]
K=16; CHUNK=100; SHARD=1000

def step(q,l,r):
    c=P[2*q+(l&1)]
    if c==24:return None
    q=c//4; w=c//2&1; d=1 if c&1 else -1
    if d==1: return q,(r&1)+2*w+4*(l//2),r//2,d
    return q,l//2,w+2*r,d

def win(q,l,r,nl,nr,k):
    for _ in range(k):
        assert nl>0
        res=step(q,l,r); assert res is not None
        q,l,r,d=res
        assert d==-1 or nr>0
        nl+=d;nr-=d
    return q,l,r,nl,nr

def lit(z):return '⟨'+','.join(map(str,z))+'⟩'
def head(imp):return f'import {imp}\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nnamespace A6ID3\nopen BB6Coverage BB6Coverage.A6BitTrace BB6Coverage.A6WindowMacro\n'
def write(name,s):Path(name+'.lean').write_text(s+'end A6ID3\n')

def generate():
    z=(0,0,0); zs=[z]; steps=[]; rules={}; seq=[]; t=0
    while True:
        q,l,r=z; cur=z; h=lo=hi=0; k=0
        for _ in range(K):
            a=step(*cur)
            if a is None:break
            cur=a[:3];h+=a[3];lo=min(lo,h);hi=max(hi,h);k+=1
        if k==0:break
        nl,nr=1-lo,hi; w=(q,l%2**nl,r%2**nr,nl,nr)
        v=win(*w,k)
        assert (v[0],v[1]+2**v[3]*(l//2**nl),v[2]+2**v[4]*(r//2**nr))==cur
        key=(k,w,v)
        if key not in rules:rules[key]=len(rules)
        seq.append(rules[key]); t+=k; steps.append(k); zs.append(cur); z=cur
    assert t==795108 and z[0]==5 and z[1]&1
    ts=[0];
    for k in steps:ts.append(ts[-1]+k)
    data=head('A6WindowMacro')+f'def p : PartialMachine := FAR.fromCodes {P}\n'
    for (k,w,v),i in rules.items():data+=f'def r{i} : Rule p := ⟨{k},{lit(w)},{lit(v)},rfl⟩\n'
    write('A6ID3Rules',data)
    modules=[];bounds=[]
    for i,lo in enumerate(range(0,len(seq),SHARD)):
        hi=min(lo+SHARD,len(seq));name=f'A6ID3Part{i}';modules.append(name);bounds.append((lo,hi))
        s=head('A6ID3Rules')
        for j in range(lo,hi,CHUNK):
            k=min(j+CHUNK,hi)
            s+=f'def z{i}_{j} : P := {lit(zs[j])}\n'
            s+=f'def a{k} : List (Rule p) := ['+','.join(f'r{x}' for x in seq[j:k])+']\n'
            s+=f'theorem check{k} : eval p a{k} z{i}_{j} = some ({ts[k]-ts[j]},{lit(zs[k])}) := rfl\n'
        s+=f'theorem extend{i} (n : Nat) (h : Reach p n {lit(zs[lo])}) : Reach p (n+{ts[hi]-ts[lo]}) {lit(zs[hi])} := by\n'
        for j in range(lo,hi,CHUNK):
            k=min(j+CHUNK,hi)
            s+=f'  have h{k} := eval_reach p a{k} _ _ _ _ '+('h' if j==lo else f'h{j}')+f' check{k}\n'
        s+=f'  simpa only [Nat.add_assoc] using h{hi}\n'
        write(name,s)
    s=''.join(f'import {m}\n' for m in modules)+'''set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace A6ID3
open BB6Coverage BB6Coverage.A6BitTrace BB6Coverage.A6WindowMacro
open BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6Coverage.Agent10ZipAudit
'''
    s+='theorem initial : Reach p 0 ⟨0,0,0⟩ := reach0 p\n'
    for i,(lo,hi) in enumerate(bounds):s+=f'theorem reach{hi} : Reach p {ts[hi]} {lit(zs[hi])} := extend{i} {ts[lo]} '+('initial' if lo==0 else f'reach{lo}')+'\n'
    s+=f'''theorem readArrival : (knownRun p {t}).map readSlot = some (5,true) := reach_read p {t} {lit(zs[-1])} reach{len(seq)}
theorem cover : Cover (WeightedBound {t+1}) p := by
  cases hr : knownRun p {t} with
  | none => have H := readArrival; simp [hr] at H
  | some c =>
    have hs : readSlot c = (5,true) := by simpa [hr] using readArrival
    have hroot : p initialSlot = some (some ⟨true,true,1⟩) := by decide
    have hh : p (5,true) = none := by decide
    have hrest : restOK p (5,true) = true := by decide
    exact .leaf _ (WeightedTNFCertificate.lastHole (cut := 6) hroot (support6 p) (by decide) hr
      (by rw [hs]; exact hh)
      (by rw [hs]; exact restOK_sound _ _ hrest)
      (by rw [hs]; exact weightOK_sound _ _ _ _ (by decide : weightOK p (5,true) {t} {t+1} = true))).sound
#print axioms readArrival
#print axioms cover
'''
    write('A6ID3',s)
    print('A6ID3Rules',*modules,'A6ID3',sep='\n')
    print(f'rules={len(rules)} calls={len(seq)} steps={t}',file=sys.stderr)
if __name__=='__main__':generate()
