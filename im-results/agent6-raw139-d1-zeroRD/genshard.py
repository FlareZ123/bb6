#!/usr/bin/env python3
"""Emit exact Lean proof shards from discovered sweep witnesses.
Invoke from the directory where discover.py wrote the JSON files.
Pass output directory via LEAN_OUT (default normalized/build).
The final consumer theorems use only kernel-checked reduction and soundness."""
import json,sys,os
from pathlib import Path
from collections import Counter
def bits(s):return '['+','.join('true' if c=='1' else 'false' for c in s)+']'
def pack(s):return f'⟨{len(s)},{int(s[::-1] or "0",2)}⟩'
def zlit(z):return f'⟨{z[0]},{pack(z[1])},{pack(z[2])}⟩'
D=Path(os.environ.get('LEAN_OUT','normalized/build'))
D.mkdir(parents=True,exist_ok=True)
def create(data,name,chunk=25,shard=500,safe=False):
    acts=data['actions']; n=len(acts);t=[0]+data['times'];z=[data.get('start',[0,'',''])]+data['endpoints']; pats={}
    for a in acts:
        if a[0]!='raw':pats.setdefault(tuple(a[:-1]),len(pats))
    ev='pleval' if safe else 'peval'; header=f'''import {'OneSideSweep' if safe else 'PackedSweepTrace'}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace {name}
open BB6Coverage BB6Coverage.Agent6SweepTrace BB6Coverage.Agent6PackedSweep{' BB6Coverage.Agent6OneSide' if safe else ''}
open BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6Coverage.Agent10ZipAudit
'''
    common=header+f'def p : PartialMachine := FAR.fromCodes {str(data["codes"]).replace(" ","")}\n'
    for pat,i in pats.items():
        side,lp,rp,I,O,k=pat
        common+=f'def s{i} (n : Nat) : Action := .{side} {bits(lp)} {bits(rp)} {bits(I)} {bits(O)} {k} n\n'
    for j in range(0,n,chunk):common+=f'def z{j} : PZ := {zlit(z[j])}\n'
    common+=f'def z{n} : PZ := {zlit(z[n])}\nend {name}\n';(D/(name+'Data.lean')).write_text(common)
    modules=[]; bounds=[]
    for i,lo in enumerate(range(0,n,shard)):
        assert shard%chunk==0
        hi=min(lo+shard,n);module=f'{name}S{i}';modules.append(module);bounds.append((lo,hi))
        s=f'import {name}Data\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nnamespace {name}\nopen BB6Coverage BB6Coverage.Agent6SweepTrace BB6Coverage.Agent6PackedSweep'+(' BB6Coverage.Agent6OneSide' if safe else '')+'\n'
        for j in range(lo,hi,chunk):
            k=min(j+chunk,hi);expr=lambda a:f'.raw {a[1]}' if a[0]=='raw' else f's{pats[tuple(a[:-1])]} {a[-1]}'
            s+=f'def a{k} : List Action := [{", ".join(map(expr,acts[j:k]))}]\ntheorem v{k} : {ev} p a{k} z{j} = some ({t[k]-t[j]},z{k}) := rfl\n'
        if safe:
            s+=f'theorem extend{i} (a : BB6Coverage.Agent31Pump.Z0) (m : Nat) (h : ExtReach p a m z{lo}) : ExtReach p a (m+{t[hi]-t[lo]}) z{hi} := by\n'
            for j in range(lo,hi,chunk):
                k=min(j+chunk,hi);s+=f'  have r{k} := extReach_extend a{k} '+('h' if j==lo else f'r{j}')+f' v{k}\n'
        else:
            s+=f'theorem extend{i} (m : Nat) (h : Reach p m z{lo}) : Reach p (m+{t[hi]-t[lo]}) z{hi} := by\n'
            for j in range(lo,hi,chunk):
                k=min(j+chunk,hi);s+=f'  have r{k} := reach_extend a{k} '+('h' if j==lo else f'r{j}')+f' v{k}\n'
        s+=f'  simpa only [Nat.add_assoc] using r{hi}\nend {name}\n';(D/(module+'.lean')).write_text(s)
    s=''.join(f'import {m}\n' for m in modules)+f'''set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace {name}
open BB6Coverage BB6Coverage.Agent6SweepTrace BB6Coverage.Agent6PackedSweep BB6Coverage.Agent31Pump'''+(' BB6Coverage.Agent6OneSide' if safe else '')+'''\nopen BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6Coverage.Agent10ZipAudit
'''
    if safe:
        q,L,R=z[0];s+=f'def initial : Z0 := ⟨{q},{bits(L)},{bits(R)}⟩\ntheorem r0 : ExtReach p initial 0 z0 := extReach0 p initial\n'
        for i,(lo,hi) in enumerate(bounds):s+=f'theorem r{hi} : ExtReach p initial {t[hi]} z{hi} := extend{i} initial {t[lo]} r{lo}\n'
        q,L,R=z[n];s+=f'def final : Z0 := ⟨{q},{bits(L)},{bits(R)}⟩\ntheorem cycle (L : List Bool) : run0 p {t[n]} (extL initial L) = some (extL final L) := extReach_exact p initial final {t[n]} r{n} L\n#print axioms cycle\n'
    else:
        s+='theorem r0 : Reach p 0 z0 := reach0 p\n'
        for i,(lo,hi) in enumerate(bounds):s+=f'theorem r{hi} : Reach p {t[hi]} z{hi} := extend{i} {t[lo]} r{lo}\n'
        q,L,R=z[n];b='true' if L.startswith('1') else 'false';time=t[n];B=time+1
        if data['codes'][2*q+(b=='true')]==24:
            s+=f'''
theorem readArrival : (knownRun p {time}).map readSlot = some ({q},{b}) := reach_read p {time} z{n} r{n}
theorem cover : Cover (WeightedBound {B}) p := by
  cases hr : knownRun p {time} with
  | none => have H := readArrival; simp [hr] at H
  | some c =>
    have hs : readSlot c = ({q},{b}) := by simpa [hr] using readArrival
    have hroot : p initialSlot = some (some ⟨true,true,1⟩) := by decide
    have hh : p ({q},{b}) = none := by decide
    have hrest : restOK p ({q},{b}) = true := by decide
    exact .leaf _ (WeightedTNFCertificate.lastHole (cut := 6) hroot (support6 p) (by decide) hr
      (by rw [hs]; exact hh)
      (by rw [hs]; exact restOK_sound _ _ hrest)
      (by rw [hs]; exact weightOK_sound _ _ _ _ (by decide : weightOK p ({q},{b}) {time} {B} = true))).sound
#print axioms cover
'''
        else:
            s+=f'theorem reached : Reach p {time} z{n} := r{n}\n#print axioms reached\n'
    s+=f'end {name}\n';(D/(name+'.lean')).write_text(s)
    return [name+'Data']+modules+[name]
if __name__=='__main__':
    ids=[int(x) for x in sys.argv[1:]];modules=[]
    for i in ids:
        if i in [3,335]:modules+=create(json.loads(Path(f'compressed-{i}.json').read_text()),f'A6Trace{i}',25,500)
        else:
            modules+=create(json.loads(Path(f'cycle-entry-{i}.json').read_text()),f'A6Entry{i}',25,500)
            modules+=create(json.loads(Path(f'cycle-period-{i}.json').read_text()),f'A6Cycle{i}',25,500,True)
    print('\n'.join(modules))
