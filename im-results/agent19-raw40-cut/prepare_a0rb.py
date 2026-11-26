#!/usr/bin/env python3
"""Rebuild audited five-hole children of Raw40 A1=0RB.
Uses canonical enumeration, FAR certificates, original sweeps and AutoPump.
Generated names avoid collisions with the A1=1RB family.
"""
import json, os, pathlib, re, subprocess, sys
root=pathlib.Path(__file__).resolve().parent
specs={
 '0LA':(100,90,90,{}, {}, ''),
 '1LC':(131,69,69,{}, {}, ''),
 '0RC':(109,76,75,{}, {1:('1RB0RB_1RC0RC_0RD0LE_1LD1LA_0LF---_1LC0RB','RB0RC')}, 'Raw40TwoSided'),
 '1RC':(202,105,104,{}, {16:('1RB0RB_1RC1RC_0RD0LE_1LD1LA_---1LF_1LC0RF','RB1RC')}, 'Raw40MoreTwoSided'),
 '0RE':(156,342,337,{233:'1012134335134',315:'0012344514401',87:'1012345414434'}, {}, ''),
 '1LB':(129,580,576,{217:'1012344454421',550:'1012344454421',6:'1012345234444'}, {}, ''),
 '1LE':(293,1282,1253,{553:'1012134012524',769:'1012134332522',770:'1012134332522',646:'1012234332534',13:'0012234544424',876:'0012301452345',896:'1012322242521',912:'1012322242521',647:'1012322242524',22:'1012322245122',185:'1012322245122',419:'1012322245122',15:'1012322245221',170:'1012322432522',184:'0012322452201',592:'1012322452223',642:'1012322452223',877:'1012341415355',167:'1012343454424',161:'1012345414434'}, {382:('1RB0RB_1RC1LE_0RD---_1LD1LA_0RF0LE_0LA1RF','ZeroRBCounters.Leaf382'),878:('1RB0RB_1RC1LE_0RD---_1LD1LA_1RA0LF_0RA0LF','ZeroRBCounters.Leaf878')}, 'Raw40ZeroRBCounters'),
 '0LE':(637,1111,1059,{1106:'1012123435353',298:'1012133454444',338:'1012133454444',620:'0012234015555',0:'0012301435151',3:'0012301435151',792:'0012301435151',194:'0012301454555',643:'0012301454555',23:'0012322405352',104:'1012322445132',543:'1012322452322',1108:'0012324504422',744:'1012344225355',802:'1012344235555',803:'0012344514401',805:'0012344514401',933:'0012344514401',865:'0012344554401',462:'1012345214444',671:'1012345234444',672:'1012345234444'}, {22:('1RB0RB_1RC0LE_0RD1RF_1LD1LA_0LA1LB_0RA---','ZeroRBCycles.Leaf22'),390:('1RB0RB_1RC0LE_0RD1RF_1LD1LA_1LA1LB_0RA---','ZeroRBCycles.Leaf390'),110:('1RB0RB_1RC0LE_0RD0LA_1LD1LA_0LF1LA_0RA---','ZeroRBCounters.Leaf110'),655:('1RB0RB_1RC0LE_0RD0RA_1LD1LA_1LF1RB_1LC---','ZeroRBNGram655')}, 'Raw40ZeroRBCycles Raw40ZeroRBCounters Raw40ZeroRBNGram655'),
 '1RE':(177,668,654,{461:'1012322242521',456:'1012322452223',459:'1012322452223',139:'0012334504423',506:'1012341554444',529:'1012345234444'}, {515:('1RB0RB_1RC1RE_0RD---_1LD1LA_0RB1LF_1RE0LF','ZeroRBNGram515')}, 'Raw40ZeroRBNGram515'),
}
c=sys.argv[1]
B,N,F,extra,proved,imports=specs[c]
if c in {'0LE','1RE'}:
    subprocess.run([sys.executable,str(root/'build_a0rb_ngrams.py'),'655' if c=='0LE' else '515'],check=True)
p=f'1RB0RB_1RC{c}_0RD---_1LD1LA_------_------'
out=root/'a0rb'/c
out.mkdir(parents=True,exist_ok=True)
for f in ('enumerate_canon','farbank'):
    subprocess.run(['g++','-std=c++20','-O3',str(root/(f+'.cpp')),'-o',str(out/f)],check=True)
run=subprocess.run([str(out/'enumerate_canon'),p],cwd=out,check=True,text=True,stdout=subprocess.PIPE)
opens=(out/'open.txt').read_text().splitlines()
assert len(opens)==N
with (out/'far5.txt').open('w') as f:
    subprocess.run([str(out/'farbank'),'5'],input=''.join(f'{i} {s.replace("_","")}\n' for i,s in enumerate(opens)),text=True,stdout=f,check=True)
ids={int(x.split()[0]) for x in (out/'far5.txt').read_text().splitlines()}
assert len(ids)==F
rows=[r for line in (root/'a0rb-pumps.jsonl').read_text().splitlines() if (r:=json.loads(line))[1][9:12]==c]
pumpids={r[0] for r in rows}
parts=[ids,set(extra),set(proved),pumpids]
assert set.union(*parts)==set(range(N)) and sum(map(len,parts))==N
for r in rows: assert opens[r[0]].replace('_','')==r[1]
for i,(s,_) in proved.items(): assert opens[i]==s
(out/'far_extra.txt').write_text(''.join(f'{i} {v}\n' for i,v in extra.items()))
ns=f'BB6.Agent19Raw40.ZeroRB{c}Pump'
(out/'proven.txt').write_text(''.join(f'{opens[i]} {ns}.Leaf{i}\n' for i in sorted(pumpids))+''.join(f'{s} BB6.Agent19Raw40.{v}\n' for s,v in proved.values()))
if rows:
    cert=out/'pumps.jsonl'
    cert.write_text(''.join(json.dumps(r)+'\n' for r in rows))
    with (root/f'Raw40ZeroRB{c}Pump.lean').open('w') as f:
        subprocess.run([sys.executable,str(root/'emit_autopump.py'),str(cert),ns],stdout=f,check=True)
    imports=f'Raw40ZeroRB{c}Pump '+imports
os.environ['RAW40_PROOF_IMPORTS']=imports.strip()
mod='Raw40C0RB'+c
subprocess.run([sys.executable,str(root/'certify_modular.py'),str(out),str(out/'shards'),p,str(B),mod,'96','600'],check=True)
m=re.search(r'maxscore=(\d+) n=(\d+) delay=(\d+) table=(\S+)',run.stdout)
assert m and int(m[1])==B
n,d,code=int(m[2]),int(m[3]),m[4]
assert B==n+1+d
s=code.replace('_','')
moves=[]
for i in range(12):
    v=s[3*i:3*i+3]
    if v not in ('HHH','---'): moves.append(f'  | {i//2},{str(bool(i%2)).lower()} => some ⟨{str(v[0]=="1").lower()},{str(v[1]=="R").lower()},{ord(v[2])-65}⟩')
(out/'shards'/f'{mod}Exact.lean').write_text(f'''import {mod}All
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.{mod}
open BB6Coverage BB6.Agent13BlankDelay

def witness : Machine := fun s =>
  match s.1.val,s.2 with
{chr(10).join(moves)}
  | _,_ => none

theorem witness_compatible : compatible p witness := by
  intro s t ht
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> first
    | have h : p (_,_) = none := by decide; rw [h] at ht; contradiction
    | cases ht <;> rfl

theorem witness_halts : HaltsAfter witness {n} := by
  constructor <;> rfl

theorem witness_delay : {d} ∈ delays (zeroNext witness) 0 := by decide

theorem exact_weighted : (∀ m, compatible p m → WeightedBound {B} m) ∧
    ∀ B' < {B}, ∃ m, compatible p m ∧ ¬ WeightedBound B' m := by
  refine ⟨all, ?_⟩
  intro B' hB
  refine ⟨witness, witness_compatible, ?_⟩
  intro hb
  have h := hb {n} {d} witness_halts witness_delay
  omega
#print axioms exact_weighted
end BB6.Agent19Raw40.{mod}
''')
