#!/usr/bin/env python3
"""Regenerate Raw40 A1=0RC certificates and child audits."""
import base64,gzip,json,os,re,subprocess,sys
from pathlib import Path
from build_ngram_cases import render
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'agent32-raw59'))
from emit_rungram import emit
specs=json.loads((ROOT/'a0rc-specs.json').read_text())
records=json.loads(gzip.decompress(base64.b64decode((ROOT/'a0rc-rungram.json.gz.b64').read_text())))
extra_records=ROOT/'a0rc-hard-rungram.jsonl'
if extra_records.exists():
    records.extend(json.loads(x) for x in extra_records.read_text().splitlines())
c=sys.argv[1]
B,N,F,extra,grams,remaining=specs[c]
p=f'1RB0RC_1RC---_0RD{c}_1LD1LA_------_------'
out=ROOT/'a0rc'/c
out.mkdir(parents=True,exist_ok=True)
for f,source,std in [('enumerate_canon',ROOT/'enumerate_canon.cpp','c++20'),('farbank',ROOT/'farbank.cpp','c++20'),('ngram',ROOT.parent/'agent1-ngram'/'ngram.cpp','c++17')]:
    subprocess.run(['g++','-std='+std,'-O3',str(source),'-o',str(out/f)],check=True)
run=subprocess.run([str(out/'enumerate_canon'),p],cwd=out,check=True,text=True,capture_output=True)
(out/'enum.log').write_text(run.stdout)
opens=(out/'open.txt').read_text().splitlines()
assert len(opens)==N
with (out/'far5.txt').open('w') as f:
    subprocess.run([str(out/'farbank'),'5'],input=''.join(f'{i} {t.replace("_","")}\n' for i,t in enumerate(opens)),text=True,stdout=f,check=True)
ids={int(x.split()[0]) for x in (out/'far5.txt').read_text().splitlines()}
assert len(ids)==F
rs=[v for v in records if v['c']==c]
rids={v['id'] for v in rs}; gids={g[0] for g in grams}
known={492:('1RB0RC_1RC0RF_0RD0LE_1LD1LA_1LA---_0RC0RB','BB6.Agent19Raw40.A0RC492')} if c=='0LE' else {}
parts=[ids,set(map(int,extra)),rids,gids,set(known),set(remaining)]
assert len(rids)==len(rs) and set.union(*parts)==set(range(N)) and sum(map(len,parts))==N
(out/'far_extra.txt').write_text(''.join(f'{i} {v}\n' for i,v in extra.items()))
mods=[];proven=[]
if known:
    with (ROOT/'Raw40A0RC492Trace.lean').open('w') as f:
        subprocess.run([sys.executable,str(ROOT/'emit_492.py')],cwd=ROOT,stdout=f,check=True)
    mods.extend(['Raw40A0RC492Core','Raw40A0RC492Trace','Raw40A0RC492'])
    for i,(t,ns) in known.items():
        assert opens[i]==t
        proven.append((t,ns))
if rs:
    mod=f'Raw40A0RC{c}Run';ns=f'BB6.Agent19Raw40.A0RC{c}Run'
    for v in rs:
        assert opens[v['id']].replace('_','')==v['table']
        proven.append((opens[v['id']],ns+'.M'+str(v['id'])))
    (ROOT/(mod+'.lean')).write_text('import FastBiDFA\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace '+ns+'\nopen BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1NGram BB6.Agent32FastBiDFA\n'+'\n'.join(emit(v['id'],v['table'],*v['dfa'],[v['states'],v['edges']]) for v in rs)+'\nend '+ns+'\n')
    mods.append(mod)
for i,k,n in grams:
    result=subprocess.run([str(out/'ngram'),str(k)],input=f'{i} {opens[i]}\n',text=True,capture_output=True,check=True).stdout.strip()
    j,cert=result.split(maxsplit=1)
    assert int(j)==i and list(map(int,cert.split()[:2]))==[k,n]
    ns=f'BB6.Agent19Raw40.A0RC{c}Gram.M{i}';mod=f'Raw40A0RC{c}Gram{i}'
    (ROOT/(mod+'.lean')).write_text('import NGramCertificate\nset_option maxRecDepth 6000000\nset_option maxHeartbeats 0\n'+render(i,opens[i],cert,ns))
    mods.append(mod);proven.append((opens[i],ns))
(out/'proven.txt').write_text(''.join(f'{t} {ns}\n' for t,ns in proven))
(out/'imports.txt').write_text(' '.join(mods))
if remaining:
    print('Open leaves:',[(i,opens[i]) for i in remaining]);sys.exit(0)
os.environ['RAW40_PROOF_IMPORTS']=' '.join(mods)
mod='Raw40C0RC'+c
subprocess.run([sys.executable,str(ROOT/'certify_modular.py'),str(out),str(out/'shards'),p,str(B),mod,'96','600'],check=True)
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
