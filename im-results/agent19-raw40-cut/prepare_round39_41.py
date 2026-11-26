#!/usr/bin/env python3
"""Regenerate Raw40 A1=0RD, B1 in {1LB,1LE,1RE} (rounds 39–41)."""
import json, os, pathlib, subprocess, sys
root=pathlib.Path(__file__).resolve().parent
specs={
39:('1LB',102,887,867,{368:'0012301450133',828:'1012322240523',563:'0012322452201',568:'0012322452201',570:'1012341454441',344:'1012344454421',561:'1012344454421',562:'1012344454421',564:'1012344454421',565:'1012344454421',566:'1012344454421',569:'1012344454421',571:'1012344454421',826:'1012344454421'},{323:('1RB0RD_1RC1LB_0RD0RE_1LD1LA_1LF1RE_---0LB','Round39Nested')},'Raw40Round39Nested'),
40:('1LE',266,980,968,{160:'1011232141513',218:'1011232141513',273:'1011232141514',152:'1012234335131',269:'0012234345444',789:'1012322242523',451:'1012343514441',754:'1012344454421'},{},''),
41:('1RE',125,1032,1024,{30:'0012131451521',901:'0012301450122',635:'1012344454423',921:'1012345454424'},{126:('1RB0RD_1RC1RE_0RD---_1LD1LA_1RA0LF_0RA0LF','BinaryCarry.Counter181'),900:('1RB0RD_1RC1RE_0RD---_1LD1LA_1LF1RB_0RA0LF','BinaryCarry.Counter184')},'Raw40BinaryCarry'),
}
n=int(sys.argv[1])
c,B,count,farcount,extra,proved,imports=specs[n]
p=f'1RB0RD_1RC{c}_0RD---_1LD1LA_------_------'
out=root/f'round{n}'/'shards-input'
out.mkdir(parents=True,exist_ok=True)
for f in ('enumerate_canon','farbank'):
    subprocess.run(['g++','-std=c++20','-O3',str(root/(f+'.cpp')),'-o',str(out/f)],check=True)
subprocess.run([str(out/'enumerate_canon'),p],cwd=out,check=True)
opens=(out/'open.txt').read_text().splitlines()
assert len(opens)==count
with (out/'far5.txt').open('w') as f:
    subprocess.run([str(out/'farbank'),'5'],input=''.join(f'{i} {s.replace("_","")}\n' for i,s in enumerate(opens)),text=True,stdout=f,check=True)
ids={int(x.split()[0]) for x in (out/'far5.txt').read_text().splitlines()}
assert len(ids)==farcount
rows=[json.loads(x) for x in (root/f'round{n}-pumps.jsonl').read_text().splitlines()]
pumpids={r[0] for r in rows}
parts=[ids,set(extra),pumpids,set(proved)]
assert set.union(*parts)==set(range(count)) and sum(map(len,parts))==count
(out/'far_extra.txt').write_text(''.join(f'{i} {v}\n' for i,v in extra.items()))
for r in rows:assert opens[r[0]].replace('_','')==r[1]
for i,(s,_) in proved.items():assert opens[i]==s
ns=f'BB6.Agent19Raw40.Round{n}Pump'
(out/'proven.txt').write_text(''.join(f'{opens[i]} {ns}.Leaf{i}\n' for i in sorted(pumpids))+''.join(f'{s} BB6.Agent19Raw40.{v}\n' for s,v in proved.values()))
(out/'late.txt').write_text('')
with (root/f'Raw40Round{n}Pump.lean').open('w') as f:
    subprocess.run([sys.executable,str(root/'emit_autopump.py'),str(root/f'round{n}-pumps.jsonl'),ns],stdout=f,check=True)
os.environ['RAW40_PROOF_IMPORTS']=f'Raw40Round{n}Pump {imports}'.strip()
subprocess.run([sys.executable,str(root/'certify_modular.py'),str(out),str(out/'shards'),p,str(B),'Raw40C0RD'+c,'96','600'],check=True)
