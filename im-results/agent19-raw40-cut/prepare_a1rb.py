#!/usr/bin/env python3
"""Rebuild all ten canonical A1=1RB child bounds; five are new certificates."""
import json, os, pathlib, subprocess, sys
root=pathlib.Path(__file__).resolve().parent
specs={
'0LA':(76,209,209,{}, {}, {}, ''),
'0LC':(100,37,37,{}, {}, {}, ''),
'0RC':(219,178,177,{}, {}, {}, 'Raw40MoreTwoSided'),
'1LC':(43,68,68,{}, {}, {}, ''),
'1RC':(60,206,206,{}, {}, {}, ''),
'0LE':(1130,716,691,{311:'0012322415101',328:'0012322415101',325:'0012322452220',450:'0012322452221',252:'1012322452322',253:'1012322452322',254:'1012322452322',310:'1012322452322',323:'0012324254440',326:'0012324254440',83:'1012344225355',255:'0012344514401'},{518:('1RB1RB_1RC0LE_0RD0RC_1LD1LA_---1LF_1LB0RF','Round43NestedRB')},{87:('1RB1RB_1RC0LE_0RD1RB_1LD1LA_---0LF_1LB0RB',1129,8)},'Raw40Round43NestedRB'),
'0RE':(212,809,805,{490:'1010234335151',115:'1012134332533',589:'1012134332533',0:'0012344514401'}, {}, {}, ''),
'1LB':(77,961,943,{632:'0012322452201',895:'0012322452201',897:'0012322452201',901:'0012322452201',903:'0012322452201',898:'0012344254401',900:'0012344254401',344:'1012344454421',625:'1012344454421',627:'1012344454421',628:'1012344454421',629:'1012344454421',631:'1012344454421',633:'1012344454421',896:'1012344454421',904:'1012344454421'},{325:('1RB1RB_1RC1LB_0RD0RE_1LD1LA_1LF1RE_---0LB','Round42NestedRB')},{},'Raw40Round42NestedRB'),
'1LE':(101,960,939,{57:'1011232141513',127:'1011232141513',184:'1011232141514',30:'1012133455155',31:'1012133455155',49:'1012234335131',179:'0012234345444',741:'0012322450141',743:'0012322450141',745:'0012322450141',765:'0012322450141',793:'0012322450141',771:'0012322452001',722:'0012322452201',737:'0012322452201',687:'0012322452241',703:'0012322452241',442:'1012341514443',367:'1012343514441'},{},{},''),
'1RE':(131,1065,1053,{155:'0010234010500',53:'0012131451521',51:'1012134454424',3:'1012234335334',950:'1012234335334',143:'0012322452201',628:'0012322452223',582:'1012322452511',645:'1012344454423',697:'1012344454423'},{},{},''),
}
c=sys.argv[1]
B,count,farcount,extra,proved,late,imports=specs[c]
p=f'1RB1RB_1RC{c}_0RD---_1LD1LA_------_------'
out=root/'a1rb'/c
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
rows=[r for x in (root/'a1rb-pumps.jsonl').read_text().splitlines() if (r:=json.loads(x))[1][9:12]==c]
pumpids={r[0] for r in rows}
parts=[ids,set(extra),pumpids,set(proved),set(late),{27} if c=='0RC' else set()]
assert set.union(*parts)==set(range(count)) and sum(map(len,parts))==count
(out/'far_extra.txt').write_text(''.join(f'{i} {v}\n' for i,v in extra.items()))
for r in rows:assert opens[r[0]].replace('_','')==r[1]
for i,(s,_) in proved.items():assert opens[i]==s
for i,(s,_,_) in late.items():assert opens[i]==s
ns=f'BB6.Agent19Raw40.RB{c}Pump'
(out/'proven.txt').write_text(''.join(f'{opens[i]} {ns}.Leaf{i}\n' for i in sorted(pumpids))+''.join(f'{s} BB6.Agent19Raw40.{v}\n' for s,v in proved.values()))
(out/'late.txt').write_text(''.join(f'{s} {n} {slot}\n' for s,n,slot in late.values()))
if c=='0RC':assert opens[27]=='1RB1RB_1RC0RC_0RD0LE_1LD1LA_1RB1LF_---1LC'
if rows:
    cert=out/'pumps.jsonl'
    cert.write_text(''.join(json.dumps(r)+'\n' for r in rows))
    with (root/f'Raw40RB{c}Pump.lean').open('w') as f:
        subprocess.run([sys.executable,str(root/'emit_autopump.py'),str(cert),ns],stdout=f,check=True)
    imports=f'Raw40RB{c}Pump '+imports
os.environ['RAW40_PROOF_IMPORTS']=imports.strip()
subprocess.run([sys.executable,str(root/'certify_modular.py'),str(out),str(out/'shards'),p,str(B),'Raw40C1RB'+c,'96','600'],check=True)
