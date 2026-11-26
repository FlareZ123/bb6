#!/usr/bin/env python3
"""Generate all nine canonical children for the complete A1=0RD certificate."""
import os, pathlib, subprocess, sys
root=pathlib.Path(__file__).resolve().parent
c=sys.argv[1]
if c in {'0LE','1LB','1LE','1RE'}:
    n={'0LE':38,'1LB':39,'1LE':40,'1RE':41}[c]
    script='prepare_round38.py' if n==38 else 'prepare_round39_41.py'
    subprocess.run([sys.executable,str(root/script)]+([] if n==38 else [str(n)]),check=True)
    sys.exit()
B,N,F,extra,imports={ 
 '0LC':(106,39,39,{},''),
 '1LC':(47,76,76,{},''),
 '1RC':(64,207,207,{},''),
 '0RC':(225,196,195,{},'Raw40MoreTwoSided'),
 '0RE':(214,836,831,{0:'0012344514401',108:'1012134332533',515:'1010234335151',608:'1012134332533',611:'1012131454434'},''),
}[c]
p=f'1RB0RD_1RC{c}_0RD---_1LD1LA_------_------'
out=root/'a0rd'/c
out.mkdir(parents=True,exist_ok=True)
for f in ('enumerate_canon','farbank'):
    subprocess.run(['g++','-std=c++20','-O3',str(root/(f+'.cpp')),'-o',str(out/f)],check=True)
subprocess.run([str(out/'enumerate_canon'),p],cwd=out,check=True)
opens=(out/'open.txt').read_text().splitlines()
assert len(opens)==N
with (out/'far5.txt').open('w') as f:
    subprocess.run([str(out/'farbank'),'5'],input=''.join(f'{i} {s.replace("_","")}\n' for i,s in enumerate(opens)),text=True,stdout=f,check=True)
ids={int(x.split()[0]) for x in (out/'far5.txt').read_text().splitlines()}
assert len(ids)==F
assert not(ids&set(extra))
if c=='0RC':
    assert [s for i,s in enumerate(opens) if i not in ids]==['1RB0RD_1RC0RC_0RD0LE_1LD1LA_1RB1LF_---1LC']
else:
    assert ids|set(extra)==set(range(N))
(out/'far_extra.txt').write_text(''.join(f'{i} {v}\n' for i,v in extra.items()))
os.environ['RAW40_PROOF_IMPORTS']=imports
subprocess.run([sys.executable,str(root/'certify_modular.py'),str(out),str(out/'shards'),p,str(B),'Raw40C0RD'+c,'96','600'],check=True)
