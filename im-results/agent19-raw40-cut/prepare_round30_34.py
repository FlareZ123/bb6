#!/usr/bin/env python3
"""Rebuild the five previously investigated A1=1RC siblings using stored evidence."""
import os,pathlib,subprocess,sys,json
root=pathlib.Path(__file__).resolve().parent
n=int(sys.argv[1]);c,B,N,F={30:('0LA',69,77,71),31:('0RB',147,275,270),32:('1RB',1147,138,136),33:('0RD',57,81,77),34:('1LB',85,81,79)}[n]
p=f'1RB1RC_1RC---_0RD{c}_1LD1LA_------_------'
out=root/f'round{n}'/'shards-input';out.mkdir(parents=True,exist_ok=True)
for f in ('enumerate_canon','farbank'):
    subprocess.run(['g++','-std=c++20','-O3',str(root/(f+'.cpp')),'-o',str(out/f)],check=True)
subprocess.run([str(out/'enumerate_canon'),p],cwd=out,check=True)
opens=(out/'open.txt').read_text().splitlines();assert len(opens)==N
with (out/'far5.txt').open('w') as f:
    subprocess.run([str(out/'farbank'),'5'],input=''.join(f'{i} {s.replace("_","")}\n' for i,s in enumerate(opens)),text=True,stdout=f,check=True)
ids={int(x.split()[0]) for x in (out/'far5.txt').read_text().splitlines()};assert len(ids)==F
extras=[];proven=[];late=[];imports=[]
ns=f'BB6.Agent19Raw40.Sibling{n}';pm=f'Raw40Sibling{n}Pump'
data={str(r[0]):r for r in map(json.loads,(root/'autopump2-certs.jsonl').read_text().splitlines())}
rows=[]
for fname in ('near2-evidence.txt','near6-evidence.txt'):
    for line in (root/fname).read_text().splitlines():
        if not line.startswith(f'1RC_{c} '):continue
        _,idx,kind,value=line.split();i=int(idx)
        if i in ids:continue
        if kind=='far':extras.append(f'{i} {value}\n')
        elif kind=='late':
            steps,slot=value.split(',');late.append(f'{opens[i]} {steps} {slot}\n')
        elif kind=='pump2' and n in (30,31):
            row=data[value][:];assert opens[i].replace('_','')==row[1];row[0]=i;rows.append(row)
            proven.append(f'{opens[i]} {ns}.Leaf{i}\n')
        else:continue
        ids.add(i)
if n==34:
    assert opens[68]=='1RB1RC_1RC1RE_0RD1LB_1LD1LA_1LF0RF_---0LB'
    assert 68 not in ids and 75 not in ids
    ids.update((68,75))
    extras.append('75 1012343514441\n')
    proven.append(opens[68]+' BB6.Agent19Raw40.OneRC1LB\n')
    src=(root/'Raw40MoreTwoSided.lean').read_text()
    i=src.index('private theorem rep_add');j=src.index('end OneRC1LB',i)+len('end OneRC1LB')
    (root/'Raw40OneRC1LB.lean').write_text('import SweepPumping\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6.Agent19Raw40\nopen BB6Coverage BB6Coverage.Agent31Pump\n'+src[i:j]+'\nend BB6.Agent19Raw40\n')
    imports.append('Raw40OneRC1LB')
assert ids==set(range(N)),sorted(set(range(N))-ids)
(out/'far_extra.txt').write_text(''.join(extras));(out/'proven.txt').write_text(''.join(proven));(out/'late.txt').write_text(''.join(late))
if rows:
    (out/'pumps.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
    with (root/f'{pm}.lean').open('w') as f:
        subprocess.run([sys.executable,str(root/'emit_autopump.py'),str(out/'pumps.jsonl'),ns],stdout=f,check=True)
    imports.append(pm)
(root/f'Raw40Round{n}Pump.lean').write_text('import SweepPumping\n')
(root/f'Raw40Round{n}Exact.lean').write_text(f'import Raw40C1RC{c}All\n#print axioms BB6.Agent19Raw40.Raw40C1RC{c}.all\n#print axioms BB6.Agent19Raw40.Raw40C1RC{c}.all_quotient\n')
os.environ['RAW40_PROOF_IMPORTS']=' '.join(imports)
subprocess.run([sys.executable,str(root/'certify_modular.py'),str(out),str(out/'shards'),p,str(B),f'Raw40C1RC{c}','96','900'],check=True)
