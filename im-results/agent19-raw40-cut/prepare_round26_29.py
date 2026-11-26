#!/usr/bin/env python3
"""Generate complete Raw40 A1=1RC parent audits, using saved compact certificates."""
import os,pathlib,subprocess,sys,json,base64,gzip,hashlib
root=pathlib.Path(__file__).resolve().parent
n=int(sys.argv[1]); c,B,N,F={26:('0LE',216,1392,1347),27:('0RE',193,2328,2265),28:('1LE',131,1453,1406),29:('1RE',5729,1504,1452)}[n]
hashes={26:'38c99c2090ade655dc708978b02756fe6c0e1f21f7f4acaf44aa7936f78278ef',27:'7890fc64fe56d250cd0199fa70d991fe9c4c70312444825ee776b0d975804b21',28:'0be841dcfd83b9b061e801d98efebdfe9e97120d3368c025513a6e3d08856f68'}
if n in hashes:
    raw=base64.b64decode((root/f'round{n}-data.json.gz.b64').read_text())
    assert hashlib.sha256(raw).hexdigest()==hashes[n]
    for f,s in json.loads(gzip.decompress(raw)).items():(root/f).write_text(s)
p=f'1RB1RC_1RC---_0RD{c}_1LD1LA_------_------';out=root/f'round{n}'/'shards-input';out.mkdir(parents=True,exist_ok=True)
for f in ('enumerate_canon','farbank'):
    subprocess.run(['g++','-std=c++20','-O3',str(root/(f+'.cpp')),'-o',str(out/f)],check=True)
subprocess.run([str(out/'enumerate_canon'),p],cwd=out,check=True)
opens=(out/'open.txt').read_text().splitlines();assert len(opens)==N
with (out/'far5.txt').open('w') as f:
    subprocess.run([str(out/'farbank'),'5'],input=''.join(f'{i} {s.replace("_","")}\n' for i,s in enumerate(opens)),text=True,stdout=f,check=True)
farids={int(x.split()[0]) for x in (out/'far5.txt').read_text().splitlines()};assert len(farids)==F
extra=(root/f'round{n}-far-extra.txt').read_text();(out/'far_extra.txt').write_text(extra)
ids=farids|{int(x.split()[0]) for x in extra.splitlines()};assert len(ids)==F+len(extra.splitlines())
ns=f'BB6.Agent19Raw40.Round{n}';pm=f'Raw40Round{n}Pump';imports=[pm];proven=[]
def add(rows,ns):
    for r in rows:
        i,s=r[:2];assert i not in ids and opens[i].replace('_','')==s
        ids.add(i);proven.append(f'{opens[i]} {ns}.Leaf{i}\n')
data=root/f'round{n}-pumps.jsonl';add([json.loads(x) for x in data.read_text().splitlines()],ns)
with (root/f'{pm}.lean').open('w') as f:
    subprocess.run([sys.executable,str(root/'emit_autopump.py'),str(data),ns],stdout=f,check=True)
if n==28:
    data=root/'digit-certs.jsonl';add([json.loads(x) for x in data.read_text().splitlines()],'BB6.Agent19Raw40.DigitLeaves');imports.append('Raw40DigitLeaves')
    with (root/'Raw40DigitLeaves.lean').open('w') as f:subprocess.run([sys.executable,str(root/'emit_digit.py'),str(data)],stdout=f,check=True)
if n==29:
    data=root/'round29-late.txt';late=data.read_text();(out/'late.txt').write_text(late)
    for x in late.splitlines():
        s,steps,slot=x.split();i=opens.index(s);assert i not in ids;ids.add(i)
assert ids==set(range(N)),sorted(set(range(N))-ids)
(out/'proven.txt').write_text(''.join(proven))
os.environ['RAW40_PROOF_IMPORTS']=' '.join(imports)
subprocess.run([sys.executable,str(root/'certify_modular.py'),str(out),str(out/'shards'),p,str(B),f'Raw40C1RC{c}','96','600'],check=True)
