"""Rebuild selected Raw47 roster, discovery bank and candidate certificates."""
import base64, hashlib, lzma, pathlib, subprocess, sys, concurrent.futures
here=pathlib.Path(__file__).resolve().parent
out=pathlib.Path(sys.argv[1]).resolve(); out.mkdir(parents=True,exist_ok=True)
base=here.parent/'agent50-raw47-depth3'
raw=(base/'raw47-depth3.open').read_bytes()
assert hashlib.sha256(raw).hexdigest()=='4ae501c6ae90d482f77d8ba65b060717112e402571f887c20fdcd4c4b0bce41d'
rows=raw.decode().splitlines()
mask=base64.b64decode((base/'broad-far-parents.b64').read_text()); assert len(mask)==1212 and sum(mask)==674
hard={int(x.split()[1]) for x in (base/'hard30.txt').read_text().splitlines()}
ids=[i for i,b in enumerate(mask) if not b and i not in hard]
assert len(ids)==515
bank=lzma.decompress(base64.b64decode((base/'broad-far-bank.xz.b64').read_text())); assert len(bank.split())==332
(out/'bank').write_bytes(bank)
for src,exe,options in [('scan.cpp','scan',['-I',str(here.parent/'agent32-linear-side-cycle')]),('far.cpp','far',[]),('run_search.cpp','run_search',[]),('long_scan.cpp','long_scan',['-I',str(here.parent/'agent32-linear-side-cycle')])]:
 subprocess.run(['g++','-std=c++20','-O3',*options,str(here/src),'-o',str(out/exe)],check=True)
def execute(name,cmd,source):
 (out/(name+'.in')).write_text(source)
 with (out/(name+'.ok')).open('w') as f,(out/(name+'.no')).open('w') as e:
  subprocess.run([str(out/cmd[0]),*cmd[1:]],input=source,text=True,stdout=f,stderr=e,check=True)
 return (out/(name+'.ok')).read_text(),(out/(name+'.no')).read_text()
def search(group,ids):
 text=''.join(f'{i} {rows[i].replace("_", "")}\n' for i in ids)
 op,log=execute(group+'-scan',['scan','10000'],text)
 (out/(group+'-open.txt')).write_text(op)
 enum=''.join(f'{i} {x.split()[1]}\n' for i,x in enumerate(op.splitlines()))
 hits,miss=execute(group+'-far',['far',str(out/'bank')],enum)
 print(group,'open',len(op.splitlines()),'FAR',len(hits.splitlines()),'miss',len(miss.splitlines()),flush=True)
 a,b=execute(group+'-cheap',['run_search','10000','150'],miss)
 c,d=execute(group+'-deep',['run_search','80000','999999'],b)
 if group=='pilot':
  assert not d.strip(); resolved=a+c; residual=''
 else:
  long,_=execute(group+'-long',['long_scan'],d)
  (out/(group+'-long.txt')).write_text(long)
  nonhalting=''.join(' '.join(x.split()[:2])+'\n' for x in long.splitlines() if x.split()[2]=='0')
  e,residual=execute(group+'-asym',['run_search','asym','5000','50000'],nonhalting)
  resolved=a+c+e
 (out/(group+'-graph-hits.txt')).write_text(resolved)
 (out/(group+'-residual.txt')).write_text(residual)
 print(group,'graphs',len(resolved.splitlines()),'residual',len(residual.splitlines()),flush=True)
 return resolved
with concurrent.futures.ThreadPoolExecutor(2) as ex:
 pilot,rest=list(ex.map(lambda args:search(*args),[('pilot',ids[:30]),('rest',ids[30:])]))
rest=''.join(str(int(x.split()[0])+1000000)+' '+x.split(' ',1)[1]+'\n' for x in rest.splitlines())
all_hits=pilot+rest
(out/'all-graph-hits.txt').write_text(all_hits)
selection=all_hits.splitlines()
if len(sys.argv)>2: selection=selection[:int(sys.argv[2])]
with (out/'graphs.txt').open('w') as f:
 subprocess.run([str(out/'run_search'),'emit'],input='\n'.join(selection)+'\n',text=True,stdout=f,check=True)
subprocess.run([sys.executable,str(here/'emit_graph.py'),str(out/'graphs.txt'),str(out/'proofs')],check=True)
