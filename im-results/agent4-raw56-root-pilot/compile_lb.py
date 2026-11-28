#!/usr/bin/env python3
"""Compile the 1LB source graph using balanced, disjoint root shards."""
import argparse,json,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'agent1-raw56'))
import root_pilot_accept as c
TAG='E11LB'
def balance(prep):
 p=prep/TAG/'manifest.json';m=json.loads(p.read_text());D={x:set(y) for x,y in m};base=m[0][0]
 def size(x):
  seen=set();todo=[x]
  while todo:
   y=todo.pop()
   if y in seen or y not in D or y==base:continue
   seen.add(y);todo.extend(D[y])
  return len(seen)
 top=m[-1][1];assert len(top)==24
 order=sorted(top,key=size,reverse=True);m[-1][1]=order[:12]+list(reversed(order[12:]));p.write_text(json.dumps(m,indent=2)+'\n')
 meta=prep/TAG/'accept-meta.json';a=json.loads(meta.read_text());a['top_roots']=m[-1][1];a['long_modules']=[x for x in a['growth_modules'] if 'Long' in x];a['growth_modules']=[x for x in a['growth_modules'] if 'Long' not in x];meta.write_text(json.dumps(a,indent=2)+'\n')
 print('Balanced cut loads',[sum(map(size,m[-1][1][i::12])) for i in range(12)])
def main():
 p=argparse.ArgumentParser();p.add_argument('mode',choices=['balance','cert','cut','long','final']);p.add_argument('--prep',type=Path,required=True);p.add_argument('--base',type=Path);p.add_argument('--out',type=Path);p.add_argument('--certs',type=Path);p.add_argument('--cuts',type=Path);p.add_argument('--shard',type=int);a=p.parse_args()
 if a.mode=='balance':balance(a.prep);return
 if a.mode=='cert':c.compile_certs(a.prep,a.base,TAG,a.shard,12,a.out);return
 if a.mode=='cut':c.compile_cut(a.prep,a.base,a.certs,TAG,a.shard,12,a.out);return
 lean=c.lean_bin();a.out.mkdir(parents=True,exist_ok=True)
 if a.mode=='long':
  mod=f'rootgrowth.E11LBLong{a.shard}'
  txt=c.compile_module(lean,a.prep,mod,a.out,c.env_for(a.base,a.out,a.prep))
  print(txt,flush=True);assert f'M{a.shard}.bound_quotient' in txt
  return
 (a.out/TAG).mkdir(exist_ok=True)
 env=c.env_for(a.base,a.out,a.out/TAG,a.cuts,a.cuts/TAG,a.certs,a.prep/TAG,a.prep)
 checker=Path('im-results/agent1-raw57/check_axioms.py')
 for mod,theorem in [('Raw56LBE11LBAll','partial_quotient'),('Raw56LBE11LBReduced','reduced_quotient')]:
  txt=c.compile_module(lean,a.prep,f'{TAG}.{mod}',a.out,env);print(txt,flush=True)
  full=f'BB6.Agent4Raw56LB.E11LB.{theorem}';assert full in txt
  log=a.out/TAG/f'{mod}.log'
  c.run([sys.executable,str(checker),str(log),'--require',full])
  assert (a.out/TAG/f'{mod}.olean').exists()
 (a.out/'accepted-meta.json').write_text((a.prep/TAG/'accept-meta.json').read_text())
if __name__=='__main__':main()
