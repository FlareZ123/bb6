#!/usr/bin/env python3
"""Rebuild Raw40 A1=1LB certificate banks without rediscovering any proofs."""
import json,os,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'agent32-raw59'))
from emit_rungram import emit
from emit_raw40_late import emit_late_module
c=sys.argv[1]
spec=json.loads((ROOT/f'a1lb-{c}-discovery.json').read_text())
p=spec['parent']; B=spec.get('bound',spec['initialBound'])
assert p==f'1RB1LB_1RC---_0RD{c}_1LD1LA_------_------'
out=ROOT/'a1lb'/c
out.mkdir(parents=True,exist_ok=True)
exe=out/'enumerate_canon'
subprocess.run(['g++','-std=c++20','-O3',str(ROOT/'enumerate_canon.cpp'),'-o',str(exe)],check=True)
run=subprocess.run([str(exe),p],cwd=out,check=True,text=True,capture_output=True)
(out/'enum.log').write_text(run.stdout)
assert int(re.search(r'maxscore=(\d+)',run.stdout)[1])==spec['initialBound']
opens=(out/'open.txt').read_text().splitlines()
assert len(opens)==spec['opens'] and len(set(opens))==len(opens)
far={};proven={};mods=[];ids=set();late={}
def validate(v):
    i=v['id']
    assert i not in ids and opens[i]==v['table'],(c,i,v['table'],opens[i])
    ids.add(i)
    return i
for v in spec['far']:
    far[validate(v)]=v['code']
records=sorted(spec['compact'],key=lambda v:v['id'])
for v in records:validate(v)
if records:
    ns=f'BB6.Agent19Raw40.A1LB{c}Compact'
    chunks=[];chunk=[];size=0
    for v in records:
        if chunk and (size+v['states']>1200 or len(chunk)>=12):
            chunks.append(chunk);chunk=[];size=0
        chunk.append(v);size+=v['states']
    if chunk:chunks.append(chunk)
    for j,chunk in enumerate(chunks):
        mod=f'Raw40A1LB{c}Compact{j:02}'
        (ROOT/(mod+'.lean')).write_text('import FastBiDFA\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace '+ns+'\nopen BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1NGram BB6.Agent32FastBiDFA\n'+'\n'.join(emit(v['id'],v['table'],*v['dfa'],[v['states'],v['edges']]) for v in chunk)+'\nend '+ns+'\n')
        mods.append(mod)
        for v in chunk:
            proven[opens[v['id']]]=ns+'.M'+str(v['id'])
cycles={}
for v in spec.get('cycles',[]):
    i=validate(v)
    assert v['period']>0 and v['entry']>=0
    cycles[opens[i]]=(v['entry'],v['period'],'R' if v['right'] else 'L',v['bound'])
assert not spec['unresolved']
for v in spec['late']:
    i=validate(v)
    assert opens[i].count('---')==1 and opens[i].replace('_','')[3*v['slot']:3*v['slot']+3]=='---'
    assert v['n']+1+v['delay']<=B
    late[opens[i]]=(v['n'],v['slot'])
assert ids==set(range(len(opens)))
(out/'cycles.txt').write_text(''.join(f'{t} {e} {k} {d} {b}\n' for t,(e,k,d,b) in cycles.items()))
(out/'late.txt').write_text(''.join(f'{t} {n} {s}\n' for t,(n,s) in late.items()))
(out/'far5.txt').write_text(''.join(f'{i} {code}\n' for i,code in sorted(far.items())))
(out/'proven.txt').write_text(''.join(f'{t} {ns}\n' for t,ns in proven.items()))
accelerated={}
if late:
    mod=f'Raw40A1LB{c}Late'
    source,accelerated=emit_late_module(c,spec['late'],B,family='A1LB')
    (ROOT/(mod+'.lean')).write_text(source)
    mods.append(mod)
(out/'imports.txt').write_text(' '.join(mods))
env=dict(os.environ,RAW40_PROOF_IMPORTS=' '.join(mods),RAW40_ACCELERATED_LAST_JSON=json.dumps(accelerated) if accelerated else '')
subprocess.run([sys.executable,str(ROOT/'certify_modular.py'),str(out),str(out/'shards'),p,str(B),'Raw40C1LB'+c,'96','600'],env=env,check=True)
print(c,'opens',len(opens),'FAR',len(far),'proven',len(proven),'bound',B,flush=True)
