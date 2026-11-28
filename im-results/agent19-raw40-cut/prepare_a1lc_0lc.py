#!/usr/bin/env python3
"""Regenerate the canonical A1=1LC five-hole proof trees from saved certificate banks.
No FAR or graph discovery is repeated; every supplied witness is re-encoded
and kernel checked. Special residuals use exact periodic-sweep proofs.
"""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'agent32-raw59'))
from emit_rungram import emit
from compact_ngram import compact,compact_run,compact_lag
from emit_raw40_late import emit_late_module,emit_pump_module
c=sys.argv[1] if len(sys.argv)>1 else '0LC'
assert c in ('0LC','1LB','0RC','1RC','1LE','0LE','0RD','1LC','1RD','0RE','1RB','1RE','1RA')
recipe=ROOT/f'a1lc-{c}-recipe.json'
spec=json.loads((recipe if recipe.exists() else ROOT/f'a1lc-{c}-discovery.json').read_text())
p=spec['parent']; B=spec.get('bound',spec['initialBound'])
assert p==f'1RB1LC_1RC{c}_0RD---_1LD1LA_------_------'
out=ROOT/'a1lc'/c
out.mkdir(parents=True,exist_ok=True)
exe=out/'enumerate_canon'
subprocess.run(['g++','-std=c++20','-O3',str(ROOT/'enumerate_canon.cpp'),'-o',str(exe)],check=True)
run=subprocess.run([str(exe),p],cwd=out,check=True,text=True,capture_output=True)
(out/'enum.log').write_text(run.stdout)
assert int(re.search(r'maxscore=(\d+)',run.stdout)[1])==spec['initialBound']
opens=(out/'open.txt').read_text().splitlines()
assert len(opens)==spec['opens'] and len(set(opens))==len(opens)
if recipe.exists():
    assert hashlib.sha256((out/'open.txt').read_bytes()).hexdigest()==spec['open_sha256']
    def expand(ranges):
        for part in ranges.split(','):
            ends=list(map(int,part.split('-')))
            yield from range(ends[0],ends[-1]+1)
    spec['far']=[dict(id=i,table=opens[i],code=code)
                 for line in spec['farGroups'].splitlines() for code,ranges in [line.split()]
                 for i in expand(ranges)]
    spec['compact']=[]
    for (kind,l,r),ranges in spec['compactGroups']:
        for i in expand(ranges):
            table=opens[i]
            record=(compact(table,[l,r]) if kind=='ngram' else
                    compact_run(table,l,r) if kind=='rungram' else
                    compact_lag(table,l,r) if kind=='compact-lag' else None)
            assert record is not None
            spec['compact'].append(dict(id=i,**record))
    (ROOT/f'Raw40A1LC{c}Pumps.lean').write_text(emit_pump_module(c,spec))
def norm(t):return t.replace('_','')
far={};proven={};mods=[];ids=set()
def validate(v):
    i=v['id']
    assert i not in ids and norm(v['table'])==norm(opens[i]),(c,i,v['table'],opens[i])
    ids.add(i)
    return i
for v in spec['far']:
    i=validate(v);far[i]=v['code']
records=sorted(spec['compact'],key=lambda v:v['id'])
for v in records:validate(v)
if records:
    ns=f'BB6.Agent19Raw40.A1LC{c}Compact'
    chunks=[];chunk=[];size=0
    for v in records:
        if chunk and (size+v['states']>1200 or len(chunk)>=12):
            chunks.append(chunk);chunk=[];size=0
        chunk.append(v);size+=v['states']
    if chunk:chunks.append(chunk)
    for j,chunk in enumerate(chunks):
        mod=f'Raw40A1LC{c}Compact{j:02}'
        (ROOT/(mod+'.lean')).write_text('import FastBiDFA\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace '+ns+'\nopen BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1NGram BB6.Agent32FastBiDFA\n'+'\n'.join(emit(v['id'],v['table'],*v['dfa'],[v['states'],v['edges']]) for v in chunk)+'\nend '+ns+'\n')
        mods.append(mod)
        for v in chunk:
            proven[opens[v['id']]]=ns+'.M'+str(v['id'])
if c=='0LC':
    special={39:'1RB1LC_1RC0LC_0RD1LE_1LD1LA_1RF1LF_---0RA',
             95:'1RB1LC_1RC0LC_0RD1RE_1LD1LA_1RB0RF_---0LD',
             118:'1RB1LC_1RC0LC_0RD1RE_1LD1LA_1RF0LD_---1RB'}
    mod='Raw40A1LC0LCPeriodic'
elif c=='0LE':
    special={1:'1RB1LC_1RC0LE_0RD0RF_1LD1LA_1RB0LA_---1RE'}
    mod='Raw40A1LC0LELeaf1'
elif c=='0RC':
    special={88:'1RB1LC_1RC0RC_0RD0RE_1LD1LA_0RF0LF_0LA---'}
    mod='Raw40A1LC0RCLeaf88'
elif recipe.exists():
    special={v['id']:v['table'] for v in spec['unresolved']}
    mod=None
    mods.extend(spec['modules'])
else:
    special={}
    mod=None
assert {v['id'] for v in spec['unresolved']}==set(special)
for v in spec['unresolved']:
    i=validate(v)
    assert opens[i]==special[i]
    proven[opens[i]]=f'BB6.Agent19Raw40.A1LC{c}.Leaf{i}'
if mod:mods.append(mod)
late={}
for v in spec['late']:
    i=validate(v)
    assert opens[i].count('---')==1 and norm(opens[i])[3*v['slot']:3*v['slot']+3]=='---'
    assert v['n']+1+v['delay']<=B
    late[opens[i]]=(v['n'],v['slot'])
(out/'late.txt').write_text(''.join(f'{t} {n} {s}\n' for t,(n,s) in late.items()))
assert ids==set(range(len(opens)))
(out/'far5.txt').write_text(''.join(f'{i} {code}\n' for i,code in sorted(far.items())))
(out/'proven.txt').write_text(''.join(f'{t} {ns}\n' for t,ns in proven.items()))
(out/'imports.txt').write_text(' '.join(mods))
accelerated={}
if late:
    mod=f'Raw40A1LC{c}Late'
    source,accelerated=emit_late_module(c,spec['late'],B)
    (ROOT/(mod+'.lean')).write_text(source)
    mods.append(mod)
    (out/'imports.txt').write_text(' '.join(mods))
env=dict(os.environ,RAW40_PROOF_IMPORTS=' '.join(mods),RAW40_ACCELERATED_LAST_JSON=json.dumps(accelerated) if accelerated else '')
subprocess.run([sys.executable,str(ROOT/'certify_modular.py'),str(out),str(out/'shards'),p,str(B),'Raw40C1LC'+c,'96','600'],env=env,check=True)
print(c,'opens',len(opens),'FAR',len(far),'proven',len(proven),'bound',B,flush=True)
