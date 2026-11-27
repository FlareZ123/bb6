#!/usr/bin/env python3
"""Materialize saved Raw40 A1=0LA banks, without proof search.\nNine children are ready for candidate source generation; 1LC additionally\nrequires the literal leaf66 nested-drain source theorem.\n"""
import base64,hashlib,json,os,re,struct,subprocess,sys,zlib
from pathlib import Path
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'agent32-raw59'))
from emit_rungram import emit
from compact_ngram import abstract,ngram,rungram,laggram
from emit_raw40_late import emit_late_module
c=sys.argv[1]
assert c in ('0LE','0RB','0RD','0RE','1LA','1LC','1LE','1RB','1RC','1RE')
if c=='1LC' and not (ROOT/'Raw40A0LA1LCLeaf66.lean').exists():
    raise SystemExit('1LC requires Raw40A0LA1LCLeaf66.lean (table + never); no proof assumed')
recipe=ROOT/f'a0la-{c}-frontier-recipe.b64'
spec=json.loads(zlib.decompress(base64.b64decode(recipe.read_text()))) if recipe.exists() else json.loads((ROOT/f'a0la-{c}-discovery.json').read_text())
audits={}
for x in ('five','0LE-0RB','0RE','1LE-1RE'):
    for row in json.loads((ROOT/f'a0la-audit-{x}.json').read_text()):
        audits[row['child']]=row
B=audits[c]['bound']
p=spec['parent']
assert p==f'1RB0LA_1RC---_0RD{c}_1LD1LA_------_------'
assert spec['opens']==audits[c]['opens'] and spec['initialBound']==audits[c]['initialBound']
assert spec.get('boundCandidate',B)==B
out=ROOT/'a0la'/c
out.mkdir(parents=True,exist_ok=True)
exe=out/'enumerate_canon'
subprocess.run(['g++','-std=c++20','-O3',str(ROOT/'enumerate_canon.cpp'),'-o',str(exe)],check=True)
run=subprocess.run([str(exe),p],cwd=out,check=True,text=True,capture_output=True)
(out/'enum.log').write_text(run.stdout)
assert int(re.search(r'maxscore=(\d+)',run.stdout)[1])==spec['initialBound']
opens=(out/'open.txt').read_text().splitlines()
assert len(opens)==spec['opens'] and len(set(opens))==len(opens)
def attach(v):
    i=v['id']
    assert 0<=i<len(opens)
    assert v.get('table',opens[i])==opens[i]
    return dict(v,table=opens[i])
def indices(key,bank):
    raw=zlib.decompress(base64.b64decode(spec[key]))
    assert len(raw)==2*len(opens)
    for i,(x,) in enumerate(struct.iter_unpack('<H',raw)):
        if x:
            assert x<=len(spec[bank])
            yield i,spec[bank][x-1]
def summary(a):
    k,r,c0,c1,m0,m1=a
    if r==0: return 0,ngram(k)
    if k==0: return (),rungram([r,c0,c1,m0,m1])
    return (0,()),laggram(a)
if recipe.exists():
    assert hashlib.sha256((out/'open.txt').read_bytes()).hexdigest()==spec['roster_sha256']
    spec['far']=[dict(id=i,table=opens[i],code=code) for i,code in indices('farZ','farBank')]
    spec['compact']=[]
    for i,a in indices('compactZ','compactBank'):
        assert len(a)==12
        l,lf=summary(a[:6]);r,rf=summary(a[6:])
        rec=abstract(opens[i],[l,r],[lf,rf],['saved-summary',a],cap=300000)
        spec['compact'].append(dict(rec,id=i,table=opens[i]))
    spec['unresolved']=[dict(id=i,table=opens[i]) for i in spec['unresolved']]
spec['cycles']=[attach(v) for v in spec.get('cycles',[])]
spec['late']=[attach(v) for v in spec['late']]
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
    ns=f'BB6.Agent19Raw40.A0LA{c}Compact'
    chunks=[];chunk=[];size=0
    for v in records:
        if chunk and (size+v['states']>1200 or len(chunk)>=12):
            chunks.append(chunk);chunk=[];size=0
        chunk.append(v);size+=v['states']
    if chunk:chunks.append(chunk)
    for j,chunk in enumerate(chunks):
        mod=f'Raw40A0LA{c}Compact{j:02}'
        (ROOT/(mod+'.lean')).write_text('import FastBiDFA\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace '+ns+'\nopen BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1NGram BB6.Agent32FastBiDFA\n'+'\n'.join(emit(v['id'],v['table'],*v['dfa'],[v['states'],v['edges']]) for v in chunk)+'\nend '+ns+'\n')
        mods.append(mod)
        for v in chunk:
            proven[opens[v['id']]]=ns+'.M'+str(v['id'])
cycles={}
for v in spec.get('cycles',[]):
    i=validate(v)
    assert v['period']>0 and v['entry']>=0
    cycles[opens[i]]=(v['entry'],v['period'],'R' if v['right'] else 'L',v['bound'])
# Bind external evidence by both canonical ID and literal table. Do not use
# an ID alone or equate an uncompiled source candidate with an accepted proof.
external={}
def register(child,i,v,kind,ns=None,module=None):
    key=(child,int(i))
    assert key not in external
    external[key]=(v,kind,ns,module)
for key,v in json.loads((ROOT.parent/'agent42-raw40-crossing-splice'/'bank.json').read_text()).items():
    child,i=key.split('-')
    register(child,i,v,'proof',f'BB6Coverage.Agent42Raw40Crossing.C{child}M{i}','Raw40CrossingLeaves')
for v in json.loads((ROOT.parent/'agent42-raw40-long-cycles'/'cycles.json').read_text()):
    register(v['child'],v['id'],v,'cycle')
short={'0LE/366','0RE/759','0RE/792','0RE/790'}
triple={'1RE/1096'}
for name in ('a0la-late-splice-bank.json','a0la-0RD-leaf154-crossing.json'):
    for key,v in json.loads((ROOT/name).read_text()).items():
        child,i=key.split('/')
        mod='Raw40LateCrossing'+('Short' if key in short else 'Triple' if key in triple else 'Long')
        register(child,i,v,'proof',f'BB6Coverage.Agent19Raw40LateCrossing.C{child}M{i}',mod)
register('1LC',66,{'table':'1RB0LA_1RC0RE_0RD1LC_1LD1LA_---0RF_1RA1RF'},'proof',
         'BB6.Agent19Raw40.A0LA1LCLeaf66','Raw40A0LA1LCLeaf66')
for rec in spec['unresolved']:
    i=validate(rec);t=opens[i]
    v,kind,ns,mod=external[c,i]
    assert t==v['table']
    if kind=='cycle':
        cycles[t]=(v['entry'],v['period'],'R' if v['right'] else 'L',v['bound'])
    else:
        proven[t]=ns
        if mod not in mods: mods.append(mod)
def delay(table,slot):
    moves=table.replace('_','')
    p=[moves[i:i+3] for i in range(0,36,3)]
    p[slot]='HHH'
    def walk(q,seen):
        return max([0]+[1+walk(j,seen|{j}) for j in range(6)
                        if j not in seen and (p[2*j]=='---' or
                           (p[2*j].startswith('0') and p[2*j][2]==chr(65+q)))])
    return walk(0,{0})
for v in spec['late']:
    i=validate(v)
    assert opens[i].count('---')==1 and opens[i].replace('_','')[3*v['slot']:3*v['slot']+3]=='---'
    d=delay(opens[i],v['slot'])
    assert v.get('delay',d)==d and v['n']+1+d<=B
    late[opens[i]]=(v['n'],v['slot'])
assert ids==set(range(len(opens)))
(out/'cycles.txt').write_text(''.join(f'{t} {e} {k} {d} {b}\n' for t,(e,k,d,b) in cycles.items()))
(out/'late.txt').write_text(''.join(f'{t} {n} {s}\n' for t,(n,s) in late.items()))
(out/'far5.txt').write_text(''.join(f'{i} {code}\n' for i,code in sorted(far.items())))
(out/'proven.txt').write_text(''.join(f'{t} {ns}\n' for t,ns in proven.items()))
accelerated={}
if late:
    mod=f'Raw40A0LA{c}Late'
    source,accelerated=emit_late_module(c,spec['late'],B,family='A0LA')
    (ROOT/(mod+'.lean')).write_text(source)
    mods.append(mod)
(out/'imports.txt').write_text(' '.join(mods))
env=dict(os.environ,RAW40_PROOF_IMPORTS=' '.join(mods),RAW40_ACCELERATED_LAST_JSON=json.dumps(accelerated) if accelerated else '')
subprocess.run([sys.executable,str(ROOT/'certify_modular.py'),str(out),str(out/'shards'),p,str(B),'Raw40C0LA'+c,'96','600'],env=env,check=True)
print(c,'opens',len(opens),'FAR',len(far),'proven',len(proven),'bound',B,flush=True)
