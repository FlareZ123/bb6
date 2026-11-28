#!/usr/bin/env python3
"""Regenerate exact-table certificates for the entire A1=0LB family.

Use uniform bound 75,493,794, attained by the existing accelerated 1LB561
witness. Every initial open leaf is assigned to one proof kind; expand
multi-hole late queries before rebuilding the canonical audit. No bounded
search failure is treated as nonhalting. Generated Lean remains the checker.
"""
import json,os,re,subprocess,sys
from pathlib import Path
from compact_ngram import compact,compact_run,find_lag
from emit_raw40_late import emit_late_module
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'agent32-raw59'))
from emit_rungram import emit
B=75493794
c=sys.argv[1]
spec=json.loads((ROOT/'a0lb-discovery.json').read_text())[c]
p=f'1RB0LB_1RC{c}_0RD---_1LD1LA_------_------'
out=ROOT/'a0lb'/c
out.mkdir(parents=True,exist_ok=True)
for f in ('enumerate_canon','farbank','expandlate'):
    subprocess.run(['g++','-std=c++20','-O3',str(ROOT/(f+'.cpp')),'-o',str(out/f)],check=True)
def runenum(exe,table,folder,*args):
    folder.mkdir(parents=True,exist_ok=True)
    run=subprocess.run([str(out/exe),table,*args],cwd=folder,check=True,text=True,capture_output=True)
    (folder/'enum.log').write_text(run.stdout)
    score=int(re.search(r'maxscore=(\d+)',run.stdout)[1])
    assert score<=B,(table,score)
    return json.loads((folder/'tree.json').read_text()),(folder/'open.txt').read_text().splitlines()
tree,opens=runenum('enumerate_canon',p,out)
assert len(opens)==spec['count'][0] and len(set(opens))==len(opens)
def far5(tables):
    run=subprocess.run([str(out/'farbank'),'5'],input=''.join(f'{i} {t.replace("_","")}\n' for i,t in enumerate(tables)),text=True,capture_output=True,check=True)
    bank={}
    for line in run.stdout.splitlines():
        i,v=line.split()
        i=int(i)
        assert i not in bank
        bank[i]=v
    return bank
bank=far5(opens)
assert len(bank)==spec['count'][1],(c,len(bank),spec['count'])
mods=[];proven={};records=[];groups=[set(bank)]
def group(ids):
    groups.append(set(ids))
def save(i,rec):
    assert rec['table']==opens[i].replace('_','')
    records.append(dict(id=i,c=c,**rec))
runfile=ROOT/f'a0lb-{c}-rungram.json'
if runfile.exists():
    runbank={v['id']:v for v in json.loads(runfile.read_text())}
    wanted={i for i,k in spec['gram']}|{i for par,ids in spec['run'] for i in ids}
    assert set(runbank)==wanted
    for i in sorted(wanted):
        rec=runbank[i]
        assert rec['id']==i and rec['c']==c and rec['table']==opens[i].replace('_','')
        records.append(rec)
    group(wanted)
else:
    for i,k in spec['gram']:
        save(i,compact(opens[i],[k,k]))
    group(i for i,k in spec['gram'])
    for par,ids in spec['run']:
        for i in ids:
            save(i,compact_run(opens[i],par,par))
        group(ids)
lagfile=ROOT/f'a0lb-{c}-lag.json'
lagbank={v['id']:v for v in json.loads(lagfile.read_text())} if lagfile.exists() else {}
assert set(lagbank)=={i for i,*_ in spec['lag']}
for i,*par in spec['lag']:
    rec=lagbank[i]
    assert rec['id']==i and rec['c']==c and rec['table']==opens[i].replace('_','')
    records.append(rec)
group(i for i,*_ in spec['lag'])
for i in spec['unclassified']:
    assert (c,i)==('1RE',198)
    rec=json.loads((ROOT/'a0lb198-compact.json').read_text())
    assert rec['id']==i and rec['c']==c and rec['table']==opens[i].replace('_','')
    records.append(rec)
group(spec['unclassified'])
if records:
    ns=f'BB6.Agent19Raw40.A0LB{c}Compact'
    # Keep per-module checks small; avoid a single memory-heavy elaboration.
    chunks=[];chunk=[];size=0
    for rec in records:
        if chunk and (size+rec['states']>1800 or len(chunk)>=16):
            chunks.append(chunk);chunk=[];size=0
        chunk.append(rec);size+=rec['states']
    if chunk:chunks.append(chunk)
    for j,chunk in enumerate(chunks):
        mod=f'Raw40A0LB{c}Compact{j:02}'
        (ROOT/(mod+'.lean')).write_text('import FastBiDFA\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace '+ns+'\nopen BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1NGram BB6.Agent32FastBiDFA\n'+'\n'.join(emit(v['id'],v['table'],*v['dfa'],[v['states'],v['edges']]) for v in chunk)+'\nend '+ns+'\n')
        mods.append(mod)
        for v in chunk:
            proven[opens[v['id']]]=ns+'.M'+str(v['id'])
    (out/'compact.json').write_text(json.dumps(records,separators=(',',':'))+'\n')
pumps=spec['pump']
group(row[0] for row in pumps)
if pumps:
    ns=f'BB6.Agent19Raw40.A0LB{c}Pump'
    mod=f'Raw40A0LB{c}Pump'
    for row in pumps:
        i=row[0]; row[1]=opens[i].replace('_','')
        proven[opens[i]]=ns+'.Leaf'+str(i)
    cert=out/'pumps.jsonl'
    cert.write_text(''.join(json.dumps(row)+'\n' for row in pumps))
    with (ROOT/(mod+'.lean')).open('w') as f:
        subprocess.run([sys.executable,str(ROOT/'emit_autopump.py'),str(cert),ns],stdout=f,check=True)
    mods.append(mod)
known=spec.get('known',[])
group(known)
for i in known:
    assert (c,i)==('0LE',110)
    assert opens[i]=='1RB0LB_1RC0LE_0RD0RC_1LD1LA_---0LF_1RF1RC'
    proven[opens[i]]='BB6.Agent19Raw40.A0LB110'
    mods.append('Raw40A0LB110')
group(i for i,*_ in spec['late'])
assert set.union(*groups)==set(range(len(opens))) and sum(map(len,groups))==len(opens),(c,list(map(len,groups)),len(opens))

# The expansion operates on literal tables, not unstable post-expansion indices.
expand=set(spec.get('expand',[])); replacements={};late={};accelerated={};query_records=[]
far_by_table={opens[i]:v for i,v in bank.items()}
for i,n,s in spec['late']:
    t=opens[i]
    assert t.replace('_','')[3*s:3*s+3]=='---'
    if (c,i)!=('1LB',561):query_records.append(dict(id=i,table=t,n=n,slot=s))
    if i in expand:
        assert t.count('---')>1
        subtree,leaves=runenum('expandlate',t,out/f'expand{i}','200000')
        assert subtree[:3]==['split',n,s]
        b=far5(leaves)
        assert len(b)==len(leaves),(c,i,len(b),len(leaves))
        for j,v in b.items():
            assert leaves[j] not in far_by_table
            far_by_table[leaves[j]]=v
        replacements[t]=subtree
    else:
        assert t.count('---')==1,(c,i,t)
        late[t]=(n,s)
        if (c,i)==('1LB',561):
            assert (n,s)==(75493793,8)
            assert t=='1RB0LB_1RC1LB_0RD1RE_1LD1LA_---0RF_1LF0LA'
            mods+=['Raw40A0LB561','Raw40A0LB561Check']
            accelerated[t]='BB6.Agent19Raw40.A0LB561'
        else:
            assert n+6<=B
assert set(replacements)=={opens[i] for i in expand}
def graft(t):
    if t[0]=='open' and t[1] in replacements:return replacements[t[1]]
    if t[0]=='split':return t[:3]+[[graft(k) for k in t[3]]]
    return t
def leaves(t):
    if t[0]=='open':yield t[1]
    if t[0]=='split':
        for k in t[3]:yield from leaves(k)
tree=graft(tree)
opens2=list(leaves(tree))
assert len(opens2)==len(set(opens2))
assert set(opens2)==set(far_by_table)|set(proven)|set(late)
assert len(opens2)==len(far_by_table)+len(proven)+len(late)
(out/'tree.json').write_text(json.dumps(tree,separators=(',',':'))+'\n')
(out/'open.txt').write_text(''.join(t+'\n' for t in opens2))
(out/'far5.txt').write_text(''.join(f'{i} {far_by_table[t]}\n' for i,t in enumerate(opens2) if t in far_by_table))
(out/'far_extra.txt').write_text('')
(out/'proven.txt').write_text(''.join(f'{t} {ns}\n' for t,ns in proven.items()))
(out/'late.txt').write_text(''.join(f'{t} {n} {s}\n' for t,(n,s) in late.items()))
accelerated_splits={}
if query_records:
    mod=f'Raw40A0LB{c}Late'
    source,names=emit_late_module(c,query_records,B,family='A0LB')
    (ROOT/(mod+'.lean')).write_text(source)
    mods.append(mod)
    accelerated.update({t:ns for t,ns in names.items() if t in late})
    accelerated_splits={t:ns for t,ns in names.items() if t in replacements}
(out/'imports.txt').write_text(' '.join(mods))
env=dict(os.environ,RAW40_PROOF_IMPORTS=' '.join(mods),
         RAW40_ACCELERATED_LAST_JSON=json.dumps(accelerated) if accelerated else '',
         RAW40_ACCELERATED_SPLIT_JSON=json.dumps(accelerated_splits) if accelerated_splits else '',
         RAW40_MAX_REC_DEPTH='1000000')
subprocess.run([sys.executable,str(ROOT/'certify_modular.py'),str(out),str(out/'shards'),p,str(B),'Raw40C0LB'+c,'96','600'],env=env,check=True)
print(c,'initial opens',len(opens),'final opens',len(opens2),'FAR',len(far_by_table),'proven',len(proven),'late',len(late),'bound',B,flush=True)
