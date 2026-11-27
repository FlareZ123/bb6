#!/usr/bin/env python3
"""Repackage frozen Raw56 root-pilot certificates into independent E0 shards.
No discovery search: all table keys, first-hole trees, FAR and automaton specs
are checked for a disjoint exact partition before emitting original Lean proofs.
Run from the extracted raw56-pilot-generated-source artifact.
"""
import argparse, json, subprocess, sys
from pathlib import Path
from discover_siblings import method
from emit_automata import emit
from minimize_cert import quotient, validate

BOUND=12000
SPECIAL={19569:('M19569Final','BB6.Agent4M19569','p'),
         5334:('Raw56LCM5334','BB6.Agent4Raw56LCM5334','p'),
         20376:('Raw56LCM20376','BB6.Agent4Raw56LCM20376','p')}

def load(p): return json.loads(p.read_text())
def write(p,x): p.write_text(json.dumps(x,indent=2)+'\n')
def table(s):
    s=s.replace('_','');assert len(s)==36
    return [s[i:i+3] for i in range(0,36,3)]
def show(p):return '_'.join(''.join(p[i:i+2]) for i in range(0,12,2))
def move(i):return f'{i//12}{"R" if i%12>=6 else "L"}{chr(65+i%6)}'

def leaves(t):
    if t[0]=='open':yield t[1]
    elif t[0]=='split':
        for k in t[3]:yield from leaves(k)

def original_emitter(src):
    """Use existing exact canonical emitter; make only parent/proof imports generic."""
    s=src.read_text()
    replacements=[
      ('PARENT=f"1RB---_1RC---_0RD---_1LD1LE_{E0}1RE_------"',"PARENT=Path(TAG+'.parent').read_text().strip()"),
      ("emit(MOD+'Base',['Raw40Nores']+AUTOS,base)","emit(MOD+'Base',['Raw40Nores'],base)\nused=set()"),
      ("return f'.proven {PROVEN[s]}.table {PROVEN[s]}.never' if s in PROVEN else far(bank[i],p)","if s in PROVEN:\n            module,tab,never=PROVEN[s];used.add(module)\n            return f'.proven {tab} {never}'\n        return far(bank[i],p)"),
      ("if current_name:emit(current_name,[MOD+'Base'],current)","if current_name:emit(current_name,[MOD+'Base']+sorted(used),current)\n    used.clear()")]
    for old,new in replacements:
        assert s.count(old)==1,old
        s=s.replace(old,new)
    return s

def prepare(tag,child,root,out):
    assert tag in ('E10RD','E11LC')
    stem=root/'rootbranches'/tag
    tree=load(stem.with_suffix('.json')); rows=stem.with_suffix('.open').read_text().splitlines()
    assert tree[:3]==['split',8 if tag=='E10RD' else 9,8] and len(tree[3])==24
    assert list(leaves(tree))==rows and len(rows)==len(set(rows))
    bank=dict((int(i),c) for i,c in (s.split() for s in stem.with_suffix('.far').read_text().splitlines()))
    far6=dict((int(i),c) for i,c in (s.split() for s in stem.with_suffix('.far6').read_text().splitlines()))
    assert not set(bank)&set(far6);bank.update(far6)
    spec=load(stem.with_suffix('.finite.json'));finite={i:(spec['params'][j],n) for i,j,n in spec['rows']}
    late={i:['last',n,slot] for i,n,slot,_ in (map(int,s.split()) for s in stem.with_suffix('.query').read_text().splitlines()) if n>=0}
    growth={int(p.stem.rsplit('M',1)[1]):(p.stem,f'BB6.Agent4Raw56Root{tag}.M{p.stem.rsplit("M",1)[1]}','table') for p in (root/'rootgrowth').glob(tag+'M*.lean')}
    if tag=='E11LC':growth.update(SPECIAL)
    sets=[set(x) for x in (bank,finite,late,growth)]
    assert sum(map(len,sets))==len(set.union(*sets))==len(rows)
    assert set.union(*sets)==set(range(len(rows)))
    assert all(rows[i].count('---')==1 and table(rows[i])[x[2]]=='---' and x[1]+6<=BOUND for i,x in late.items())
    t=tree[3][child];assert t[0]=='split', (tag,child,t[0])
    childrows=list(leaves(t));index={r:i for i,r in enumerate(rows)}
    name=f'{tag}C{child:02}';dest=out/name;dest.mkdir(parents=True,exist_ok=True)
    parent=table(f'1RB---_1RC---_0RD---_1LD1LE_---{tag[2:]}_------');parent[8]=move(child)
    (out/(name+'.parent')).write_text(show(parent)+'\n');write(out/(name+'.json'),t)
    (out/(name+'.open')).write_text(''.join(r+'\n' for r in childrows))
    (out/(name+'.far')).write_text(''.join(f'{j} {bank[index[r]]}\n' for j,r in enumerate(childrows) if index[r] in bank))
    proven={};late_rows={};automata=[];parts=[];nodes=0;namespace=f'BB6.Agent4Raw56Root{tag}C{child:02}Automata'
    def flush():
        nonlocal parts,nodes
        if not parts:return
        mod=f'Raw56{name}Automata{len(automata):02}';automata.append(mod)
        (dest/(mod+'.lean')).write_text('import TwoSidedAutomata\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace '+namespace+'\nopen BB6Coverage\n'+'\n'.join(parts)+'\nend '+namespace+'\n')
        for r,i in pending:proven[r]=[mod,f'{namespace}.M{i}.table',f'{namespace}.M{i}.never']
        pending.clear();parts=[];nodes=0
    pending=[]
    for r in childrows:
        i=index[r]
        if i in bank:continue
        if i in late:late_rows[r]=late[i];continue
        if i in growth:
            mod,ns,tab=growth[i];proven[r]=[mod,f'{ns}.{tab}',f'{ns}.never'];continue
        (kind,left,right),n=finite[i];p=table(r);cert=method(p,kind,left,right,max(12000,n+1))
        assert cert[0] and cert[1]==n,(tag,i,n,cert[:2]);cert=quotient(cert);validate(p,cert)
        if nodes+cert[1]>1200 or len(parts)>=8:flush()
        parts.append(emit(i,p,cert));pending.append((r,i));nodes+=cert[1]
    flush();write(dest/'proven.json',proven);write(dest/'late.json',late_rows);write(dest/'automata_modules.json',automata)
    emitter=out/'emit_root_cut.py';emitter.write_text(original_emitter(root/'emit_cut.py'))
    subprocess.run([sys.executable,str(emitter),name,str(BOUND)],cwd=out,check=True)
    print('prepared',name,'open',len(childrows),'finite',sum(index[r] in finite for r in childrows),'growth',sum(index[r] in growth for r in childrows),'late',len(late_rows),flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('tag',choices=['E10RD','E11LC']);ap.add_argument('children',nargs='+',type=int);ap.add_argument('--root',type=Path,default=Path.cwd());ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();root=a.root.resolve();out=a.out.resolve();out.mkdir(parents=True,exist_ok=True)
    for child in a.children:prepare(a.tag,child,root,out)
