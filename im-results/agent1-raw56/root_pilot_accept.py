#!/usr/bin/env python3
"""Generate and compile source-faithful Raw56 root-pilot Covers.

Consumes the exact raw56-pilot-generated-source artifact from run 46062134943.
Search/discovery remains untrusted: every emitted finite certificate, symbolic proof,
late-query leaf and canonical cut is rechecked by Lean 4.36.0-rc2.
"""
import argparse, concurrent.futures, hashlib, json, os, shutil, subprocess, sys
from pathlib import Path

TAGS=("E10RD","E11LC","E10RB")
BOUND=12000
BAD_MARKERS=("sorryAx","native_decide","declaration uses 'sorry'")

def run(cmd, cwd=None, env=None, log=None):
    p=subprocess.run(cmd,cwd=cwd,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    if log: Path(log).write_text(p.stdout)
    if p.returncode or any(x in p.stdout for x in BAD_MARKERS):
        print(p.stdout[-16000:],file=sys.stderr);raise RuntimeError(f"command failed: {cmd}")
    return p.stdout

def module_path(root, mod, ext): return root / Path(*mod.split('.')).with_suffix(ext)

def patch_emitter(src:Path,dst:Path):
    s=src.read_text()
    s=s.replace("TAG=sys.argv[1]; NS='BB6.Agent4Raw56.'+TAG; MOD='Raw56'+TAG",
                "TAG=sys.argv[1]; NS='BB6.Agent1Raw56Pilot.'+TAG; MOD='Raw56Pilot'+TAG")
    s=s.replace('E0={"RELA":"0LA","RERB":"0RB"}.get(TAG,TAG[2:])\nPARENT=f"1RB---_1RC---_0RD---_1LD1LE_{E0}1RE_------"',
                'E1=TAG[2:]\nPARENT=f"1RB---_1RC---_0RD---_1LD1LE_---{E1}_------"')
    if "PARENT=f\"1RB---_1RC---_0RD---_1LD1LE_---{E1}_------\"" not in s: raise RuntimeError("emitter patch failed")
    dst.write_text(s)

def prepare(src:Path,out:Path):
    if out.exists(): shutil.rmtree(out)
    shutil.copytree(src,out)
    sys.path.insert(0,str(out))
    from discover_siblings import method
    from minimize_cert import quotient,validate
    from emit_automata import emit
    patch_emitter(out/'emit_cut.py',out/'emit_root_cut.py')
    (out/'Raw56PilotSpecial.lean').write_text('''import Raw56LCM5334
import Raw56LCM20376
import M19569Final
namespace BB6.Agent1Raw56PilotSpecial
open BB6Coverage
namespace M5334
abbrev table := BB6.Agent4Raw56LCM5334.p
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6.Agent4Raw56LCM5334.never m hm
end M5334
namespace M19569
abbrev table := BB6.Agent4M19569.p
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6.Agent4M19569.never m hm
end M19569
namespace M20376
abbrev table := BB6.Agent4Raw56LCM20376.p
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6.Agent4Raw56LCM20376.never m hm
end M20376
end BB6.Agent1Raw56PilotSpecial
''')
    summary={}
    for tag in ("E10RD","E11LC"):
        rb=out/'rootbranches'/tag; opens=rb.with_suffix('.open').read_text().splitlines(); D=json.loads(rb.with_suffix('.finite.json').read_text())
        # Reject transferred FAR-bank codes whose digits reference states outside the encoded automaton.
        valid=[]; invalid=[]
        for line in rb.with_suffix('.far').read_text().splitlines():
            i,code=line.split(); ds=[int(x,16) for x in code[1:]]; n=len(ds)//2
            (valid if len(ds)==2*n and all(0<=x<n for x in ds) else invalid).append((int(i),code))
        rb.with_suffix('.far').write_text(''.join(f'{i} {c}\n' for i,c in valid))
        finite=[tuple(x) for x in D['rows']]
        for i,_ in invalid:
            t=opens[i]; p=t.replace('_',''); p=[p[k:k+3] for k in range(0,36,3)]; found=None
            for pid,(kind,left,right) in enumerate(D['params']):
                c=method(p,kind,left,right,150000)
                if c[0]: found=(i,pid,c[1]); break
            if found is None: raise RuntimeError(f"{tag} invalid FAR leaf {i} has no replacement")
            finite.append(found)
        proven={}; certmods=[]; ns=f'BB6.Agent1Raw56PilotFinite.{tag}'
        fdir=out/'finite'/tag;fdir.mkdir(parents=True,exist_ok=True)
        for i,pid,n in finite:
            kind,left,right=D['params'][pid];t=opens[i];p=t.replace('_','');p=[p[k:k+3] for k in range(0,36,3)]
            c=method(p,kind,left,right,150000)
            if not c[0] or c[1]!=n: raise RuntimeError((tag,i,c[:2],n))
            c=quotient(c);validate(p,c); body=emit(i,p,c)
            mod=f'finite.{tag}.F{i}'; module_path(out,mod,'.lean').write_text('import TwoSidedAutomata\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace '+ns+'\nopen BB6Coverage\n'+body+'\nend '+ns+'\n')
            certmods.append(mod);proven[t]=f'{ns}.M{i}'
        syms=[json.loads(x) for x in rb.with_suffix('.symbolic.jsonl').read_text().splitlines() if x]
        for r in syms: proven[opens[r['index']]]=f'BB6.Agent4Raw56Root{tag}.M{r["index"]}'
        growth=[f'rootgrowth.{tag}M{r["index"]}' for r in syms]
        if tag=='E11LC':
            special={26:'BB6.Agent4Raw56RootE11LC.M26',4517:'BB6.Agent4Raw56RootE11LC.M4517',4598:'BB6.Agent4Raw56RootE11LC.M4598',5334:'BB6.Agent1Raw56PilotSpecial.M5334',19569:'BB6.Agent1Raw56PilotSpecial.M19569',20376:'BB6.Agent1Raw56PilotSpecial.M20376'}
            for i,nm in special.items(): proven[opens[i]]=nm
            growth += ['rootgrowth.E11LCM26','rootgrowth.E11LCM4517','rootgrowth.E11LCM4598','Raw56PilotSpecial']
            add=[x for x in rb.with_suffix('.far6').read_text().splitlines() if x.strip()]
            with rb.with_suffix('.far').open('a') as f:
                for x in add:f.write(x+'\n')
        late={}
        for l in rb.with_suffix('.query').read_text().splitlines():
            i,t,slot,_=map(int,l.split())
            if t>=0:late[opens[i]]=['last',t,slot]
        bank={int(x.split()[0]) for x in rb.with_suffix('.far').read_text().splitlines()}
        covered=bank|{i for i,t in enumerate(opens) if t in proven or t in late}
        if covered!=set(range(len(opens))): raise RuntimeError((tag,len(opens),len(covered),sorted(set(range(len(opens)))-covered)[:20]))
        od=out/tag;od.mkdir(exist_ok=True)
        (od/'proven.json').write_text(json.dumps(proven));(od/'automata_modules.json').write_text(json.dumps(certmods+growth));(od/'late.json').write_text(json.dumps(late))
        for ext in ('json','open','far'): shutil.copy2(rb.with_suffix('.'+ext),out/f'{tag}.{ext}')
        run([sys.executable,'emit_root_cut.py',tag,str(BOUND)],cwd=out,log=out/f'{tag}-emit.log')
        manifest=json.loads((od/'manifest.json').read_text()); top=manifest[-1][1]
        meta={'tag':tag,'bound':BOUND,'open':len(opens),'valid_far':len(bank),'invalid_far_replaced':len(invalid),'finite':len(finite),'proven':len(proven),'late':len(late),'cert_modules':certmods,'growth_modules':growth,'cut_modules':len(manifest),'top_roots':top,'final_module':manifest[-1][0]}
        (od/'accept-meta.json').write_text(json.dumps(meta,indent=2)+'\n');summary[tag]=meta
    (out/'accept-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

def env_for(base:Path,*paths):
    e=dict(os.environ);e['LEAN_PATH']=os.pathsep.join(str(p) for p in [*paths,base]);return e

def lean_bin():
    p=shutil.which('lean')
    if not p: raise RuntimeError('lean not found')
    v=run([p,'--version'])
    if '4.36.0-rc2' not in v: raise RuntimeError(v)
    return p

def compile_module(lean,prep:Path,mod:str,outroot:Path,env):
    src=module_path(prep,mod,'.lean'); out=module_path(outroot,mod,'.olean'); out.parent.mkdir(parents=True,exist_ok=True)
    rel=src.relative_to(prep); log=out.with_suffix('.log')
    return run([lean,'-j','1','-o',str(out),str(rel)],cwd=prep,env=env,log=log)

def compile_certs(prep:Path,base:Path,tag:str,shard:int,shards:int,out:Path):
    lean=lean_bin();out.mkdir(parents=True,exist_ok=True); env=env_for(base,out,prep)
    compile_module(lean,prep,'TwoSidedAutomata',out,env)
    meta=json.loads((prep/tag/'accept-meta.json').read_text()); mods=meta['cert_modules']
    mine=[m for j,m in enumerate(mods) if j%shards==shard]
    for m in mine:
        compile_module(lean,prep,m,out,env); print('CERT',m,flush=True)
    growth=[m for j,m in enumerate(meta['growth_modules']) if j%shards==shard and m!='Raw56PilotSpecial']
    for m in growth:
        compile_module(lean,prep,m,out,env);print('GROWTH',m,flush=True)
    if tag=='E11LC' and shard==0:
        for m in ['RunStack','M19569Data']+[f'M19569Check{i}' for i in range(36)]+['M19569Final','Raw56LCM5334','Raw56LCM20376','Raw56PilotSpecial']:
            compile_module(lean,prep,m,out,env);print('SPECIAL',m,flush=True)
    (out/'cert-meta.json').write_text(json.dumps({'tag':tag,'shard':shard,'shards':shards,'modules':mine+growth},indent=2)+'\n')

def manifest_graph(prep:Path,tag:str):
    man=json.loads((prep/tag/'manifest.json').read_text());return man,{m:set(ds) for m,ds in man}

def compile_cut(prep:Path,base:Path,certs:Path,tag:str,shard:int,shards:int,out:Path):
    lean=lean_bin();out.mkdir(parents=True,exist_ok=True); outtag=out/tag;outtag.mkdir(exist_ok=True)
    env=env_for(base,out,outtag,certs,prep/tag,prep)
    man,deps=manifest_graph(prep,tag); allmods=set(deps); final=man[-1][0]; top=man[-1][1]
    base_mod=man[0][0]; compile_module(lean,prep,f'{tag}.{base_mod}',out,env)
    selected=[m for j,m in enumerate(top) if j%shards==shard]
    closure=set()
    def add(m):
        if m in closure or m not in allmods or m in (base_mod,final):return
        closure.add(m)
        for d in deps[m]:add(d)
    for m in selected:add(m)
    done={base_mod};pending=set(closure)
    while pending:
        ready=sorted(m for m in pending if all(d not in allmods or d in done for d in deps[m]))
        if not ready: raise RuntimeError(('cut cycle',tag,shard,list(pending)[:20]))
        for m in ready:
            compile_module(lean,prep,f'{tag}.{m}',out,env);done.add(m);pending.remove(m);print('CUT',m,flush=True)
    (out/'cut-meta.json').write_text(json.dumps({'tag':tag,'shard':shard,'roots':selected,'modules':sorted(closure)},indent=2)+'\n')

def compile_final(prep:Path,base:Path,certs:Path,cuts:Path,tag:str,out:Path):
    lean=lean_bin();out.mkdir(parents=True,exist_ok=True);outtag=out/tag;outtag.mkdir(exist_ok=True)
    man,_=manifest_graph(prep,tag); final=man[-1][0]
    env=env_for(base,out,outtag,cuts,cuts/tag,certs,prep/tag,prep)
    log=out/f'{tag}-final.log'; src=prep/tag/f'{final}.lean'; olean=outtag/f'{final}.olean'
    txt=run([lean,'-j','1','-o',str(olean),str(src.relative_to(prep))],cwd=prep,env=env,log=log)
    theorem=f'BB6.Agent1Raw56Pilot.{tag}.all_quotient'
    if theorem not in txt: raise RuntimeError(f'missing axiom print for {theorem}')
    checker=Path('im-results/agent1-raw57/check_axioms.py')
    if checker.exists(): run([sys.executable,str(checker),str(log),'--require',theorem])
    meta=json.loads((prep/tag/'accept-meta.json').read_text());meta.update({'theorem':theorem,'final_olean_sha256':hashlib.sha256(olean.read_bytes()).hexdigest()})
    (out/f'{tag}-accepted.json').write_text(json.dumps(meta,indent=2)+'\n');print(json.dumps(meta,indent=2))

def main():
    ap=argparse.ArgumentParser();sp=ap.add_subparsers(dest='cmd',required=True)
    p=sp.add_parser('prepare');p.add_argument('--source',type=Path,required=True);p.add_argument('--out',type=Path,required=True)
    for name in ('compile-certs','compile-cut'):
        p=sp.add_parser(name);p.add_argument('--prep',type=Path,required=True);p.add_argument('--base',type=Path,required=True);p.add_argument('--tag',choices=TAGS,required=True);p.add_argument('--shard',type=int,required=True);p.add_argument('--shards',type=int,required=True);p.add_argument('--out',type=Path,required=True)
        if name=='compile-cut':p.add_argument('--certs',type=Path,required=True)
    p=sp.add_parser('compile-final');p.add_argument('--prep',type=Path,required=True);p.add_argument('--base',type=Path,required=True);p.add_argument('--certs',type=Path,required=True);p.add_argument('--cuts',type=Path,required=True);p.add_argument('--tag',choices=TAGS,required=True);p.add_argument('--out',type=Path,required=True)
    a=ap.parse_args()
    if a.cmd=='prepare':prepare(a.source,a.out)
    elif a.cmd=='compile-certs':compile_certs(a.prep,a.base,a.tag,a.shard,a.shards,a.out)
    elif a.cmd=='compile-cut':compile_cut(a.prep,a.base,a.certs,a.tag,a.shard,a.shards,a.out)
    else:compile_final(a.prep,a.base,a.certs,a.cuts,a.tag,a.out)
if __name__=='__main__':main()
