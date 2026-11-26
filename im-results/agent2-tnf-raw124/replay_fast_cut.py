"""Replay archived raw124 fast-partition witnesses. All verdicts are kernel checked."""
from pathlib import Path
import argparse, json, sys, subprocess, tempfile
from collections import Counter
import base64,hashlib,zlib
from itertools import product

ROOT=Path(__file__).resolve().parent
IM=ROOT.parent
sys.path[:0]=[str(IM/x) for x in ('agent31-three-hole-tnf','agent13-raw125','agent10-tnf-multipump')]
import audit_shards as shards
from audit_shards import Node
from generate_four_hole import masks,move,slot,parse
import multi
from generate_growth import pump
sys.path.insert(0,str(IM/'agent1-ngram'))
from emit_ngram import emit as emit_ngram

PARENT='1RB---_1RC---_0RD---_1LD1RE_---1LF_---'

def replay(spec,out):
    b=spec['branch'];out.mkdir(parents=True,exist_ok=True)
    ns='BB6.Agent2Raw124New'+b;stem='Raw124New'+b;bound=3006
    shards.ROOT=out;shards.NS=ns;shards.B=bound
    shards.HEADER=f"""set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {ns}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
"""
    with tempfile.TemporaryDirectory() as d:
        tmp=Path(d);exe=tmp/'partition';prefix=tmp/'tree'
        subprocess.run(['g++','-std=c++20','-O3',str(ROOT/'fast_partition.cpp'),'-o',str(exe)],check=True)
        subprocess.run([str(exe),PARENT+b,str(spec['cap']),str(spec['lookback']),str(prefix)],check=True)
        raw=prefix.with_suffix('.open').read_bytes();treebytes=prefix.with_suffix('.json').read_bytes()
        assert hashlib.sha256(raw).hexdigest()==spec['open_sha256']
        assert hashlib.sha256(treebytes).hexdigest()==spec['tree_sha256']
        opens=[s.replace('_','') for s in raw.decode().splitlines()];index={s:i for i,s in enumerate(opens)}
        assert len(opens)==len(index)==len(spec['far'])
        far={i:spec['bank'][j] for i,j in enumerate(spec['far']) if j>=0}
        growth=spec['growth'];ref={}
        if spec.get('ngram'):
            exe=tmp/'ngram'
            subprocess.run(['g++','-std=c++17','-O3',str(IM/'agent1-ngram'/'ngram.cpp'),'-o',str(exe)],check=True)
            for si,k in spec['ngram'].items():
                i=int(si);assert i not in far
                cert=subprocess.run([str(exe),str(k)],input=f'{i} {opens[i]}\n',text=True,capture_output=True,check=True).stdout.strip().split(maxsplit=1)[1]
                name=stem+f'NGram{i}';gns='BB6.Agent2'+name
                body=emit_ngram(i,opens[i],cert)
                checks=[]
                for q,a in product(range(6),['false','true']):
                    checks.append(f'theorem row{q}{a} : (row c{i} {q} {a}).all (fun j => stateStepOK p{i} c{i} {q} {a} (j/2^(c{i}.n+1)) (j%2^(c{i}.n+1))) = true := by decide')
                checks.append(f"""theorem ok{i} : check p{i} c{i} = true := by
  unfold check
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨by decide, by decide⟩, by decide⟩, ?_⟩
  apply List.all_eq_true.mpr
  intro q _
  apply List.all_eq_true.mpr
  intro a _
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases a""")
                checks += [f'  · exact row{q}{a}' for q,a in product(range(6),['false','true'])]
                body=body.replace(f'theorem ok{i} : check p{i} c{i} = true := by decide','\n'.join(checks))
                (out/(name+'.lean')).write_text(f"""import NGramCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {gns}
open BB6Coverage BB6.Agent1NGram
{body}
def table : PartialMachine := p{i}
theorem never_source (m : Machine) (hm : compatible table m) : NeverHalts m := never{i} m hm
#print axioms never_source
end {gns}
""")
                ref[i]=(name,gns)
    for j in range(0,len(growth),12):
        name=stem+f'Growth{j//12:02}'
        gns='BB6.Agent2'+name
        lines=['import SweepPumping','set_option maxRecDepth 100000','set_option maxHeartbeats 0',f'namespace {gns}','open BB6Coverage BB6Coverage.Agent31Pump']
        for i,flat,t,q,l,r,l2,r2,a,beta in growth[j:j+12]:
            assert opens[i]==flat and i not in far and i not in ref
            st=multi.C(q,tuple(map(tuple,l)),tuple(map(tuple,r)));tg=multi.C(q,tuple(map(tuple,l2)),tuple(map(tuple,r2)))
            p=multi.parse(flat);ans=pump(p,st,tg);assert ans is not None,(i,flat)
            hist,_=ans;assert (sum(x[3] for x in hist if x[0]=='step'),sum(x[3] for x in hist if x[0]=='loop'))==(a,beta),(i,flat)
            proof,_=multi.generate(i,p,(t,st,tg,ans));lines.append(proof)
            ref[i]=(name,gns+f'.M{i}')
        lines.append(f'end {gns}');(out/(name+'.lean')).write_text('\n\n'.join(lines)+'\n')
    base=stem+'Base'
    shards.emit(base,['PartialAudit'],[f'''abbrev parent124 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨true,false,5⟩)
abbrev branch : PartialMachine := refine parent124 (5,true) (some {move(b)})
theorem branch_root : branch initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem parent_nohalt : weightedTNFNoAssignedHalt parent124 :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt)
theorem branch_nohalt : weightedTNFNoAssignedHalt branch := weightedTNFNoAssignedHalt_refine _ _ _ parent_nohalt
'''])
    counts=Counter();remaining=[]
    def build(n):
        tag,*v=n
        if tag=='cycle':
            counts[tag]+=1;e,k,r,x=v
            return Node(f'.cycle {e} {k} {str(bool(r)).lower()} ({x})')
        if tag=='last':
            counts[tag]+=1;t,s=v;return Node(f'.last {t} {slot(s)}')
        if tag=='open':
            table=v[0].replace('_','');i=index[table]
            if i in far:
                counts['far']+=1;code=far[i];n,D,L,R,z=masks(parse(table),int(code[0]),[int(c,36) for c in code[1:]])
                return Node(f'.far {str(bool(int(code[0]))).lower()} {n} ⟨0,{D},{L},{R},{z}⟩')
            if i in ref:
                mod,gns=ref[i];kind='ngram' if 'NGram' in mod else 'growth';counts[kind]+=1;return Node(f'.proven {gns}.table {gns}.'+('never_source' if kind=='ngram' else 'never'))
            counts['unresolved']+=1;remaining.append(table);return Node('.unresolved',open_count=1)
        assert tag=='split';counts[tag]+=1;t,s,kids=v;assert len(kids)==24
        cs=[build(k) for k in kids];return Node(f'.split {t} {slot(s)}',cs,1+sum(k.size for k in cs),sum(k.open_count for k in cs))
    tree=build(json.loads(treebytes));assert len(remaining)==tree.open_count
    name='raw124New'+b
    mod=shards.build_module(tree,'branch',name,[base,*sorted({m for m,_ in ref.values()})],limit=120,shardlimit=5000)
    treeexpr=name if tree.open_count else f'(.closed {name})'
    shards.emit(stem+'Cut',[mod],[f'''def cut : PartialAudit := {treeexpr}
theorem cut_checked : partialCheck {bound} branch cut = true := {name}_checked
def residuals := partialResiduals branch cut
theorem residual_count : residuals.length = {len(remaining)} := by decide
theorem branch_sound : ∀ m, compatible branch m → WeightedBound {bound} m ∨ ∃ e ∈ residuals, compatible e.2 m :=
  partialSound {bound} branch cut branch_root branch_nohalt cut_checked
#print axioms cut_checked
#print axioms residual_count
#print axioms branch_sound'''])
    (out/(stem+'.remaining')).write_text('\n'.join(remaining)+'\n')
    print(b,dict(counts),'nodes',tree.size,'remaining mass',sum(25**(s.count('---')) for s in remaining),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('spec',type=Path);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
    replay(json.loads(zlib.decompress(base64.b64decode(a.spec.read_bytes()))),a.out)
