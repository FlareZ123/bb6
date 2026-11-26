"""Replay archived Raw124 candidate trees using the accepted zipper checker.
No new witness search for archived branches. Emit disjoint structural shards.
"""
import argparse, base64, hashlib, json, subprocess, sys, zlib
from pathlib import Path

HERE=Path(__file__).resolve().parent
IM=HERE.parent
D=IM/'agent2-tnf-raw124'
sys.path[:0]=[str(D),str(IM/'agent31-three-hole-tnf'),str(IM/'agent13-raw125')]
import generate_bundle as old
import audit_shards as shards
from generate_four_hole import masks,slot,move,parse

def main(branch,out):
    out.mkdir(parents=True,exist_ok=True)
    data={v['branch']:v for p in D.glob('complete-bundle*.json.zlib.b64') for v in json.loads(zlib.decompress(base64.b64decode(p.read_bytes())))}
    subprocess.run(['g++','-std=c++17','-O3',str(IM/'agent2-tnf-raw99/enumerate.cpp'),'-o',str(out/'enumerate')],check=True)
    subprocess.run([str(out/'enumerate'),'1RB---_1RC---_0RD---_1LD1RE_---1LF_---'+branch],cwd=out,check=True)
    raw=(out/'open.txt').read_bytes();rawtree=(out/'tree.json').read_bytes();opens=raw.decode().splitlines();index={s:i for i,s in enumerate(opens)}
    if branch=='0RF':
        assert hashlib.sha256(raw).hexdigest()=='d3b2229b49131b93d467dec5a282832bfb8d3aebd62fc268939be8023fef84c0'
        ds=dict((int(i),s) for i,s in (x.split() for x in (D/'rf-dfa.txt').read_text().splitlines()));assert set(ds)==set(range(len(opens)))
        bundle=dict(branch=branch,bound=71,far=list(range(len(opens))),pool=[(int(ds[i][0]),list(map(int,ds[i][1:]))) for i in range(len(opens))],single={},multi={},long={})
    else:
        bundle=data[branch];assert hashlib.sha256(raw).hexdigest()==bundle['hash'] and hashlib.sha256(rawtree).hexdigest()==bundle['tree_hash']
    B=bundle['bound'];stem='Raw124Z'+branch;NS='BB6.Agent32'+stem
    shards.ROOT=out;shards.B=B;shards.NS=NS
    shards.HEADER=f'''set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {NS}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
'''
    single={int(i):v for i,v in bundle['single'].items()};multi={int(i):v for i,v in bundle['multi'].items()};long={int(i):v for i,v in bundle['long'].items()};nested={int(i):v for i,v in bundle.get('nested',{}).items()};extra=bundle.get('extra_tree',{})
    far={i:bundle['pool'][k] for i,k in enumerate(bundle['far']) if k>=0}
    assert len(opens)==len(index)==len(bundle['far'])
    assert sum(map(len,(single,multi,long,far,nested)))+len(extra)==len(opens)
    assert set(single)|set(multi)|set(long)|set(far)|set(nested)|{index[k] for k in extra}==set(range(len(opens)))
    imports=['ZipThreeHoleAudit'];body=[]
    if single or multi or nested:
        imports+=['BlockPump','Agent2MultiPump'];body+=["open BB6Coverage.Agent50Pump BB6.Agent2MultiPump","def fromRows (xs : List (Option (Option Move))) : PartialMachine := fun s => (xs[2*s.1.val+s.2.toNat]?).getD none"]
        for is_multi,wits in [(False,single),(True,multi)]:
            for i,(entry,sh,spec) in sorted(wits.items()):
                if is_multi:
                    q,l,r=sh.split();sh=f'⟨{q},{old.mword(l)},{old.mword(r)}⟩'
                else:sh=old.shape(sh)
                typ='MCertificate' if is_multi else 'Certificate'
                table='['+','.join('none' if a=='---' else 'some (some '+move(a)+')' for a in parse(opens[i]))+']'
                body += [f'def pumpTable{i} : PartialMachine := fromRows {table}',f'def pumpCert{i} : {typ} := ⟨{entry},{sh},{old.compile_ops(spec,is_multi)}⟩',f'theorem pumpCheck{i} : pumpCert{i}.check pumpTable{i} = true := by decide',f'theorem pumpNever{i} : ∀ m, compatible pumpTable{i} m → NeverHalts m := {typ}.never pumpTable{i} pumpCert{i} pumpCheck{i}']
        for i,(mod,t,p) in sorted(nested.items()):
            imports.append(mod);body += [f'abbrev pumpTable{i} : PartialMachine := {t}',f'theorem pumpNever{i} : ∀ m, compatible pumpTable{i} m → NeverHalts m := {p}']
    base=stem+'Base'
    shards.emit(base,list(dict.fromkeys(imports)),body+[f'''abbrev p124 : PartialMachine := refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨true,false,5⟩)
abbrev pBranch : PartialMachine := refine p124 (5,true) (some {move(branch)})
theorem p124_nohalt : weightedTNFNoAssignedHalt p124 := weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt)
theorem pBranch_root : pBranch initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem pBranch_nohalt : weightedTNFNoAssignedHalt pBranch := weightedTNFNoAssignedHalt_refine _ _ _ p124_nohalt'''])
    def build(node):
        tag,*v=node
        if tag=='open':
            code=v[0]
            if code in extra:return build(extra[code])
            i=index[code]
            if i in single or i in multi or i in nested:return shards.Node(f'.proven pumpTable{i} pumpNever{i}')
            if i in long:
                a,*v=long[i];assert a in ('hole','cycle');tag='last' if a=='hole' else 'cycle'
                if a=='hole':assert code.count('---')==1
            else:
                rev,dfa=far[i];d,D,L,R,z=masks(parse(code),rev,dfa)
                return shards.Node(f'.far {str(bool(rev)).lower()} {d} ⟨0,{D},{L},{R},{z}⟩')
        if tag=='cycle':
            e,k,r,h=v;return shards.Node(f'.cycle {e} {k} {str(bool(r)).lower()} ({h})')
        if tag=='last':
            n,s=v;return shards.Node(f'.last {n} {slot(s)}')
        assert tag=='split';n,s,kids=v;assert len(kids)==24;ks=list(map(build,kids))
        return shards.Node(f'.split {n} {slot(s)}',ks,1+sum(k.size for k in ks),0)
    root=build(json.loads(rawtree));name=stem+'Tree';mod=shards.build_module(root,'pBranch',name,[base],limit=180,shardlimit=5000)
    shards.emit(stem+'Data',[mod],[f'''noncomputable def certificate : WeightedTNFCertificate {B} pBranch 6 := certifiedZip {B} pBranch {name} pBranch_root pBranch_nohalt {name}_checked
theorem bound_all : ∀ m, compatible pBranch m → WeightedBound {B} m := certificate.sound
#print axioms bound_all'''])
    print(f'{branch}: {root.size} nodes, {len(opens)} archived opens, weighted bound {B}',flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--branch',required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();main(a.branch,a.out.resolve())
