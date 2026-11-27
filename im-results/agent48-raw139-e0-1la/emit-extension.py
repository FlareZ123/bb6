"""Check exact extension subtrees and width-two reflected certificates."""
import json,zlib,base64,pathlib,sys
from blockcert import generate
from package import block_source, bl, slot
here=pathlib.Path(__file__).resolve().parent
m=json.loads(zlib.decompress(base64.b64decode((here/'extension.json.zlib.b64').read_text())))
B=881057
ORDER=[4*q+2*w+r for w in range(2) for r in range(2) for q in range(6)]
ns='BB6.Agent48Raw139E0OneLAExtension'
def leaf(k):
    t,a=m[k];kind,*p=a
    if k in ('9138','9162'):
        q=f'BB6.Agent48Raw139E0OneLASweeps.Sweep{k}'
        return f'.proven {q}.ctr {q}.never'
    if kind=='wide' and p[0]==2:
        q=f'{ns}Blocks.R{k}'
        return f'.proven {q}.ctr {q}.never'
    if kind=='cycle':
        e,s,r,x=p
        return f'.cycle {e} {s} {bl(r)} ({x})'
    if kind=='last':
        n,s=p
        return f'.last {n} {slot(s)}'
    if kind=='far':
        rev,d,dfa,t0,t1,z=p
        return f'.far {bl(rev)} {d} ⟨0,{dfa},{t0},{t1},{z}⟩'
    if kind=='split':
        n,s=p;ss=[]
        for v in ORDER:
            k2=f'{k}_{v}';t2=t.copy();t2[s]=v
            assert t2==m[k2][0]
            ss.append(leaf(k2))
        return f'.split {n} {slot(s)} (byMove [\n'+',\n'.join(ss)+'])'
    raise ValueError((k,a))
def render(k):
    t,a=m[k]
    return f"""namespace R{k}
def parent : PartialMachine := fromCodes {t}
def tree : Audit := {leaf(k)}
theorem checked : fastCheck {B} parent tree = true := by decide +kernel
theorem root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide +kernel
theorem nohalt : weightedTNFNoAssignedHalt parent := by
  intro s
  unfold parent fromCodes
  cases h : ({t} : List Nat)[2 * s.1.val + s.2.toNat]? with
  | none => simp [h]
  | some n => by_cases hn : n < 24 <;> simp [h, hn]
noncomputable def certificate : WeightedTNFCertificate {B} parent 6 :=
  certifiedFast {B} parent tree root nohalt checked
theorem all_completions_weighted : ∀ m, compatible parent m → WeightedBound {B} m := certificate.sound
#print axioms all_completions_weighted
end R{k}
"""
def block(k,out):
    t,(_,w,c,mod,r,flip,ph)=m[k]
    assert w==2 and flip
    mirror=[v^1 if v!=24 else v for v in t]
    data=generate(mirror,w,c,mod,r,False,phase=ph)
    assert data is not None
    s='import BlockFAR2\nimport BlockFARBridge\nimport FastThreeHoleAudit\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n'
    s+=block_source(int(k),mirror,data).replace('BB6.Agent48F1OneRABlocks',ns+'Blocks')
    q=f'{ns}Blocks.H{k}'
    s+=f"""namespace {ns}Blocks.R{k}
open BB6Coverage BB6Coverage.FAR
def ctr : PartialMachine := fromCodes {t}
theorem same : reflectPartial ctr = {q}.ctr :=
  BB6.Agent31ThreeHole.tableOK_sound _ _ (by decide +kernel)
theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m := by
  apply reflectNever m
  apply {q}.never
  rw [← same]
  exact reflectCompatible ctr m hm
#print axioms never
end {ns}Blocks.R{k}
"""
    (out/f'OneLAExtBlock{k}.lean').write_text(s)
def main(out):
    out.mkdir(exist_ok=True,parents=True)
    keys=[];modules=[]
    for k,(t,a) in m.items():
        if '_' in k or k in ('8938','11147') or (a[0]=='wide' and a[1]!=2):continue
        imports='import FastThreeHoleAudit\n'
        if a[0]=='wide':
            block(k,out);imports+=f'import OneLAExtBlock{k}\n'
        if k in ('9138','9162'):imports+='import OneLAGrowth\n'
        s=imports+'set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n'+f'namespace {ns}\nopen BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10FastAudit\n'+render(k)+f'end {ns}\n'
        name=f'OneLAExt{k}'
        (out/(name+'.lean')).write_text(s);keys.append(k);modules.append(name)
    covered=[m[k][0] for k in keys]
    src=''.join('import '+v+'\n' for v in modules)+f"""set_option maxHeartbeats 0
namespace {ns}
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay
def covered : List (List Nat) := {covered}
theorem all_covered (t : List Nat) (ht : t ∈ covered) (m : Machine)
    (hm : compatible (fromCodes t) m) : WeightedBound {B} m := by
  simp only [covered,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with """+' | '.join('rfl' for _ in keys)+'\n'+''.join(f'  · exact R{k}.all_completions_weighted m hm\n' for k in keys)+f'#print axioms all_covered\nend {ns}\n'
    (out/'OneLAExtension.lean').write_text(src)
    print('Generated',len(keys),'exact extension roots:',keys)
if __name__=='__main__':main(pathlib.Path(sys.argv[1]))
