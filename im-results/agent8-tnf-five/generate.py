"""Regenerate and emit chunked, proof-carrying audits for five-hole siblings.
No branch is discharged by a search cutoff. Shared ThreeHoleAudit checks all data.
"""
from pathlib import Path
from collections import Counter
from itertools import product
import hashlib, json, subprocess, sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'agent31-three-hole-tnf'))
from generate_four_hole import masks, slot, move, parse
MOVES=[''.join(x) for x in product('01','LR','ABCDEF')]
SPECS={
  73: ('0LD',367,366,0,9,225,599,11624,1929,'55ba96537acce2e6b0bd2fea4ac9bb6768f7ced7cc30db3756f2857e4a5a54c9','1RB0LA_1RC0LD_0RD1RF_1LD1RE_1LA0LB_0RBHHH',[(8,'1LA'),(1,'0LA'),(5,'1RF'),(10,'0RB'),(11,'HHH')]),
  80: ('1RE',164,161,2,8,395,916,17511,3163,'6acaa10cd8d1191ade9661b63a3b3c8f53a67f64990a6587a0596d1dc39eed56','1RB1LA_1RC1RE_0RDHHH_1LD1RE_0RF0LB_0LA0LF',[(8,'0RF'),(11,'0LF'),(10,'0LA'),(1,'1LA'),(5,'HHH')]),
}
CHUNK=120

def generate(raw):
    divergence,B,steps,delay,first,nopen,nsplit,ncycle,nlast,sha,witness,assignments=SPECS[raw]
    folder=ROOT/f'raw{raw}'; folder.mkdir(exist_ok=True)
    parent=f'1RB---_1RC{divergence}_0RD---_1LD1RE_---0LB_------'
    subprocess.run(['g++','-std=c++17','-O3',str(ROOT.parent/'agent2-tnf-raw99/enumerate.cpp'),'-o','enumerate'],cwd=folder,check=True)
    subprocess.run([str(folder/'enumerate'),parent],cwd=folder,check=True)
    opens=(folder/'open.txt').read_bytes(); assert hashlib.sha256(opens).hexdigest()==sha
    opens=opens.decode().splitlines();assert len(opens)==len(set(opens))==nopen
    dfa=['00102030400']*nopen
    for row in (folder/'dfa.txt').read_text().split():
        a,indices=row.split(':')
        for i in indices.split(','):dfa[int(i)]=a
    certs=dict(zip(opens,dfa)); used=set()
    tree=json.loads((folder/'tree.json').read_text());assert tree[:3]==['split',first,8]
    prefix=f'Raw{raw}'; ns=f'BB6.Agent8{prefix}'
    header=f'''set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {ns}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole
'''
    def emit(name,imports,body):
        (folder/(name+'.lean')).write_text(''.join('import '+i+'\n' for i in imports)+header+body+f'\nend {ns}\n')
    p=f'p{raw}'
    base=f'''
abbrev {p} : PartialMachine :=
  refine (pathEnd root 2 (path.take 5)).1 (1,true) (some {move(divergence)})
theorem {p}_root : {p} initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem {p}_nohalt : weightedTNFNoAssignedHalt {p} :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 5) firstOneCylinder_no_assigned_halt)

theorem split_checked (p : PartialMachine) (n : Nat) (s : Slot) (kids : Move → Audit)
    (hq : queryOK {B} p n s = true)
    (hk : ∀ mv, check {B} (refine p s (some mv)) (kids mv) = true) :
    check {B} p (.split n s kids) = true := by
  change (queryOK {B} p n s && allMoves (fun mv => check {B} (refine p s (some mv)) (kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨hq, allMoves_of _ hk⟩
'''
    emit(prefix+'Base',['ThreeHoleAudit'],base)
    stats=Counter()
    def size(t):
        stats[t[0]]+=1
        return 1+sum(map(size,t[3])) if t[0]=='split' else 1
    size(tree)
    assert stats==Counter(split=nsplit,cycle=ncycle,last=nlast,open=nopen),stats
    def count(t):return 1+sum(map(count,t[3])) if t[0]=='split' else 1
    def render(t):
        tag,*v=t
        if tag=='cycle':
            e,k,r,b=v;return f'.cycle {e} {k} {str(r).lower()} ({b})'
        if tag=='last':
            n,s=v;return f'.last {n} {slot(s)}'
        if tag=='open':
            code=v[0];assert code not in used;used.add(code);a=certs[code]
            d,D,L,R,z=masks(parse(code),int(a[0]),[int(x,36) for x in a[1:]])
            return f'.far {str(a[0]=="1").lower()} {d} ⟨0,{D},{L},{R},{z}⟩'
        assert tag=='split';n,s,kids=v;assert len(kids)==24
        return f'.split {n} {slot(s)} (byMove [\n'+',\n'.join(map(render,kids))+'])'
    def compose(pname,name,t):
        if count(t)<=CHUNK:
            return f'def t_{name} : Audit := {render(t)}\ntheorem c_{name} : check {B} {pname} t_{name} = true := by decide\n'
        assert t[0]=='split';_,n,s,kids=t
        out=[];names=[]
        for i,kid in enumerate(kids):
            a=f'{name}_{i:02}';names.append(a)
            out.append(f'abbrev p_{a} := refine {pname} {slot(s)} (some {move(MOVES[i])})\n')
            out.append(compose(f'p_{a}',a,kid))
        out.append(combine(pname,name,n,s,names))
        return ''.join(out)
    def combine(pname,name,n,s,names):
        cases='\n'.join(f'  · exact c_{names[12*w+6*r+q]}' for q,w,r in product(range(6),range(2),range(2)))
        return f'''
def k_{name} : Move → Audit := byMove [{','.join('t_'+x for x in names)}]
def t_{name} : Audit := .split {n} {slot(s)} k_{name}
theorem q_{name} : queryOK {B} {pname} {n} {slot(s)} = true := by decide
theorem kcheck_{name} (mv : Move) : check {B} (refine {pname} {slot(s)} (some mv)) (k_{name} mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
theorem c_{name} : check {B} {pname} t_{name} = true :=
  split_checked {pname} {n} {slot(s)} k_{name} q_{name} kcheck_{name}
'''
    mods=[];names=[]
    for i,kid in enumerate(tree[3]):
        a=f'kid{i:02}';names.append(a);name=f'{prefix}Kid{i:02}';mods.append(name)
        emit(name,[prefix+'Base'],f'abbrev p_{a} := refine {p} (4,false) (some {move(MOVES[i])})\n'+compose(f'p_{a}',a,kid))
    body=combine(p,'root',first,8,names)
    body+=f'''
noncomputable def certificate{raw} : WeightedTNFCertificate {B} {p} 6 :=
  certified {B} {p} t_root {p}_root {p}_nohalt c_root
theorem all{raw} : ∀ m, compatible {p} m → WeightedBound {B} m := certificate{raw}.sound

theorem attained{raw} : ∃ m, compatible {p} m ∧ HaltsAfter m {steps} ∧ {delay} ∈ delays (zeroNext m) 0 := by
  let p0 := {p}
'''
    for i,(s,a) in enumerate(assignments):
        t='none' if a=='HHH' else '(some '+move(a)+')'
        body+=f'  let p{i+1} := refine p{i} {slot(s)} {t}\n'
    body+=f'  let m := weightedTNFDefaultCompletion p{len(assignments)}\n'
    for i,(s,a) in enumerate(assignments):body+=f'  have h{i} : p{i} {slot(s)} = none := by decide\n'
    last=assignments[-1][0];end=len(assignments);assert assignments[-1][1]=='HHH'
    body+=f'  have hr : (knownRun p{end-1} {steps}).map readSlot = some {slot(last)} := by decide\n'
    body+=f'  have hm{end} : compatible p{end} m := weightedTNFDefaultCompletion_compatible _\n'
    for i in reversed(range(end)):
        s,a=assignments[i];t='none' if a=='HHH' else '(some '+move(a)+')'
        body+=f'  have hm{i} : compatible p{i} m := refine_preserves_compat p{i} m {slot(s)} {t} h{i} hm{i+1}\n'
    body+=f'''  have hd : {delay} ∈ delays (zeroNext m) 0 := by decide
  refine ⟨m,hm0,?_,hd⟩
  cases hrun : knownRun p{end-1} {steps} with
  | none => simp [hrun] at hr
  | some c =>
    have hs : readSlot c = {slot(last)} := by simpa [hrun] using hr
    apply first_hole_halts p{end-1} {steps} c hrun
    · simpa [hs] using h{end-1}
    · simpa [hs] using hm{end}

theorem exact{raw} (T : Nat) :
    (∀ m, compatible {p} m → WeightedBound T m) ↔ {B} ≤ T := by
  constructor
  · intro h
    obtain ⟨m,hm,hh,hd⟩ := attained{raw}
    have hb := h m hm {steps} {delay} hh hd
    omega
  · intro hb m hm k d hk hd
    exact Nat.le_trans (all{raw} m hm k d hk hd) hb

#print axioms c_root
#print axioms all{raw}
#print axioms attained{raw}
#print axioms exact{raw}
'''
    assert used==set(certs)
    emit(prefix+'Data',mods,body)
    print(raw,stats,'all FAR witnesses emitted; chunk limit',CHUNK)

if __name__=='__main__':
    for raw in map(int,sys.argv[1:] or SPECS):generate(raw)
