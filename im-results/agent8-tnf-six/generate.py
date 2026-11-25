"""Regenerate and emit chunked, proof-carrying audits for six-hole siblings.
No branch is discharged by a search cutoff. Shared ThreeHoleAudit checks all data.
"""
from pathlib import Path
from collections import Counter
from itertools import product
import hashlib, json, subprocess, sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'agent31-three-hole-tnf'))
from generate_four_hole import masks, slot, move, parse
import generate_sweeps as one
sys.path.insert(0,str(ROOT.parent/'agent10-tnf-multipump'))
import multi
MOVES=[''.join(x) for x in product('01','LR','ABCDEF')]
SPECS={119: ('0RE',572,571,0,8,8765,6651,112287,31922,'102df4cbc607678e502f404889cf0f0982d2ccd6c20c19d16642635a095036a6','1RB0LF_1RC1RE_0RDHHH_1LD1RE_1LF0RE_1LA0LA',[(8,'1LF'),(10,'1LA'),(3,'1RE'),(1,'0LF'),(11,'0LA'),(5,'HHH')])}
COUNTERS={119:[5619,5750,5751,5752,5753,5754,5755,5756,5757]}
ONE={119:[461,462,509,510,2010,2284,5152,6530,7958]}
TWO={119:[4028]}
CHUNK=240

def generate(raw):
    divergence,B,steps,delay,first,nopen,nsplit,ncycle,nlast,sha,witness,assignments=SPECS[raw]
    folder=ROOT/f'raw{raw}'; folder.mkdir(exist_ok=True)
    parent=f'1RB---_1RC---_0RD---_1LD1RE_---{divergence}_------'
    subprocess.run(['g++','-std=c++17','-O3',str(ROOT.parent/'agent2-tnf-raw99/enumerate.cpp'),'-o','enumerate'],cwd=folder,check=True)
    subprocess.run([str(folder/'enumerate'),parent],cwd=folder,check=True)
    opens=(folder/'open.txt').read_bytes(); assert hashlib.sha256(opens).hexdigest()==sha
    opens=opens.decode().splitlines();assert len(opens)==len(set(opens))==nopen
    subprocess.run(['g++','-std=c++17','-O3',str(ROOT/'bank.cpp'),'-o','bank'],cwd=folder,check=True)
    hits=subprocess.check_output([str(folder/'bank'),str(folder/'bank.txt'),str(folder/'open.txt')],text=True)
    certs={}
    for row in hits.splitlines():
        i,a=row.split(':');certs[opens[int(i)]]=a
    symbolic=set(COUNTERS[raw]+ONE[raw]+TWO[raw])
    assert set(certs)==set(opens)-{opens[i] for i in symbolic}
    pumps={opens[i]:(f'BB6.Agent8Raw{raw}Counter.M{i}.pt',f'BB6.Agent8Raw{raw}Counter.M{i}.never') for i in COUNTERS[raw]}
    pumpns=f'BB6.Agent8Raw{raw}Sweeps'
    pc=['import SweepPumping','set_option maxRecDepth 100000','set_option maxHeartbeats 0',f'namespace {pumpns}','open BB6Coverage BB6Coverage.Agent31Pump']
    for i in ONE[raw]:
        p=one.parse(opens[i]);ans=one.candidate(p,one.concrete_events(p,10000));assert ans is not None,(raw,i)
        code,info=one.generate(i,p,ans);pc.append(code)
        pumps[opens[i]]=(f'{pumpns}.M{i}.table',f'{pumpns}.M{i}.never')
        print(i,'one',info)
    for i in TWO[raw]:
        assert raw==119 and i==4028
        p=one.parse(opens[i])
        st=multi.C(4,multi.lit('0000')+multi.rep('0')+multi.lit('10100')+multi.rep('100'),())
        tg=multi.C(4,multi.lit('00000')+multi.rep('0')+multi.lit('10100100')+multi.rep('100'),())
        ans=multi.pump(p,st,tg);assert ans is not None
        code,info=multi.generate(i,p,(56,st,tg,ans));assert info==(56,66,8),info
        pc.append(code);pumps[opens[i]]=(f'{pumpns}.M{i}.table',f'{pumpns}.M{i}.never')
    pc.append(f'end {pumpns}')
    (folder/f'Raw{raw}Sweeps.lean').write_text('\n\n'.join(pc)+'\n')
    used=set()

    tree=json.loads((folder/'tree.json').read_text());assert tree[:3]==['split',first,8]; root_slot=tree[2]
    prefix=f'Raw{raw}'; ns=f'BB6.Agent8{prefix}'
    header=f'''set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {ns}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
'''
    def emit(name,imports,body):
        (folder/(name+'.lean')).write_text(''.join('import '+i+'\n' for i in imports)+header+body+f'\nend {ns}\n')
    p=f'p{raw}'
    base=f'''
abbrev {p} : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some {move(divergence)})
theorem {p}_root : {p} initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem {p}_nohalt : weightedTNFNoAssignedHalt {p} :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt)

theorem split_checked (p : PartialMachine) (n : Nat) (s : Slot) (kids : Move → Audit)
    (hq : zipQueryOK {B} p n s = true)
    (hk : ∀ mv, zipCheck {B} (refine p s (some mv)) (kids mv) = true) :
    zipCheck {B} p (.split n s kids) = true := by
  change (zipQueryOK {B} p n s && allMoves (fun mv => zipCheck {B} (refine p s (some mv)) (kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨hq, allMoves_of _ hk⟩
'''
    emit(prefix+'Base',['ZipThreeHoleAudit',prefix+'CounterEntries',prefix+'Sweeps'],base)
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
            code=v[0];assert code not in used;used.add(code)
            if code in pumps:return '.proven '+ ' '.join(pumps[code])
            a=certs[code]
            d,D,L,R,z=masks(parse(code),int(a[0]),[int(x,36) for x in a[1:]])
            return f'.far {str(a[0]=="1").lower()} {d} ⟨0,{D},{L},{R},{z}⟩'
        assert tag=='split';n,s,kids=v;assert len(kids)==24
        return f'.split {n} {slot(s)} (byMove [\n'+',\n'.join(map(render,kids))+'])'
    def compose(pname,name,t):
        if count(t)<=CHUNK:
            return f'def t_{name} : Audit := {render(t)}\ntheorem c_{name} : zipCheck {B} {pname} t_{name} = true := by decide\n'
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
theorem q_{name} : zipQueryOK {B} {pname} {n} {slot(s)} = true := by decide
theorem kcheck_{name} (mv : Move) : zipCheck {B} (refine {pname} {slot(s)} (some mv)) (k_{name} mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
theorem c_{name} : zipCheck {B} {pname} t_{name} = true :=
  split_checked {pname} {n} {slot(s)} k_{name} q_{name} kcheck_{name}
'''
    mods=[];names=[]
    for i,kid in enumerate(tree[3]):
        a=f'kid{i:02}';names.append(a);name=f'{prefix}Kid{i:02}';mods.append(name)
        emit(name,[prefix+'Base'],f'abbrev p_{a} := refine {p} {slot(root_slot)} (some {move(MOVES[i])})\n'+compose(f'p_{a}',a,kid))
    body=combine(p,'root',first,root_slot,names)
    body+=f'''
noncomputable def certificate{raw} : WeightedTNFCertificate {B} {p} 6 :=
  certifiedZip {B} {p} t_root {p}_root {p}_nohalt c_root
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
    assert used==set(opens)
    emit(prefix+'Data',mods,body)
    print(raw,stats,'all FAR and symbolic witnesses emitted; chunk limit',CHUNK)

if __name__=='__main__':
    for raw in map(int,sys.argv[1:] or SPECS):generate(raw)
