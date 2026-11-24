"""Replay the exact candidate search; emit checked Lean modules, never trust a cutoff."""
from pathlib import Path
import sys, json, hashlib, subprocess
from collections import Counter
from itertools import product
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent31-three-hole-tnf"))
from generate_four_hole import masks, slot, move, parse
PARENT="1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---0RE"
MOVES=[w+d+q for w,d,q in product("01","LR","ABCDEF")]
subprocess.run(["g++","-std=c++17","-O3","enumerate.cpp","-o","enumerate"],cwd=ROOT,check=True)
subprocess.run([str(ROOT/"enumerate")],cwd=ROOT,check=True)
raw=(ROOT/"open.txt").read_bytes()
assert hashlib.sha256(raw).hexdigest()=="66b28e7a39b97c39b3dcacbb30e1efdadef9a33f8246911fb3a7459ca1246861"
opens=raw.decode().splitlines()
assert len(opens)==297 and len(set(opens))==297
index={s:i for i,s in enumerate(opens)}
dfa=["00102030400"]*len(opens)
rows=[x for x in (ROOT/"dfa.txt").read_text().splitlines() if x and not x.startswith("#")]
for i in map(int,rows[0].split(",")):dfa[i]="00102030401"
for x in rows[1].split():
    i,v=x.split(":");dfa[int(i)]=v
pumprows=[x for x in (ROOT/"pumps.txt").read_text().splitlines() if x and not x.startswith("#")]
HEADER="""set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent2Raw99
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole
"""
FOOTER="\nend BB6.Agent2Raw99\n"
def emit(name,imports,body):
    (ROOT/(name+".lean")).write_text("".join("import "+i+"\n" for i in imports)+HEADER+body+FOOTER)
def shape(s):
    q,v=s.split(":");a,b,c,d,e,f=v.split(",")
    return f'⟨{q},(word "{a}" "{b}" "{c}"),(word "{d}" "{e}" "{f}")⟩'
def ops(s):
    out=[]
    for v in s.split():
        if v.isdigit():out.extend([".step"]*int(v))
        elif v.startswith("W"):out.append(".rewrite "+shape(v[1:]))
        else:
            k,c,w=v[1:].split(",")
            out.append(f'.{"left" if v[0]=="L" else "right"} {k} {c} (bits "{w}")')
    return "["+",".join(out)+"]"
pumpidx=set()
body="""open BB6Coverage.Agent50Pump

def fromRows (xs : List (Option (Option Move))) : PartialMachine :=
  fun s => (xs[2*s.1.val+s.2.toNat]?).getD none
"""
for line,opline in zip(pumprows[::2],pumprows[1::2]):
    i,entry,pad,sh=line.split();i=int(i);pumpidx.add(i)
    assert dfa[i]=="-"
    table="["+",".join("none" if a=="---" else "some (some "+move(a)+")" for a in parse(opens[i]))+"]"
    test=f"padCheck pumpTable{i} pumpCert{i}" if pad=="1" else f"pumpCert{i}.check pumpTable{i}"
    sound="padNever" if pad=="1" else "Certificate.never"
    body+=f"""
def pumpTable{i} : PartialMachine := fromRows {table}
def pumpCert{i} : Certificate := ⟨{entry},{shape(sh)},{ops(opline)}⟩
theorem pumpCheck{i} : {test} = true := by decide
theorem pumpNever{i} : ∀ m, compatible pumpTable{i} m → NeverHalts m :=
  {sound} pumpTable{i} pumpCert{i} pumpCheck{i}
#print axioms pumpNever{i}
"""
assert pumpidx=={i for i,v in enumerate(dfa) if v=="-"}
emit("Raw99Pumps",["ThreeHoleAudit","Raw99Pad"],body)
tree=json.loads((ROOT/"tree.json").read_text())
stats=Counter()
def build(node):
    tag,*v=node;stats[tag]+=1
    if tag=="cycle":
        e,k,r,b=v
        return f".cycle {e} {k} {str(r).lower()} ({b})"
    if tag=="last":
        n,s=v;return f".last {n} {slot(s)}"
    if tag=="open":
        code=v[0];i=index[code];a=dfa[i]
        if a=="-":return f".proven pumpTable{i} pumpNever{i}"
        rev=int(a[0]);d,D,L,R,z=masks(parse(code),rev,list(map(int,a[1:])))
        return f".far {str(bool(rev)).lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
    assert tag=="split"
    n,s,kids=v;assert len(kids)==24
    return f".split {n} {slot(s)} (byMove [\n"+",\n".join(build(k) for k in kids)+"])"
assert tree[:3]==["split",17,10]
emit("Raw99Base",["Raw99Pumps"],"""
abbrev p99 : PartialMachine :=
  refine (pathEnd root 2 (path.take 6)).1 (5,true) (some ⟨false,true,4⟩)
theorem p99_root : p99 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p99_nohalt : weightedTNFNoAssignedHalt p99 :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 6) firstOneCylinder_no_assigned_halt)
abbrev child99 (mv : Move) := refine p99 (5,false) (some mv)
theorem query99 : queryOK 196 p99 17 (5,false) = true := by decide
""")
mods=[]
for i,kid in enumerate(tree[3]):
    name=f"Raw99Kid{i:02}";mods.append(name)
    emit(name,["Raw99Base"],f"""
def kid{i:02} : Audit := {build(kid)}
theorem check{i:02} : check 196 (child99 {move(MOVES[i])}) kid{i:02} = true := by decide
""")
assert stats==Counter(split=164,cycle=2649,last=850,open=297),stats
cases="\n".join(f"  · exact check{12*w+6*r+q:02}" for q,w,r in product(range(6),range(2),range(2)))
body="""
def kids99 : Move → Audit := byMove ["""+",".join(f"kid{i:02}" for i in range(24))+"""]
theorem kids99_checked (mv : Move) : check 196 (child99 mv) (kids99 mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
"""+cases+"""
def tree99 : Audit := .split 17 (5,false) kids99
theorem tree99_checked : check 196 p99 tree99 = true := by
  change (queryOK 196 p99 17 (5,false) && allMoves (fun mv => check 196 (child99 mv) (kids99 mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query99, allMoves_of _ kids99_checked⟩
noncomputable def certificate99 : WeightedTNFCertificate 196 p99 6 :=
  certified 196 p99 tree99 p99_root p99_nohalt tree99_checked
theorem all99 : ∀ m, compatible p99 m → WeightedBound 196 m :=
  certificate99.sound

theorem attained99 : ∃ m, compatible p99 m ∧ HaltsAfter m 195 := by
  let p := child99 ⟨true,false,0⟩
  let p' := refine p (4,false) (some ⟨true,true,1⟩)
  let p'' := refine p' (0,true) (some ⟨false,true,3⟩)
  let m := weightedTNFDefaultCompletion (refine p'' (2,true) none)
  have h0 : p99 (5,false) = none := by decide
  have h1 : p (4,false) = none := by decide
  have h2 : p' (0,true) = none := by decide
  have h3 : p'' (2,true) = none := by decide
  have hr : (knownRun p'' 195).map readSlot = some (2,true) := by decide
  have hm : compatible (refine p'' (2,true) none) m :=
    weightedTNFDefaultCompletion_compatible _
  have hp'' : compatible p'' m := refine_preserves_compat p'' m (2,true) none h3 hm
  have hp' : compatible p' m := refine_preserves_compat p' m (0,true) (some ⟨false,true,3⟩) h2 hp''
  have hp : compatible p m := refine_preserves_compat p m (4,false) (some ⟨true,true,1⟩) h1 hp'
  have hpar : compatible p99 m := refine_preserves_compat p99 m (5,false) (some ⟨true,false,0⟩) h0 hp
  refine ⟨m,hpar,?_⟩
  cases hrun : knownRun p'' 195 with
  | none => simp [hrun] at hr
  | some c =>
    have hs : readSlot c = (2,true) := by simpa [hrun] using hr
    apply first_hole_halts p'' 195 c hrun
    · simpa [hs] using h3
    · simpa [hs] using hm

theorem exact99 (B : Nat) :
    (∀ m, compatible p99 m → WeightedBound B m) ↔ 196 ≤ B := by
  constructor
  · intro h
    obtain ⟨m,hm,hh⟩ := attained99
    have hz := firstOne_terminal p99 p99_root m hm
    have hd : 0 ∈ delays (zeroNext m) 0 :=
      (mem_delays_iff hz).mpr ⟨0, TerminalPath.stop 0 hz⟩
    have hb := h m hm 195 0 hh hd
    omega
  · intro hb m hm k d hk hd
    exact Nat.le_trans (all99 m hm k d hk hd) hb

#print axioms tree99_checked
#print axioms all99
#print axioms attained99
#print axioms exact99
"""
emit("Raw99Data",mods,body)
print("Candidate tree:",stats,"FAR",len(opens)-len(pumpidx),"pumps",len(pumpidx))
