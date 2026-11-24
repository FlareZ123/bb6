"""Deterministic witness generation; every verdict is checked by Lean."""
from collections import defaultdict, Counter
from itertools import product
from pathlib import Path
from generate_sweeps import TABLES, parse, show

ROOT = Path(__file__).parent
PARENT = "1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---0LA"
MOVES = [w+d+q for w,d,q in product("01","LR","ABCDEF")]
PUMPS = {parse(p): i for i,p in enumerate(TABLES)}
DFAS = {}
for line in (ROOT / "four_hole_dfas.txt").read_text().splitlines():
    if not line or line.startswith("#"):
        continue
    c,a,e,f,rev,dfa = line.split()
    DFAS[c,a,e,f] = (int(rev), list(map(int,dfa)))

def classify(p):
    q,h,ones = 0,0,frozenset()
    trace = []
    prev = defaultdict(list)
    for n in range(1001):
        s = 2*q+int(h in ones)
        if p[s] == "---":
            return ("hole",n,s)
        low=high=h
        i=len(trace)-1
        for j in reversed(prev[q]):
            if n-j>256:
                break
            while i>=j:
                h0=trace[i][1]
                low=min(low,h0)
                high=max(high,h0)
                i-=1
            _,h0,o0=trace[j]
            delta=h-h0
            if delta>=0 and {x for x in o0 if x>=low}=={x-delta for x in ones if x-delta>=low}:
                return ("cycle",j,n-j,True,low)
            if delta<=0 and {x for x in o0 if x<=high}=={x-delta for x in ones if x-delta<=high}:
                return ("cycle",j,n-j,False,high)
        trace.append((q,h,ones))
        prev[q].append(n)
        a=p[s]
        ones=ones|{h} if a[0]=="1" else ones-{h}
        h+=1 if a[1]=="R" else -1
        q=ord(a[2])-65
    return ("open",)

def refine(p,s,a):
    return p[:s]+(a,)+p[s+1:]

def masks(p,rev,dfa):
    d=len(dfa)//2
    N=6*d+1
    H=N-1
    halt=1<<H
    T=[0]*(2*N)
    T[H]=T[N+H]=halt
    rules=[]
    for l,q,a in product(range(d),range(6),range(2)):
        mv=p[2*q+a]
        dst=a*N+6*l+q
        if mv=="---":
            T[dst]=halt
            continue
        w=int(mv[0])
        r=int(mv[1]=="R")
        nxt=ord(mv[2])-65
        if r!=rev:
            T[dst]=1<<(6*dfa[2*l+w]+nxt)
        else:
            for j,b in product(range(d),range(2)):
                if dfa[2*j+b]==l:
                    rules.append((dst,b*N+6*j+nxt,w*N))
    while True:
        z=halt
        while True:
            zz=z
            for j in range(N):
                if T[j]&z:
                    z|=1<<j
            if z==zz:
                break
        assert not z&1,(show(p),dfa)
        changed=False
        for dst,src,off in rules:
            v=T[dst]
            bits=T[src]
            while bits:
                b=bits&-bits
                v|=T[off+b.bit_length()-1]
                bits^=b
            if v!=T[dst]:
                T[dst]=v
                changed=True
        if not changed:
            return d,dfa,T[:N],T[N:],z

def slot(s):
    return f"({s//2},{str(bool(s%2)).lower()})"

def move(a):
    return "⟨"+",".join([str(a[0]=="1").lower(),str(a[1]=="R").lower(),str(ord(a[2])-65)])+"⟩"

stats=Counter()
def build(p,depth=1):
    res=classify(p)
    typ=res[0]
    if typ=="cycle":
        stats[typ]+=1
        _,e,k,r,b=res
        return f".cycle {e} {k} {str(r).lower()} ({b})"
    if typ=="open":
        if p in PUMPS:
            stats["proven"]+=1
            ns=f"BB6Coverage.Agent31Pump.M{PUMPS[p]}"
            return f".proven {ns}.table {ns}.never"
        key=tuple(p[i] for i in (5,1,8,10))
        rev,dfa=DFAS[key]
        d,D,L,R,z=masks(p,rev,dfa)
        stats["far"]+=1
        return f".far {str(bool(rev)).lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
    _,n,s=res
    if p.count("---")==1:
        stats["last"]+=1
        return f".last {n} {slot(s)}"
    stats["split"]+=1
    pad="  "*depth
    kids=(",\n"+pad).join(build(refine(p,s,a),depth+1) for a in MOVES)
    return f".split {n} {slot(s)} (byMove [\n{pad}{kids}\n{pad[:-2]}])"

HEADER = """set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent31FourHole
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole
"""
FOOTER="\nend BB6.Agent31FourHole\n"
def emit(name, imports, body):
    (ROOT/(name+".lean")).write_text("".join(f"import {i}\n" for i in imports)+HEADER+body+FOOTER)

def main():
    p=parse(PARENT)
    assert classify(p)==("hole",11,5)
    emit("FourHoleBase",["ThreeHoleAudit","SweepData"],"""
abbrev wideParent : PartialMachine := (pathEnd root 2 (path.take 7)).1
theorem wide_reachable : FirstHolePath wideParent 6 := by
  have hc : pathOK root 2 (path.take 7) = true := by decide
  exact pathOK_sound root 2 (path.take 7) FirstHolePath.root hc
theorem wide_root : wideParent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem wide_nohalt : weightedTNFNoAssignedHalt wideParent :=
  pathEnd_nohalt root 2 (path.take 7) firstOneCylinder_no_assigned_halt
abbrev wideChild (mv : Move) := refine wideParent (2,true) (some mv)
theorem wideQuery : queryOK 395 wideParent 11 (2,true) = true := by decide
""")
    stats["split"]+=1
    mods=[]
    for i,a in enumerate(MOVES):
        name=f"FourHoleKid{i:02}"
        mods.append(name)
        audit=build(refine(p,5,a))
        emit(name,["FourHoleBase"],f"""
def kid{i:02} : Audit := {audit}
theorem check{i:02} : check 395 (wideChild {move(a)}) kid{i:02} = true := by decide
""")
    assert stats==Counter(split=285,last=2757,cycle=3670,far=120,proven=9),stats
    print(stats)
    cases="\n".join(f"  · exact check{12*w+6*r+q:02}" for q,w,r in product(range(6),range(2),range(2)))
    body="""
def kids : Move → Audit := byMove ["""+",".join(f"kid{i:02}" for i in range(24))+"""]
theorem kids_checked (mv : Move) : check 395 (wideChild mv) (kids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
"""+cases+"""
def tree : Audit := .split 11 (2,true) kids
theorem tree_checked : check 395 wideParent tree = true := by
  change (queryOK 395 wideParent 11 (2,true) && allMoves (fun mv => check 395 (wideChild mv) (kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨wideQuery, allMoves_of _ kids_checked⟩

noncomputable def certificate : WeightedTNFCertificate 395 wideParent 6 :=
  certified 395 wideParent tree wide_root wide_nohalt tree_checked
theorem all_completions_weighted : ∀ m, compatible wideParent m → WeightedBound 395 m :=
  certificate.sound

theorem attained : ∃ m, compatible wideParent m ∧ HaltsAfter m 394 := by
  let p := wideChild ⟨true,true,2⟩
  let p' := refine p (4,false) (some ⟨true,true,3⟩)
  let p'' := refine p' (0,true) (some ⟨true,true,3⟩)
  let m := weightedTNFDefaultCompletion (refine p'' (5,false) none)
  have h0 : wideParent (2,true) = none := by decide
  have h1 : p (4,false) = none := by decide
  have h2 : p' (0,true) = none := by decide
  have h3 : p'' (5,false) = none := by decide
  have hr : (knownRun p'' 394).map readSlot = some (5,false) := by decide
  have hm : compatible (refine p'' (5,false) none) m :=
    weightedTNFDefaultCompletion_compatible _
  have hp'' : compatible p'' m := refine_preserves_compat p'' m (5,false) none h3 hm
  have hp' : compatible p' m := refine_preserves_compat p' m (0,true) (some ⟨true,true,3⟩) h2 hp''
  have hp : compatible p m := refine_preserves_compat p m (4,false) (some ⟨true,true,3⟩) h1 hp'
  have hpar : compatible wideParent m := refine_preserves_compat wideParent m (2,true) (some ⟨true,true,2⟩) h0 hp
  refine ⟨m,hpar,?_⟩
  cases hrun : knownRun p'' 394 with
  | none => simp [hrun] at hr
  | some c =>
    have hs : readSlot c = (5,false) := by simpa [hrun] using hr
    apply first_hole_halts p'' 394 c hrun
    · simpa [hs] using h3
    · simpa [hs] using hm

theorem exact_weighted_threshold (B : Nat) :
    (∀ m, compatible wideParent m → WeightedBound B m) ↔ 395 ≤ B := by
  constructor
  · intro h
    obtain ⟨m,hm,hh⟩ := attained
    have hz := firstOne_terminal wideParent wide_root m hm
    have hd : 0 ∈ delays (zeroNext m) 0 :=
      (mem_delays_iff hz).mpr ⟨0, TerminalPath.stop 0 hz⟩
    have hb := h m hm 394 0 hh hd
    omega
  · intro hb m hm k d hk hd
    exact Nat.le_trans (all_completions_weighted m hm k d hk hd) hb

#print axioms wide_reachable
#print axioms tree_checked
#print axioms exact_weighted_threshold
"""
    emit("FourHoleData",mods,body)

if __name__=="__main__":
    main()
