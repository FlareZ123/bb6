import Lean.Elab.Tactic.Omega
import AIterDoubleZero
import EAltBoundaryFirst

set_option maxHeartbeats 16000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace BB6.Agent2AIterDoubleZeroFirst
open CryptidBoundary
open BB6.Agent2EAltBoundaryFirst
open BB6.Agent2AIterDoubleZero

private abbrev NoF := BB6.Agent2ATurnFamily.NoF

private theorem appendNoF (c d : Cfg) (a b : Nat)
    (ha : NoF c a) (he : run a c = d) (hb : NoF d b) :
    NoF c (a+b) := by
  intro t ht
  by_cases hs : t<a
  · exact ha t hs
  · have heq : t=a+(t-a) := by omega
    rw [heq,run_add,he]
    exact hb (t-a) (by omega)

private theorem appendNoPhysical (c d : Cfg) (a b : Nat)
    (ha : NoPhysical c a) (he : run a c = d)
    (hb : NoPhysical d b) : NoPhysical c (a+b) := by
  intro t ht
  by_cases hs : t<a
  · exact ha t hs
  · have heq : t=a+(t-a) := by omega
    rw [heq,run_add,he]
    exact hb (t-a) (by omega)

private theorem noF_to_noPhysical (c : Cfg) (n : Nat)
    (h : NoF c n) : NoPhysical c n := by
  intro t ht hp
  exact h t ht hp.1

private theorem aTenTwo_noF (L zs : List Bool) :
    NoF (⟨L,false,[true,false]++zs,0⟩ : Cfg) 2 := by
  intro t ht
  have cases : t=0 ∨ t=1 := by omega
  rcases cases with rfl | rfl
  all_goals simp [run,step,goL,goR]

/-- A-scanner arbitrarily many 10 tokens visits no F at any time. -/
private theorem aTenAll_noF (n : Nat) (L zs : List Bool) :
    NoF (⟨L,false,pairs n ++ zs,0⟩ : Cfg) (2*n) := by
  induction n generalizing L with
  | zero =>
      intro t ht
      omega
  | succ n ih =>
      have ht : 2*(n+1)=2+2*n := by omega
      rw [ht]
      change NoF
        (⟨L,false,[true,false]++(pairs n ++zs),0⟩ : Cfg)
        (2+2*n)
      exact appendNoF
        (⟨L,false,[true,false]++(pairs n++zs),0⟩ : Cfg)
        (⟨[false,true]++L,false,pairs n++zs,0⟩ : Cfg)
        2 (2*n)
        (aTenTwo_noF L (pairs n++zs))
        (aTenOppStep L (pairs n++zs))
        (ih ([false,true]++L))

private theorem aDoubleSeven_noF (L zs : List Bool) :
    NoF (⟨L,false,[true,true,false]++zs,0⟩ : Cfg) 7 := by
  intro t ht
  have cases :
      t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [run,step,goL,goR]

private theorem aZeroTwo_noF (L zs : List Bool) :
    NoF (⟨L,false,false::zs,0⟩ : Cfg) 2 := by
  intro t ht
  have cases : t=0 ∨ t=1 := by omega
  rcases cases with rfl | rfl
  all_goals simp [run,step,goL,goR]

private theorem cWalkTwo_noF (n : Nat) (L zs : List Bool) :
    NoF (cWalk (n+1) L zs) 2 := by
  intro t ht
  have cases : t=0 ∨ t=1 := by omega
  rcases cases with rfl | rfl
  all_goals simp [cWalk,oppairs,run,step,goL,goR]

private theorem cWalkAll_noF (n : Nat) (L zs : List Bool) :
    NoF (cWalk n L zs) (2*n) := by
  induction n generalizing zs with
  | zero =>
      intro t ht
      omega
  | succ n ih =>
      have ht : 2*(n+1)=2+2*n := by omega
      rw [ht]
      exact appendNoF
        (cWalk (n+1) L zs) (cWalk n L (true::true::zs))
        2 (2*n)
        (cWalkTwo_noF n L zs)
        (cWalk_step n L zs)
        (ih (true::true::zs))

/-- The C seven-step cleanup visits F scanning 0 once, with a guaranteed
    nonblank marked left tape. Physical blank-left F0 cannot occur. -/
theorem cSeven_noPhysical (L zs : List Bool) :
    NoPhysical
      (⟨[false,true,true,false,true,false,true]++L,true,zs,2⟩ : Cfg)
      7 := by
  intro t ht hp
  have cases :
      t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Physical,run,step,goL,goR] at hp

/-- First-physical-return safety of the entire doubly indexed A turnaround.
    It is deliberately weaker than no-F, since an internal F/0 scan with
    nonblank marked left tape is a real source event. -/
theorem a_double_zero_turn_noPhysical (v r : Nat) (L ys : List Bool) :
    NoPhysical
      (⟨L,false,BB6.Agent2AIterDoubleZero.front v r ++ ys,0⟩ : Cfg)
      (4*v+4*r+20) := by
  let U : List Bool := oppairs (v+2) ++ L
  let V : List Bool := [false,true,true] ++ U
  let R : List Bool := oppairs r ++ V
  let zs : List Bool := pairs r ++ false::ys
  let start : Cfg :=
    ⟨L,false,BB6.Agent2AIterDoubleZero.front v r ++ ys,0⟩
  let a : Cfg := ⟨U,false,[true,true,false]++zs,0⟩
  let b : Cfg := ⟨V,false,zs,0⟩
  let c : Cfg := ⟨R,false,false::ys,0⟩
  let d : Cfg := ⟨R,true,true::ys,2⟩
  let e : Cfg := ⟨V,true,List.replicate (2*r) true++true::ys,2⟩
  let f : Cfg := ⟨oppairs v++L,true,
    [true,false,true,true,true,true,true]++
      (List.replicate (2*r) true++true::ys),2⟩
  have hab : run (2*(v+2)) start = a := by
    dsimp [start,a,zs,U,BB6.Agent2AIterDoubleZero.front]
    simpa only [List.append_assoc,List.cons_append,List.nil_append]
      using (aTenOppIter (v+2) L
        ([true,true,false]++(pairs r++false::ys)))
  have hbc : run 7 a = b := by
    dsimp [a,b,U,V,zs]
    exact aDoubleSeven (v+1) L (pairs r++false::ys)
  have hcd : run (2*r) b = c := by
    dsimp [b,c,R,V,zs]
    exact aTenOppIter r
      ([false,true,true] ++ (oppairs (v+2) ++ L)) (false::ys)
  have hde : run 2 c = d := by
    dsimp [c,d]
    exact aZeroTwo R ys
  have hef : run (2*r) d = e := by
    dsimp [d,e,R]
    exact cWalk_run r V (true::ys)
  have hfg : run 7 e = f := by
    dsimp [e,f,V,U]
    have hswap :
        (⟨[false,true,true] ++ (oppairs (v+2) ++ L),true,
          List.replicate (2*r) true ++ true::ys,2⟩ : Cfg) =
        (⟨[false,true,true,false,true,false,true] ++ (oppairs v ++ L),true,
          List.replicate (2*r) true ++ true::ys,2⟩ : Cfg) :=
      congrArg (fun xs : List Bool =>
        (⟨xs,true,List.replicate (2*r) true ++ true::ys,2⟩ : Cfg))
        (opSplit v L)
    exact (congrArg (run 7) hswap).trans
      (cSeven (oppairs v++L)
        (List.replicate (2*r) true ++ true::ys))
  have hstart : NoPhysical start (2*(v+2)) := by
    dsimp [start,BB6.Agent2AIterDoubleZero.front]
    apply noF_to_noPhysical
    simpa only [List.append_assoc,List.cons_append,List.nil_append]
      using (aTenAll_noF (v+2) L
        ([true,true,false]++(pairs r++false::ys)))
  have ha : NoPhysical a 7 :=
    noF_to_noPhysical a 7
      (aDoubleSeven_noF U zs)
  have hb : NoPhysical b (2*r) :=
    noF_to_noPhysical b (2*r)
      (aTenAll_noF r V (false::ys))
  have hc : NoPhysical c 2 :=
    noF_to_noPhysical c 2
      (aZeroTwo_noF R ys)
  have hd : NoPhysical d (2*r) :=
    noF_to_noPhysical d (2*r)
      (cWalkAll_noF r V (true::ys))
  have he : NoPhysical e 7 := by
    have hswap :
        (⟨[false,true,true] ++ (oppairs (v+2) ++ L),true,
          List.replicate (2*r) true ++ true::ys,2⟩ : Cfg) =
        (⟨[false,true,true,false,true,false,true] ++ (oppairs v ++ L),true,
          List.replicate (2*r) true ++ true::ys,2⟩ : Cfg) :=
      congrArg (fun xs : List Bool =>
        (⟨xs,true,List.replicate (2*r) true ++ true::ys,2⟩ : Cfg))
        (opSplit v L)
    dsimp [e,V,U]
    rw [hswap]
    exact cSeven_noPhysical (oppairs v++L)
      (List.replicate (2*r) true ++ true::ys)
  have hf : NoPhysical f (2*v) :=
    noF_to_noPhysical f (2*v)
      (cWalkAll_noF v L
        ([true,false,true,true,true,true,true] ++
          (List.replicate (2*r) true ++ true::ys)))
  have hEF : NoPhysical e (7+2*v) :=
    appendNoPhysical e f 7 (2*v) he hfg hf
  have hDE : NoPhysical d (2*r+(7+2*v)) :=
    appendNoPhysical d e (2*r) (7+2*v) hd hef hEF
  have hCD : NoPhysical c (2+(2*r+(7+2*v))) :=
    appendNoPhysical c d 2 (2*r+(7+2*v)) hc hde hDE
  have hBC : NoPhysical b (2*r+(2+(2*r+(7+2*v)))) :=
    appendNoPhysical b c (2*r) (2+(2*r+(7+2*v)))
      hb hcd hCD
  have hAB : NoPhysical a
      (7+(2*r+(2+(2*r+(7+2*v))))) :=
    appendNoPhysical a b 7 (2*r+(2+(2*r+(7+2*v))))
      ha hbc hBC
  have hAll : NoPhysical start
      (2*(v+2)+(7+(2*r+(2+(2*r+(7+2*v)))))) :=
    appendNoPhysical start a (2*(v+2))
      (7+(2*r+(2+(2*r+(7+2*v)))))
      hstart hab hAB
  have ht : 2*(v+2)+(7+(2*r+(2+(2*r+(7+2*v))))) =
      4*v+4*r+20 := by omega
  simpa only [start,ht] using hAll

#print axioms a_double_zero_turn_noPhysical
end BB6.Agent2AIterDoubleZeroFirst
