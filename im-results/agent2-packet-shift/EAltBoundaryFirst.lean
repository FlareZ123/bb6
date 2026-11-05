import Lean.Elab.Tactic.Omega
import ATurnFamily
import EGenericTurn
import NoEarlierF

set_option maxHeartbeats 20000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace BB6.Agent2EAltBoundaryFirst
open CryptidBoundary BB6.Agent2ATurnFamily BB6.Agent2EGenericTurn
open BB6.CryptidFirstReturn

/-- True physically blank-left F-on-zero, even if the finite left list
    contains syntactically explicit zeroes. -/
def Physical (c : Cfg) : Prop :=
  c.st=5 ∧ c.h=false ∧ c.l.all (!·)=true

def NoPhysical (c : Cfg) (n : Nat) : Prop :=
  ∀ t, t<n → ¬ Physical (run t c)

private theorem noF_to_noPhysical (c : Cfg) (n : Nat)
    (h : BB6.Agent2ATurnFamily.NoF c n) :
    NoPhysical c n := by
  intro t ht hp
  exact h t ht hp.1

private theorem appendNoPhysical (c d : Cfg) (a b : Nat)
    (hc : NoPhysical c a) (he : run a c = d)
    (hd : NoPhysical d b) : NoPhysical c (a+b) := by
  intro t ht
  by_cases hs : t<a
  · exact hc t hs
  · have heq : t=a+(t-a) := by omega
    rw [heq,run_add,he]
    exact hd (t-a) (by omega)

private theorem appendNoF (c d : Cfg) (a b : Nat)
    (hc : BB6.Agent2ATurnFamily.NoF c a)
    (he : run a c = d)
    (hd : BB6.Agent2ATurnFamily.NoF d b) :
    BB6.Agent2ATurnFamily.NoF c (a+b) := by
  intro t ht
  by_cases hs : t<a
  · exact hc t hs
  · have heq : t=a+(t-a) := by omega
    rw [heq,run_add,he]
    exact hd (t-a) (by omega)

private theorem initial_noF (m q : Nat) (zs : List Bool) :
    BB6.Agent2ATurnFamily.NoF (eStart m q zs) 2 := by
  intro t ht
  have cases : t=0 ∨ t=1 := by omega
  rcases cases with rfl | rfl
  all_goals simp [eStart,run,step,goL,goR,pairs]

private theorem scan_noF (n : Nat) (L zs : List Bool) :
    BB6.Agent2ATurnFamily.NoF (scanStart n L zs) (2*n) := by
  induction n generalizing L zs with
  | zero =>
      intro t ht
      omega
  | succ n ih =>
      have ht : 2*(n+1)=2+2*n := by omega
      rw [ht]
      apply appendNoF
        (scanStart (n+1) L zs)
        (scanStart n ([false,true]++L) zs) 2 (2*n)
      · intro t hlt
        have cases : t=0 ∨ t=1 := by omega
        rcases cases with rfl | rfl
        all_goals simp [scanStart,run,step,goL,goR,pairs]
      · exact scan_step n L zs
      · exact ih ([false,true]++L) zs

private theorem cWalk_noF (n : Nat) (L zs : List Bool) :
    BB6.Agent2ATurnFamily.NoF (cWalk n L zs) (2*n) := by
  induction n generalizing zs with
  | zero =>
      intro t ht
      omega
  | succ n ih =>
      have ht : 2*(n+1)=2+2*n := by omega
      rw [ht]
      apply appendNoF
        (cWalk (n+1) L zs)
        (cWalk n L (true::true::zs)) 2 (2*n)
      · intro t hlt
        have cases : t=0 ∨ t=1 := by omega
        rcases cases with rfl | rfl
        all_goals simp [cWalk,oppairs,run,step,goL,goR]
      · exact cWalk_step n L zs
      · exact ih (true::true::zs)

private theorem cBase_noPhysical (m : Nat) (zs : List Bool) :
    NoPhysical
      (⟨pairs (m+2)++[true,true],true,zs,2⟩ : Cfg) 4 := by
  intro t ht hp
  have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  all_goals simp [Physical,run,step,goL,goR,pairs] at hp

private theorem sweepB_two_noF (m : Nat) (zs : List Bool) :
    BB6.Agent2ATurnFamily.NoF (sweepB (m+1) zs) 2 := by
  intro t ht
  have cases : t=0 ∨ t=1 := by omega
  rcases cases with rfl | rfl
  all_goals simp [sweepB,run,step,goL,goR,pairs]

private theorem sweepB_two (m : Nat) (zs : List Bool) :
    run 2 (sweepB (m+1) zs) = sweepD m ([true,true]++zs) := by
  simp [sweepB,sweepD,run,step,goL,goR,pairs]

private theorem sweepD_noF (m : Nat) (zs : List Bool) :
    BB6.Agent2ATurnFamily.NoF (sweepD m zs) (2*m+3) := by
  intro t ht
  cases t with
  | zero => simp [sweepD,run]
  | succ t =>
      have hstep : step (sweepD m zs) = step (sweepB m zs) := by
        simp [sweepD,sweepB,step,goL,goR]
      have heq : (run (t+1) (sweepD m zs)).st =
          (run (t+1) (sweepB m zs)).st := by
        simp only [run]
        rw [hstep]
      rw [heq]
      exact sweepB_firstF m zs (t+1) (by omega)

/-- For all m,q,r,Y, the E boundary consumes the arbitrary alternating
    A-turn, C scan, C base and D sweep without a physically blank-left
    F/0 return at any strictly earlier source step. -/
theorem boundary_first_physical (m q r : Nat) (ys : List Bool) :
    NoPhysical
      (eStart m q (BB6.Agent2ATurnFamily.front (r+1)++ys))
      (2*m+4*q+6*(r+1)+29) := by
  let F : List Bool := BB6.Agent2ATurnFamily.front (r+1)++ys
  let L : List Bool := pairs (m+3) ++ [true,true]
  let s : Cfg := scanStart (q+1) L F
  let a : Cfg := aStart (r+1) (oppairs (q+1)++L) ys
  let c : Cfg := cWalk (q+1) L (pairs (r+3)++ys)
  let d : Cfg := ⟨L,true,List.replicate (2*(q+1)) true ++
      (pairs (r+3)++ys),2⟩
  let b : Cfg := sweepB (m+1)
    ([false,true,true,true]++List.replicate (2*(q+1)) true ++
      (pairs (r+3)++ys))
  let fin : Cfg := sweepD m
    (BB6.Agent2EGenericTurn.outPacket q (pairs (r+3)) ys)
  have h1 : run 2 (eStart m q F) = s := by
    dsimp [s,F,L]
    exact eStart_two m q
      (BB6.Agent2ATurnFamily.front (r+1)++ys)
  have h2 : run (2*(q+1)) s = a := by
    dsimp [s,a,F]
    rw [scan_run]
    rfl
  have h3 : run (6*(r+1)+14) a =
      (⟨oppairs (q+1)++L,true,pairs (r+3)++ys,2⟩ : Cfg) := by
    dsimp [a]
    exact a_turn_all r (oppairs (q+1)++L) ys
  have h3c : run (6*(r+1)+14) a = c := by
    rw [h3]
    rfl
  have h4 : run (2*(q+1)) c = d := by
    dsimp [c,d]
    exact cWalk_run (q+1) L (pairs (r+3)++ys)
  have h5 : run 4 d = b := by
    dsimp [d,b,L]
    exact cBase (m+1) (List.replicate (2*(q+1)) true ++
      (pairs (r+3)++ys))
  have h6 : run 2 b = fin := by
    dsimp [b,fin,BB6.Agent2EGenericTurn.outPacket]
    rw [sweepB_two]
    rfl
  have h0 : NoPhysical (eStart m q F) 2 :=
    noF_to_noPhysical _ _ (initial_noF m q F)
  have hsc : NoPhysical s (2*(q+1)) :=
    noF_to_noPhysical _ _ (scan_noF (q+1) L F)
  have hat : NoPhysical a (6*(r+1)+14) :=
    noF_to_noPhysical _ _
      (a_turn_all_noF r (oppairs (q+1)++L) ys)
  have hc : NoPhysical c (2*(q+1)) :=
    noF_to_noPhysical _ _
      (cWalk_noF (q+1) L (pairs (r+3)++ys))
  have hd : NoPhysical d 4 :=
    cBase_noPhysical (m+1)
      (List.replicate (2*(q+1)) true ++ (pairs (r+3)++ys))
  have hb : NoPhysical b 2 :=
    noF_to_noPhysical _ _
      (sweepB_two_noF m
        ([false,true,true,true]++List.replicate (2*(q+1)) true ++
          (pairs (r+3)++ys)))
  have hf : NoPhysical fin (2*m+3) :=
    noF_to_noPhysical _ _
      (sweepD_noF m
        (BB6.Agent2EGenericTurn.outPacket q (pairs (r+3)) ys))
  have hjoin : NoPhysical (eStart m q F)
      (2+(2*(q+1)+((6*(r+1)+14)+
         (2*(q+1)+(4+(2+(2*m+3))))))) :=
    appendNoPhysical (eStart m q F) s 2
      (2*(q+1)+((6*(r+1)+14)+(2*(q+1)+(4+(2+(2*m+3))))))
      h0 h1
      (appendNoPhysical s a (2*(q+1))
        ((6*(r+1)+14)+(2*(q+1)+(4+(2+(2*m+3)))))
        hsc h2
        (appendNoPhysical a c (6*(r+1)+14)
          (2*(q+1)+(4+(2+(2*m+3))))
          hat h3c
          (appendNoPhysical c d (2*(q+1)) (4+(2+(2*m+3)))
            hc h4
            (appendNoPhysical d b 4 (2+(2*m+3))
              hd h5
              (appendNoPhysical b fin 2 (2*m+3) hb h6 hf)))))
  have ht : 2+(2*(q+1)+((6*(r+1)+14)+
         (2*(q+1)+(4+(2+(2*m+3)))))) =
      2*m+4*q+6*(r+1)+29 := by omega
  simpa only [ht] using hjoin


/-- A uniform source-level first-physical-return compiler. ANY finite A/0
    turn preserving the arbitrary left tape and suffix, and avoiding F until
    its C/1 endpoint, gives a strictly earlier-physical-return-free E gate.
    N, front, out, Y, the left stack size m and the scanner q are independent. -/
theorem boundary_first_from_local_noF_turn
    (m q N : Nat) (front out ys : List Bool)
    (hTurn : ∀ L : List Bool,
      run N (⟨L,false,front++ys,0⟩ : Cfg) =
        ⟨L,true,out++ys,2⟩)
    (hTurnNoF : ∀ L : List Bool,
      BB6.Agent2ATurnFamily.NoF
        (⟨L,false,front++ys,0⟩ : Cfg) N) :
    NoPhysical (eStart m q (front++ys))
      (2*m+4*q+N+15) := by
  let L : List Bool := pairs (m+3)++[true,true]
  let s : Cfg := scanStart (q+1) L (front++ys)
  let a : Cfg := ⟨oppairs (q+1)++L,false,front++ys,0⟩
  let c : Cfg := cWalk (q+1) L (out++ys)
  let d : Cfg := ⟨L,true,
    List.replicate (2*(q+1)) true ++ (out++ys),2⟩
  let b : Cfg := sweepB (m+1)
    ([false,true,true,true] ++
      List.replicate (2*(q+1)) true ++ (out++ys))
  let fin : Cfg := sweepD m (outPacket q out ys)
  have h1 : run 2 (eStart m q (front++ys)) = s := by
    dsimp [s,L]
    exact eStart_two m q (front++ys)
  have h2 : run (2*(q+1)) s = a := by
    dsimp [s,a]
    rw [scan_run]
    rfl
  have h3 : run N a = c := by
    dsimp [a,c]
    rw [hTurn]
    rfl
  have h4 : run (2*(q+1)) c = d := by
    dsimp [c,d]
    exact cWalk_run (q+1) L (out++ys)
  have h5 : run 4 d = b := by
    dsimp [d,b,L]
    exact cBase (m+1)
      (List.replicate (2*(q+1)) true ++ (out++ys))
  have h6 : run 2 b = fin := by
    dsimp [b,fin,outPacket]
    rw [sweepB_two]
    rfl
  have hn0 : NoPhysical (eStart m q (front++ys)) 2 :=
    noF_to_noPhysical _ _
      (initial_noF m q (front++ys))
  have hns : NoPhysical s (2*(q+1)) :=
    noF_to_noPhysical _ _
      (scan_noF (q+1) L (front++ys))
  have hna : NoPhysical a N :=
    noF_to_noPhysical _ _
      (hTurnNoF (oppairs (q+1)++L))
  have hnc : NoPhysical c (2*(q+1)) :=
    noF_to_noPhysical _ _
      (cWalk_noF (q+1) L (out++ys))
  have hnd : NoPhysical d 4 :=
    cBase_noPhysical (m+1)
      (List.replicate (2*(q+1)) true ++ (out++ys))
  have hnb : NoPhysical b 2 :=
    noF_to_noPhysical _ _
      (sweepB_two_noF m
        ([false,true,true,true] ++
          List.replicate (2*(q+1)) true ++ (out++ys)))
  have hnf : NoPhysical fin (2*m+3) :=
    noF_to_noPhysical _ _
      (sweepD_noF m (outPacket q out ys))
  have hjoined : NoPhysical (eStart m q (front++ys))
      (2+(2*(q+1)+(N+(2*(q+1)+(4+(2+(2*m+3))))))) :=
    appendNoPhysical (eStart m q (front++ys)) s 2
      (2*(q+1)+(N+(2*(q+1)+(4+(2+(2*m+3))))))
      hn0 h1
      (appendNoPhysical s a (2*(q+1))
        (N+(2*(q+1)+(4+(2+(2*m+3)))))
        hns h2
        (appendNoPhysical a c N
          (2*(q+1)+(4+(2+(2*m+3))))
          hna h3
          (appendNoPhysical c d (2*(q+1)) (4+(2+(2*m+3)))
            hnc h4
            (appendNoPhysical d b 4 (2+(2*m+3))
              hnd h5
              (appendNoPhysical b fin 2 (2*m+3)
                hnb h6 hnf)))))
  have ht : 2+(2*(q+1)+(N+(2*(q+1)+(4+(2+(2*m+3)))))) =
      2*m+4*q+N+15 := by omega
  simpa only [ht] using hjoined

/-- Stronger physical-safety compiler: a local A turn may transiently
    visit F while its left tape retains a nonzero marker. Only physically
    blank-left F/0 visits are excluded. -/
theorem boundary_first_from_local_noPhysical_turn
    (m q N : Nat) (front out ys : List Bool)
    (hTurn : ∀ L : List Bool,
      run N (⟨L,false,front++ys,0⟩ : Cfg) =
        ⟨L,true,out++ys,2⟩)
    (hTurnNoPhysical : ∀ L : List Bool,
      NoPhysical
        (⟨L,false,front++ys,0⟩ : Cfg) N) :
    NoPhysical (eStart m q (front++ys))
      (2*m+4*q+N+15) := by
  let L : List Bool := pairs (m+3)++[true,true]
  let s : Cfg := scanStart (q+1) L (front++ys)
  let a : Cfg := ⟨oppairs (q+1)++L,false,front++ys,0⟩
  let c : Cfg := cWalk (q+1) L (out++ys)
  let d : Cfg := ⟨L,true,
    List.replicate (2*(q+1)) true ++ (out++ys),2⟩
  let b : Cfg := sweepB (m+1)
    ([false,true,true,true] ++
      List.replicate (2*(q+1)) true ++ (out++ys))
  let fin : Cfg := sweepD m (outPacket q out ys)
  have h1 : run 2 (eStart m q (front++ys)) = s := by
    dsimp [s,L]
    exact eStart_two m q (front++ys)
  have h2 : run (2*(q+1)) s = a := by
    dsimp [s,a]
    rw [scan_run]
    rfl
  have h3 : run N a = c := by
    dsimp [a,c]
    rw [hTurn]
    rfl
  have h4 : run (2*(q+1)) c = d := by
    dsimp [c,d]
    exact cWalk_run (q+1) L (out++ys)
  have h5 : run 4 d = b := by
    dsimp [d,b,L]
    exact cBase (m+1)
      (List.replicate (2*(q+1)) true ++ (out++ys))
  have h6 : run 2 b = fin := by
    dsimp [b,fin,outPacket]
    rw [sweepB_two]
    rfl
  have hn0 : NoPhysical (eStart m q (front++ys)) 2 :=
    noF_to_noPhysical _ _
      (initial_noF m q (front++ys))
  have hns : NoPhysical s (2*(q+1)) :=
    noF_to_noPhysical _ _
      (scan_noF (q+1) L (front++ys))
  have hna : NoPhysical a N :=
    hTurnNoPhysical (oppairs (q+1)++L)
  have hnc : NoPhysical c (2*(q+1)) :=
    noF_to_noPhysical _ _
      (cWalk_noF (q+1) L (out++ys))
  have hnd : NoPhysical d 4 :=
    cBase_noPhysical (m+1)
      (List.replicate (2*(q+1)) true ++ (out++ys))
  have hnb : NoPhysical b 2 :=
    noF_to_noPhysical _ _
      (sweepB_two_noF m
        ([false,true,true,true] ++
          List.replicate (2*(q+1)) true ++ (out++ys)))
  have hnf : NoPhysical fin (2*m+3) :=
    noF_to_noPhysical _ _
      (sweepD_noF m (outPacket q out ys))
  have hjoined : NoPhysical (eStart m q (front++ys))
      (2+(2*(q+1)+(N+(2*(q+1)+(4+(2+(2*m+3))))))) :=
    appendNoPhysical (eStart m q (front++ys)) s 2
      (2*(q+1)+(N+(2*(q+1)+(4+(2+(2*m+3))))))
      hn0 h1
      (appendNoPhysical s a (2*(q+1))
        (N+(2*(q+1)+(4+(2+(2*m+3)))))
        hns h2
        (appendNoPhysical a c N
          (2*(q+1)+(4+(2+(2*m+3))))
          hna h3
          (appendNoPhysical c d (2*(q+1)) (4+(2+(2*m+3)))
            hnc h4
            (appendNoPhysical d b 4 (2+(2*m+3))
              hnd h5
              (appendNoPhysical b fin 2 (2*m+3)
                hnb h6 hnf)))))
  have ht : 2+(2*(q+1)+(N+(2*(q+1)+(4+(2+(2*m+3)))))) =
      2*m+4*q+N+15 := by omega
  simpa only [ht] using hjoined

#print axioms boundary_first_from_local_noPhysical_turn

#print axioms boundary_first_from_local_noF_turn

#print axioms boundary_first_physical
end BB6.Agent2EAltBoundaryFirst
