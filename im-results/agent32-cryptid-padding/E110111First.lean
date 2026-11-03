import Lean.Elab.Tactic.Omega
import E110111Pairs
import PrefixENoFSource
import NoEarlierF

set_option maxHeartbeats 20000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

namespace BB6.Agent32E110111First
open CryptidBoundary
open BB6.Agent37E110111
open BB6.CryptidPrefixFirstReturn
open BB6.CryptidFirstReturn

/-- Exact no-F interval in the unmodified six-state machine. -/
private theorem append_noF (c d : Cfg) (a b : Nat)
    (hc : NoF c a) (he : run a c = d) (hd : NoF d b) :
    NoF c (a+b) := by
  intro t ht
  by_cases hs : t < a
  · exact hc t hs
  · have htime : t = a+(t-a) := by omega
    rw [htime,run_add,he]
    exact hd (t-a) (by omega)

/-- F/0 section requires a physically empty left half-tape. -/
private def PhysicalF0 (c : Cfg) : Prop :=
  c.st = 5 ∧ c.h = false ∧ (c.l.any id) = false

private def NoPhysical (c : Cfg) (n : Nat) : Prop :=
  ∀ t, t<n → ¬ PhysicalF0 (run t c)

private theorem noF_to_NoPhysical (c : Cfg) (n : Nat)
    (h : NoF c n) : NoPhysical c n := by
  intro t ht hp
  exact h t ht hp.1

private theorem append_noPhysical (c d : Cfg) (a b : Nat)
    (hc : NoPhysical c a) (he : run a c = d)
    (hd : NoPhysical d b) :
    NoPhysical c (a+b) := by
  intro t ht
  by_cases hs : t < a
  · exact hc t hs
  · have htime : t = a+(t-a) := by omega
    rw [htime,run_add,he]
    exact hd (t-a) (by omega)

private theorem scanner_noF (n : Nat) (L ys : List Bool) :
    NoF (scanStart n L ys) (2*n) := by
  induction n generalizing L ys with
  | zero =>
      intro t ht
      omega
  | succ n ih =>
      have ht : 2*(n+1) = 2+2*n := by omega
      rw [ht]
      exact append_noF
        (scanStart (n+1) L ys)
        (scanStart n ([false,true]++L) ys)
        2 (2*n)
        (by
          intro t ht
          have hc : t=0 ∨ t=1 := by omega
          rcases hc with rfl | rfl
          all_goals simp [scanStart,run,step,goL,goR,pairs])
        (scan_step n L ys)
        (ih ([false,true]++L) ys)

private theorem eStart_noF (m q : Nat) (ys : List Bool) :
    NoF (eLong m q ys) 2 := by
  intro t ht
  have hc : t=0 ∨ t=1 := by omega
  rcases hc with rfl | rfl
  all_goals simp [eLong,run,step,goL,goR,pairs]

private theorem eScan_noF (m q : Nat) (ys : List Bool) :
    NoF (eLong m q ys) (2*q+4) := by
  have ht : 2*q+4 = 2+2*(q+1) := by omega
  rw [ht]
  exact append_noF (eLong m q ys)
    (scanStart (q+1) (pairs (m+3) ++ [true,true])
      ([true,true,false,true,true,true] ++ ys))
    2 (2*(q+1))
    (eStart_noF m q ys) (eLong_two m q ys)
    (scanner_noF (q+1) (pairs (m+3) ++ [true,true])
      ([true,true,false,true,true,true] ++ ys))

/-- The special 110111 turn visits no state F at any earlier time. -/
private theorem turn20_noF (L ys : List Bool) :
    NoF (⟨L,false,[true,true,false,true,true,true] ++ ys,0⟩ : Cfg) 20 := by
  intro t ht
  have hc : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 ∨ t = 15 ∨ t = 16 ∨ t = 17 ∨ t = 18 ∨ t = 19 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [run,step,goL,goR]

private theorem walk2_noF (n : Nat) (L ys : List Bool) :
    NoF (cWalk (n+1) L ys) 2 := by
  intro t ht
  have hc : t=0 ∨ t=1 := by omega
  rcases hc with rfl | rfl
  all_goals simp [cWalk,run,step,goL,goR,oppairs]

private theorem walk_noF (n : Nat) (L ys : List Bool) :
    NoF (cWalk n L ys) (2*n) := by
  induction n generalizing ys with
  | zero =>
      intro t ht
      omega
  | succ n ih =>
      have ht : 2*(n+1) = 2+2*n := by omega
      rw [ht]
      exact append_noF
        (cWalk (n+1) L ys)
        (cWalk n L (true::true::ys))
        2 (2*n)
        (walk2_noF n L ys) (cWalk_step n L ys)
        (ih (true::true::ys))

/-- No visit to F before the six-step C-to-D join. -/
private theorem tail6_noPhysical (m q : Nat) (ys : List Bool) :
    NoPhysical
      (⟨pairs ((m+1)+2) ++ [true,true], true,
        List.replicate (2*(q+1)) true ++
          ([true,false,true,false,true,false] ++ ys),2⟩ : Cfg) 6 := by
  intro t ht hp
  have hc : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [PhysicalF0,run,step,goL,goR,pairs] at hp

/-- The A/C turnaround excludes physical blank-left F/0 returns. -/
private theorem aLong_noPhysical (m q : Nat) (ys : List Bool) :
    NoPhysical
      (⟨oppairs (q+1) ++ (pairs (m+3) ++ [true,true]),false,
        [true,true,false,true,true,true] ++ ys,0⟩ : Cfg)
      (2*q+28) := by
  let L := pairs (m+3) ++ [true,true]
  let s : Cfg := ⟨oppairs (q+1) ++ L, false,
    [true,true,false,true,true,true] ++ ys,0⟩
  let w : Cfg := cWalk (q+1) L ([true,false,true,false,true,false] ++ ys)
  let d : Cfg := ⟨L,true,
    List.replicate (2*(q+1)) true ++
      ([true,false,true,false,true,false] ++ ys),2⟩
  have hturn : run 20 s = w := by
    change run 20
      (⟨oppairs (q+1) ++ L,false,[true,true,false,true,true,true] ++ ys,0⟩ : Cfg) = _
    rw [a110111_turn20]
    rfl
  have hwalk : run (2*(q+1)) w = d := by
    dsimp [w,d]
    rw [cWalk_run]
  have htail : run 6 d = sweepD m (longPacket q ys) := by
    dsimp [d,L]
    simpa only [List.cons_append, List.nil_append, show (m+1)+2=m+3 by omega] using cTailSix m q ys
  have h1 : NoPhysical s 20 := by
    apply noF_to_NoPhysical
    dsimp [s,L]
    exact turn20_noF (oppairs (q+1) ++ (pairs (m+3) ++ [true,true])) ys
  have h2 : NoPhysical w (2*(q+1)) :=
    noF_to_NoPhysical _ _ (walk_noF (q+1) L
      ([true,false,true,false,true,false] ++ ys))
  have h3 : NoPhysical d 6 := by
    dsimp [d,L]
    simpa only [List.cons_append, List.nil_append, show (m+1)+2=m+3 by omega]
      using tail6_noPhysical m q ys
  have h : NoPhysical s (20+(2*(q+1)+6)) :=
    append_noPhysical s w 20 (2*(q+1)+6) h1 hturn
      (append_noPhysical w d (2*(q+1)) 6 h2 hwalk h3)
  have ht : 20+(2*(q+1)+6) = 2*q+28 := by omega
  simpa only [s,L,ht] using h

private theorem eFront_noPhysical (m q : Nat) (ys : List Bool) :
    NoPhysical (eLong m q ys) (4*q+32) := by
  have ht : 4*q+32=(2*q+4)+(2*q+28) := by omega
  rw [ht]
  exact append_noPhysical
    (eLong m q ys)
    (⟨oppairs (q+1) ++ (pairs (m+3) ++ [true,true]),false,
      [true,true,false,true,true,true] ++ ys,0⟩ : Cfg)
    (2*q+4) (2*q+28)
    (noF_to_NoPhysical _ _ (eScan_noF m q ys)) (eLong_scan m q ys)
    (aLong_noPhysical m q ys)

/-- The original D sweep and B sweep agree after one primitive step. -/
private theorem sweepD_firstF (m : Nat) (ys : List Bool)
    (t : Nat) (ht : t<2*m+3) :
    (run t (sweepD m ys)).st ≠ 5 := by
  by_cases hz : t=0
  · subst t
    simp [sweepD,run]
  · have ht1 : t=1+(t-1) := by omega
    have hstep : step (sweepD m ys) = step (sweepB m ys) := by
      simp [sweepD,sweepB,step,goL]
    have heq : run t (sweepD m ys) = run t (sweepB m ys) := by
      rw [ht1]
      simp only [run_add]
      simpa only [run] using
        congrArg (run (t-1)) hstep
    rw [heq]
    exact sweepB_firstF m ys t ht

/-- Strict first state-F arrival of the entire E(10)^q110111 boundary. -/
theorem eLong_firstPhysical (m q : Nat) (ys : List Bool) :
    NoPhysical (eLong m q ys) (2*m+4*q+35) := by
  have ht : 2*m+4*q+35=(4*q+32)+(2*m+3) := by omega
  rw [ht]
  exact append_noPhysical (eLong m q ys) (sweepD m (longPacket q ys))
    (4*q+32) (2*m+3)
    (eFront_noPhysical m q ys) (eLong_front m q ys)
    (noF_to_NoPhysical _ _
      (fun t ht => sweepD_firstF m (longPacket q ys) t ht))

/-- Original D-start machine, exact first positive physical F/0 return
    from the full all-k,all-q,all-suffix E(10)^q110111 cylinder.
    All previously source-certified endpoints retain their raw step counts. -/
theorem full_E_110111_first_return (k q : Nat) (ys : List Bool) :
    let duration := 12*k*k+49*k+68+4*q
    let initial := init (List.replicate (3*k+2) true ++
      false :: (pairs q ++ ([true,true,false,true,true,true] ++ ys)))
    run duration initial =
      ⟨[],false,List.replicate (8*k+3) true ++ longPacket q ys,5⟩ ∧
    ∀ t, 0<t → t<duration →
      ¬ ((run t initial).st = 5 ∧
        (run t initial).h = false ∧
        (run t initial).l.any id = false) := by
  dsimp
  constructor
  · exact full_E_110111_pairs_raw k q ys
  · intro t hpos hlt hphys
    by_cases hp : t < 12*k*k+41*k+33
    · exact
        (prefixE_positive_noF k (pairs q ++
            ([true,true,false,true,true,true] ++ ys))
          t hpos hp) hphys.1
    · have hprefix :
        run (12*k*k+41*k+33)
          (init (List.replicate (3*k+2) true ++
            false :: (pairs q ++ ([true,true,false,true,true,true] ++ ys)))) =
          eLong (4*k) q ys := by
        rw [prefix_E]
        rfl
      have htime : t=(12*k*k+41*k+33)+(t-(12*k*k+41*k+33)) := by omega
      have hrest : t-(12*k*k+41*k+33) <
          2*(4*k)+4*q+35 := by omega
      rw [htime,run_add] at hphys
      simp only [List.cons_append, List.nil_append] at hprefix
      rw [hprefix] at hphys
      exact (eLong_firstPhysical (4*k) q ys)
        (t-(12*k*k+41*k+33)) hrest hphys

#print axioms eLong_firstPhysical
#print axioms full_E_110111_first_return
end BB6.Agent32E110111First
