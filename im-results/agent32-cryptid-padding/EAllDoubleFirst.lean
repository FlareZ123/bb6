import Lean.Elab.Tactic.Omega
import EAllDouble
import PrefixENoFSource
import NoEarlierF

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace BB6.Agent32EDoubleFirst
open CryptidBoundary
open BB6.Agent32EAll
open BB6.Agent32EZero
open BB6.Agent35
open BB6.CryptidPrefixFirstReturn
open BB6.CryptidFirstReturn

/-- A genuine physical return has no marked cell to the left of its head;
    syntactic left-list emptiness is unnecessarily restrictive. -/
def PhysicalF0 (c : Cfg) : Prop :=
  c.st = 5 ∧ c.h = false ∧ (c.l.any id) = false

def NoPhysical (c : Cfg) (n : Nat) : Prop :=
  ∀ t, t<n → ¬ PhysicalF0 (run t c)

private theorem noF_to_noPhysical (c : Cfg) (n : Nat)
    (h : NoF c n) : NoPhysical c n := by
  intro t ht hp
  exact h t ht hp.1

private theorem append_noPhysical (c d : Cfg) (a b : Nat)
    (hc : NoPhysical c a) (he : run a c = d)
    (hd : NoPhysical d b) : NoPhysical c (a+b) := by
  intro t ht
  by_cases hs : t<a
  · exact hc t hs
  · have htime : t=a+(t-a) := by omega
    rw [htime,run_add,he]
    exact hd (t-a) (by omega)

private theorem scanner_noF (n : Nat) (L ys : List Bool) :
    NoF (scanStart n L ys) (2*n) := by
  induction n generalizing L ys with
  | zero =>
      intro t ht
      omega
  | succ n ih =>
      have ht : 2*(n+1)=2+2*n := by omega
      rw [ht]
      exact BB6.Agent32EDoubleFirst.append_noPhysical
         (scanStart (n+1) L ys)
         (scanStart n ([false,true]++L) ys)
         2 (2*n)
         (by
           intro t ht hp
           have hc : t=0 ∨ t=1 := by omega
           rcases hc with rfl | rfl
           all_goals simp [PhysicalF0,scanStart,run,step,goL,goR,pairs] at hp)
         (scan_step n L ys)
         (noF_to_noPhysical _ _ (ih ([false,true]++L) ys))

/-- The forward scan is handled in the actual physical-return predicate. -/
private theorem scanner_noPhysical (n : Nat) (L ys : List Bool) :
    NoPhysical (scanStart n L ys) (2*n) := by
  induction n generalizing L ys with
  | zero => intro t ht; omega
  | succ n ih =>
      have ht : 2*(n+1)=2+2*n := by omega
      rw [ht]
      exact append_noPhysical
        (scanStart (n+1) L ys)
        (scanStart n ([false,true]++L) ys)
        2 (2*n)
        (by
          intro t ht hp
          have hc : t=0 ∨ t=1 := by omega
          rcases hc with rfl | rfl
          all_goals simp [PhysicalF0,scanStart,run,step,goL,goR,pairs] at hp)
        (scan_step n L ys)
        (ih ([false,true]++L) ys)

private theorem walk_noPhysical (n : Nat) (L ys : List Bool) :
    NoPhysical (cWalk n L ys) (2*n) := by
  induction n generalizing ys with
  | zero => intro t ht; omega
  | succ n ih =>
      have ht : 2*(n+1)=2+2*n := by omega
      rw [ht]
      exact append_noPhysical
        (cWalk (n+1) L ys) (cWalk n L (true::true::ys))
        2 (2*n)
        (by
          intro t ht hp
          have hc : t=0 ∨ t=1 := by omega
          rcases hc with rfl | rfl
          all_goals simp [PhysicalF0,cWalk,run,step,goL,goR,oppairs] at hp)
        (cWalk_step n L ys)
        (ih (true::true::ys))

/-- The q=0 E-1100 sector has two interior F visits but neither has blank left. -/
private theorem eZeroFront_noPhysical (m : Nat) (ys : List Bool) :
    NoPhysical (eZero m ys) 60 := by
  intro t ht hp
  have hc : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 ∨ t = 15 ∨ t = 16 ∨ t = 17 ∨ t = 18 ∨ t = 19 ∨ t = 20 ∨ t = 21 ∨ t = 22 ∨ t = 23 ∨ t = 24 ∨ t = 25 ∨ t = 26 ∨ t = 27 ∨ t = 28 ∨ t = 29 ∨ t = 30 ∨ t = 31 ∨ t = 32 ∨ t = 33 ∨ t = 34 ∨ t = 35 ∨ t = 36 ∨ t = 37 ∨ t = 38 ∨ t = 39 ∨ t = 40 ∨ t = 41 ∨ t = 42 ∨ t = 43 ∨ t = 44 ∨ t = 45 ∨ t = 46 ∨ t = 47 ∨ t = 48 ∨ t = 49 ∨ t = 50 ∨ t = 51 ∨ t = 52 ∨ t = 53 ∨ t = 54 ∨ t = 55 ∨ t = 56 ∨ t = 57 ∨ t = 58 ∨ t = 59 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [PhysicalF0,eZero,run,step,goL,goR,pairs] at hp

/-- The q=1 E-1100 boundary has interior F visits with marked left tape. -/
private theorem eDoubleBase_noPhysical (m : Nat) (ys : List Bool) :
    NoPhysical (eDouble m 0 ys) 26 := by
  intro t ht hp
  have hc : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 ∨ t = 15 ∨ t = 16 ∨ t = 17 ∨ t = 18 ∨ t = 19 ∨ t = 20 ∨ t = 21 ∨ t = 22 ∨ t = 23 ∨ t = 24 ∨ t = 25 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [PhysicalF0,eDouble,run,step,goL,goR,pairs] at hp

private theorem eDoubleStart_noPhysical (m q : Nat) (ys : List Bool) :
    NoPhysical (eDouble m q ys) 2 := by
  intro t ht hp
  have hc : t=0 ∨ t=1 := by omega
  rcases hc with rfl | rfl
  all_goals simp [PhysicalF0,eDouble,run,step,goL,goR,pairs] at hp

/-- Sixteen A-turn steps, including its interior F/0 with marked left tape. -/
private theorem aFront16_noPhysical (q : Nat) (L ys : List Bool) :
    NoPhysical
      (⟨oppairs (q+3) ++ L,false,[true,true,false,false] ++ ys,0⟩ : Cfg)
      16 := by
  intro t ht hp
  have hc : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 ∨ t = 15 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [PhysicalF0,run,step,goL,goR,oppairs] at hp

/-- Four final C-to-B steps after reverse walking retain marks left at F. -/
private theorem cTail4_noPhysical (m q : Nat) (ys : List Bool) :
    NoPhysical
      (⟨pairs (m+2) ++ [true,true], true,
        List.replicate (2*(q+1)) true ++
          ([true,false] ++ List.replicate 6 true ++ ys),2⟩ : Cfg)
      4 := by
  intro t ht hp
  have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  all_goals simp [PhysicalF0,run,step,goL,goR,pairs] at hp

/-- Source-preserving all-parameter guard for E boundary with >=2 pairs. -/
private theorem eDoubleFrontSucc_noPhysical (m q : Nat)
    (ys : List Bool) :
    NoPhysical (eDouble m (q+1) ys) (4*(q+2)+22) := by
  let L : List Bool := pairs (m+2) ++ [true,true]
  let scan : Cfg := scanStart (q+3) L ([true,true,false,false] ++ ys)
  let a : Cfg := ⟨oppairs (q+3) ++ L,false,[true,true,false,false] ++ ys,0⟩
  let walk : Cfg := cWalk (q+1) L
    ([true,false] ++ List.replicate 6 true ++ ys)
  let c : Cfg := ⟨L,true,List.replicate (2*(q+1)) true ++
    ([true,false] ++ List.replicate 6 true ++ ys),2⟩
  have he0 : run 2 (eDouble m (q+1) ys) = scan := by
    dsimp [scan,L]
    simpa only [show (q+1)+2=q+3 by omega] using
      (eDouble_two m (q+1) ys)
  have he1 : run (2*(q+3)) scan = a := by
    dsimp [scan,a]
    rw [scan_run]
    rfl
  have he2 : run 16 a = walk := by
    change run 16
      (⟨oppairs (q+3) ++ L,false,[true,true,false,false] ++ ys,0⟩ : Cfg) = _
    rw [aFront16]
    rfl
  have he3 : run (2*(q+1)) walk = c := by
    dsimp [walk,c]
    rw [cWalk_run]
  have h0 : NoPhysical (eDouble m (q+1) ys) 2 :=
    eDoubleStart_noPhysical m (q+1) ys
  have h1 : NoPhysical scan (2*(q+3)) :=
    scanner_noPhysical (q+3) L ([true,true,false,false] ++ ys)
  have h2 : NoPhysical a 16 :=
    aFront16_noPhysical q L ys
  have h3 : NoPhysical walk (2*(q+1)) :=
    walk_noPhysical (q+1) L
      ([true,false] ++ List.replicate 6 true ++ ys)
  have h4 : NoPhysical c 4 := by
    dsimp [c,L]
    exact cTail4_noPhysical m q ys
  have h : NoPhysical (eDouble m (q+1) ys)
      (2+(2*(q+3)+(16+(2*(q+1)+4)))) :=
    append_noPhysical _ scan 2 (2*(q+3)+(16+(2*(q+1)+4)))
      h0 he0
      (append_noPhysical scan a (2*(q+3)) (16+(2*(q+1)+4))
        h1 he1
        (append_noPhysical a walk 16 (2*(q+1)+4)
          h2 he2
          (append_noPhysical walk c (2*(q+1)) 4
            h3 he3 h4)))
  have ht : 2+(2*(q+3)+(16+(2*(q+1)+4))) = 4*(q+2)+22 := by omega
  simpa only [ht] using h

/-- All E-(10)^(q+1)1100 boundaries avoid a physical F/0 return until the
    final certified B sweep, including the distinct one-pair base case. -/
theorem eDouble_firstPhysical (m q : Nat) (ys : List Bool) :
    NoPhysical (eDouble m q ys) (2*m+4*(q+1)+25) := by
  have hfront : NoPhysical (eDouble m q ys) (4*(q+1)+22) := by
    cases q with
    | zero =>
        simpa using eDoubleBase_noPhysical m ys
    | succ q =>
        simpa using eDoubleFrontSucc_noPhysical m q ys
  have hB : NoPhysical
      (sweepB m (false :: List.replicate (2*(q+1)+2) true ++
        (false :: List.replicate 6 true ++ ys))) (2*m+3) :=
    noF_to_noPhysical _ _
      (fun t ht => sweepB_firstF m _ t ht)
  have ht : 2*m+4*(q+1)+25 = (4*(q+1)+22)+(2*m+3) := by omega
  rw [ht]
  exact append_noPhysical _ _ (4*(q+1)+22) (2*m+3)
    hfront (eDouble_front m q ys) hB

/-- The separate zero-pair E1100 branch also has a strict first return. -/
theorem eZero_firstPhysical (m : Nat) (ys : List Bool) :
    NoPhysical (eZero m ys) (2*m+63) := by
  have hB : NoPhysical (sweepB m (packetZero ++ ys)) (2*m+3) :=
    noF_to_noPhysical _ _
      (fun t ht => sweepB_firstF m _ t ht)
  have ht : 2*m+63=60+(2*m+3) := by omega
  rw [ht]
  exact append_noPhysical _ _ 60 (2*m+3)
    (eZeroFront_noPhysical m ys) (eZero_front m ys) hB

/-- For EVERY E-(10)^q1100 input and arbitrary right suffix, the designated
    exact original-machine endpoint is its first physical F/0 return.
    Blank-left means no 1 anywhere to the left, including in padded lists. -/
theorem all_e_double_first_return (k q : Nat) (ys : List Bool) :
    run (duration k q) (start k q ys) = output k q ys ∧
    ∀ t, 0<t → t<duration k q →
      ¬ PhysicalF0 (run t (start k q ys)) := by
  constructor
  · exact all_e_double k q ys
  · intro t hpos ht hp
    by_cases hearly : t<12*k*k+41*k+33
    · exact
        (prefixE_positive_noF k (pairs q ++
            ([true,true,false,false] ++ ys)) t hpos hearly) hp.1
    · cases q with
      | zero =>
          have hprefix :
              run (12*k*k+41*k+33) (start k 0 ys) =
              eZero (4*k) ys := by
            dsimp [start]
            rw [prefix_E]
            rfl
          have htime :
              t=(12*k*k+41*k+33)+(t-(12*k*k+41*k+33)) := by omega
          have hrest : t-(12*k*k+41*k+33)<2*(4*k)+63 := by
            dsimp [duration] at ht
            omega
          rw [htime,run_add] at hp
          rw [hprefix] at hp
          exact (eZero_firstPhysical (4*k) ys)
            (t-(12*k*k+41*k+33)) hrest hp
      | succ q =>
          have hprefix :
              run (12*k*k+41*k+33) (start k (q+1) ys) =
              eDouble (4*k+1) q ys := by
            dsimp [start]
            rw [prefix_E]
            rfl
          have htime :
              t=(12*k*k+41*k+33)+(t-(12*k*k+41*k+33)) := by omega
          have hrest : t-(12*k*k+41*k+33)<
              2*(4*k+1)+4*(q+1)+25 := by
            dsimp [duration] at ht
            omega
          rw [htime,run_add] at hp
          rw [hprefix] at hp
          exact (eDouble_firstPhysical (4*k+1) q ys)
            (t-(12*k*k+41*k+33)) hrest hp

#print axioms eDouble_firstPhysical
#print axioms eZero_firstPhysical
#print axioms all_e_double_first_return

end BB6.Agent32EDoubleFirst
