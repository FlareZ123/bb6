import Lean.Elab.Tactic.Omega
import PrefixNoF
import CryptidTriplePairs

/-!
  Intended for the unchanged original CryptidBoundary source modules.
  Exact source imports and compiler verification remain mandatory.
  All source-specific finite-step lemmas below are proved, not assumed.
-/
namespace BB6.CryptidETriplePairsFirstReturn
open CryptidBoundary
open BB6.CryptidPrefixFirstReturn
open BB6.CryptidFirstReturn
open BB6.CryptidE111FirstReturn

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

private theorem append_noF (c d : Cfg) (a b : Nat)
    (hc : NoF c a) (he : run a c = d) (hd : NoF d b) :
    NoF c (a+b) := by
  intro t ht
  by_cases hsmall : t < a
  · exact hc t hsmall
  · have heq : t = a+(t-a) := by omega
    rw [heq, run_add, he]
    exact hd (t-a) (by omega)

private theorem scan_noF (n : Nat) (L ys : List Bool) :
    NoF (scanStart n L ys) (2*n) := by
  induction n generalizing L ys with
  | zero =>
    intro t ht
    omega
  | succ n ih =>
    have ht : 2*(n+1) = 2+2*n := by omega
    rw [ht]
    apply append_noF (scanStart (n+1) L ys)
      (scanStart n ([false,true]++L) ys) 2 (2*n)
    · intro t hlt
      have hcases : t=0 ∨ t=1 := by omega
      rcases hcases with rfl | rfl
      all_goals simp [scanStart,run,step,goL,goR,pairs]
    · exact scan_step n L ys
    · exact ih ([false,true]++L) ys

private theorem start_noF (m q : Nat) (ys : List Bool) :
    NoF (eTriplePairs m q ys) 2 := by
  intro t ht
  have hcases : t=0 ∨ t=1 := by omega
  rcases hcases with rfl | rfl
  all_goals simp [eTriplePairs,run,step,goL,goR,pairs]

private theorem aTriple8_noF (L ys : List Bool) :
    NoF (⟨L,false,[true,true,true]++ys,0⟩ : Cfg) 8 := by
  intro t ht
  have hcases :
    t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    cases L with
    | nil => simp [run,step,goL,goR]
    | cons v L => cases v <;> simp [run,step,goL,goR]

private theorem bPop_four_noF (q : Nat) (L ys : List Bool) :
    NoF (bPop (q+1) L ys) 4 := by
  intro t ht
  have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  all_goals simp [bPop,oppairs,run,step,goL,goR]

private theorem bPop_noF (q : Nat) (L ys : List Bool) :
    NoF (bPop q L ys) (4*q) := by
  induction q generalizing ys with
  | zero =>
    intro t ht
    omega
  | succ q ih =>
    have ht : 4*(q+1) = 4+4*q := by omega
    rw [ht]
    exact append_noF (bPop (q+1) L ys)
      (bPop q L (false::true::ys)) 4 (4*q)
      (bPop_four_noF q L ys) (bPop_step q L ys)
      (ih (false::true::ys))

/-- The entire source E(10)^q111 boundary traversal excludes state F,
    including during the scanner, eight-step turn and 4q pair-popping sweep. -/
theorem eTriplePairs_front_noF (m q : Nat) (ys : List Bool) :
    NoF (eTriplePairs m q ys) (6*q+16) := by
  let L := pairs m ++ [true,true]
  let scan : Cfg := scanStart (q+1) L ([true,true,true]++ys)
  let a8 : Cfg := ⟨oppairs (q+1) ++ L,false,[true,true,true]++ys,0⟩
  let pop : Cfg := bPop (q+1) L ([false,true,false]++ys)
  let finish : Cfg := sweepB m (oppairs (q+2)++false::ys)
  have h1 : run 2 (eTriplePairs m q ys) = scan := by
    simpa [scan,L] using eTriplePairs_two m q ys
  have h2 : run (2*(q+1)) scan = a8 := by
    dsimp [scan,a8]
    rw [scan_run]
  have h3 : run 8 a8 = pop := by
    change run 8 (⟨oppairs (q+1)++L,false,[true,true,true]++ys,0⟩ : Cfg) = _
    rw [aTriple8]
    rfl
  have h4 : run (4*(q+1)) pop = finish := by
    dsimp [pop,finish,L]
    rw [bPop_run]
    have hp : oppairs (q+1) ++ ([false,true,false] ++ ys) =
        oppairs (q+2) ++ false::ys := by
      calc
        _ = (oppairs (q+1) ++ [false,true]) ++ false::ys := by
          simp [List.append_assoc]
        _ = ([false,true] ++ oppairs (q+1)) ++ false::ys := by
          rw [oppairs_comm_one]
        _ = _ := by simp [oppairs]
    exact congrArg (fun z : List Bool => sweepB m z) hp
  have hf : NoF (eTriplePairs m q ys)
      (2+(2*(q+1)+(8+4*(q+1)))) := by
    apply append_noF (eTriplePairs m q ys) scan
      2 (2*(q+1)+(8+4*(q+1))) (start_noF m q ys) h1
    apply append_noF scan a8 (2*(q+1)) (8+4*(q+1))
      (scan_noF (q+1) L ([true,true,true]++ys)) h2
    exact append_noF a8 pop 8 (4*(q+1))
      (aTriple8_noF (oppairs (q+1)++L) ys) h3
      (bPop_noF (q+1) L ([false,true,false]++ys))
  have hn : 2+(2*(q+1)+(8+4*(q+1)))=6*q+16 := by omega
  simpa only [hn] using hf

/-- The full E(10)^q111 boundary returns at its first state-F encounter. -/
theorem eTriplePairs_firstF (m q : Nat) (ys : List Bool) :
    run (2*m+6*q+19) (eTriplePairs m q ys) =
      ⟨[],false,List.replicate (2*m+3) true ++
        (oppairs (q+2) ++ false::ys),5⟩ ∧
    NoF (eTriplePairs m q ys) (2*m+6*q+19) := by
  constructor
  · exact eTriplePairs_run m q ys
  · have ht : 2*m+6*q+19=(6*q+16)+(2*m+3) := by omega
    rw [ht]
    exact append_noF (eTriplePairs m q ys)
      (sweepB m (oppairs (q+2)++false::ys)) (6*q+16) (2*m+3)
      (eTriplePairs_front_noF m q ys) (eTriplePairs_front m q ys)
      (fun t ht => sweepB_firstF m (oppairs (q+2)++false::ys) t ht)

/-- Every original I_(3k+4)(0(10)^q111 ys) section reaches F/0 at
    its first positive physically blank-left F/0 return at the
    exact 12k^2+49k+58+6q primitive-step endpoint. -/
theorem full_E_triple_pairs_first_return (k q : Nat) (ys : List Bool) :
    let tmax := 12*k*k+49*k+58+6*q
    let start := init (List.replicate (3*k+2) true ++
      false :: (pairs q ++ ([true,true,true] ++ ys)))
    run tmax start =
      ⟨[],false,List.replicate (8*k+9) true ++
        (oppairs (q+2) ++ false::ys),5⟩ ∧
    ∀ t, 0<t → t<tmax → ¬ IsPhysicalReturn (run t start) := by
  dsimp
  constructor
  · exact full_E_triple_pairs k q ys
  · intro t hpos hlt hphys
    by_cases hp : t<12*k*k+41*k+33
    · exact (prefixE_positive_noF k
        (pairs q ++ ([true,true,true]++ys)) t hpos hp) hphys.1
    · have hprefix :
        run (12*k*k+41*k+33)
          (init (List.replicate (3*k+2) true ++
            false :: (pairs q ++ ([true,true,true]++ys)))) =
          eTriplePairs (4*k+3) q ys := by
        rw [prefix_E]
        rfl
      have ht : t=(12*k*k+41*k+33)+(t-(12*k*k+41*k+33)) := by omega
      have hr : t-(12*k*k+41*k+33)<
          2*(4*k+3)+6*q+19 := by omega
      rw [ht,run_add] at hphys
      simp only [List.cons_append, List.nil_append] at hprefix
      rw [hprefix] at hphys
      exact (eTriplePairs_firstF (4*k+3) q ys).2
        (t-(12*k*k+41*k+33)) hr hphys.1

#print axioms eTriplePairs_front_noF
#print axioms eTriplePairs_firstF
#print axioms full_E_triple_pairs_first_return
end BB6.CryptidETriplePairsFirstReturn
