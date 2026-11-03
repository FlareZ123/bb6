import Lean.Elab.Tactic.Omega
import Boundary
import DRegular
import BoundaryPadding
import DObsSourceCandidate

set_option maxHeartbeats 5000000
namespace BB6.BRegularSource
open CryptidBoundary
open BB6.BoundaryPadding BB6.Padding

def sourceSection (s : DRegular.L) : Cfg :=
  init (List.replicate (s.a - 2) true ++
    oppairs s.q ++ List.replicate s.b true)

/-- The two positive-alternation B regular rows have exact literal
    original-source configurations, rather than a conditional model transport. -/
theorem b_positive (k q b : Nat) :
    run (12*k*k+49*k+40)
      (sourceSection ⟨3*k+2,q+1,b⟩) =
    sourceSection ⟨8*k+10,q,b⟩ := by
  have hin : sourceSection (DRegular.L.mk (3*k+2) (q+1) b) =
      init (List.replicate (3*k) true ++
        false::true::(oppairs q ++ List.replicate b true)) := by
    simp [sourceSection, init, oppairs, List.append_assoc, Nat.add_sub_cancel]
  rw [hin, full_B]
  have hrepl : List.replicate (8*k+9) true ++ [true] =
      List.replicate (8*k+10) true := by
    calc
      _ = List.replicate (8*k+9) true ++ List.replicate 1 true := rfl
      _ = List.replicate ((8*k+9)+1) true := List.replicate_append_replicate
      _ = _ := by congr 1
  have hrepl2 : List.replicate (8*k+10) true =
      [true,true] ++ List.replicate (8*k+8) true := by
    calc
      _ = List.replicate (2+(8*k+8)) true := by congr 1; omega
      _ = List.replicate 2 true ++ List.replicate (8*k+8) true :=
        (List.replicate_append_replicate).symm
      _ = _ := rfl
  have hlist :
      List.replicate (8*k+9) true ++
        (true :: (oppairs q ++ List.replicate b true)) =
      [true,true] ++ List.replicate (8*k+8) true ++
        (oppairs q ++ List.replicate b true) := by
    calc
      _ = (List.replicate (8*k+9) true ++ [true]) ++
        (oppairs q ++ List.replicate b true) := by simp [List.append_assoc]
      _ = List.replicate (8*k+10) true ++
        (oppairs q ++ List.replicate b true) := by rw [hrepl]
      _ = ([true,true] ++ List.replicate (8*k+8) true) ++
        (oppairs q ++ List.replicate b true) := by rw [hrepl2]
      _ = _ := by simp [List.append_assoc]
  have hnum : 8*k+10-2 = 8*k+8 := by omega
  simpa only [sourceSection, init, hnum, List.append_assoc, List.cons_append, List.nil_append] using
    congrArg (fun r : List Bool => (⟨[],false,r,5⟩ : Cfg)) hlist

theorem unary_merge (n b : Nat) (hn : n ≥ 2) :
    sourceSection ⟨n,0,b⟩ = sourceSection ⟨n+b,0,0⟩ := by
  have hnum : n+b-2 = (n-2)+b := by omega
  simp only [sourceSection, oppairs, List.nil_append, List.append_nil,
    List.replicate_zero, hnum]
  rw [← List.replicate_append_replicate]

private theorem b_duration (k q b : Nat) :
    DRegular.duration ⟨3*k+2,q,b⟩ = 12*k*k+49*k+40 := by
  have hm : (3*k+2)%3=2 := by omega
  have hd : (3*k+2)/3=k := by omega
  simp [DRegular.duration,hm,hd]

theorem b_one (k b : Nat) :
    run (DRegular.duration ⟨3*k+2,1,b⟩)
      (sourceSection ⟨3*k+2,1,b⟩) =
    sourceSection ⟨8*k+10+b,0,0⟩ := by
  rw [b_duration]
  have h := b_positive k 0 b
  simpa only [unary_merge (8*k+10) b (by omega)] using h

theorem b_many (k q b : Nat) :
    run (DRegular.duration ⟨3*k+2,q+2,b⟩)
      (sourceSection ⟨3*k+2,q+2,b⟩) =
    sourceSection ⟨8*k+10,q+1,b⟩ := by
  rw [b_duration]
  simpa only [show q+1+1=q+2 by omega] using (b_positive k (q+1) b)

/-- The zero-alternating-pair B row consumes a physically implicit right-hand
    blank. The result is observationally equivalent to a canonical unary section. -/
theorem b_zero (k : Nat) :
    ObsEq
      (run (DRegular.duration ⟨3*k+2,0,0⟩)
        (sourceSection ⟨3*k+2,0,0⟩))
      (sourceSection ⟨8*k+9,0,0⟩) := by
  have hnum : (3*k+2)-2 = 3*k := by omega
  have hinput : ObsEq (sourceSection ⟨3*k+2,0,0⟩)
      (init (List.replicate (3*k) true ++ [false])) := by
    change CfgEq (represent (sourceSection ⟨3*k+2,0,0⟩))
      (represent (init (List.replicate (3*k) true ++ [false])))
    simpa only [sourceSection, init, represent, oppairs, List.replicate_zero,
      List.append_nil, List.nil_append, hnum] using
      (show CfgEq
        ⟨[],false,true::true::List.replicate (3*k) true,5⟩
        ⟨[],false,true::true::(List.replicate (3*k) true ++ [false]),5⟩ from
       ⟨tapeEq_refl [],rfl,
        tapeEq_cons true (tapeEq_cons true
          (tapeEq_pad (List.replicate (3*k) true) 1)),rfl⟩)
  have hrep : List.replicate (8*k+9) true =
      true :: true :: List.replicate (8*k+7) true := by
    calc
      _ = List.replicate (2+(8*k+7)) true := by congr 1; omega
      _ = List.replicate 2 true ++ List.replicate (8*k+7) true :=
        (List.replicate_append_replicate).symm
      _ = _ := rfl
  have htarget : (⟨[],false,List.replicate (8*k+9) true,5⟩ : Cfg) =
      sourceSection ⟨8*k+9,0,0⟩ := by
    have hn : (8*k+9)-2 = 8*k+7 := by omega
    simp only [sourceSection, init, oppairs, List.replicate_zero,
      List.nil_append, List.append_nil, hn, hrep]
  rw [b_duration]
  have hs := source_congr (12*k*k+49*k+40) hinput
  have hexact : run (12*k*k+49*k+40)
      (init (List.replicate (3*k) true ++ [false])) =
      (⟨[],false,List.replicate (8*k+9) true,5⟩ : Cfg) := by
    simpa using (full_B k [])
  rw [hexact, htarget] at hs
  exact hs

#print axioms b_zero

private theorem b_one_next (k b : Nat) :
    DRegular.next ⟨3*k+2,1,b⟩ = some ⟨8*k+10+b,0,0⟩ := by
  have hm : (3*k+2)%3=2 := by omega
  have hd : (3*k+2)/3=k := by omega
  simp [DRegular.next,hm,hd]

private theorem b_many_next (k q b : Nat) :
    DRegular.next ⟨3*k+2,q+2,b⟩ = some ⟨8*k+10,q+1,b⟩ := by
  have hm : (3*k+2)%3=2 := by omega
  have hd : (3*k+2)/3=k := by omega
  simp [DRegular.next,hm,hd]

theorem b_positive_contract (s t : DRegular.L)
    (hb : s.a % 3 = 2) (hq : s.q > 0)
    (hn : DRegular.next s = some t) :
    run (DRegular.duration s) (sourceSection s) = sourceSection t := by
  obtain ⟨a,q,b⟩ := s
  change a % 3 = 2 at hb
  change q > 0 at hq
  have ha : a = 3*(a/3)+2 := by omega
  rw [ha] at hn ⊢
  cases q with
  | zero => omega
  | succ q =>
    cases q with
    | zero =>
      rw [b_one_next] at hn
      cases hn
      exact b_one (a/3) b
    | succ q =>
      have hs : q+1+1 = q+2 := by omega
      rw [hs] at hn ⊢
      rw [b_many_next] at hn
      cases hn
      exact b_many (a/3) q b

private theorem b_zero_next (k : Nat) :
    DRegular.next ⟨3*k+2,0,0⟩ = some ⟨8*k+9,0,0⟩ := by
  have hm : (3*k+2)%3=2 := by omega
  have hd : (3*k+2)/3=k := by omega
  simp [DRegular.next,hm,hd]

/-- The complete B residue of the eleven-case DRegular source contract.
    Its two nonempty-prefix rows are exact; the q=0 row uses genuine
    physical right-end blank padding. No assumption about blank reachability. -/
theorem b_contract (s t : DRegular.L)
    (hc : DRegular.Canon s) (hb : s.a % 3 = 2)
    (hn : DRegular.next s = some t) :
    ObsEq (run (DRegular.duration s) (sourceSection s)) (sourceSection t) := by
  obtain ⟨a,q,b⟩ := s
  change a % 3 = 2 at hb
  rcases hc with ⟨ha2, hcanon⟩
  have ha : a = 3*(a/3)+2 := by omega
  rw [ha] at hn ⊢
  cases q with
  | zero =>
    have hb0 : b=0 := by
      cases hcanon with
      | inl h => exact False.elim (h rfl)
      | inr h => exact h
    subst b
    rw [b_zero_next] at hn
    cases hn
    exact b_zero (a/3)
  | succ q =>
    have hq : (DRegular.L.mk (3*(a/3)+2) (q+1) b).q > 0 := by
      change q+1>0
      omega
    have hpos := b_positive_contract
      (DRegular.L.mk (3*(a/3)+2) (q+1) b) t
      (by change (3*(a/3)+2)%3=2; omega) hq hn
    rw [hpos]
    exact cfgEq_refl _

/-- Discharge the B residue of Agent35's real eleven-row source contract,
    using its exact sourceSection representation and physical ObsEq relation. -/
theorem original_B_row (s t : DRegular.L)
    (hc : DRegular.Canon s) (hb : s.a % 3 = 2)
    (hn : DRegular.next s = some t) :
    ObsEq
      (run (DRegular.duration s) (DRegularSource.sourceSection s))
      (DRegularSource.sourceSection t) := by
  exact b_contract s t hc hb hn

#print axioms original_B_row

#print axioms b_contract

#print axioms b_positive_contract

#print axioms unary_merge
#print axioms b_one
#print axioms b_many

#print axioms b_positive
end BB6.BRegularSource
