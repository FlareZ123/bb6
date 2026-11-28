import Q0ExhaustiveTree
import ExactOneHoleOrdinary

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Sharp ordinary-step interpretation of *the same* exhaustive first-hole tree
previously checked only for WeightedBound. The machine's ordinary halting
transition counts as one step. A checked B+5 weighted tree has an ordinary
n+1 certificate at each first hole, and never-halt certificates at every
side-cycle, two-stack automaton, or supplied symbolic branch. No
normalization/blank-delay slack is needed to bound primitive blank steps.
-/
namespace BB6.Agent47OrdinaryQ0Exhaustive
open BB6Coverage BB6.Agent13BlankDelay
open Q0ExhaustiveTree
open BB6.Agent5ExactOneHole (OrdinaryBound)

theorem hole_sharp (B n : Nat) (p : PartialMachine) (c : FinRayCfg)
    (h : holeOK (B+5) p n c = true) :
    p (readSlot (embedFinRay c)) = none ∧ n+1 ≤ B := by
  simp only [holeOK,firstOK,Bool.and_eq_true,decide_eq_true_eq] at h
  exact ⟨h.1.2, by omega⟩

theorem check_sharp (B : Nat) (sym : PartialMachine → Bool)
    (hsym : ∀ p, sym p = true → Cover (OrdinaryBound B) p)
    (fuel : Nat) (p : PartialMachine) (t : Tree)
    (h : check (B+5) sym fuel p t = true) :
    Cover (OrdinaryBound B) p := by
  induction fuel generalizing p t with
  | zero => contradiction
  | succ fuel ih =>
    cases t with
    | fail => contradiction
    | side right entry period k =>
      exact .leaf _ fun m hm =>
        Or.inr (sideCheck_sound p right entry period k h m hm)
    | pair cert =>
      exact .leaf _ fun m hm =>
        Or.inr (BB6.Agent4Automata.never p cert h m hm)
    | symbolic => exact hsym p h
    | last n =>
      simp only [check] at h
      split at h
      · contradiction
      · rename_i c hc
        simp only [Bool.and_eq_true] at h
        obtain ⟨hu,hb⟩ := hole_sharp B n p c h.1
        exact .leaf _ (last_hole_exact B p n (embedFinRay c)
          (finite_known p n c hc) hu
          (allOrdExcept_sound h.2) hb)
    | split n kids =>
      simp only [check] at h
      split at h
      · contradiction
      · rename_i c hc
        simp only [Bool.and_eq_true] at h
        obtain ⟨hu,hb⟩ := hole_sharp B n p c h.1
        apply Cover.branch p (readSlot (embedFinRay c)) hu
        intro tr ht
        cases tr with
        | none =>
          exact .leaf _ fun m hm =>
            Or.inl ⟨n, first_hole_halts p n (embedFinRay c)
              (finite_known p n c hc) hu m hm, hb⟩
        | some mv =>
          exact ih _ _ (List.all_eq_true.mp h.2 mv (moves_mem mv))

theorem split_sharp (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot)
    (h : splitOK (B+5) p n s = true)
    (children : ∀ mv, Cover (OrdinaryBound B) (refine p s (some mv))) :
    Cover (OrdinaryBound B) p := by
  unfold splitOK at h
  split at h
  · contradiction
  · rename_i c hc
    simp only [Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨hu,hb⟩ := hole_sharp B n p c h.1
    have he := h.2
    subst s
    apply Cover.branch p (readSlot (embedFinRay c)) hu
    intro tr ht
    cases tr with
    | none =>
      exact .leaf _ fun m hm =>
        Or.inl ⟨n, first_hole_halts p n (embedFinRay c)
          (finite_known p n c hc) hu m hm, hb⟩
    | some mv => exact children mv

#print axioms hole_sharp
#print axioms check_sharp
#print axioms split_sharp
end BB6.Agent47OrdinaryQ0Exhaustive
