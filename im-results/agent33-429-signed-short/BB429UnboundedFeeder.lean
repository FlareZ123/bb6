import BB429Rank
import BB429Mod8
import Lean.Elab.Tactic.Omega

namespace BB429UnboundedFeeder
set_option maxHeartbeats 30000000
set_option maxRecDepth 30000

/-!
# A renormalization ray in the authentic machine #429 accelerator.

The exact positive-state inverse word F E F S takes
(8z+15, 8z+1536*(16v)+27)
to
(8(z+960v-1)+15, 8(z+960v-1)+1536v+27),
with all four inverse transitions genuine source steps.
Iterating n times from v=16^n generates 4n actual forward steps
ending at an odd-reset 15-line candidate whose parameter is
q=3*16^(n+1). This is NOT a blank-root reachability witness.
It proves that bounded inverse-depth enumeration using only local
backward transition equations cannot uniformly exclude all such q.
-/

def anchor (z v : Nat) : BB429.State :=
  (8*z+15,8*z+1536*v+27)

/-- Final inverse S edge: original accelerator goes from S-child to F-child. -/
theorem source_S (z v : Nat) (hv : 1 ≤ v) :
    BB429.next (8*z+7680*v+7,8*z+9216*v+19) =
      some (4*z+3072*v+5,16*z+18432*v+34) := by
  simp only [BB429.next]
  repeat' (split <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

theorem source_F_inner (z v : Nat) (hv : 1 ≤ v) :
    BB429.next (4*z+3072*v+5,16*z+18432*v+34) =
      some (8*z+6144*v+13,8*z+12288*v+21) := by
  simp only [BB429.next]
  repeat' (split <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

theorem source_E (z v : Nat) (hv : 1 ≤ v) :
    BB429.next (8*z+6144*v+13,8*z+12288*v+21) =
      some (4*z+6,16*z+24576*v+42) := by
  simp only [BB429.next]
  repeat' (split <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

theorem source_F_outer (z v : Nat) (hv : 1 ≤ v) :
    BB429.next (4*z+6,16*z+24576*v+42) =
      some (8*z+15,8*z+24576*v+27) := by
  simp only [BB429.next]
  repeat' (split <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

/-- Four genuine accelerated forward steps from the renormalized
    descendant to its original affine ancestor. -/
theorem source_four_step (z v : Nat) (hv : 1 ≤ v) :
    BB429.run 4 (anchor (z+960*v-1) v) =
      some (anchor z (16*v)) := by
  have hza : 8*(z+960*v-1)+15 = 8*z+7680*v+7 := by omega
  have hzb : 8*(z+960*v-1)+1536*v+27 =
      8*z+9216*v+19 := by omega
  have hya : 8*z+1536*(16*v)+27 =
      8*z+24576*v+27 := by omega
  simp only [anchor, hza, hzb, hya]
  simp [BB429.run, source_S z v hv, source_F_inner z v hv,
    source_E z v hv, source_F_outer z v hv]

/-- For every desired number n of four-step inverse blocks and
    every nonnegative seed z, a genuine accelerated forward orbit
    segment reaches anchor(z,16^n) from another nonnegative state.
    No inference about starting at the blank state is claimed. -/
theorem arbitrary_inverse_depth (n : Nat) :
    ∀ z : Nat, ∃ s : BB429.State,
      BB429.run (4*n) s = some (anchor z (16^n)) := by
  induction n with
  | zero =>
    intro z
    exact ⟨anchor z 1,rfl⟩
  | succ n ih =>
    intro z
    have hv : 1 ≤ 16^n := by
      have hpos : 0 < 16^n := Nat.pow_pos (by omega)
      omega
    obtain ⟨s,hs⟩ := ih (z+960*16^n-1)
    refine ⟨s, ?_⟩
    have hm := source_four_step z (16^n) hv
    have hlen : 4*(n+1)=4*n+4 := by omega
    have hpow : 16^(n+1)=16*(16^n) := by
      rw [Nat.pow_succ]
      omega
    rw [hlen, BB429.run_add, hs]
    simp only [Option.bind_some]
    rw [hpow]
    exact hm

/-- There is NO uniform finite upper bound on the length of a
    genuine inverse orbit segment ending in the 15 odd-reset line,
    even when its parameter is divisible by exponentially large
    powers of sixteen. The prefix need not be blank-reachable. -/
theorem branch15_has_arbitrarily_deep_actual_predecessors (n : Nat) :
    ∃ s : BB429.State,
      BB429.run (4*n) s =
        some (32*(3*16^(n+1))+15,64*(3*16^(n+1))+27) := by
  obtain ⟨s,hs⟩ := arbitrary_inverse_depth n (192*16^n)
  have hpow : 16^(n+1)=16^n*16 := by
    rw [Nat.pow_succ]
  have ha : 8*(192*16^n)+15 = 32*(3*16^(n+1))+15 := by
    rw [hpow]
    omega
  have hb : 8*(192*16^n)+1536*16^n+27 =
      64*(3*16^(n+1))+27 := by
    rw [hpow]
    omega
  unfold anchor at hs
  rw [ha,hb] at hs
  exact ⟨s,hs⟩

#print axioms source_four_step
#print axioms arbitrary_inverse_depth
#print axioms branch15_has_arbitrarily_deep_actual_predecessors
end BB429UnboundedFeeder
