import P1InverseFixed
import ConeKernel
import P1Gate

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

/-!
An executable, source-connected finite inverse-cone certificate checker for
the genuine P1 blank-entry acceleration. Unlike sampled forward trajectories,
a successful certificate proves an all-time reachability exclusion.

This module imports the original Agent1 GAncestor semantics and the complete
source-level inverse theorem, with no new axioms.
-/

namespace BB6.Agent12Numeric
open BB6.Agent47P1 BB6.Agent4Cone BB6.P1Reduction

def modProp (b d : Nat) : Prop :=
  b%2=0 ∧ 0<d ∧ 2<b ∧ b%4=2

def powerProp (N b d : Nat) : Prop :=
  b%2=0 ∧ 0<d ∧ d%2=0 ∧
    14*2^(N-1)<b+12 ∧ b+12<14*2^N

instance (b d : Nat) : Decidable (modProp b d) := by
  unfold modProp
  infer_instance

instance (N b d : Nat) : Decidable (powerProp N b d) := by
  unfold powerProp
  infer_instance

/-- Fuel controls recursive cone depth; M bounds each individual G inverse
exponent via a checked nondivisibility test, rather than a simulation limit. -/
def good (M N : Nat) : Nat → Nat → Nat → Bool
  | fuel,b,d =>
    if modProp b d then true
    else if powerProp N b d then true
    else match fuel with
    | 0 => false
    | f+1 =>
      decide (8≤b ∧ b%4=0 ∧ 0<d ∧ (d+b/2+3)%2^(M+1) ≠ 0) &&
      (List.range (M+1)).all (fun t =>
        match inverseAt b d t with
        | none => true
        | some (k,c) => decide (2≤c) && good M N f (2*k-4) (c+4))

private theorem no_power_in_gap (N b : Nat)
    (hlo : 14*2^(N-1)<b+12)
    (hhi : b+12<14*2^N) : ∀ j : Nat, b+12≠14*2^j := by
  intro j heq
  by_cases hN : N=0
  · subst N
    simp at hlo
    omega
  by_cases hj : j < N
  · have he : j≤N-1 := by omega
    have hp : 2^j≤2^(N-1) := Nat.pow_le_pow_right (by decide) he
    omega
  · have hp : 2^N≤2^j := Nat.pow_le_pow_right (by decide) (by omega)
    omega

private theorem mod_justified (b d : Nat) (h : modProp b d) : Blocked b d :=
  Blocked.modLeaf b d h.1 h.2.1 h.2.2.1 h.2.2.2

private theorem power_justified (N b d : Nat)
    (h : powerProp N b d) : Blocked b d :=
  Blocked.powerLeaf b d h.1 h.2.1 h.2.2.1
    (no_power_in_gap N b h.2.2.2.1 h.2.2.2.2)

/-- Sound executable inverse-cone checker. Every successful Boolean
certificate constructs a finite Blocked proof using exhaustive G ancestors. -/
theorem good_sound (M N : Nat) :
    ∀ fuel b d, good M N fuel b d = true → Blocked b d := by
  intro fuel
  induction fuel with
  | zero =>
      intro b d h
      by_cases hm : modProp b d
      · exact mod_justified b d hm
      by_cases hp : powerProp N b d
      · exact power_justified N b d hp
      simp [good, hm, hp] at h
  | succ f ih =>
      intro b d h
      by_cases hm : modProp b d
      · exact mod_justified b d hm
      by_cases hp : powerProp N b d
      · exact power_justified N b d hp
      have hh : decide (8≤b ∧ b%4=0 ∧ 0<d ∧
            (d+b/2+3)%2^(M+1)≠0) &&
         (List.range (M+1)).all (fun t =>
            match inverseAt b d t with
            | none => true
            | some (k,c) => decide (2≤c) && good M N f (2*k-4) (c+4)) = true := by
              simpa [good,hm,hp] using h
      obtain ⟨hb,hlist⟩ := Bool.and_eq_true_iff.mp hh
      obtain ⟨hb8,hb4,hdpos,hshift⟩ := of_decide_eq_true hb
      have hcheck (k c : Nat) (hanc : GAncestor b d k c) :
          2≤c ∧ Blocked (2*k-4) (c+4) := by
        obtain ⟨t,ht,hval⟩ :=
          inverse_at_depth_le_of_nonzero_mod b d k c M hanc hshift
        have hmem : t ∈ List.range (M+1) := List.mem_range.mpr (by omega)
        have hentry := (List.all_eq_true.mp hlist) t hmem
        rw [hval] at hentry
        obtain ⟨hc,hchild⟩ := Bool.and_eq_true_iff.mp hentry
        exact ⟨of_decide_eq_true hc, ih _ _ hchild⟩
      apply Blocked.feeder b d hb8 hb4 hdpos
      · intro k hanc
        have hcontr := (hcheck k 1 hanc).1
        omega
      · intro k c hanc _
        exact (hcheck k c hanc).2

/-- Index 382 survived the existing modulo-1024 universal P1 certificates.
The finite inverse cone closes by the kernel's exact arithmetic reduction. -/
theorem p1_382_blocked :
    Blocked (14*2^382-2*382-16) 3 :=
  good_sound 8 382 12 _ _ (by decide +kernel)

theorem p1_382_no_hub :
    ¬BB6.Agent1.Reach (14*2^382-2*382-16) 3 :=
  BB6.Agent4Cone.blocked_no_reach _ _ p1_382_blocked

theorem p1_382_no_critical :
    ¬BB6.Agent1.Reach 2 (14*2^382-2*382-10) := by
  have hbound : 10≤14*2^382-2*382-10 := by decide
  have hmod : (14*2^382-2*382-10)%4=2 := by decide
  intro hr
  have hhub := BB6.Agent50P1.critical_target_implies_three
    (14*2^382-2*382-10) hbound hmod hr
  have heq : (14*2^382-2*382-10)-6 =
      14*2^382-2*382-16 := by decide
  exact p1_382_no_hub (by simpa only [heq] using hhub)

#print axioms good_sound
#print axioms p1_382_blocked
#print axioms p1_382_no_critical
end BB6.Agent12Numeric
