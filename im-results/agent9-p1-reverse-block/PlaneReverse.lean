import Lean

namespace BB6.Agent9PlaneReverse

/-- A target-weight interval begins at this quotient. The assumption Y < M
makes the natural subtraction exact. -/
def first (M Y W : Nat) : Nat := (W+M-1-Y)/M

/-- The first carry residue of the interval. -/
def residue (M Y W : Nat) : Nat := M*first M Y W+Y-W

theorem first_identity (M Y W : Nat) (hM : 0<M) (hY : Y<M) :
    M*first M Y W+Y=W+residue M Y W ∧ residue M Y W<M := by
  let S := W+M-1-Y
  have hs : S+Y+1=W+M := by dsimp [S]; omega
  have hd := Nat.div_add_mod S M
  have hr := Nat.mod_lt S hM
  change M*(S/M)+S%M=S at hd
  have hf : first M Y W=S/M := rfl
  unfold residue
  rw [hf]
  omega

/-- Each fixed selected word contributes a strided interval, with exact
    start and residue; no fitted-block hypothesis is required. -/
theorem interval_iff (M Y W q z c : Nat) (hM : 0<M) (hY : Y<M) :
    (M*z+Y=W+c ∧ c<q) ↔
    ∃ t, z=first M Y W+t ∧ c=residue M Y W+M*t ∧ c<q := by
  obtain ⟨he,hr⟩ := first_identity M Y W hM hY
  constructor
  · rintro ⟨h,hc⟩
    have hle : first M Y W≤z := by
      by_cases hn : first M Y W≤z
      · exact hn
      · have hh := Nat.mul_le_mul_left M (show z+1≤first M Y W by omega)
        rw [Nat.mul_add,Nat.mul_one] at hh
        omega
    let t := z-first M Y W
    have hz : z=first M Y W+t := by dsimp [t]; omega
    have hz' : M*z=M*first M Y W+M*t := by rw [hz,Nat.mul_add]
    exact ⟨t,hz,by omega,hc⟩
  · rintro ⟨t,hz,hc,hq⟩
    rw [hz,Nat.mul_add,hc]
    exact ⟨by omega,by omega⟩

/-- The upper length bound used by an interval-copy implementation. -/
theorem interval_index_iff (M r q t : Nat) (hM : 0<M) (hr : r<q) :
    r+M*t<q ↔ t<(q-1-r)/M+1 := by
  have hq : q-1-r+r+1=q := by omega
  constructor
  · intro h
    have hle : M*t≤q-1-r := by omega
    have h := (Nat.le_div_iff_mul_le hM).2 (by simpa [Nat.mul_comm] using hle : t*M≤q-1-r)
    omega
  · intro h
    have hle : t≤(q-1-r)/M := by omega
    have hm := (Nat.le_div_iff_mul_le hM).1 hle
    rw [Nat.mul_comm] at hm
    omega

/-- Exact set semantics of copying each terminal interval into its output
    residue lane. The weight function is arbitrary: this identity needs
    only the weighted endpoint equation. -/
theorem plane_membership_iff (M Y q F c : Nat) (w : Nat → Nat)
    (ends : Nat → Prop) (hM : 0<M) (hY : Y<M) :
    (∃ B<M, ∃ z<F, ends z ∧ M*z+Y=w B+c ∧ c<q) ↔
    ∃ B<M, ∃ t, first M Y (w B)+t<F ∧
      ends (first M Y (w B)+t) ∧
      c=residue M Y (w B)+M*t ∧ c<q := by
  constructor
  · rintro ⟨B,hB,z,hz,ht,he,hc⟩
    obtain ⟨t,hs,hr,hq⟩ := (interval_iff M Y (w B) q z c hM hY).1 ⟨he,hc⟩
    exact ⟨B,hB,t,by simpa [←hs] using hz,by simpa [←hs] using ht,hr,hq⟩
  · rintro ⟨B,hB,t,hz,ht,hr,hq⟩
    have he := (interval_iff M Y (w B) q (first M Y (w B)+t) c hM hY).2 ⟨t,rfl,hr,hq⟩
    exact ⟨B,hB,_,hz,ht,he.1,he.2⟩

#print axioms first_identity
#print axioms interval_iff
#print axioms interval_index_iff
#print axioms plane_membership_iff
end BB6.Agent9PlaneReverse
