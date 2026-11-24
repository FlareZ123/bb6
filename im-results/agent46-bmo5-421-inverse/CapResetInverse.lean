import CapRayParent

namespace CapSieve

/-- Strip the complete power of three from a positive natural number. -/
def strip3 (v : Nat) : Nat × Nat :=
  if 0<v ∧ v%3=0 then
    let a := strip3 (v/3)
    (a.1+1,a.2)
  else (0,v)
termination_by v
decreasing_by omega

theorem strip3_spec {v : Nat} (hv : 0<v) :
    0<(strip3 v).2 ∧ (strip3 v).2%3≠0 ∧
      v=3^(strip3 v).1*(strip3 v).2 := by
  rw [strip3]
  split
  next h =>
    have hsmall : 0<v/3 := by omega
    have hs := strip3_spec hsmall
    dsimp
    refine ⟨hs.1,hs.2.1,?_⟩
    rw [Nat.pow_succ,show 3^(strip3 (v/3)).1*3*(strip3 (v/3)).2=
      3*(3^(strip3 (v/3)).1*(strip3 (v/3)).2) by ac_rfl,←hs.2.2]
    omega
  next h =>
    simp only [Nat.pow_zero,Nat.one_mul]
    exact ⟨hv,by omega,True.intro⟩
termination_by v
decreasing_by omega

theorem strip3_unique {v n w : Nat} (hw : w%3≠0) (he : v=3^n*w) :
    strip3 v=(n,w) := by
  induction n generalizing v with
  | zero =>
    simp at he
    subst v
    rw [strip3,if_neg (by omega)]
  | succ n ih =>
    have hpow : 0<3^n := Nat.pow_pos (by decide)
    have hwp : 0<w := by omega
    have hvp : 0<v := by
      rw [he]
      exact Nat.mul_pos (Nat.pow_pos (by decide)) hwp
    rw [Nat.pow_succ,show 3^n*3*w=3*(3^n*w) by ac_rfl] at he
    rw [strip3,if_pos (by omega)]
    have hdiv : v/3=3^n*w := by omega
    rw [ih hdiv]

theorem negative_unscale_valid {k n w : Nat} (h : CapNegative.Valid (k+n) (3^n*w)) :
    CapNegative.Valid k w := by
  induction n generalizing k w with
  | zero => simpa using h
  | succ n ih =>
    have hh : CapNegative.Valid (k+1+n) (3^n*(3*w)) := by
      rw [←Nat.mul_assoc,←Nat.pow_succ,show k+1+n=k+(n+1) by omega]
      exact h
    have hv := ih hh
    unfold CapNegative.Valid at *
    omega

/-- A final negative state whose next event returns positive. -/
def FinalReturn (b v j q : Nat) : Prop :=
  CapNegative.Valid b v ∧
    ((v=2*b+7 ∧ j=b+1 ∧ q=3*b+15) ∨
     (v≠2*b+3 ∧ v≠2*b+7 ∧ 2*b+9<3*v ∧ j=b+2 ∧ q=(3*v+3)/2))

theorem negative_event_final {k w j q : Nat} (hv : CapNegative.Valid k w)
    (he : (CapNegative.event k w).2=some (j,q)) :
    FinalReturn (k+CapNegative.stopCount k w) (3^(CapNegative.stopCount k w)*w) j q := by
  have hs := CapNegative.stop_spec hv
  unfold CapNegative.event at he
  dsimp at hs he
  generalize CapNegative.stopCount k w = n at *
  generalize k+n = b at *
  generalize 3^n*w = v at *
  refine ⟨hs.1,?_⟩
  by_cases ht : v=2*b+3
  · simp [ht] at he
  · rw [if_neg ht] at he
    by_cases hsp : v=2*b+7
    · rw [if_pos hsp] at he
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj he)
      exact Or.inl ⟨hsp,rfl,rfl⟩
    · rw [if_neg hsp] at he
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj he)
      exact Or.inr ⟨ht,hsp,by rcases hs.2 with h|h|h <;> omega,rfl,rfl⟩

theorem final_return_div3 {b v j q : Nat} (h : FinalReturn b v j q) :
    q%3=0 := by
  have hphase := h.1.2.2
  rcases h.2 with hsp|hsk
  · omega
  · have he := hsk.2.2.2.2
    omega

/-- Reconstruct the final negative state from a positive return. -/
def resetFinal (j q : Nat) : Option (Nat × Nat) :=
  if 1≤j ∧ q=3*j+12 then some (j-1,2*j+5)
  else if 2≤j ∧ q%3=0 ∧ q≤3*j-6 then some (j-2,(2*q-3)/3)
  else none

theorem final_return_reset {b v j q : Nat} (h : FinalReturn b v j q) :
    resetFinal j q=some (b,v) := by
  unfold resetFinal
  rcases h.2 with hsp|hsk
  · rw [if_pos (by omega : 1≤j ∧ q=3*j+12)]
    have hB : j-1=b := by omega
    have hV : 2*j+5=v := by omega
    rw [hB,hV]
  · obtain ⟨ht,hs,hcross,hj,hq⟩ := hsk
    have hv := h.1.2.1
    have hphase := h.1.2.2
    have hsharp : v≤2*b-1 := by omega
    have hqdiv : q%3=0 := final_return_div3 h
    rw [if_neg (by omega : ¬(1≤j ∧ q=3*j+12)),
      if_pos (by omega : 2≤j ∧ q%3=0 ∧ q≤3*j-6)]
    have hB : j-2=b := by omega
    have hV : (2*q-3)/3=v := by omega
    rw [hB,hV]

theorem reset_final_sound {j q b v : Nat} (hj : 5≤j) (hq : PosQ j q)
    (he : resetFinal j q=some (b,v)) : 3≤b ∧ FinalReturn b v j q := by
  unfold resetFinal at he
  split at he
  next h =>
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj he)
    refine ⟨by omega,⟨?_,Or.inl ⟨by omega,by omega,by omega⟩⟩⟩
    unfold CapNegative.Valid
    omega
  next hs =>
    split at he
    next h =>
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj he)
      have hl := hq.1
      have hp := hq.2.2
      have hdiv : 3*((2*q-3)/3)=2*q-3 := by omega
      have hphase : ((2*q-3)/3)%4=(2*(j-2)+3)%4 := by omega
      refine ⟨by omega,⟨⟨by omega,by omega,hphase⟩,Or.inr ?_⟩⟩
      exact ⟨by omega,by omega,by omega,by omega,by omega⟩
    next h => contradiction

theorem negative_final_event {k n w j q : Nat} (hk : 1≤k)
    (hf : FinalReturn (k+n) (3^n*w) j q) :
    (CapNegative.event k w).2=some (j,q) := by
  have hv := negative_unscale_valid hf.1
  have hwin : 3^n*w≤2*(k+n)+7 ∧ 2*(k+n)+9<3^(n+1)*w := by
    rw [Nat.pow_succ,show 3^n*3*w=3*(3^n*w) by ac_rfl]
    refine ⟨hf.1.2.1,?_⟩
    rcases hf.2 with h|h <;> omega
  have hn := CapNegative.window_unique (CapNegative.stop_window hk hv) hwin
  unfold CapNegative.event
  dsimp
  rw [hn]
  rcases hf.2 with ⟨hsp,hj,hq⟩|⟨ht,hs,hcross,hj,hq⟩
  · rw [if_neg (by omega : 3^n*w≠2*(k+n)+3),if_pos hsp,←hj,←hq]
  · rw [if_neg ht,if_neg hs,←hj,←hq]

/-- A final negative state in band at least three must strip to a unit
    strictly above band zero. -/
theorem strip_below_band {b v : Nat} (hb : 3≤b) (hv : CapNegative.Valid b v) :
    (strip3 v).1<b := by
  have h := strip3_spec hv.1
  have hbound := hv.2.1
  have hexp_all : ∀ a : Nat, 3≤a → 2*a+7<3^a := by
    intro a
    induction a with
    | zero => omega
    | succ a ih =>
      intro ha
      by_cases h : 3≤a
      · have hh := ih h
        rw [Nat.pow_succ]
        omega
      · have he : a=2 := by omega
        subst a
        decide
  have hexp := hexp_all b hb
  by_cases hlt : (strip3 v).1<b
  · exact hlt
  · have hpow := Nat.pow_le_pow_right (by decide : 0<3) (show b≤(strip3 v).1 by omega)
    have hm := Nat.le_mul_of_pos_right (3^(strip3 v).1) h.1
    omega

#print axioms strip3_spec
#print axioms strip3_unique
#print axioms reset_final_sound
#print axioms final_return_reset
#print axioms negative_final_event
#print axioms strip_below_band
end CapSieve
