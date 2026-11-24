import CapUpRun
namespace CapSieve

/-- A two-band inverse skip from a positive sector returns to the negative
    boundary sector, with magnitude bounded by the smaller band index. -/
theorem skip_negative {j x y : Nat} (h : RegFrom j x y) (hb : Band (j+2) y) :
    -(2*(j:Int)+7)≤W j x ∧ W j x<0 := by
  have hx : Band j x := by obtain ⟨r,hr,rfl,_⟩:=h; exact regular_band j r hr
  have hxb:=(w_bounds hx).1
  have hyb:=(w_bounds hb).2
  have he:=w_regular_skip h
  rw [show P (j+2)=4*P j by rw [show j+2=(j+1)+1 by omega,p_succ,p_succ]; omega] at hyb
  exact ⟨hxb,by omega⟩

theorem special_negative (j : Nat) : W j (L j+(P j-2))= -(2*(j:Int)+7) := by
  have hp:=p_ge j
  have hl:=l_add j
  unfold W
  omega

/-- In the negative sector the only possible branches are a divisible
    one-band descent or a same-band jump back into the positive sector. -/
theorem negative_parent_partition {j x y : Nat} (hj : 6≤j) (hy : Band j y)
    (hn : W j y<0) (he : Arc x y) :
    (RegFrom (j-1) x y ∧ W j y=3*W (j-1) x ∧ W (j-1) x<0) ∨
    (RegFrom j x y ∧ 0<W j x) := by
  have hp:=p_ge_large hj
  have hb:=w_bounds hy
  have hlow : P j+3≤y := by unfold W at hn; omega
  rcases (large_band_arc hj hy).mp he with h|h|h|h
  · exact Or.inr ⟨h,by have hh:=w_regular_same h; omega⟩
  · have hh:=w_regular_down h
    rw [show j-1+1=j by omega] at hh
    exact Or.inl ⟨h,hh,by omega⟩
  · obtain ⟨r,hr,_,hry⟩:=h
    have hp : P j=4*P (j-2) := by
      calc
        P j = P ((j-2)+1+1) := congrArg P (by omega)
        _ = 4*P (j-2) := by rw [p_succ,p_succ]; omega
    omega
  · omega

/-- The maximal divisible negative run (provided its bottom band stays above
    five) ends at a genuine root or a positive-sector inverse step. -/
theorem negative_strip_general {j n y : Nat} {w : Int} (hj : 6≤j)
    (hy : Band (j+n) y) (hw : W (j+n) y= -(3^n:Int)*w)
    (hpos : 0<w) (hu : w%3≠0) :
    ∃ x, UpRun j n x y ∧ W j x= -w ∧
      ((¬∃ z, Arc z x) ∨ ∃ z, RegFrom j z x ∧ 0<W j z) := by
  have hd : (3^n:Int)∣ W (j+n) y := ⟨-w,by rw [hw]; grind⟩
  obtain ⟨x,hr⟩ := (up_run_exists (by omega : 1≤j) hy).mpr hd
  have he := up_run_w hr
  have hx : W j x= -w := by
    have hp : (3^n:Int)≠0 := Int.ne_of_gt (Int.pow_pos (by decide))
    apply Int.eq_of_mul_eq_mul_left hp
    rw [←he,hw,Int.mul_neg,Int.neg_mul]
  have hb := (up_run_bands hr).1
  refine ⟨x,hr,hx,?_⟩
  by_cases h : ∃ z, Arc z x
  · obtain ⟨z,hz⟩:=h
    have hp:=negative_unit_parent_positive hj hb (by omega) (by omega) hz
    exact Or.inr ⟨z,hp⟩
  · exact Or.inl h

/-- Uniform bound on the length of a negative one-band inverse phase. -/
theorem negative_run_length {j n x y : Nat} (hr : UpRun j n x y)
    (hy : W (j+n) y<0) : (3^n:Int)≤2*((j+n:Nat):Int)+7 := by
  have he:=up_run_w hr
  have hpow : 0<(3^n:Int) := Int.pow_pos (by decide)
  have hx : W j x≤ -1 := by
    by_cases h : W j x≤ -1
    · exact h
    · have hm:=Int.mul_nonneg (Int.le_of_lt hpow) (show 0≤W j x by omega)
      omega
  have hm:=Int.mul_le_mul_of_nonneg_left hx (Int.le_of_lt hpow)
  have hb:=(w_bounds (up_run_bands hr).2).1
  omega

/-- Above the low boundary, the positive sector has only two possible
    regular predecessors. Their existence is determined by W modulo three. -/
theorem positive_safe_parent {j y : Nat} (hj : 6≤j) (hy : Band j y)
    (hs : P j+3≤y) (hw : 0<W j y) :
    ((∃ x, RegFrom (j-1) x y ∧ 0<W (j-1) x) ↔ W j y%3=0) ∧
    ((∃ x, RegFrom j x y ∧ 0<W j x) ↔ W j y%3=(P j:Int)%3) ∧
    ((¬ ∃ x, Arc x y) ↔ W j y%3≠0 ∧ W j y%3≠(P j:Int)%3) := by
  have hP:=p_ge_large hj
  have hP1:=p_ge_mid (j:=j-1) (by omega)
  have h1 : P j=2*P (j-1) := by exact (congrArg P (show j=j-1+1 by omega)).trans (p_succ (j-1))
  have hb:=band_bounds hy
  have hm:=p_adjacent (j-1)
  rw [show j-1+1=j by omega] at hm
  have he : W j y%3=(2*(P j:Int)-(y:Int))%3 := by unfold W; omega
  have hR1 : (∃ x, RegFrom (j-1) x y) ↔ W j y%3=0 := by
    rw [regFrom_iff]; omega
  have hR0 : (∃ x, RegFrom j x y) ↔ W j y%3=(P j:Int)%3 := by
    rw [regFrom_iff]; omega
  constructor
  · constructor
    · rintro ⟨x,hx,_⟩; exact hR1.mp ⟨x,hx⟩
    · intro h
      obtain ⟨x,hx⟩:=hR1.mpr h
      have hW:=w_regular_down hx
      rw [show j-1+1=j by omega] at hW
      exact ⟨x,hx,by omega⟩
  constructor
  · constructor
    · rintro ⟨x,hx,_⟩; exact hR0.mp ⟨x,hx⟩
    · intro h
      obtain ⟨x,hx⟩:=hR0.mpr h
      have hW:=w_regular_same hx
      exact ⟨x,hx,by omega⟩
  · rw [large_band_no_parent hj hy]
    have hp:=p_nonzero j
    omega

/-- Outside the safe positive region, the only transitions that change
    the sign of W from positive to negative are the two exceptional exits. -/
theorem positive_to_negative {j x y : Nat} (hj : 6≤j) (hy : Band j y)
    (hw : 0<W j y) (he : Arc x y) :
    (RegFrom j x y ∧ 0<W j x) ∨
    (RegFrom (j-1) x y ∧ 0<W (j-1) x) ∨
    (RegFrom (j-2) x y ∧ W (j-2) x<0) ∨
    (y=P j ∧ x=L (j-1)+(P (j-1)-2) ∧ W (j-1) x<0) := by
  have hp:=p_ge_large hj
  rcases (large_band_arc hj hy).mp he with h|h|h|⟨heq,hx⟩
  · exact Or.inl ⟨h,by have hW:=w_regular_same h; omega⟩
  · have hW:=w_regular_down h
    rw [show j-1+1=j by omega] at hW
    exact Or.inr (Or.inl ⟨h,by omega⟩)
  · have hy' : Band ((j-2)+2) y := by simpa [show j-2+2=j by omega] using hy
    exact Or.inr (Or.inr (Or.inl ⟨h,(skip_negative h hy').2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨heq,hx,by rw [hx,special_negative]; omega⟩))

#print axioms positive_safe_parent
#print axioms positive_to_negative
#print axioms skip_negative
#print axioms special_negative
#print axioms negative_parent_partition
#print axioms negative_strip_general
#print axioms negative_run_length
end CapSieve
