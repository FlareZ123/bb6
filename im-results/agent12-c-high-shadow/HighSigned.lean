import SignedCone
import Lean.Elab.Tactic.Omega

namespace BB6.Agent12SignedCone
open BB6.Agent12HighShadow

def highOffset (j m : Nat) : Offset := ⟨2*(j:Int)+3,-((j:Int)+3*(m:Int)+5)⟩
def highExcluded (f j m : Nat) : Bool :=
  decide (2≤j ∧ 2≤m) && check f (bits m) (highOffset j m)

private theorem high_rep (j m k : Nat) (hj : 2≤j)
    (hstop : k+j+3*m+5=2^(bits m)*(j+3)) :
    Rep (bits m) (2*j+3) k (highOffset j m) := by
  refine ⟨0,(j:Int)+3,by omega,by omega,Or.inr ?_,?_,?_⟩
  · unfold highOffset; dsimp; omega
  · unfold highOffset; simp
  · unfold highOffset; dsimp
    have hs : (k:Int)+(j:Int)+3*(m:Int)+5=p (bits m)*((j:Int)+3) := by
      exact congrArg Int.ofNat hstop
    omega

theorem highExcluded_sound (reach : Nat → Nat → Prop)
    (parent : ParentContract reach)
    (forbid : ∀ x y, 5≤y → y%2=1 → ((x+y)%4=1 ∨ (x+y)%4=2) → ¬reach x y)
    (f j m k : Nat) (h : highExcluded f j m=true)
    (hstop : k+j+3*m+5=2^(bits m)*(j+3)) : ¬reach (2*j+3) k := by
  simp only [highExcluded,Bool.and_eq_true,decide_eq_true_eq] at h
  exact check_sound reach parent forbid f (bits m) (2*j+3) k (highOffset j m) h.2
    (high_rep j m k h.1.1 hstop)

/-- A centered representative uses only the chosen precision, never
    the full exponent 2m+2 unless the caller chooses it. -/
def centered (r : Nat) (z : Int) : Int :=
  let t:=z%p r
  if 2*t<p r then t else t-p r

private theorem ppos (r : Nat) : 0<p r := Int.pow_pos (by decide)
private theorem pcast (r : Nat) : p r=(↑((2:Nat)^r):Int) := by simp [p]
private theorem pdvd (b r : Nat) (h : r≤b) : p r∣p b := by
  refine ⟨p (b-r),?_⟩
  unfold p
  rw [←Int.pow_add]
  congr 1
  omega

private theorem centered_lt (r : Nat) (z : Int) : centered r z<p r := by
  have ht := Int.emod_lt_of_pos z (ppos r)
  unfold centered
  dsimp
  split <;> omega

private theorem centered_dvd (r : Nat) (z : Int) : p r∣z-centered r z := by
  unfold centered
  dsimp
  have he := Int.emod_add_mul_ediv z (p r)
  split
  · exact ⟨z/p r,by omega⟩
  · refine ⟨z/p r+1,?_⟩
    rw [Int.mul_add,Int.mul_one]
    omega

private theorem centered_periodic (r : Nat) (z w : Int) (h : p r∣w-z) :
    centered r w=centered r z := by
  have hmod := Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd h)
  unfold centered
  rw [hmod]

/-- Congruence plus size replaces explicit coefficients at the entrance. -/
theorem rep_of_congruence (r x y : Nat) (s : Offset)
    (hx : 5<x) (hy : p r≤(y:Int)) (hsx : s.x<p r) (hsy : s.y<p r)
    (h1 : p r∣(x:Int)-s.x) (h2 : p r∣(y:Int)-s.y) : Rep r x y s := by
  obtain ⟨A,hA⟩ := h1
  obtain ⟨B,hB⟩ := h2
  have hA0 : 0≤A := by
    by_cases hn : 0≤A
    · exact hn
    · have hneg : A≤ -1 := by omega
      have hh := Int.mul_le_mul_of_nonneg_left hneg (Int.le_of_lt (ppos r))
      simp at hh
      omega
  have hB1 : 1≤B := by
    by_cases hn : 1≤B
    · exact hn
    · have hh := Int.mul_le_mul_of_nonneg_left (show B≤0 by omega) (Int.le_of_lt (ppos r))
      simp at hh
      omega
  have hleft : 1≤A ∨ 5<s.x := by
    by_cases h : 1≤A
    · exact Or.inl h
    · have ha : A=0 := by omega
      subst A
      simp at hA
      omega
  exact ⟨A,B,hA0,hB1,hleft,by omega,by omega⟩

private theorem high_k_bound (j m k : Nat) (hj : 2≤j)
    (hstop : k+j+3*m+5=2^(bits m)*(j+3)) : 2^(bits m)≤k := by
  have hp : ∀ m : Nat, 3*m+4≤2^(bits m) := by
    intro m
    induction m with
    | zero => decide
    | succ m ih =>
      rw [show bits (m+1)=bits m+2 by unfold bits; omega,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega
  have hmul := Nat.mul_le_mul_right (j+2) (hp m)
  have he : 2^(bits m)*(j+3)=2^(bits m)*(j+2)+2^(bits m) := by
    rw [show j+3=j+2+1 by omega,Nat.mul_add,Nat.mul_one]
  have hlin : (3*m+4)*(j+2)≥j+3*m+5 := by
    rw [Nat.mul_add]
    have hh := Nat.mul_le_mul_right j (show 1≤3*m+4 by omega)
    omega
  omega

def adaptiveOffset (r j m : Nat) : Offset :=
  ⟨centered r (2*(j:Int)+3),centered r (-((j:Int)+3*(m:Int)+5))⟩
def adaptiveExcluded (f r j m : Nat) : Bool :=
  decide (2≤j ∧ 2≤m ∧ r≤bits m) && check f r (adaptiveOffset r j m)

private theorem adaptive_rep (r j m k : Nat) (hj : 2≤j) (hr : r≤bits m)
    (hstop : k+j+3*m+5=2^(bits m)*(j+3)) :
    Rep r (2*j+3) k (adaptiveOffset r j m) := by
  apply rep_of_congruence r (2*j+3) k (adaptiveOffset r j m) (by omega)
  · rw [pcast]
    apply Int.ofNat_le.mpr
    exact Nat.le_trans (Nat.pow_le_pow_right (by decide) hr) (high_k_bound j m k hj hstop)
  · exact centered_lt _ _
  · exact centered_lt _ _
  · change p r∣2*(j:Int)+3-centered r (2*(j:Int)+3)
    exact centered_dvd _ _
  · have hs : (k:Int)+(j:Int)+3*(m:Int)+5=p (bits m)*((j:Int)+3) := by
      exact congrArg Int.ofNat hstop
    have hd := Int.dvd_trans (pdvd (bits m) r hr) (Int.dvd_mul_right (p (bits m)) ((j:Int)+3))
    have hcenter := centered_dvd r (-((j:Int)+3*(m:Int)+5))
    have he : (k:Int)-(adaptiveOffset r j m).y = p (bits m)*((j:Int)+3) +
        (-((j:Int)+3*(m:Int)+5)-centered r (-((j:Int)+3*(m:Int)+5))) := by
      unfold adaptiveOffset; dsimp; omega
    rw [he]
    exact Int.dvd_add hd hcenter

theorem adaptiveExcluded_sound (reach : Nat → Nat → Prop)
    (parent : ParentContract reach)
    (forbid : ∀ x y, 5≤y → y%2=1 → ((x+y)%4=1 ∨ (x+y)%4=2) → ¬reach x y)
    (f r j m k : Nat) (h : adaptiveExcluded f r j m=true)
    (hstop : k+j+3*m+5=2^(bits m)*(j+3)) : ¬reach (2*j+3) k := by
  simp only [adaptiveExcluded,Bool.and_eq_true,decide_eq_true_eq] at h
  exact check_sound reach parent forbid f r (2*j+3) k (adaptiveOffset r j m) h.2
    (adaptive_rep r j m k h.1.1 h.1.2.2 hstop)

/-- Every accepted finite branching certificate transfers to the whole
    parameter rectangle with independently periodic j and m. -/
theorem adaptive_lift (f r j m u v : Nat) (h : adaptiveExcluded f r j m=true) :
    adaptiveExcluded f r (j+2^r*u) (m+2^r*v)=true := by
  simp only [adaptiveExcluded,Bool.and_eq_true,decide_eq_true_eq] at h ⊢
  refine ⟨⟨by omega,by omega,?_⟩,?_⟩
  · have hh := h.1.2.2
    unfold bits at *
    omega
  have he : adaptiveOffset r (j+2^r*u) (m+2^r*v)=adaptiveOffset r j m := by
    unfold adaptiveOffset
    congr 1
    · apply centered_periodic
      refine ⟨2*(u:Int),?_⟩
      rw [pcast,show (↑(j+2^r*u):Int)=(j:Int)+(↑((2:Nat)^r):Int)*(u:Int) by rfl]
      have hh : (↑((2:Nat)^r):Int)*(2*(u:Int))=2*((↑((2:Nat)^r):Int)*(u:Int)) := by ac_rfl
      omega
    · apply centered_periodic
      refine ⟨-((u:Int)+3*(v:Int)),?_⟩
      rw [pcast,show (↑(j+2^r*u):Int)=(j:Int)+(↑((2:Nat)^r):Int)*(u:Int) by rfl,
        show (↑(m+2^r*v):Int)=(m:Int)+(↑((2:Nat)^r):Int)*(v:Int) by rfl]
      simp only [Int.mul_neg,Int.mul_add]
      have hh : (↑((2:Nat)^r):Int)*(3*(v:Int))=3*((↑((2:Nat)^r):Int)*(v:Int)) := by ac_rfl
      omega
  rw [he]
  exact h.2

/-- Coupled shifts preserve both signed offsets; independent rectangles
    are only a special case of this parameter lattice. -/
theorem adaptive_lattice_lift (f r j m u v : Nat) (h : adaptiveExcluded f r j m=true)
    (hu : p r∣2*(u:Int)) (hv : p r∣(u:Int)+3*(v:Int)) :
    adaptiveExcluded f r (j+u) (m+v)=true := by
  simp only [adaptiveExcluded,Bool.and_eq_true,decide_eq_true_eq] at h ⊢
  refine ⟨⟨by omega,by omega,?_⟩,?_⟩
  · have hh:=h.1.2.2; unfold bits at *; omega
  have he : adaptiveOffset r (j+u) (m+v)=adaptiveOffset r j m := by
    unfold adaptiveOffset
    congr 1
    · apply centered_periodic
      have hh : 2*((j+u:Nat):Int)+3-(2*(j:Int)+3)=2*(u:Int) := by omega
      rwa [hh]
    · apply centered_periodic
      have hh : -(((j+u:Nat):Int)+3*((m+v:Nat):Int)+5) -
          (-((j:Int)+3*(m:Int)+5))= -((u:Int)+3*(v:Int)) := by omega
      rw [hh,Int.dvd_neg]
      exact hv
  rw [he]
  exact h.2

/-- Example genuinely outside j<=3m at the seed and not a forced
    single-parent path: its two first branches end in forbidden leaves. -/
theorem branching_seed : adaptiveExcluded 2 10 40 5=true := by decide

theorem branching_diagonal (t : Nat) : adaptiveExcluded 2 10 (40+512*t) (5+512*t)=true := by
  apply adaptive_lattice_lift _ _ _ _ _ _ branching_seed
  · refine ⟨(t:Int),?_⟩
    change 2*((512*t:Nat):Int)=1024*(t:Int)
    omega
  · refine ⟨2*(t:Int),?_⟩
    change ((512*t:Nat):Int)+3*((512*t:Nat):Int)=1024*(2*(t:Int))
    omega

#print axioms adaptive_lattice_lift
#print axioms branching_diagonal
#print axioms highExcluded_sound
#print axioms rep_of_congruence
#print axioms adaptiveExcluded_sound
#print axioms adaptive_lift
end BB6.Agent12SignedCone
