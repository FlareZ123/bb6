import Std

namespace F119ModularCore

/-- Generic tag-one section formulas, for h,t≥0 (t>0 for r=1). -/
def input (h t r : Nat) : Nat := 3^h * (3*t+r)
def output (h t r : Nat) : Nat := (3^(h+1)+1)*t + 3^h*r + h + 3 + (if r=2 then 1 else 0)

theorem affine_one (h t : Nat) :
    3^(h+1) * output h t 1 = (3^(h+1)+1) * input h t 1 + 3^h*(3*h+8) := by
  simp [input, output, Nat.pow_succ]
  grind

theorem affine_two (h t : Nat) :
    3^(h+1) * output h t 2 = (3^(h+1)+1) * input h t 2 + 3^h*(3*h+10) := by
  simp [input, output, Nat.pow_succ]
  grind

/-- The generic formula is affine in the free quotient t. -/
theorem input_shift (h t r L : Nat) : input h (t+L) r = input h t r + 3^(h+1)*L := by
  simp [input, Nat.pow_succ]
  grind

theorem output_shift (h t r L : Nat) : output h (t+L) r = output h t r + (3^(h+1)+1)*L := by
  simp [output]
  grind

/-- Binary digit weights with arbitrary odd multipliers can realize every
    residue modulo 2^n. This is the finite lifting core of the odd h maps. -/
inductive Digits (w : Nat → Nat) : Nat → Nat → Prop
  | nil : Digits w 0 0
  | zero {n x} : Digits w n x → Digits w (n+1) x
  | one {n x} : Digits w n x → Digits w (n+1) (x+2^n*w n)

theorem shift_toggle (m x w : Nat) (hm : 0 < m) (hw : w%2=1) :
    (x+m*w)%(2*m) = if x%(2*m)<m then x%(2*m)+m else x%(2*m)-m := by
  have he : w = 2*(w/2)+1 := by omega
  have hh : m*w = (2*m)*(w/2)+m := by rw [he]; grind
  rw [hh]
  have hr : (x+(2*m)*(w/2)+m)%(2*m) = (x+m)%(2*m) := by
    rw [show x+(2*m)*(w/2)+m = x+m+(2*m)*(w/2) by omega]
    simp [Nat.add_mod]
  rw [← Nat.add_assoc, hr, Nat.add_mod]
  have hm' : m%(2*m)=m := Nat.mod_eq_of_lt (by omega)
  rw [hm']
  have hx := Nat.mod_lt x (show 0<2*m by omega)
  split <;> rename_i h
  · exact Nat.mod_eq_of_lt (by omega)
  · rw [Nat.mod_eq_sub_mod (by omega : 2*m ≤ x%(2*m)+m)]
    rw [show x%(2*m)+m-2*m = x%(2*m)-m by omega]
    exact Nat.mod_eq_of_lt (by omega)

theorem digits_cover (w : Nat → Nat) (hw : ∀ j, w j % 2 = 1) (n target : Nat) :
    ∃ x, Digits w n x ∧ x % (2^n) = target % (2^n) := by
  induction n with
  | zero => exact ⟨0, .nil, by simp [Nat.mod_one]⟩
  | succ n ih =>
    obtain ⟨x,hx,he⟩ := ih
    let m := 2^n
    have hm : 0<m := Nat.pow_pos (by decide)
    have hmod : 2^(n+1)=2*m := by simp [m,Nat.pow_succ,Nat.mul_comm]
    by_cases same : x%(2*m)=target%(2*m)
    · exact ⟨x,.zero hx,by rw [hmod,same]⟩
    · refine ⟨x+m*w n, .one hx, ?_⟩
      rw [hmod,shift_toggle m x (w n) hm (hw n)]
      have hxlt := Nat.mod_lt x (show 0<2*m by omega)
      have hylt := Nat.mod_lt target (show 0<2*m by omega)
      have hxred : (x%(2*m))%m=x%m := Nat.mod_mod_of_dvd x ⟨2,by omega⟩
      have hyred : (target%(2*m))%m=target%m := Nat.mod_mod_of_dvd target ⟨2,by omega⟩
      change x%m=target%m at he
      have hh : (x%(2*m))%m=(target%(2*m))%m := hxred.trans (he.trans hyred.symm)
      by_cases hxx : x%(2*m)<m <;> by_cases hyy : target%(2*m)<m
      · rw [Nat.mod_eq_of_lt hxx,Nat.mod_eq_of_lt hyy] at hh; contradiction
      · rw [Nat.mod_eq_of_lt hxx,Nat.mod_eq_sub_mod (by omega : m≤target%(2*m)),Nat.mod_eq_of_lt (by omega : target%(2*m)-m<m)] at hh
        simp [hxx]; omega
      · rw [Nat.mod_eq_sub_mod (by omega : m≤x%(2*m)),Nat.mod_eq_of_lt (by omega : x%(2*m)-m<m),Nat.mod_eq_of_lt hyy] at hh
        simp [hxx]; omega
      · rw [Nat.mod_eq_sub_mod (by omega : m≤x%(2*m)),Nat.mod_eq_of_lt (by omega : x%(2*m)-m<m),Nat.mod_eq_sub_mod (by omega : m≤target%(2*m)),Nat.mod_eq_of_lt (by omega : target%(2*m)-m<m)] at hh
        omega

#print axioms affine_one
#print axioms affine_two
#print axioms digits_cover
end F119ModularCore
