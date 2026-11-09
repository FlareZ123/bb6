import Lean.Elab.Tactic.Omega

namespace BB6.Agent11Tower

/-- Right counter of the depth-n positive-density cylinder. -/
def b (t : Nat) : Nat → Nat
| 0 => 4*t+5
| n+1 => 2*b t n+2

/-- Periodic left-counter phase ensuring successive forced direct parents. -/
def xr : Nat → Nat
| 0 => 1
| 1 => 7
| 2 => 7
| n+3 => 10-xr (n+2)

theorem b_mod4_after_two (n t : Nat) : (b t (n+2))%4=2 := by
  induction n with
  | zero => simp [b]; omega
  | succ n ih =>
      change (2*b t (n+2)+2)%4=2
      omega

theorem xr_after_two (n : Nat) : xr (n+2)=3 ∨ xr (n+2)=7 := by
  induction n with
  | zero => simp [xr]
  | succ n ih =>
      change (10-xr (n+2)=3 ∨ 10-xr (n+2)=7)
      omega

theorem phase_step (n t x : Nat) (hx : x%8=xr (n+1)) :
    (x+2*b t n)%8=xr n := by
  cases n with
  | zero =>
      have hb : b t 0 %4 = 1 := by simp [b]
      simp only [xr] at hx ⊢
      omega
  | succ n =>
      cases n with
      | zero =>
          have hb : b t 1 %4=0 := by simp only [b]; omega
          change x%8=7 at hx
          change (x+2*b t 1)%8=7
          omega
      | succ m =>
          have hb := b_mod4_after_two m t
          have hxr := xr_after_two m
          change x%8=xr (m+3) at hx
          change (x+2*b t (m+2))%8=xr (m+2)
          change x%8=10-xr (m+2) at hx
          omega

/-- The missing-image endpoint is reached after n forced inverses. -/
def cone : Nat → Nat × Nat → Prop
| 0, (x,y) => 5≤y ∧ y%2=1 ∧ (x+y)%4=2
| n+1, (x,y) =>
  6≤y ∧ y%2=0 ∧
  ((x+y)%8=1 ∨ (x+y)%8=3 ∨ (x+y)%8=5) ∧
  cone n (x+y-2,(y-2)/2)

theorem b_ge_five (n t : Nat) : 5≤b t n := by
  induction n with
  | zero => simp [b]
  | succ n ih =>
      change 5≤2*b t n+2
      omega

theorem xr_good (n : Nat) : xr n = 1 ∨ xr n = 3 ∨ xr n = 7 := by
  cases n with
  | zero => simp [xr]
  | succ n =>
      cases n with
      | zero => simp [xr]
      | succ n =>
          obtain h3 | h7 := xr_after_two n
          · right; left; exact h3
          · right; right; exact h7

/-- An explicit, two-parameter image-difference cone at every depth. -/
theorem cylinder_cone (n t x : Nat)
    (hx : 8≤x) (hres : x%8=xr n) : cone n (x,b t n) := by
  induction n generalizing x with
  | zero =>
      change 5≤b t 0 ∧ (b t 0)%2=1 ∧ (x+b t 0)%4=2
      have hb : b t 0=4*t+5 := rfl
      have hr : xr 0=1 := rfl
      rw [hb]
      constructor
      · omega
      constructor
      · omega
      · rw [hr] at hres
        omega
  | succ n ih =>
      have hy : 6≤b t (n+1) := by
        change 6≤2*b t n+2
        have hm := b_ge_five n t
        omega
      have he : (b t (n+1))%2=0 := by
        change (2*b t n+2)%2=0
        omega
      have hp := phase_step n t x hres
      have hr := xr_good n
      have hs : (x+b t (n+1))%8=1 ∨
        (x+b t (n+1))%8=3 ∨
        (x+b t (n+1))%8=5 := by
        change (x+2*b t n+2)%8=1 ∨
          (x+2*b t n+2)%8=3 ∨
          (x+2*b t n+2)%8=5
        omega
      change 6≤b t (n+1) ∧ (b t (n+1))%2=0 ∧
        ((x+b t (n+1))%8=1 ∨
         (x+b t (n+1))%8=3 ∨
         (x+b t (n+1))%8=5) ∧
        cone n (x+b t (n+1)-2,((b t (n+1))-2)/2)
      refine ⟨hy,he,hs,?_⟩
      have hleft : x+b t (n+1)-2=x+2*b t n := by
        change x+(2*b t n+2)-2=x+2*b t n
        omega
      have hright : (b t (n+1)-2)/2=b t n := by
        change ((2*b t n+2)-2)/2=b t n
        omega
      rw [hleft,hright]
      exact ih (x+2*b t n) (by omega) hp

/-- Each depth is a whole positive-density right-counter progression. -/
theorem b_closed (n t : Nat) : b t n + 2 = (4*t+7)*2^n := by
  induction n with
  | zero => simp [b]
  | succ n ih =>
      change 2*b t n+2+2=(4*t+7)*2^(n+1)
      calc
        2*b t n+2+2 = 2*(b t n+2) := by omega
        _ = 2*((4*t+7)*2^n) := by rw [ih]
        _ = (4*t+7)*2^(n+1) := by rw [Nat.pow_succ]; ac_rfl

#print axioms cylinder_cone
#print axioms b_closed
end BB6.Agent11Tower
