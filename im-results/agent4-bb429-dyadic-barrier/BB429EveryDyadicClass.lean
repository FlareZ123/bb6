import BB429DyadicStarts
import Lean.Elab.Tactic.Omega

namespace BB429EveryDyadicClass

/-- The base-four geometric sum, computed without division. -/
def geom : Nat → Nat
  | 0 => 0
  | k+1 => 4*geom k + 1

private theorem geom_id (k : Nat) : 3*geom k + 1 = 4^k := by
  induction k with
  | zero => decide
  | succ k ih =>
      change 3*(4*geom k+1)+1 = 4^(k+1)
      rw [Nat.pow_succ]
      omega

def height (k C : Nat) : Nat :=
  C*geom k + (C+k+1)*4^k

private theorem height_cost (k C : Nat) :
    3*height k C + C = (4*C+3*k+3)*4^k := by
  unfold height
  calc
    3*(C*geom k+(C+k+1)*4^k)+C =
      C*(3*geom k+1)+3*(C+k+1)*4^k := by
        simp only [Nat.mul_add, Nat.add_mul]
        ac_rfl
    _ = C*4^k+3*(C+k+1)*4^k := by rw [geom_id]
    _ = (C+3*(C+k+1))*4^k := by rw [Nat.add_mul]
    _ = (4*C+3*k+3)*4^k := by
      have hc : C+3*(C+k+1)=4*C+3*k+3 := by omega
      rw [hc]

private theorem height_large (k C : Nat) : C + k + 1 ≤ height k C := by
  unfold height
  have hp : 0<4^k := Nat.pow_pos (by decide)
  have hb : C+k+1 ≤ (C+k+1)*4^k := by
    calc
      C+k+1 = (C+k+1)*1 := by omega
      _ ≤ (C+k+1)*4^k := Nat.mul_le_mul_left _ (by omega)
  omega

private theorem power_big (n : Nat) : n+1 ≤ 2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.pow_succ]
      omega

private theorem four_exponential_bound (u C n : Nat) (h : C ≤ n) :
    3*n+C ≤ 4*(u+3)*2^n := by
  have hp := power_big n
  have hu : 0≤u := Nat.zero_le u
  -- nonlinear multiplication by (u+3) is monotone, isolate the term
  have hx : 12*2^n ≤ 4*(u+3)*2^n := by
    have hh : 12 ≤ 4*(u+3) := by omega
    exact Nat.mul_le_mul_right (2^n) hh
  omega

def initialC (u w : Nat) : Nat := 2*u+w+13

def demand (k u w : Nat) : Nat :=
  4*(u+3)*2^(height k (initialC u w)) -
    (2*u+3*height k (initialC u w)+13)

private theorem demand_identity (k u w : Nat) :
    demand k u w + 2*u+3*height k (initialC u w)+13 =
      4*(u+3)*2^(height k (initialC u w)) := by
  unfold demand
  have hh : initialC u w ≤ height k (initialC u w) := by
    have x:=height_large k (initialC u w)
    omega
  have hb := four_exponential_bound u (initialC u w)
      (height k (initialC u w)) hh
  dsimp [initialC] at *
  omega

private theorem demand_ge_w (k u w : Nat) : w ≤ demand k u w := by
  have hh : initialC u w ≤ height k (initialC u w) := by
    have x:=height_large k (initialC u w)
    omega
  have hb := four_exponential_bound u (initialC u w)
      (height k (initialC u w)) hh
  have he:=demand_identity k u w
  dsimp [initialC] at *
  omega

private theorem power_four_multiple (k : Nat) : 2^k ∣ 4^k := by
  have h : 4^k=2^k*2^k := by
    calc
      4^k=(2*2)^k := by rfl
      _=2^k*2^k := by rw [Nat.mul_pow]
  rw [h]
  exact Nat.dvd_mul_right _ _

private theorem demand_mod (k u w : Nat) :
    demand k u w % (2^k) = w % (2^k) := by
  let C:=initialC u w
  let n:=height k C
  have hn : k ≤ n := by
    have h:=height_large k C
    omega
  have hp : 2^k ∣ 2^n := Nat.pow_dvd_pow 2 hn
  have hfirst : 2^k ∣ 4*(u+3)*2^n := by
    obtain ⟨j,hj⟩ := hp
    refine ⟨4*(u+3)*j, ?_⟩
    rw [hj]
    ac_rfl
  have hsecond : 2^k ∣ 3*n+C := by
    have hm := height_cost k C
    have hmul : 2^k ∣ 4^k := power_four_multiple k
    have hfactor : 4^k ∣ 3*n+C := by
      rw [hm]
      exact Nat.dvd_mul_left _ _
    exact Nat.dvd_trans hmul hfactor
  have he : demand k u w - w = 4*(u+3)*2^n - (3*n+C) := by
    have hid := demand_identity k u w
    have hb := demand_ge_w k u w
    dsimp [C,n,initialC] at *
    omega
  have hd : 2^k ∣ demand k u w - w := by
    rw [he]
    exact Nat.dvd_sub hfirst hsecond
  have hw := demand_ge_w k u w
  have heq : demand k u w = w+(demand k u w-w) := by omega
  rw [heq, Nat.add_mod, Nat.mod_eq_zero_of_dvd hd]
  simp

/-- Each dyadic residue class has a synthetically halting accelerated state. -/
theorem every_dyadic_class_has_halting_start (k u w : Nat) :
    ∃ W n a b,
      W % (2^k) = w % (2^k) ∧
      BB429.run n (u,W) = some (a,b) ∧
      BB429.next (a,b) = none := by
  let n := height k (initialC u w)
  let W := demand k u w
  have he : 2*u+W+3*n+13 = 4*((u+3)*2^n) := by
    have hh:=demand_identity k u w
    dsimp [n,W]
    simp only [Nat.mul_assoc] at hh ⊢
    omega
  obtain ⟨m,a,b,hr,hgate⟩ :=
    (BB429Burst.burst_gateway_iff u W).mpr ⟨n,he⟩
  exact ⟨W,m,a,b,demand_mod k u w,
    BB429DyadicStarts.first_prefix_is_source _ _ _ hr,
    (BB429.next_none_iff_halt_line a b).mpr hgate⟩

/-- Every entire dyadic residue cylinder contains a synthetic halting start.
    Hence no nonempty dyadic-congruence-saturated inductive invariant of the
    complete source map can exclude every halting state. -/
theorem no_nonempty_dyadic_haltfree_invariant
    (k u w : Nat) (P : Nat × Nat → Prop)
    (hmod : ∀ x y, x.1%(2^k)=y.1%(2^k) →
        x.2%(2^k)=y.2%(2^k) → P x → P y)
    (hinit : P (u,w))
    (hstep : ∀ x y, P x → BB429.next x = some y → P y)
    (hhalt : ∀ x, P x → BB429.next x ≠ none) : False := by
  obtain ⟨W,n,a,b,heq,hr,hn⟩ := every_dyadic_class_has_halting_start k u w
  have hseed : P (u,W) := by
    apply hmod (u,w) (u,W)
    · simp
    · exact heq.symm
    · exact hinit
  have hrun : ∀ (m : Nat) (s t : Nat × Nat), P s →
      BB429.run m s = some t → P t := by
    intro m
    induction m with
    | zero =>
        intro s t hs ht
        simp [BB429.run] at ht
        simpa [ht] using hs
    | succ m ih =>
        intro s t hs ht
        simp only [BB429.run] at ht
        cases hp : BB429.run m s with
        | none => simp [hp] at ht
        | some p =>
            simp only [hp, Option.bind_some] at ht
            exact hstep p t (ih s p hs hp) ht
  exact hhalt (a,b) (hrun n (u,W) (a,b) hseed hr) hn

#print axioms every_dyadic_class_has_halting_start
#print axioms no_nonempty_dyadic_haltfree_invariant
end BB429EveryDyadicClass
