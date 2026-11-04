import EvenChild
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- For targets x = 7 mod 8, y = 4 mod 8 and y >= 12, the unique
    direct predecessor is itself outside the entire section map image.
    This is a source-semantic statement independent of any blank seed. -/
theorem seven_four_parent_no_source
    (x y a k u v : Nat)
    (hx : x%8=7) (hy : y%8=4) (hbound : 12≤y)
    (hp : secNext (a,k)=some (x,y)) :
    secNext (u,v) ≠ some (a,k) := by
  have hpar := (even_child_parent_iff a k x y (by omega) (by omega)
      (by omega) (by omega)).mp hp
  rcases hpar with ⟨ha,hk⟩
  intro he
  have him := section_odd_image u v a k he (by omega) (by omega)
  omega

/-- After any two or more section returns from ANY starting state,
    the target rectangle is impossible. No finite-run cutoff is used. -/
theorem seven_four_no_two
    (start : Nat × Nat) (n x y : Nat)
    (hx : x%8=7) (hy : y%8=4) (hbound : 12≤y) :
    BB6.Agent8Section.run secNext (n+2) (some start) ≠ some (x,y) := by
  intro ht
  rw [show n+2=(n+1)+1 by omega] at ht
  change (BB6.Agent8Section.run secNext (n+1) (some start)).bind secNext = some (x,y) at ht
  cases hp : BB6.Agent8Section.run secNext (n+1) (some start) with
  | none => simp [hp] at ht
  | some p =>
      rcases p with ⟨a,k⟩
      have hstep : secNext (a,k)=some (x,y) := by
        simpa [hp] using ht
      change (BB6.Agent8Section.run secNext n (some start)).bind secNext = some (a,k) at hp
      cases hr : BB6.Agent8Section.run secNext n (some start) with
      | none => simp [hr] at hp
      | some r =>
          rcases r with ⟨u,v⟩
          have hprev : secNext (u,v)=some (a,k) := by
            simpa [hr] using hp
          exact (seven_four_parent_no_source x y a k u v hx hy hbound hstep) hprev

/-- Every point has a legal single incoming transition, making the
    universal maximum predecessor depth exactly one. -/
theorem seven_four_one_witness (x y : Nat)
    (hx : x%8=7) (hy : y%8=4) (hbound : 12≤y) :
    secNext (x+y-2,y/2-1)=some (x,y) := by
  apply (even_child_parent_iff (x+y-2) (y/2-1) x y
    (by omega) (by omega) (by omega) (by omega)).mpr
  exact ⟨rfl,rfl⟩

private theorem pow_bound (n : Nat) :
    8*(n+2) ≤ 2^(2*n+4) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have he : 2*(n+1)+4 = (2*n+4)+2 := by omega
      rw [he, Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

private theorem second_k_large (j m k : Nat)
    (hm : 1≤m)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) : 12≤k := by
  have hp : 8*(m+1) ≤ 2^(2*m+2) := by
    cases m with
    | zero => omega
    | succ n =>
      have hh := pow_bound n
      simpa only [show 8*(n+1+1)=8*(n+2) by omega,
        show 2*(n+1)+2=2*n+4 by omega] using hh
  have hh1 : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using
      Nat.mul_le_mul_right j (by omega : 1≤2^(2*m+2))
  have hh2 : 3*(8*(m+1)) ≤ 3*2^(2*m+2) := Nat.mul_le_mul_left 3 hp
  rw [Nat.mul_add] at hgate
  omega

/-- Map a genuine higher Machine C stopping family into the
    no-two-predecessor rectangle by an exact modular argument. -/
theorem seven_four_high_parameter_residues
    (j m k : Nat) (hm : 1≤m) (hj : j%4=2)
    (hjm : (j+m)%8=1)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    (2*j+3)%8=7 ∧ k%8=4 ∧ 12≤k := by
  have hdiv : 8∣2^(2*m+2) := by
    change 2^3∣2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨z,hz⟩ := hdiv
  have hmod : (k+j+3*m+5)%8=0 := by
    have hd : 8 ∣ k+j+3*m+5 := by
      refine ⟨z*(j+3),?_⟩
      calc
        k+j+3*m+5 = 2^(2*m+2)*(j+3) := hgate
        _ = (8*z)*(j+3) := by rw [hz]
        _ = 8*(z*(j+3)) := by ac_rfl
    exact Nat.mod_eq_zero_of_dvd hd
  have hk := second_k_large j m k hm hgate
  omega

private theorem true_first_step :
    secNext (5,1)=some (3,4) := by decide

/-- Entire two-dimensional cone is absent from the actual Machine C
    blank-start orbit, at every section-return time. -/
theorem seven_four_blank_unreachable
    (time x y : Nat) (hx : x%8=7) (hy : y%8=4) (hbound : 12≤y) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (x,y) := by
  cases time with
  | zero =>
      intro ht
      simp [BB6.Agent8Section.run] at ht
      omega
  | succ n =>
      cases n with
      | zero =>
          intro ht
          have hfirst : BB6.Agent8Section.run secNext 1 (some (5,1)) = some (3,4) := by
            simpa [BB6.Agent8Section.run] using true_first_step
          rw [hfirst] at ht
          have heq := Option.some.inj ht
          have hfirstEq := congrArg Prod.fst heq
          omega
      | succ n =>
          simpa only [show n+1+1=n+2 by omega] using
            seven_four_no_two (5,1) n x y hx hy hbound

/-- Every higher stopping input in this full infinite parameter
    cylinder is inaccessible from the true blank-entry section. -/
theorem seven_four_high_stopping_unreachable
    (j m k time : Nat) (hm : 1≤m) (hj : j%4=2)
    (hjm : (j+m)%8=1)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (2*j+3,k) := by
  obtain ⟨hx,hy,hbound⟩ := seven_four_high_parameter_residues j m k hm hj hjm hgate
  exact seven_four_blank_unreachable time (2*j+3) k hx hy hbound

#print axioms seven_four_no_two
#print axioms seven_four_one_witness
#print axioms seven_four_blank_unreachable
#print axioms seven_four_high_stopping_unreachable

end BB6.Agent3
