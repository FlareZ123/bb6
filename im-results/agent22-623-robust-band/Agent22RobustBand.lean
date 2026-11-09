import Std

namespace BB6Robust

/-! Standalone exact ternary failure-band theorem.
The recurrence is an independent copy of Agent49's source-certified
"badAll" predicate. The source bridge is in RobustBandSource.lean. -/

def bad (a b : Nat) : Bool :=
  if b=0 then false
  else if b%3=0 then bad (a+1) (b/3-1)
  else if b%3=1 then
    if a=0 then true else bad (a-1) (b/3)
  else if a=0 then bad 0 (b/3)
  else bad (a-1) (b/3+1)
termination_by b
decreasing_by all_goals omega

def u : Nat → Nat
  | 0 => 0
  | n+1 => 3*u n+1

private theorem b1 (a n : Nat) (ha : a>0) :
    bad a (3*u n+1) = bad (a-1) (u n) := by
  rw [bad]
  have hb : 3*u n+1 ≠ 0 := by omega
  have h0 : (3*u n+1)%3≠0 := by omega
  have h1 : (3*u n+1)%3=1 := by omega
  have hn : (3*u n+1)/3 = u n := by omega
  simp only [if_neg hb, if_neg h0, if_pos h1, if_neg (by omega : a≠0),hn]

private theorem b10 (n : Nat) : bad 0 (3*u n+1)=true := by
  rw [bad]
  have hb : 3*u n+1 ≠ 0 := by omega
  have h0 : (3*u n+1)%3≠0 := by omega
  have h1 : (3*u n+1)%3=1 := by omega
  simp only [if_neg hb, if_neg h0, if_pos h1]
  rfl

private theorem b2 (a n : Nat) (ha : a>0) :
    bad a (3*u n+2) = bad (a-1) (u n+1) := by
  rw [bad]
  have hb : 3*u n+2 ≠ 0 := by omega
  have h0 : (3*u n+2)%3≠0 := by omega
  have h1 : (3*u n+2)%3≠1 := by omega
  have hn : (3*u n+2)/3 = u n := by omega
  simp only [if_neg hb, if_neg h0, if_neg h1, if_neg (by omega : a≠0),hn]

private theorem b20 (n : Nat) : bad 0 (3*u n+2) = bad 0 (u n) := by
  rw [bad]
  have hb : 3*u n+2 ≠ 0 := by omega
  have h0 : (3*u n+2)%3≠0 := by omega
  have h1 : (3*u n+2)%3≠1 := by omega
  have hn : (3*u n+2)/3 = u n := by omega
  simp only [if_neg hb, if_neg h0, if_neg h1, hn]
  rfl

theorem boundary_fatal (n a : Nat) (ha : a<n) : bad a (u n) = true := by
  induction n generalizing a with
  | zero => omega
  | succ n ih =>
    rw [u]
    by_cases hz : a=0
    · subst a
      exact b10 n
    · rw [b1 a n (by omega)]
      exact ih (a-1) (by omega)

theorem boundary_plus_fatal (n a : Nat) (ha : a+1<n) :
    bad a (u n+1) = true := by
  induction n generalizing a with
  | zero => omega
  | succ n ih =>
    rw [u]
    by_cases hz : a=0
    · subst a
      rw [show 3*u n+1+1=3*u n+2 by omega,b20]
      exact boundary_fatal n 0 (by omega)
    · rw [show 3*u n+1+1=3*u n+2 by omega,b2 a n (by omega)]
      exact ih (a-1) (by omega)

private theorem digit_one_pos (a v : Nat) (ha : 0<a) :
    bad a (3*v+1) = bad (a-1) v := by
  rw [bad]
  have hb : 3*v+1≠0 := by omega
  have h0 : (3*v+1)%3≠0 := by omega
  have h1 : (3*v+1)%3=1 := by omega
  have hdiv : (3*v+1)/3 = v := by omega
  simp only [if_neg hb, if_neg h0, if_pos h1, if_neg (by omega : a≠0),hdiv]

private theorem digit_one_zero (v : Nat) : bad 0 (3*v+1)=true := by
  rw [bad]
  have hb : 3*v+1≠0 := by omega
  have h0 : (3*v+1)%3≠0 := by omega
  have h1 : (3*v+1)%3=1 := by omega
  simp only [if_neg hb, if_neg h0, if_pos h1]
  rfl

private theorem digit_two_pos (a v : Nat) (ha : 0<a) :
    bad a (3*v+2) = bad (a-1) (v+1) := by
  rw [bad]
  have hb : 3*v+2≠0 := by omega
  have h0 : (3*v+2)%3≠0 := by omega
  have h1 : (3*v+2)%3≠1 := by omega
  have hdiv : (3*v+2)/3 = v := by omega
  simp only [if_neg hb, if_neg h0, if_neg h1, if_neg (by omega : a≠0),hdiv]

private theorem digit_two_zero (v : Nat) : bad 0 (3*v+2)=bad 0 v := by
  rw [bad]
  have hb : 3*v+2≠0 := by omega
  have h0 : (3*v+2)%3≠0 := by omega
  have h1 : (3*v+2)%3≠1 := by omega
  have hdiv : (3*v+2)/3 = v := by omega
  simp only [if_neg hb, if_neg h0, if_neg h1,hdiv]
  rfl

private theorem digit_zero (a v : Nat) (hv : 0<v) :
    bad a (3*v) = bad (a+1) (v-1) := by
  rw [bad]
  have hb : 3*v≠0 := by omega
  have h0 : (3*v)%3=0 := by omega
  have hdiv : (3*v)/3-1 = v-1 := by omega
  simp only [if_neg hb, if_pos h0,hdiv]

/-- All first counters in the indicated interval fail for an unbounded
exponential band of block counts just above the ternary-ones boundary. -/
theorem band_fatal (k : Nat) : ∀ n a e : Nat,
    a+2*k+2 ≤ n → e ≤ 3^k → bad a (u n+e) = true := by
  induction k with
  | zero =>
      intro n a e hn he
      have he' : e=0 ∨ e=1 := by simp at he; omega
      rcases he' with hzero | hone
      · subst e
        simpa only [Nat.add_zero] using boundary_fatal n a (by omega)
      · subst e
        exact boundary_plus_fatal n a (by omega)
  | succ k ih =>
      intro n a e hn he
      cases n with
      | zero => omega
      | succ n =>
          have hp : 3^(k+1) = 3*3^k := by simp [Nat.pow_succ, Nat.mul_comm]
          have hrem : e = 3*(e/3)+e%3 := by omega
          have hq : e/3 ≤ 3^k := by omega
          by_cases hr0 : e%3=0
          · have harg : u (n+1)+e = 3*(u n+e/3)+1 := by rw [u]; omega
            rw [harg]
            by_cases ha0 : a=0
            · subst a
              exact digit_one_zero _
            · rw [digit_one_pos a _ (by omega)]
              exact ih n (a-1) (e/3) (by omega) hq
          · by_cases hr1 : e%3=1
            · have harg : u (n+1)+e = 3*(u n+e/3)+2 := by rw [u]; omega
              rw [harg]
              by_cases ha0 : a=0
              · subst a
                rw [digit_two_zero]
                exact ih n 0 (e/3) (by omega) hq
              · rw [digit_two_pos a _ (by omega)]
                have hplus : u n+e/3+1=u n+(e/3+1) := by omega
                rw [hplus]
                have hqp : e/3+1 ≤ 3^k := by omega
                exact ih n (a-1) (e/3+1) (by omega) hqp
            · have hr2 : e%3=2 := by omega
              have harg : u (n+1)+e = 3*(u n+e/3+1) := by rw [u]; omega
              rw [harg,digit_zero a (u n+e/3+1) (by omega)]
              have hreduce : u n+e/3+1-1=u n+e/3 := by omega
              rw [hreduce]
              exact ih n (a+1) (e/3) (by omega) hq

/-- An explicit linear subfamily consumed by the exponential band. -/
theorem linear_exponential (q : Nat) (hq : 4 ≤ q) :
    8*q+26 ≤ 3^q := by
  induction q with
  | zero => omega
  | succ q ih =>
      by_cases hq4 : 4 ≤ q
      · have h := ih hq4
        rw [Nat.pow_succ]
        omega
      · have hq3 : q=3 := by omega
        subst q
        decide

theorem linear_band_fatal (q : Nat) (hq : 1 ≤ q) :
    bad 3 (u (2*q+5) + (8*q+26)) = true := by
  by_cases hq4 : 4 ≤ q
  · exact band_fatal q (2*q+5) 3 (8*q+26) (by omega)
      (linear_exponential q hq4)
  · have he : q=1 ∨ q=2 ∨ q=3 := by omega
    rcases he with h1 | h2 | h3
    · subst q
      decide +kernel
    · subst q
      decide +kernel
    · subst q
      decide +kernel


/-- First nonfatal offset as a function of the boundary-depth surplus. -/
def escape : Nat → Nat
  | 0 => 0
  | 1 => 1
  | r+2 => 3*escape r+2

theorem escape_lt_succ (r : Nat) : escape r < escape (r+1) := by
  induction r using Nat.strongRecOn with
  | ind r ih =>
      cases r with
      | zero => decide
      | succ r =>
          cases r with
          | zero => decide
          | succ r =>
              have h := ih r (by omega)
              change 3*escape r+2 < 3*escape (r+1)+2
              omega

private theorem boundary_equal_safe (a : Nat) : bad a (u a)=false := by
  induction a with
  | zero => decide +kernel
  | succ a ih =>
      rw [u, digit_one_pos (a+1) _ (by omega)]
      simpa using ih

private theorem boundary_one_safe (a : Nat) : bad a (u (a+1)+1)=false := by
  induction a with
  | zero => decide +kernel
  | succ a ih =>
      have he : u (a+1+1)+1=3*(u (a+1))+2 := by rw [u]
      rw [he,digit_two_pos (a+1) _ (by omega)]
      simpa using ih

private theorem u_digit_one (n e : Nat) (he : e%3=0) :
    u (n+1)+e=3*(u n+e/3)+1 := by rw [u]; omega

private theorem u_digit_two (n e : Nat) (he : e%3=1) :
    u (n+1)+e=3*(u n+e/3)+2 := by rw [u]; omega

private theorem u_digit_zero (n e : Nat) (he : e%3=2) :
    u (n+1)+e=3*(u n+e/3+1) := by rw [u]; omega

/-- The sharp maximal consecutive fatal interval to the right of u_(a+r).
All offsets e<escape r are fatal; e=escape r is the first survivor. -/
theorem exact_initial_band (r : Nat) : ∀ a : Nat,
    (∀ e : Nat, e < escape r → bad a (u (a+r)+e)=true) ∧
    bad a (u (a+r)+escape r)=false := by
  induction r using Nat.strongRecOn with
  | ind r ih =>
      cases r with
      | zero =>
          intro a
          constructor
          · intro e he
            simp [escape] at he
          · simpa [escape] using boundary_equal_safe a
      | succ r =>
          cases r with
          | zero =>
              intro a
              constructor
              · intro e he
                have he0 : e=0 := by simp [escape] at he; omega
                subst e
                simpa only [Nat.add_zero] using boundary_fatal (a+1) a (by omega)
              · simpa [escape] using boundary_one_safe a
          | succ r =>
              intro a
              induction a with
              | zero =>
                  have hs : (∀ e : Nat, e < escape (r+2) →
                      bad 0 (u (r+2)+e)=true) := by
                    intro e he
                    have hepow : escape (r+2)=3*escape r+2 := rfl
                    have hq : e/3 ≤ escape r := by rw [hepow] at he; omega
                    by_cases hr0 : e%3=0
                    · rw [u_digit_one (r+1) e hr0]
                      exact digit_one_zero _
                    · by_cases hr1 : e%3=1
                      · rw [u_digit_two (r+1) e hr1, digit_two_zero]
                        have hlt : e/3 < escape (r+1) := by
                          have hs := escape_lt_succ r
                          omega
                        simpa only [Nat.zero_add] using (ih (r+1) (by omega) 0).1 (e/3) hlt
                      · have hr2 : e%3=2 := by omega
                        rw [u_digit_zero (r+1) e hr2,
                            digit_zero 0 (u (r+1)+e/3+1) (by omega)]
                        have hred : u (r+1)+e/3+1-1=u (r+1)+e/3 := by omega
                        rw [hred]
                        have hlt : e/3<escape r := by rw [hepow] at he; omega
                        simpa only [Nat.one_add] using
                          (ih r (by omega) 1).1 (e/3) hlt
                  constructor
                  · intro e he
                    simpa only [Nat.zero_add, Nat.add_assoc] using hs e he
                  · have hepow : escape (r+2)=3*escape r+2 := rfl
                    have hnorm : 0+(r+1+1)=r+2 := by omega
                    have hnormE : r+1+1=r+2 := by omega
                    rw [hnorm, hnormE]
                    rw [hepow,u_digit_zero (r+1) (3*escape r+2) (by omega)]
                    have hdiv : (3*escape r+2)/3=escape r := by omega
                    rw [hdiv,
                        digit_zero 0 (u (r+1)+escape r+1) (by omega)]
                    have hred : u (r+1)+escape r+1-1=u (r+1)+escape r := by omega
                    rw [hred]
                    simpa only [Nat.one_add] using (ih r (by omega) 1).2
              | succ a ia =>
                  have hs : ∀ e : Nat, e<escape (r+2) →
                      bad (a+1) (u (a+1+(r+2))+e)=true := by
                    intro e he
                    have hepow : escape (r+2)=3*escape r+2 := rfl
                    have hq : e/3≤escape r := by rw [hepow] at he; omega
                    by_cases hr0 : e%3=0
                    · have hrebase : a+1+(r+2)= (a+r+2)+1 := by omega
                      rw [hrebase,u_digit_one (a+r+2) e hr0,
                          digit_one_pos (a+1) _ (by omega)]
                      have hlt : e/3<escape (r+2) := by rw [hepow] at he; omega
                      exact ia.1 (e/3) hlt
                    · by_cases hr1 : e%3=1
                      · have hrebase : a+1+(r+2)= (a+r+2)+1 := by omega
                        rw [hrebase,u_digit_two (a+r+2) e hr1,
                            digit_two_pos (a+1) _ (by omega)]
                        have hplus : u (a+r+2)+e/3+1 = u (a+(r+2))+(e/3+1) := by
                          simp only [Nat.add_assoc]
                        rw [hplus]
                        have hlt : e/3+1<escape (r+2) := by rw [hepow] at he; omega
                        exact ia.1 (e/3+1) hlt
                      · have hr2 : e%3=2 := by omega
                        have hrebase : a+1+(r+2)= (a+r+2)+1 := by omega
                        rw [hrebase,u_digit_zero (a+r+2) e hr2,
                            digit_zero (a+1) (u (a+r+2)+e/3+1) (by omega)]
                        have hred : u (a+r+2)+e/3+1-1=u (a+r+2)+e/3 := by omega
                        rw [hred]
                        have harg : a+r+2 = (a+2)+r := by omega
                        rw [harg]
                        have hlt : e/3<escape r := by rw [hepow] at he; omega
                        exact (ih r (by omega) (a+2)).1 (e/3) hlt
                  constructor
                  · intro e he
                    exact hs e he
                  · have hepow : escape (r+2)=3*escape r+2 := rfl
                    have hrebase : a+1+(r+2)= (a+r+2)+1 := by omega
                    rw [hepow,hrebase,u_digit_zero (a+r+2) (3*escape r+2) (by omega)]
                    have hdiv : (3*escape r+2)/3=escape r := by omega
                    rw [hdiv,digit_zero (a+1) (u (a+r+2)+escape r+1) (by omega)]
                    have hred : u (a+r+2)+escape r+1-1=u (a+r+2)+escape r := by omega
                    rw [hred]
                    have harg : a+r+2=(a+2)+r := by omega
                    rw [harg]
                    exact (ih r (by omega) (a+2)).2

theorem escape_even (k : Nat) : escape (2*k)+1=3^k := by
  induction k with
  | zero => decide
  | succ k ih =>
      have hr : 2*(k+1) = 2*k+2 := by omega
      rw [hr]
      change 3*escape (2*k)+2+1 = 3^(k+1)
      rw [Nat.pow_succ]
      omega

theorem escape_odd (k : Nat) : escape (2*k+1)+1=2*3^k := by
  induction k with
  | zero => decide
  | succ k ih =>
      have hr : 2*(k+1)+1 = (2*k+1)+2 := by omega
      rw [hr]
      change 3*escape (2*k+1)+2+1 = 2*3^(k+1)
      rw [Nat.pow_succ]
      omega

#print axioms escape_even
#print axioms escape_odd
#print axioms exact_initial_band

#print axioms band_fatal
#print axioms linear_band_fatal

end BB6Robust
