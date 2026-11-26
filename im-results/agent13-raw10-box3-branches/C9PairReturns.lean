import C9PairMacros
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000
namespace C9Pair
set_option linter.unusedSimpArgs false

theorem y_even (short : Bool) (a k : Nat) (w z : Stream) :
    run short (2*a+4*k+9+extra short)
      (Y a w (rep true (2*k+1) (rep false 2 z))) =
    some (B0 (push false (alt k (rep true (a+2) w))) (rep true 2 z)) := by
  have h1 := y_to_e short a w (rep true (2*k+1) (rep false 2 z))
  have h2 := e_pairs short k (rep true (a+2) w) (push true (rep false 2 z))
  have h3 := e_even_double short (alt k (rep true (a+2) w)) z
  have he : push true (rep true (2*k+1) (rep false 2 z)) =
      rep true (2*k) (push true (push true (rep false 2 z))) := by
    rw [← rep_succ, ← rep_two true (rep false 2 z), rep_append]
  rw [he] at h1
  rw [rep_two false z] at h1 h2
  have h := join (join h1 h2) h3
  rw [show 2*a+4+4*k+(5+extra short)=2*a+4*k+9+extra short by omega] at h
  simpa only [rep_two false z] using h

theorem y_odd_double (short : Bool) (a k : Nat) (w z : Stream) :
    run short (2*a+4*k+6) (Y a w (rep true (2*k) (rep false 2 z))) =
      some (B0 (alt 1 (alt k (rep true (a+2) w))) z) := by
  have h1 := y_to_e short a w (rep true (2*k) (rep false 2 z))
  have h2 := e_pairs short k (rep true (a+2) w) (rep false 2 z)
  have he : push true (rep true (2*k) (rep false 2 z)) =
      rep true (2*k) (push true (rep false 2 z)) := by
    rw [← rep_succ, ← rep_one true (rep false 2 z), rep_append]
  rw [he] at h1
  rw [rep_two false z] at h1 h2
  have h := join (join h1 h2) (e_odd_double short (alt k (rep true (a+2) w)) z)
  rw [show 2*a+4+4*k+2=2*a+4*k+6 by omega] at h
  simpa only [rep_two false z] using h

theorem y_odd_single (short : Bool) (a k : Nat) (w z : Stream) :
    run short (2*a+4*k+8) (Y a w (rep true (2*k) (push false (push true z)))) =
      some (B0 (alt k (rep true (a+2) w)) (rep true 2 z)) := by
  have h1 := y_to_e short a w (rep true (2*k) (push false (push true z)))
  have h2 := e_pairs short k (rep true (a+2) w) (push false (push true z))
  have he : push true (rep true (2*k) (push false (push true z))) =
      rep true (2*k) (push true (push false (push true z))) := by
    rw [← rep_succ, ← rep_one true (push false (push true z)), rep_append]
  rw [he] at h1
  have h := join (join h1 h2) (e_odd_single short (alt k (rep true (a+2) w)) z)
  rwa [show 2*a+4+4*k+4=2*a+4*k+8 by omega] at h

theorem y_halt_live (short : Bool) (a k : Nat) (w z : Stream) :
    ∃ c, run short (2*a+4*k+7) (Y a w (rep true (2*k+1) (push false (push true z)))) = some c ∧
      step short c = none := by
  have h1 := y_to_e short a w (rep true (2*k+1) (push false (push true z)))
  have h2 := e_pairs short k (rep true (a+2) w) (push true (push false (push true z)))
  have he : push true (rep true (2*k+1) (push false (push true z))) =
      rep true (2*k) (push true (push true (push false (push true z)))) := by
    rw [← rep_succ, ← rep_two true (push false (push true z)), rep_append]
  rw [he] at h1
  have h := join (join h1 h2) (e_even_single_live short (alt k (rep true (a+2) w)) z)
  rw [show 2*a+4+4*k+3=2*a+4*k+7 by omega] at h
  exact ⟨_,h,rfl⟩

-- Odd right run: sweep to E, perform the even-length transformation,
-- then discard all fresh alternating pairs from the left.
theorem y_even_strip (short : Bool) (a u k : Nat) (v z : Stream) :
    run short (2*a+10*k+15+extra short)
      (Y a (rep true u (push false v)) (rep true (2*k+1) (rep false 2 z))) =
    some (B0 (rep true (a+1+u) (push false v)) (rep true (2*k+4) z)) := by
  have h1 := y_even short a k (rep true u (push false v)) z
  rw [rep_append] at h1
  have h2 := x0_pairs short k (rep true (a+2+u) (push false v)) (rep true 2 z)
  rw [rep_append] at h2
  have h3 := x0 short (rep true (a+1+u) (push false v)) (rep true (2*k+2) z)
  have he : rep true (a+2+u) (push false v) = push true (rep true (a+1+u) (push false v)) := by
    rw [show a+2+u=a+1+u+1 by omega,rep_succ]
  rw [he] at h1 h2
  have h := join (join h1 h2) h3
  rw [rep_append,show 2+(2*k+2)=2*k+4 by omega] at h
  rwa [show 2*a+4*k+9+extra short+6*k+6=2*a+10*k+15+extra short by omega] at h

theorem y_even_terminal (short : Bool) (a u k : Nat) (z : Stream) :
    run short (2*a+10*k+15+extra short)
      (Y a (rep true u zero) (rep true (2*k+1) (rep false 2 z))) =
    some (Y (a+1+u) zero (rep true (2*k+4) z)) := by
  have h := y_even_strip short a u k zero z
  simpa only [push_zero_blank,Y] using h

theorem y_even_internal (short : Bool) (a u k v : Nat) (w z : Stream) :
    run short (3*a+u+10*k+20+5*v+extra short)
      (Y a (rep true u (push false (rep true (v+1) (push false w))))
        (rep true (2*k+1) (rep false 2 z))) =
    some (Y 1 w (rep true v (rep false (a+u) (rep true (2*k+5) z)))) := by
  have h1 := y_even_strip short a u k (rep true (v+1) (push false w)) z
  have h2 := x_pos short (a+u) (rep true v (push false w)) (rep true (2*k+4) z)
  rw [show a+1+u=a+u+1 by omega] at h1
  have h3 := x1_run short v (push false w) (rep false (a+u) (rep true (2*k+5) z))
  rw [rep_succ true v] at h1
  rw [← rep_succ true (2*k+4)] at h2
  have h := join (join h1 h2) h3
  simp only [alt_one,rep_one,Y,rep_succ true v] at h ⊢
  rwa [show 2*a+10*k+15+extra short+(a+u+5)+5*v=3*a+u+10*k+20+5*v+extra short by omega] at h

theorem y_odd_double_zero (short : Bool) (a u : Nat) (v z : Stream) :
    run short (2*a+6+5*(a+2+u)) (Y a (rep true u (push false v)) (rep false 2 z)) =
      some (Y 1 v (rep true (a+2+u) z)) := by
  have h1 := y_odd_double short a 0 (rep true u (push false v)) z
  rw [rep_append] at h1
  have h2 := x1_run short (a+2+u) (push false v) z
  simp only [alt_zero] at h1
  have h := join h1 h2
  simpa only [Nat.mul_zero,Nat.add_zero,rep_zero,alt_one,rep_one,Y] using h

theorem y_odd_double_succ (short : Bool) (a u k : Nat) (v z : Stream) :
    run short (2*a+4*(k+1)+11) (Y a (rep true u (push false v)) (rep true (2*(k+1)) (rep false 2 z))) =
      some (Y 1 (alt k (rep true (a+2+u) (push false v))) (push true z)) := by
  have h1 := y_odd_double short a (k+1) (rep true u (push false v)) z
  rw [rep_append] at h1
  have h2 := x1_run short 1 (push false (alt k (rep true (a+2+u) (push false v)))) z
  simp only [alt_succ] at h1
  simp only [rep_one,alt_one] at h2
  have h := join h1 h2
  rw [show 2*a+4*(k+1)+6+5=2*a+4*(k+1)+11 by omega] at h
  simpa only [Y,rep_one] using h

theorem y_odd_single_zero_terminal (short : Bool) (a u : Nat) (z : Stream) :
    run short (2*a+8) (Y a (rep true u zero) (push false (push true z))) =
      some (Y (a+2+u) zero (rep true 2 z)) := by
  have h := y_odd_single short a 0 (rep true u zero) z
  rw [rep_append] at h
  simpa only [Y,push_zero_blank,Nat.mul_zero,Nat.add_zero,rep_zero,alt_zero] using h

theorem y_odd_single_zero_internal (short : Bool) (a u v : Nat) (w z : Stream) :
    run short (3*a+u+14+5*v)
      (Y a (rep true u (push false (rep true (v+1) (push false w)))) (push false (push true z))) =
    some (Y 1 w (rep true v (rep false (a+1+u) (rep true 3 z)))) := by
  have h1 := y_odd_single short a 0 (rep true u (push false (rep true (v+1) (push false w)))) z
  rw [rep_append,show a+2+u=a+1+u+1 by omega] at h1
  have h2 := x_pos short (a+1+u) (rep true v (push false w)) (rep true 2 z)
  have h3 := x1_run short v (push false w) (rep false (a+1+u) (rep true 3 z))
  simp only [alt_zero,Nat.mul_zero,rep_zero] at h1
  rw [rep_succ true v] at h1
  rw [← rep_succ true 2] at h2
  have h := join (join h1 h2) h3
  rw [show 2*a+4*0+8+(a+1+u+5)+5*v=3*a+u+14+5*v by omega] at h
  simpa only [alt_one,rep_one,Y,rep_succ true v] using h

theorem y_odd_single_one (short : Bool) (a u : Nat) (v z : Stream) :
    run short (2*a+12+5*(a+2+u)) (Y a (rep true u (push false v)) (rep true 2 (push false (push true z)))) =
      some (Y 1 v (rep true (a+4+u) z)) := by
  have h1 := y_odd_single short a 1 (rep true u (push false v)) z
  rw [rep_append] at h1
  have h2 := x1_run short (a+2+u) (push false v) (rep true 2 z)
  have h := join h1 h2
  rw [rep_append,show a+2+u+2=a+4+u by omega] at h
  simpa only [Y,alt_one,rep_one] using h

theorem y_odd_single_two (short : Bool) (a u k : Nat) (v z : Stream) :
    run short (2*a+4*(k+2)+13)
      (Y a (rep true u (push false v)) (rep true (2*(k+2)) (push false (push true z)))) =
    some (Y 1 (alt k (rep true (a+2+u) (push false v))) (rep true 3 z)) := by
  have h1 := y_odd_single short a (k+2) (rep true u (push false v)) z
  rw [rep_append] at h1
  have h2 := x1_run short 1 (push false (alt k (rep true (a+2+u) (push false v)))) (rep true 2 z)
  simp only [alt_succ] at h1
  simp only [alt_one,rep_one] at h2
  have h := join h1 h2
  rw [← rep_succ true 2,show 2*a+4*(k+2)+8+5*1=2*a+4*(k+2)+13 by omega] at h
  simpa only [Y,rep_one] using h

theorem triplet (short : Bool) (k : Nat) (w : Stream) :
    run short (10*k+52+extra short) (Y 1 (alt 3 w) (rep true (2*k+1) zero)) =
      some (Y 1 w (rep true (2*k+9) zero)) := by
  have h1 := y_even_internal short 1 1 k 0 (alt 1 w) zero
  simp only [rep_zero_blank,rep_zero] at h1
  have h2 := y_odd_double_zero short 1 1 w (rep true (2*k+5) zero)
  simp only [alt_one,rep_one] at h1 h2
  have h := join h1 h2
  rw [rep_append,show 1+2+1+(2*k+5)=2*k+9 by omega] at h
  have ha : alt 3 w = push true (push false (push true (push false (push true (push false w))))) := by rw [show 3=2+1 by rfl,alt_succ,show 2=1+1 by rfl,alt_succ,alt_one]
  rw [ha]
  simp only [Nat.zero_add,rep_one] at h
  rwa [show 3*1+1+10*k+20+5*0+extra short+(2*1+6+5*(1+2+1))=10*k+52+extra short by omega] at h

theorem triplets (short : Bool) (n k : Nat) (w : Stream) :
    run short (n*(10*k+32+extra short+20*n))
      (Y 1 (alt (3*n) w) (rep true (2*k+1) zero)) =
      some (Y 1 w (rep true (2*k+1+8*n) zero)) := by
  induction n generalizing k with
  | zero => simp only [Nat.mul_zero,Nat.zero_mul,alt_zero,Nat.add_zero,run]
  | succ n ih =>
    have h1 := triplet short k (alt (3*n) w)
    have h2 := ih (k+4)
    rw [show 2*(k+4)+1=2*k+9 by omega] at h2
    have h := join h1 h2
    rw [alt_append,show 3+3*n=3*(n+1) by omega,show 2*k+9+8*n=2*k+1+8*(n+1) by omega] at h
    have hc : 10*k+52+extra short+n*(10*(k+4)+32+extra short+20*n) =
        (n+1)*(10*k+32+extra short+20*(n+1)) := by
      simp only [Nat.mul_add,Nat.add_mul,← Nat.mul_assoc]
      omega
    rwa [hc] at h

#print axioms triplets
#print axioms y_halt_live
end C9Pair
