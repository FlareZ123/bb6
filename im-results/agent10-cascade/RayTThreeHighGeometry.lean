import RayTThreeExtendedGeometry
set_option maxHeartbeats 0
namespace CascadeTThreeLow

private theorem scale_high (n:Nat) (hn:20≤n):
  2^(n-4)=4*2^(n-6) := by
  have hh:n-4=(n-6)+2:=by omega
  calc
    2^(n-4)=2^((n-6)+2):=congrArg (fun k:Nat=>2^k) hh
    _=4*2^(n-6):=by rw[Nat.pow_add];simp only [show (2:Nat)^2=4 by decide];ac_rfl

/-- The next t=3 odd inverse ancestor r lies inside a genuine even
    image band, but its unique even inverse r1 immediately exits into
    the strict no-even-image gap. -/
theorem third_high_child_one_even_gap (n q d r r1:Nat) (hn:20≤n)
  (hlo:9*2^(n-4)+5*n+40≤q)
  (htight:8*q+40*n+320≤75*2^(n-4))
  (hz:2*q+5=81*d)
  (he:16*d=8*2^(n-6)+r+(n-6)+5)
  (hev:2*r=8*2^(n-6)+r1+(n-6)):
  (6*2^(n-6)-1≤r ∧ r≤8*2^(n-6)-3) ∧
  (4*2^(n-6)-3<r1 ∧ r1<6*2^(n-6)-1) := by
  have hp:=scale_high n hn
  rw [hp] at hlo htight
  constructor
  · constructor <;> omega
  · constructor <;> omega

/-- Geometric gap in the exact image-gap format used by the source
    root exclusion lemma. -/
theorem third_high_child_gap_strong (n q d r r1:Nat) (hn:20≤n)
 (hlo:9*2^(n-4)+5*n+40≤q)
 (htight:8*q+40*n+320≤75*2^(n-4))
 (hz:2*q+5=81*d)
 (he:16*d=8*2^(n-6)+r+(n-6)+5)
 (hev:2*r=8*2^(n-6)+r1+(n-6)):
 2^(n-4)<r1 ∧ 2*r1+2<3*2^(n-4) := by
 have hp:=scale_high n hn
 rw[hp] at hlo htight ⊢
 constructor <;> omega

private theorem pow_mod_three (j:Nat):
  2^j%3=(if j%2=0 then 1 else 2) := by
  induction j with
  | zero => decide
  | succ j ih =>
      rw [Nat.pow_succ,Nat.mul_mod,ih]
      by_cases h:j%2=0
      · simp[h];omega
      · have hj:j%2=1:=by omega
        simp[hj];omega

/-- The surviving n mod6 sectors make the high-child even reset
    subtraction constant divisible by three at scale n-6. -/
theorem high_child_even_constant_mod3 (n:Nat) (hn:20≤n)
  (hsector:n%6=4 ∨ n%6=5):
  (8*2^(n-6)+(n-6))%3=0 := by
  let k:=n-6
  have hk:k%6=4 ∨ k%6=5:=by
    dsimp[k]
    rcases hsector with h|h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have h2:=pow_mod_three k
  change (8*2^k+k)%3=0
  rcases hk with h|h
  · have hpar:k%2=0:=by omega
    rw[if_pos hpar] at h2
    omega
  · have hpar:k%2=1:=by omega
    have hneq:k%2≠0:=by omega
    rw[if_neg hneq] at h2
    omega

/-- If the next t=3 parent has residue zero modulo three, its sole
    admissible even source predecessor stays residue zero and enters the
    no-even-image gap. -/
theorem high_child_even_mod_zero (n r r1:Nat) (hn:20≤n)
 (hsector:n%6=4 ∨ n%6=5)
 (hr:r%3=0)
 (hev:2*r=8*2^(n-6)+r1+(n-6)):
 r1%3=0 := by
 have hE:=high_child_even_constant_mod3 n hn hsector
 omega

#print axioms third_high_child_one_even_gap
#print axioms third_high_child_gap_strong
#print axioms high_child_even_constant_mod3
#print axioms high_child_even_mod_zero
end CascadeTThreeLow
