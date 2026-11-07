import Std
set_option maxHeartbeats 0
namespace CascadeTThreeLow

theorem pow_shift (n:Nat) (hn:20≤n) :
  2^n=16*2^(n-4) ∧ 2^(n-2)=4*2^(n-4) ∧ 2^(n-3)=2*2^(n-4) := by
  have h1:n=(n-4)+4:=by omega
  have h2:n-2=(n-4)+2:=by omega
  have h3:n-3=(n-4)+1:=by omega
  constructor
  · calc
      2^n=2^((n-4)+4):=congrArg (fun k:Nat=>2^k) h1
      _=16*2^(n-4):=by rw[Nat.pow_add]; simp only [show (2:Nat)^4=16 by decide]; ac_rfl
  constructor
  · calc
      2^(n-2)=2^((n-4)+2):=congrArg (fun k:Nat=>2^k) h2
      _=4*2^(n-4):=by rw[Nat.pow_add]; simp only [show (2:Nat)^2=4 by decide]; ac_rfl
  · calc
      2^(n-3)=2^((n-4)+1):=congrArg (fun k:Nat=>2^k) h3
      _=2*2^(n-4):=by rw[Nat.pow_succ];omega

/-- Strong-margin source third-valuation odd-parent equation confines
    its genuine reset parent q to a narrow interval inside the dyadic gap. -/
theorem third_parent_interval (n D q:Nat) (hn:20≤n)
  (hm:2048*D+16384*n+16384≤2^n)
  (hl:81*q+32*D+81*n+82=47*2^n) :
  9*2^(n-4)+5*n+40≤q ∧ q+5*n+40≤10*2^(n-4) := by
  have hp := (pow_shift n hn).1
  rw[hp] at hm hl
  constructor <;> omega

/-- Arithmetic ancestor of a t=0 odd return from the third-valuation q:
    its height h belongs to a forbidden even image gap. -/
theorem third_precursor_gap (n q d h:Nat) (hn:20≤n)
  (hlo:9*2^(n-4)+5*n+40≤q)
  (hhi:q+5*n+40≤10*2^(n-4))
  (hd:3*d=2*q+5)
  (he:2*d=8*2^(n-4)+h+(n-4)+5):
  2^(n-2)<h ∧ 2*h+2<3*2^(n-2) := by
  have hp := (pow_shift n hn).2.1
  rw[hp]
  constructor <;> omega

/-- If the first odd return q is of exact valuation one, and its
    t=0 antecedent obeys the legal source equation, the antecedent
    cannot have residue 2 modulo 3 in a surviving #746 index sector. -/
theorem third_precursor_residue (n q d h:Nat)
  (hE:(8*2^(n-4)+(n-4))%3=2)
  (hd:3*d=2*q+5)
  (hnot9:(2*q+5)%9≠0)
  (he:2*d=8*2^(n-4)+h+(n-4)+5):
  h%3≠2 := by
  have hdmod:d%3≠0:=by omega
  omega

#print axioms third_parent_interval
#print axioms third_precursor_gap
#print axioms third_precursor_residue
end CascadeTThreeLow
