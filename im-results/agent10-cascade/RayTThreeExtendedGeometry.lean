import RayTThreeLowGeometry
set_option maxHeartbeats 0
namespace CascadeTThreeLow

theorem third_parent_upper_tight (n D q:Nat) (hn:20≤n)
  (hm:2048*D+16384*n+16384≤2^n)
  (hl:81*q+32*D+81*n+82=47*2^n):
  8*q+40*n+320≤75*2^(n-4) := by
  have hp := (pow_shift n hn).1
  rw [hp] at hm hl
  omega

/-- Physical t=0 precursor from the #746 t3 gap is inside the narrow
    reset-image gap that excludes every first parent if its own numerator
    is indivisible by nine. -/
theorem third_precursor_narrow (n q d h:Nat) (hn:20≤n)
 (hlo:9*2^(n-4)+5*n+40≤q)
 (hhi:8*q+40*n+320≤75*2^(n-4))
 (hd:3*d=2*q+5)
 (he:2*d=8*2^(n-4)+h+(n-4)+5):
 2^(n-2)<h ∧ 8*h+32<9*2^(n-2) := by
  have hp := (pow_shift n hn).2.1
  rw [hp]
  constructor <;> omega

/-- From the q interval, t=1 and t=2 odd first-parent image quantities
    lie strictly inside dyadic gaps, at scales n-2 and n-3. -/
theorem third_tone_gap (n q d:Nat) (hn:20≤n)
 (hlo:9*2^(n-4)+5*n+40≤q)
 (hhi:q+5*n+40≤10*2^(n-4))
 (hz:2*q+5=9*d):
 2^(n-2)<2*d ∧ 2*(2*d)+2<3*2^(n-2) := by
  have hp := (pow_shift n hn).2.1
  rw [hp]
  constructor <;> omega

theorem third_ttwo_gap (n q d:Nat) (hn:20≤n)
 (hlo:9*2^(n-4)+5*n+40≤q)
 (hhi:q+5*n+40≤10*2^(n-4))
 (hz:2*q+5=27*d):
 2^(n-3)<4*d ∧ 2*(4*d)+2<3*2^(n-3) := by
  have hp := (pow_shift n hn).2.2
  rw [hp]
  have hmin:100≤2^(n-4):=by
    have hp':16≤n-4:=by omega
    have h:=Nat.pow_le_pow_right (by decide:0<(2:Nat)) hp'
    omega
  constructor <;> omega

#print axioms third_parent_upper_tight
#print axioms third_precursor_narrow
#print axioms third_tone_gap
#print axioms third_ttwo_gap
end CascadeTThreeLow
