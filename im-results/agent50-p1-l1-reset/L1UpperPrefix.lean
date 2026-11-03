import L1UpperMass

namespace BB6.Agent50L1All
open BB6.Agent1RootWall
open BB6.Agent1UpperTail
open BB6.Agent45TwoRoot

/-- Any authentic L1 upper prefix ending in the b%4=0 inverse sector
    has length bounded by the small q-sector source correction. -/
theorem l1_upper_prefix_short (q bp dp mp r : Nat)
    (hq : 1≤q)
    (hpre : UpperTail (6*u2 q-2) (2*u2 q+5) 0 bp dp mp r)
    (hb4 : bp%4=0) : 2^r≤6*q+2 := by
  let u := u2 q
  let P := 2^(16*q)
  let X := 2^r
  have hPpos : 0<P := Nat.two_pow_pos _
  have hXpos : 0<X := Nat.two_pow_pos _
  have hlarge := large_power q hq
  have hqle : q≤q*q := by
    have hh := Nat.mul_le_mul_right q hq
    omega
  have hqbig : 65536*q ≤ P := by
    have hscaled := Nat.mul_le_mul_left 65536 hqle
    have hlargeEq : 65536*(q*q)≤P := by simpa only [Nat.mul_assoc] using hlarge
    omega
  have hNsmall : 128*q+32<P := by omega
  have hu : u+4*q+3=7*P := by dsimp [u,u2,P]; omega
  have hu1 : 1≤u := by omega
  have hrootshift : X*(bp+12)=6*u+10 := by
    have hh := (upper_tail_dyadic (6*u2 q-2) (2*u2 q+5) 0 bp dp mp r hpre).1
    change X*(bp+12)=6*u-2+12 at hh
    omega
  have hroot : X*(bp+12)+24*q+8=42*P := by omega
  have hrbound : r<16*q := by
    by_cases hr : r<16*q
    · exact hr
    have hPdivX : P∣X := by
      dsimp [P,X]
      exact Nat.pow_dvd_pow 2 (by omega)
    have hPdivTerm : P∣X*(bp+12) := by
      obtain ⟨w,hw⟩:=hPdivX
      refine ⟨w*(bp+12),?_⟩
      rw [hw]
      ac_rfl
    have hPdivWhole : P∣42*P := ⟨42,by ac_rfl⟩
    have hPdivN : P∣24*q+8 := by
      apply (Nat.dvd_add_iff_right hPdivTerm).mpr
      rw [show X*(bp+12)+(24*q+8)=42*P by omega]
      exact hPdivWhole
    have hh := Nat.le_of_dvd (by omega : 0<24*q+8) hPdivN
    omega
  have hXdivP : X∣P := by
    dsimp [P,X]
    exact Nat.pow_dvd_pow 2 (by omega)
  have hXdivTerm : X∣X*(bp+12) := ⟨bp+12,rfl⟩
  have hXdivWhole : X∣42*P := by
    obtain ⟨w,hw⟩:=hXdivP
    refine ⟨42*w,?_⟩
    rw [hw]
    ac_rfl
  have hXdivN : X∣24*q+8 := by
    apply (Nat.dvd_add_iff_right hXdivTerm).mpr
    rw [show X*(bp+12)+(24*q+8)=42*P by omega]
    exact hXdivWhole
  have hXsmall : X≤24*q+8 := Nat.le_of_dvd (by omega) hXdivN
  have hr2 : r+2≤16*q := by
    by_cases hr2 : r+2≤16*q
    · exact hr2
    have hPdiv : P∣2^(r+1) := by
      dsimp [P]
      exact Nat.pow_dvd_pow 2 (by omega)
    have hpSmall := Nat.le_of_dvd (Nat.two_pow_pos _) hPdiv
    have hrew : 2^(r+1)=2*X := by dsimp [X]; rw [Nat.pow_succ]; omega
    omega
  have h4XdivP : 4*X ∣ P := by
    have hh : 2^(r+2)∣2^(16*q) := Nat.pow_dvd_pow 2 hr2
    have h4Xeq : 2^(r+2)=4*X := by
      dsimp [X]
      calc
        2^(r+2)=2^r*2^2 := by rw [Nat.pow_add]
        _=4*2^r := by omega
    simpa only [P,h4Xeq] using hh
  have h4divbp : 4∣bp+12 := by
    apply Nat.dvd_iff_mod_eq_zero.mpr
    omega
  have h4XdivTerm : 4*X∣X*(bp+12) := by
    obtain ⟨w,hw⟩:=h4divbp
    refine ⟨w,?_⟩
    rw [hw]
    ac_rfl
  have h4XdivWhole : 4*X∣42*P := by
    obtain ⟨w,hw⟩:=h4XdivP
    refine ⟨42*w,?_⟩
    rw [hw]
    ac_rfl
  have h4XdivN : 4*X∣24*q+8 := by
    apply (Nat.dvd_add_iff_right h4XdivTerm).mpr
    rw [show X*(bp+12)+(24*q+8)=42*P by omega]
    exact h4XdivWhole
  have h4small : 4*X≤24*q+8 := Nat.le_of_dvd (by omega) h4XdivN
  dsimp [X] at *
  omega

#print axioms l1_upper_prefix_short
end BB6.Agent50L1All
