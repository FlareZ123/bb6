import RenewalLate

set_option maxHeartbeats 1000000

namespace BB6.Agent9Renewal
open BB6P1Unit

/-- Products of nonzero residues modulo seven remain nonzero. -/
theorem unit_mul7 (x y : Int) (hx : x%7≠0) (hy : y%7≠0) : (x*y)%7≠0 := by
  rw [Int.mul_emod]
  have hx' := Int.emod_nonneg x (by decide : (7:Int) ≠ 0)
  have hy' := Int.emod_nonneg y (by decide : (7:Int) ≠ 0)
  have hxu := Int.emod_lt_of_pos x (by decide : 0<(7:Int))
  have hyu := Int.emod_lt_of_pos y (by decide : 0<(7:Int))
  have hxc : x%7=1 ∨ x%7=2 ∨ x%7=3 ∨ x%7=4 ∨ x%7=5 ∨ x%7=6 := by omega
  rcases hxc with h|h|h|h|h|h <;> rw [h] <;> omega

/-- The next phase numerator is exactly a 7-unit after division by G.
This is the finite form of the denominator-growth argument. -/
theorem numerator_factor (D p a d G U V l : Int) (L : Nat)
    (hdiv : D ∣ (2:Int)^L-1) (hD : D=7*G*U) (hM : (2:Int)^L-1=7*G*V)
    (hL : (L:Int)=l*G) (hl : l%7≠0) (hp : p%7≠0) :
    ∃ u : Int, D*((2:Int)^L-1)*d-((2:Int)^L-1)*a*p-cycleSum D p L=G*u ∧ u%7≠0 := by
  obtain ⟨z,hz⟩ := cycle_mod (p:=p) L hdiv
  refine ⟨-l*p+7*(U*((2:Int)^L-1)*d-V*a*p-U*z),?_,?_⟩
  · grind
  · rw [Int.add_mul_emod_self_left]
    have hn : (-l)%7≠0 := by
      intro h
      have he := Int.emod_add_mul_ediv (-l) 7
      have he' := Int.emod_add_mul_ediv l 7
      omega
    exact unit_mul7 (-l) p hn hp

/-- A full n-step block, with an exact interior endpoint on the next
rational grid, using only finite integer arithmetic. -/
theorem renewal_block (q d n K L : Nat) (D p a C B G Dnew U V l : Int)
    (hD : 0<D) (hodd : D%2=1) (hp : 0<p) (hpD : p<D) (hp7 : p%7≠0)
    (hdq : d<q) (hclock : (q:Int)=7*(2:Int)^n+a)
    (hdiv : D ∣ (2:Int)^L-1) (hM : 0<(2:Int)^L-1)
    (hG : 0<G) (hDfactor : D=7*G*U) (hMfactor : (2:Int)^L-1=7*G*V)
    (hL : (L:Int)=l*G) (hl : l%7≠0) (hnew : 7*D*((2:Int)^L-1)=G*Dnew) (hnew7 : Dnew%7=0)
    (hC : 0≤C) (hB : 0≤B) (ha : ∀ j : Nat, j≤n → Bound (a+j) C)
    (hinit : Bound (D*(d:Int)-7*(2:Int)^n*p) (D*B))
    (hK : K≤n) (hsmall : D*(2:Int)^K*(B+C)<(2:Int)^n)
    (hgap : D*((2:Int)^L-1)*((2:Int)^(n-K)*(2*C+2)+C+8)<(2:Int)^K) :
    (∀ j≤n, 2≤run q d j ∧ run q d j+8≤q+j) ∧
    ∃ p' : Int, 0<p' ∧ p'<Dnew ∧ p'%7≠0 ∧
      Bound (Dnew*(run q d n:Int)-7*(2:Int)^n*p')
        (Dnew*((2:Int)^(n-K)*(2*C+2))) := by
  let P := (2:Int)^n
  let M := (2:Int)^L-1
  let R := D*M
  let N := R*(d:Int)-M*a*p-cycleSum D p L
  let E := (2:Int)^(n-K)*(2*C+2)
  have hP : 0<P := Int.pow_pos (by decide)
  have hMp : 0<M := hM
  have hR : 0<R := Int.mul_pos hD hMp
  have hnew' : 7*R=G*Dnew := by dsimp [R,M]; grind
  have hnewpos : 0<Dnew := by
    have hh := Int.lt_of_mul_lt_mul_left (show G*0<G*Dnew by rw [←hnew']; simp; omega) (show 0≤G by omega)
    omega
  obtain ⟨u,hu,hu7⟩ := numerator_factor D p a d G U V l L hdiv hDfactor hMfactor hL hl hp7
  change N=G*u at hu
  have hN : ¬ (7*R ∣ N) := by
    rintro ⟨z,hz⟩
    have hh : G*u=G*(Dnew*z) := by grind
    have hh' := Int.eq_of_mul_eq_mul_left (by omega : G≠0) hh
    rw [hh',Int.mul_emod,hnew7,Int.zero_mul,Int.zero_emod] at hu7
    exact hu7 rfl
  have hE : 0≤E := Int.mul_nonneg (Int.pow_nonneg (by decide)) (by omega)
  have hgap' : R*(E+C+8)<(2:Int)^K := hgap
  have hlate : ∀ j : Nat, K≤j → j≤n →
      ∃ z e : Int, R*(run q d j:Int)=(2:Int)^j*N+7*P*R*z+e ∧ Bound e (R*E) := by
    intro j hjK hjn
    obtain ⟨z,e,he,hb⟩ := late_shadow q d n K L D p a C B hD hodd hp hpD hdq hclock hdiv hM hC hB ha hinit hK hsmall (j-K) (by omega)
    rw [show K+(j-K)=j by omega] at he
    have hpmono := pow_mono (show j-K≤n-K by omega)
    have hm := Int.mul_le_mul_of_nonneg_right hpmono (show 0≤2*C+2 by omega)
    have hm' := Int.mul_le_mul_of_nonneg_left (show (2:Int)^(j-K)*(2*C+2)-C≤E by dsimp [E]; omega) (show 0≤R by omega)
    exact ⟨z,e,he,bound_weaken hb hm'⟩
  have hsep : ∀ j : Nat, K≤j → j≤n → ∀ z e : Int,
      R*(run q d j:Int)=(2:Int)^j*N+7*P*R*z+e → Bound e (R*E) →
      0<N+7*R*(2:Int)^(n-j)*z ∧ N+7*R*(2:Int)^(n-j)*z<7*R*(2:Int)^(n-j) ∧
      2≤run q d j ∧ run q d j+8≤q+j := by
    intro j hjK hjn z e he hb
    have hPS : P=(2:Int)^j*(2:Int)^(n-j) := by dsimp [P]; rw [←Int.pow_add,show j+(n-j)=n by omega]
    have hjpow := pow_mono hjK
    have hjgap : R*(E+C+8)<(2:Int)^j := by omega
    have hc : Bound ((q:Int)+j-7*P) C := by
      change Bound ((q:Int)+j-7*(2:Int)^n) C
      rw [hclock,show 7*(2:Int)^n+a+j-7*(2:Int)^n=a+j by omega]
      exact ha j hjn
    have hres := separate_phase R P ((2:Int)^j) ((2:Int)^(n-j)) N z e (run q d j) ((q:Int)+j) C E hR hP (Int.pow_pos (by decide)) (Int.pow_pos (by decide)) hPS hC (by omega) (by have := run_lt q d j hdq; omega) hc hb hjgap hN he
    exact ⟨hres.1,hres.2.1,by omega,by omega⟩
  constructor
  · intro j hjn
    by_cases hjK : K≤j
    · obtain ⟨z,e,he,hb⟩ := hlate j hjK hjn
      exact (hsep j hjK hjn z e he hb).2.2
    · have hb := (early_shadow q d n K L D p a C B hD hodd hp hpD hdq hclock hdiv hM hC hB ha hinit hK hsmall j (by omega)).1
      let v := orbit D p j
      have hv := orbit_range hD hodd hp hpD j
      have hm := Int.mul_le_mul_of_nonneg_right (pow_mono (show j≤K by omega)) (show 0≤B+C by omega)
      have hm' := Int.mul_le_mul_of_nonneg_left (show (2:Int)^j*(B+C)-C≤(2:Int)^K*(B+C) by omega) (show 0≤D by omega)
      have hb' : Bound (D*(run q d j:Int)-7*P*v) P := by
        apply bound_weaken hb
        have hh : D*(2:Int)^K*(B+C)=D*((2:Int)^K*(B+C)) := by ac_rfl
        rw [hh] at hsmall
        omega
      have hJmono := pow_mono hK
      have hMone : 1≤M := by omega
      have hRD : D≤R := by
        have hh := Int.mul_le_mul_of_nonneg_left hMone (show 0≤D by omega)
        simpa [R] using hh
      have hEC : 0≤E+C := by omega
      have hRgap : R*(C+8)≤R*(E+C+8) := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      have hDgap : D*(C+8)≤R*(C+8) := Int.mul_le_mul_of_nonneg_right hRD (by omega)
      have hdmargin : D*(C+8)<P := by omega
      have hphaseLo := Int.mul_le_mul_of_nonneg_left (show 1≤v by omega) (show 0≤7*P by omega)
      have hphaseHi := Int.mul_le_mul_of_nonneg_left (show v≤D-1 by omega) (show 0≤7*P by omega)
      have hphaseHi' : 7*P*(D-1)=7*P*D-7*P := by grind
      rw [hphaseHi'] at hphaseHi
      have hD8 : 8*D≤D*(C+8) := by
        have hh := Int.mul_le_mul_of_nonneg_left (show 8≤C+8 by omega) (show 0≤D by omega)
        simpa [Int.mul_comm 8 D] using hh
      have hlo : D*2≤D*(run q d j:Int) := by unfold Bound at hb'; omega
      have hlo' := Int.le_of_mul_le_mul_left hlo hD
      have hclock' : 7*P-C≤(q:Int)+j := by
        have hh := ha j hjn
        unfold Bound at hh
        omega
      have hcl := Int.mul_le_mul_of_nonneg_left hclock' (show 0≤D by omega)
      have hcl' : D*(7*P-C)=7*P*D-D*C := by grind
      rw [hcl'] at hcl
      have hDc : D*(C+8)=D*C+8*D := by grind
      rw [hDc] at hdmargin
      have hhi : D*((run q d j:Int)+8)≤D*((q:Int)+j) := by
        unfold Bound at hb'
        rw [Int.mul_add]
        omega
      have hhi' := Int.le_of_mul_le_mul_left hhi hD
      exact ⟨by omega,by omega⟩
  · obtain ⟨z,e,he,hb⟩ := hlate n hK (by omega)
    have hs := hsep n hK (by omega) z e he hb
    simp only [Nat.sub_self,Int.pow_zero,Int.mul_one] at hs
    let p' := u+Dnew*z
    have hw : N+7*R*z=G*p' := by dsimp [p']; grind
    rw [hw] at hs
    have hpp : 0<p' := by
      have hh := Int.lt_of_mul_lt_mul_left (show G*0<G*p' by simpa using hs.1) (show 0≤G by omega)
      omega
    have hp'D : p'<Dnew := by
      have hh := Int.lt_of_mul_lt_mul_left (show G*p'<G*Dnew by rw [←hnew']; exact hs.2.1) (show 0≤G by omega)
      exact hh
    have hp'7 : p'%7≠0 := by
      dsimp [p']
      rw [Int.add_emod,Int.mul_emod,hnew7,Int.zero_mul,Int.zero_emod,Int.add_zero,Int.emod_emod]
      exact hu7
    have hid : G*(Dnew*(run q d n:Int)-7*P*p')=7*e := by
      change R*(run q d n:Int)=P*N+7*P*R*z+e at he
      rw [Int.mul_sub,←Int.mul_assoc,←hnew']
      have h1 : G*(7*P*p')=7*P*(G*p') := by ac_rfl
      rw [h1,←hw]
      have h2 : (7*R)*(run q d n:Int)=7*(R*(run q d n:Int)) := by ac_rfl
      rw [h2,he]
      grind only
    have hlo : G*(-(Dnew*E))≤G*(Dnew*(run q d n:Int)-7*P*p') := by
      rw [hid,Int.mul_neg]
      have hh := Int.mul_le_mul_of_nonneg_left hb.1 (by decide : 0≤(7:Int))
      have hEq : G*(Dnew*E)=7*(R*E) := by rw [←Int.mul_assoc,←hnew',Int.mul_assoc]
      rw [hEq]
      simpa [Int.mul_neg] using hh
    have hhi : G*(Dnew*(run q d n:Int)-7*P*p')≤G*(Dnew*E) := by
      rw [hid]
      have hh := Int.mul_le_mul_of_nonneg_left hb.2 (by decide : 0≤(7:Int))
      have hEq : G*(Dnew*E)=7*(R*E) := by rw [←Int.mul_assoc,←hnew',Int.mul_assoc]
      rwa [hEq]
    exact ⟨p',hpp,hp'D,hp'7,Int.le_of_mul_le_mul_left hlo hG,Int.le_of_mul_le_mul_left hhi hG⟩

#print axioms numerator_factor
#print axioms renewal_block
end BB6.Agent9Renewal
