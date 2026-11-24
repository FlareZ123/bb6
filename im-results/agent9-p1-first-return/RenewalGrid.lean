import RenewalNumeric

namespace BB6.Agent9Renewal
set_option maxHeartbeats 2000000

/-- First-order binomial congruence, with an explicit integer quotient. -/
theorem power_linear (M : Int) (t : Nat) :
    ∃ z : Int, (1+M)^t=1+(t:Int)*M+M*M*z := by
  induction t with
  | zero => exact ⟨0,by simp⟩
  | succ t ih =>
    obtain ⟨z,hz⟩ := ih
    refine ⟨(t:Int)+(1+M)*z,?_⟩
    rw [Int.pow_succ,hz,Int.natCast_succ]
    grind

/-- A single seven-adic lift, with no use of a factorization or multiplicative order. -/
theorem power_lift7 (M v : Int) (hM : M=7*v) :
    ∃ w : Int, (1+M)^7=1+7*M*w ∧ w%7=1 := by
  let w := 1+3*M+5*M^2+5*M^3+3*M^4+M^5+v*M^5
  refine ⟨w,?_,?_⟩
  · dsimp [w]
    simp only [show (7:Nat)=6+1 by decide, Int.pow_succ, show (6:Nat)=5+1 by decide,
      show (5:Nat)=4+1 by decide, show (4:Nat)=3+1 by decide,
      show (3:Nat)=2+1 by decide, show (2:Nat)=1+1 by decide]
    grind
  · have he : w=1+7*(v*(3+5*M+5*M^2+3*M^3+M^4+v*M^4)) := by
      dsimp [w]
      grind
    rw [he,Int.add_mul_emod_self_left]
    decide


/-- General period data. The normalized period and both normalized factors
are units modulo seven; the next grid is exact. -/
structure RenewalGrid (D G : Int) (L : Nat) where
  pos : 0<D
  odd : D%2=1
  Gpos : 0<G
  divides : D ∣ (2:Int)^L-1
  Mpos : 0<(2:Int)^L-1
  U : Int
  V : Int
  l : Int
  Dfactor : D=7*G*U
  Mfactor : (2:Int)^L-1=7*G*V
  Lfactor : (L:Int)=l*G
  Uunit : U%7≠0
  Vunit : V%7≠0
  lunit : l%7≠0

#print axioms power_linear
#print axioms power_lift7
/-- A nonzero integer residue product and positivity certify the next grid. -/
theorem odd_factor (a b : Int) (h : (a*b)%2=1) : a%2=1 ∧ b%2=1 := by
  rw [Int.mul_emod] at h
  have ha := Int.emod_nonneg a (by decide : (2:Int)≠0)
  have hb := Int.emod_nonneg b (by decide : (2:Int)≠0)
  have ha' := Int.emod_lt_of_pos a (by decide : 0<(2:Int))
  have hb' := Int.emod_lt_of_pos b (by decide : 0<(2:Int))
  have ha2 : a%2=0 ∨ a%2=1 := by omega
  have hb2 : b%2=0 ∨ b%2=1 := by omega
  rcases ha2 with h1|h1 <;> rcases hb2 with h2|h2 <;> rw [h1,h2] at h <;> omega

theorem odd_mul (a b : Int) (ha : a%2=1) (hb : b%2=1) : (a*b)%2=1 := by
  rw [Int.mul_emod,ha,hb]; decide

theorem grid_next (D G : Int) (L : Nat) (g : RenewalGrid D G L)
    (hG7 : G%7=0) :
    Nonempty (RenewalGrid (49*g.U*((2:Int)^L-1)) (49*G) (L*49*g.U.toNat)) := by
  let M := (2:Int)^L-1
  have hM : 0<M := g.Mpos
  have hU : 0<g.U := by
    have hp := g.pos
    have h := g.Dfactor
    have hG := g.Gpos
    by_cases hu : 0<g.U
    · exact hu
    · have hh := Int.mul_nonpos_of_nonneg_of_nonpos (show 0≤7*G by omega) (show g.U≤0 by omega)
      omega
  let t := g.U.toNat
  have ht : (t:Int)=g.U := Int.toNat_of_nonneg (by omega)
  have htpos : 0<t := by omega
  have hLpos : 0<L := by
    by_cases he : L=0
    · simp [M,he] at hM
    · omega
  let L' := L*49*t
  have hL' : 0<L' := by dsimp [L']; exact Nat.mul_pos (Nat.mul_pos hLpos (by decide)) htpos
  have hLcast : (L':Int)=(L:Int)*49*g.U := by dsimp [L']; push_cast; rw [ht]
  have hMfact : M=7*G*g.V := g.Mfactor
  obtain ⟨w1,hw1,hu1⟩ := power_lift7 M (G*g.V) (by grind)
  let M1 := 7*M*w1
  obtain ⟨w2,hw2,hu2⟩ := power_lift7 M1 (M*w1) (by dsimp [M1]; ac_rfl)
  let M2 := 7*M1*w2
  have h1 : (2:Int)^(L*7)=1+M1 := by
    rw [Int.pow_mul,show (2:Int)^L=1+M by dsimp [M]; omega,hw1]
  have h2 : (2:Int)^(L*49)=1+M2 := by
    rw [show L*49=L*7*7 by omega,Int.pow_mul,h1,hw2]
  obtain ⟨z,hz⟩ := power_linear M2 t
  have h3 : (2:Int)^L'-1=M2*(g.U+M2*z) := by
    dsimp [L']
    rw [Int.pow_mul,h2,hz,ht]
    grind
  have hM2mod : M2%7=0 := by
    dsimp [M2]
    have he : 7*M1*w2=7*(M1*w2) := by ac_rfl
    rw [he,Int.mul_emod]; simp
  have hw3 : (g.U+M2*z)%7≠0 := by
    rw [Int.add_emod,Int.mul_emod,hM2mod,Int.zero_mul,Int.zero_emod,Int.add_zero,Int.emod_emod]
    exact g.Uunit
  let V' := g.V*w1*w2*(g.U+M2*z)
  have hV' : V'%7≠0 := unit_mul7 _ _ (unit_mul7 _ _ (unit_mul7 _ _ g.Vunit (by omega)) (by omega)) hw3
  have hM' : (2:Int)^L'-1=7*(49*G)*V' := by
    rw [h3]
    change (7*(7*M*w1)*w2)*(g.U+M2*z)=7*(49*G)*(g.V*w1*w2*(g.U+M2*z))
    rw [hMfact]
    grind only
  have hD' : 49*g.U*M=7*(49*G)*(g.U*g.V) := by rw [hMfact]; grind only
  have hU' : (g.U*g.V)%7≠0 := unit_mul7 _ _ g.Uunit g.Vunit
  have hLfactor : (L':Int)=(g.l*g.U)*(49*G) := by rw [hLcast,g.Lfactor]; ac_rfl
  have hGpos : 0<49*G := by have := g.Gpos; omega
  have hDpos : 0<49*g.U*M := Int.mul_pos (by omega) hM
  have hMpos' : 0<(2:Int)^L'-1 := by
    have hp := pow_mono (show 1≤L' by omega)
    simp at hp
    omega
  have hUodd : g.U%2=1 := by
    have h := g.odd
    rw [g.Dfactor] at h
    exact (odd_factor _ _ h).2
  have hModd : M%2=1 := by
    -- Every positive power of two is even.
    have hpow : (2:Int)^L=2*(2:Int)^(L-1) := by
      have h : L-1+1=L := by omega
      calc
        (2:Int)^L=(2:Int)^(L-1+1) := congrArg (fun j : Nat => (2:Int)^j) h.symm
        _ = _ := by rw [Int.pow_succ]; ac_rfl
    dsimp [M]
    omega
  have hDodd : (49*g.U*M)%2=1 := odd_mul _ _ (odd_mul _ _ (by decide) hUodd) hModd
  obtain ⟨s,hs⟩ := g.divides
  obtain ⟨g0,hg0⟩ := Int.dvd_iff_emod_eq_zero.mpr hG7
  have hMdiv : M=49*g.U*(g0*s) := by
    change M=D*s at hs
    calc
      M = D*s := hs
      _ = (7*G*g.U)*s := congrArg (fun x : Int => x*s) g.Dfactor
      _ = (7*(7*g0)*g.U)*s := congrArg (fun x : Int => 7*x*g.U*s) hg0
      _ = _ := by grind only
  obtain ⟨v,hv⟩ := power_linear M (49*t)
  have hdiv' : 49*g.U*M ∣ (2:Int)^L'-1 := by
    refine ⟨1+g0*s*v,?_⟩
    have hh : (2:Int)^L'=(1+M)^(49*t) := by
      rw [show L'=L*(49*t) by dsimp [L']; ac_rfl,Int.pow_mul,show (2:Int)^L=1+M by dsimp [M]; omega]
    rw [hh,hv]
    push_cast
    rw [ht]
    have hmul : M*M*v=(49*g.U*M)*(g0*s*v) := by
      calc
        M*M*v = M*(M*v) := by ac_rfl
        _ = M*((49*g.U*(g0*s))*v) := by rw [←hMdiv]
        _ = _ := by ac_rfl
    rw [hmul]
    grind only
  exact ⟨⟨hDpos,hDodd,hGpos,hdiv',hMpos',g.U*g.V,V',g.l*g.U,hD',hM',hLfactor,hU',hV',unit_mul7 _ _ g.lunit g.Uunit⟩⟩

#print axioms grid_next
end BB6.Agent9Renewal
