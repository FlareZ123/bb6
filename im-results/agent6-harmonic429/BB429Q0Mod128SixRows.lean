import BB429NewResidue
import BB429RootEven8
import Lean.Elab.Tactic.Omega

namespace BB429Q0Mod128SixRows
open BB429NewResidue

private theorem noReach_even_not8 (a b : Nat) (ha : 0<a) (he : a%2=0)
    (hb : b%8≠2) : ¬ Reach a b := by
  intro hr
  rcases hr with ⟨n, hrun⟩
  have h := BB429RootEven8.rooted_positive_even_eight n a b hrun ha he
  omega

private theorem noReach_even_not4 (a b : Nat) (ha : 0<a) (he : a%2=0)
    (hb : b%4≠2) : ¬ Reach a b := by
  intro hr
  rcases hr with ⟨n, hrun⟩
  have h := BB429RootEven8.rooted_positive_even_eight n a b hrun ha he
  omega

private theorem noReach_notAllowed (a b : Nat)
    (hnot : ¬ BB429Mod8.Allowed a b) : ¬ Reach a b := by
  intro hr
  exact hnot (BB429NewResidue.reach_allowed a b hr)

private theorem noReach_odd_only_F (a b : Nat) (ha : 13≤a) (ho : a%2=1)
    (hb : b%4≠2)
    (hF : ¬ Reach ((a-3)/2) (b+a)) : ¬ Reach a b := by
  intro hr
  rcases BB429NewResidue.odd_back a b ha ho hr with
    ⟨x,y,hxy,hax,hby⟩ | ⟨x,y,hxy,hx,hy,hmod⟩
  · have hxe : x=(a-3)/2 := by omega
    have hye : y=b+a := by omega
    exact hF (by simpa [hxe,hye] using hxy)
  · omega

private theorem noReach_odd_split (a b : Nat) (ha : 13≤a) (ho : a%2=1)
    (hF : ¬ Reach ((a-3)/2) (b+a))
    (hS : ¬ Reach ((4*a+b-26)/4) ((b+4)/2)) : ¬ Reach a b := by
  intro hr
  rcases BB429NewResidue.odd_back a b ha ho hr with
    ⟨x,y,hxy,hax,hby⟩ | ⟨x,y,hxy,hx,hy,hmod⟩
  · have hxe : x=(a-3)/2 := by omega
    have hye : y=b+a := by omega
    exact hF (by simpa [hxe,hye] using hxy)
  · have hxe : x=(4*a+b-26)/4 := by omega
    have hye : y=(b+4)/2 := by omega
    exact hS (by simpa [hxe,hye] using hxy)

private theorem noReach_even (a b : Nat) (ha : 6≤a) (he : a%2=0)
    (hE : ¬ Reach ((4*a+b-14)/4) (b/2)) : ¬ Reach a b := by
  intro hr
  obtain ⟨x,y,hxy,hx,hy,hmod⟩ := BB429NewResidue.even_back a b ha he hr
  have hxe : x=(4*a+b-14)/4 := by omega
  have hye : y=b/2 := by omega
  exact hE (by simpa [hxe,hye] using hxy)

private theorem noReach_odd_3_1 (a b : Nat) (ha : 13≤a)
    (ha8 : a%8=3) (hb8 : b%8=1) : ¬ Reach a b := by
  apply noReach_odd_only_F a b (by omega) (by omega) (by omega)
  apply noReach_even_not8
  · omega
  · omega
  · omega

private theorem noReach_odd_7_1 (a b : Nat)
    (ha8 : a%8=7) (hb8 : b%8=1) : ¬ Reach a b := by
  apply noReach_notAllowed
  intro h
  unfold BB429Mod8.Allowed at h
  omega

private theorem noReach_odd_1_5 (a b : Nat) (ha : 29≤a)
    (ha8 : a%8=1) (hb8 : b%8=5) : ¬ Reach a b := by
  apply noReach_odd_only_F a b (by omega) (by omega) (by omega)
  have hc : 13≤(a-3)/2 := by omega
  have hco : ((a-3)/2)%2=1 := by omega
  apply noReach_odd_split ((a-3)/2) (b+a) hc hco
  · apply noReach_even_not4
    · omega
    · omega
    · omega
  · apply noReach_even_not4
    · omega
    · omega
    · omega

private theorem noReach_seed_of_p3 (a : Nat) (ha : 1000000≤a)
    (hmod : a%16=5)
    (hF : ¬ Reach ((a-21)/8) ((15*a-67)/4))
    (hS : ¬ Reach ((5*a-57)/8) ((11*a-63)/4)) :
    ¬ Reach a (2*a-13) := by
  apply noReach_odd_only_F a (2*a-13) (by omega) (by omega) (by omega)
  let c := (a-3)/2
  let d := 2*a-13+a
  have hc : 13≤c := by dsimp [c]; omega
  have hco : c%2=1 := by dsimp [c]; omega
  let p2fA := (c-3)/2
  let p2fB := d+c
  have hP2F : ¬ Reach p2fA p2fB := by
    apply noReach_odd_only_F p2fA p2fB (by dsimp [p2fA,c]; omega)
      (by dsimp [p2fA,c]; omega) (by dsimp [p2fB,p2fA,c,d]; omega)
    have hx : (p2fA-3)/2=(a-21)/8 := by dsimp [p2fA,c]; omega
    have hy : p2fB+p2fA=(15*a-67)/4 := by dsimp [p2fA,p2fB,c,d]; omega
    intro h
    have h' : Reach ((a-21)/8) ((15*a-67)/4) := by
      rw [←hx, ←hy]
      exact h
    exact hF h'
  let p2sA := (4*c+d-26)/4
  let p2sB := (d+4)/2
  have hP2S : ¬ Reach p2sA p2sB := by
    apply noReach_odd_only_F p2sA p2sB (by dsimp [p2sA,c,d]; omega)
      (by dsimp [p2sA,c,d]; omega) (by dsimp [p2sB,p2sA,c,d]; omega)
    have hx : (p2sA-3)/2=(5*a-57)/8 := by dsimp [p2sA,c,d]; omega
    have hy : p2sB+p2sA=(11*a-63)/4 := by dsimp [p2sA,p2sB,c,d]; omega
    intro h
    have h' : Reach ((5*a-57)/8) ((11*a-63)/4) := by
      rw [←hx, ←hy]
      exact h
    exact hS h'
  exact noReach_odd_split c d hc hco hP2F hP2S

/-- Six entire q=0 branch-10 residue sectors are excluded from the authentic
    BB429 blank-root orbit by the exact inverse grammar and root invariants. -/
theorem noReach_q0_six_mod128 (a : Nat) (ha : 1000000≤a)
    (hres : a%128=5 ∨ a%128=53 ∨ a%128=69 ∨ a%128=85 ∨ a%128=101 ∨ a%128=117) :
    ¬ Reach a (2*a-13) := by
  rcases hres with h5 | h53 | h69 | h85 | h101 | h117
  · apply noReach_seed_of_p3 a ha (by omega)
    · apply noReach_even
      · omega
      · omega
      · apply noReach_odd_3_1 <;> omega
    · apply noReach_even_not8 <;> omega
  · apply noReach_seed_of_p3 a ha (by omega)
    · apply noReach_even_not8 <;> omega
    · apply noReach_even
      · omega
      · omega
      · apply noReach_odd_7_1 <;> omega
  · apply noReach_seed_of_p3 a ha (by omega)
    · apply noReach_even
      · omega
      · omega
      · apply noReach_odd_7_1 <;> omega
    · apply noReach_even_not8 <;> omega
  · apply noReach_seed_of_p3 a ha (by omega)
    · apply noReach_even_not8 <;> omega
    · apply noReach_even
      · omega
      · omega
      · apply noReach_odd_1_5 <;> omega
  · apply noReach_seed_of_p3 a ha (by omega)
    · apply noReach_even
      · omega
      · omega
      · apply noReach_odd_1_5 <;> omega
    · apply noReach_even_not8 <;> omega
  · apply noReach_seed_of_p3 a ha (by omega)
    · apply noReach_even_not8 <;> omega
    · apply noReach_even
      · omega
      · omega
      · apply noReach_odd_3_1 <;> omega

/-- The q=0 branch-10 affine seed for d=7 and n=23+32u. -/
def q0A (u : Nat) : Nat := 13 * 2^(23+32*u) - 24*u - 19

private theorem two_pow_32_mul_ge (u : Nat) : u+1 ≤ 2^(32*u) := by
  induction u with
  | zero => decide
  | succ u ih =>
    calc
      u+1+1 ≤ 2*(u+1) := by omega
      _ ≤ 2*2^(32*u) := Nat.mul_le_mul_left 2 ih
      _ = 2^(32*u)*2 := by omega
      _ ≤ 2^(32*u)*2^32 := Nat.mul_le_mul_left (2^(32*u)) (by decide)
      _ = 2^(32*(u+1)) := by
        rw [← Nat.pow_add]
        congr 1 <;> omega

private theorem q0_pow_mod128 (u : Nat) : 2^(23+32*u)%128=0 := by
  have hd : 2^7 ∣ 2^(23+32*u) := Nat.pow_dvd_pow 2 (by omega)
  have hd' : 128 ∣ 2^(23+32*u) := by simpa using hd
  exact Nat.mod_eq_zero_of_dvd hd'

theorem q0A_ge_million (u : Nat) : 1000000≤q0A u := by
  have hp := two_pow_32_mul_ge u
  have hconst : 13*2^23=109051904 := by decide
  have hbig : 109051904*(u+1) ≤ 13*2^(23+32*u) := by
    calc
      109051904*(u+1) ≤ 109051904*2^(32*u) := Nat.mul_le_mul_left 109051904 hp
      _ = 13*(2^23*2^(32*u)) := by rw [← hconst, Nat.mul_assoc]
      _ = 13*2^(23+32*u) := by rw [← Nat.pow_add]
  have hlinear : 1000000+24*u+19 ≤ 109051904*(u+1) := by omega
  unfold q0A
  omega

theorem q0A_mod128_six (u : Nat)
    (hu : u%16=1 ∨ u%16=5 ∨ u%16=7 ∨ u%16=11 ∨ u%16=13 ∨ u%16=15) :
    q0A u%128=5 ∨ q0A u%128=53 ∨ q0A u%128=69 ∨
    q0A u%128=85 ∨ q0A u%128=101 ∨ q0A u%128=117 := by
  have hp := q0_pow_mod128 u
  have hsum : q0A u + 24*u + 19 = 13*2^(23+32*u) := by
    unfold q0A
    have hlarge := q0A_ge_million u
    dsimp [q0A] at hlarge
    omega
  have hdiv : (q0A u + 24*u + 19)%128=0 := by
    have hmult : (13*2^(23+32*u))%128=0 := by omega
    omega
  rcases hu with h1|h5|h7|h11|h13|h15 <;> omega

/-- All six odd u mod-16 sectors of the (n,d)=(23 mod 32,7) q=0
    branch-10 family are excluded. Ten other u mod-16 sectors remain open. -/
theorem q0_six_sectors_not_reachable (u : Nat)
    (hu : u%16=1 ∨ u%16=5 ∨ u%16=7 ∨ u%16=11 ∨ u%16=13 ∨ u%16=15) :
    ¬ Reach (q0A u) (2*q0A u-13) := by
  apply noReach_q0_six_mod128
  · exact q0A_ge_million u
  · exact q0A_mod128_six u hu

#print axioms noReach_q0_six_mod128
#print axioms q0_six_sectors_not_reachable
end BB429Q0Mod128SixRows
