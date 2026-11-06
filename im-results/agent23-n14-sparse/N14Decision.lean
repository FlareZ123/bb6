import N14SourceBridge
import N14Bounds
import GenericBudgetBlocked
import RootWallSharpArithmetic
import P1Gate

namespace Agent23N14
open BB6.Agent1Quarter BB6.Agent47P1 BB6.Shadow BB6.Agent23RootWall
open BB6.Agent1ShortCone BB6.Agent9Budget BB6.Agent4Cone BB6.Agent50P1

private def nn (r : Nat) : Nat := 65536*r+14
private def rootB (r : Nat) : Nat := 14*2^(nn r)-2*(nn r)-16

private theorem rootPower (r : Nat) :
    rootB r + 2*(nn r)+16=14*2^(nn r) := by
  have hn : 14≤nn r := by dsimp [nn]; omega
  have hp := large_pow (nn r) hn
  have hp14 := Nat.mul_le_mul_left 14 hp
  dsimp [rootB]
  omega

private theorem massPower (r b d m : Nat)
    (hcone : OddCone (rootB r) 3 b d m) :
    b+d+2*m+2*(nn r)+13=14*2^(nn r) := by
  have hr := rootPower r
  have hm := odd_cone_mass (rootB r) 3 b d m hcone
  omega

private theorem massEncoded (r b d m : Nat)
    (hcone : OddCone (rootB r) 3 b d m) :
    b+d+2*m+2*(65536*r+19)+3=56*2^(65536*r+12) := by
  have hm := massPower r b d m hcone
  have he : nn r=65536*r+12+2 := by
    change 65536*r+14=65536*r+12+2
    omega
  have hp : (2:Nat)^(nn r)=4*2^(65536*r+12) := by
    rw [he,Nat.pow_add]
    simp [Nat.mul_comm]
  rw [hp] at hm
  dsimp [nn] at hm
  omega

private theorem start_form (r : Nat) (hr : 1≤r) :
    8 ≤ rootB r ∧ rootB r % 4 = 0 := by
  have hroot := rootPower r
  have hn : nn r = 65536*r+14 := rfl
  have hn2 : 2≤nn r := by omega
  have hpow4 : 4 ∣ 2^(nn r) := by
    have hp : 2^2 ∣ (2:Nat)^(nn r) := Nat.pow_dvd_pow 2 hn2
    simpa using hp
  have hmod : 2^(nn r) % 4 = 0 := Nat.dvd_iff_mod_eq_zero.mp hpow4
  have hp := large_pow (nn r) (by omega)
  have hlarge := Nat.mul_le_mul_left 14 hp
  dsimp [rootB,nn] at *
  constructor <;> omega

private theorem source_wall_gap (r b d m : Nat) (hr : 1≤r)
    (hcone : OddCone (rootB r) 3 b d m) (hmod : b%4=0) :
    4*(nn r+m)<b := by
  have hm := authentic_n14_sparse_odd_cone_cost r b d m hr (by simpa [rootB,nn] using hcone) hmod
  have hl := odd_cone_left_bound (rootB r) 3 b d m hcone
  exact wall_impossible (nn r) (rootB r) b m (by dsimp [nn]; omega)
    hm (rootPower r) hl

private theorem source_depth (r b d m t k c : Nat) (hr : 1≤r)
    (hcone : OddCone (rootB r) 3 b d m)
    (hmod : b%4=0)
    (hi : inverseAt b d t=some (k,c)) : t≤8 := by
  obtain ⟨w,z,alpha,hmem,hz,hw,hoff,hscaled⟩ :=
    authentic_n14_sparse_odd_cone_encoded r b d m hr
      (by simpa [rootB,nn] using hcone) hmod
  have hm := nodes_small r m z hmem
  have hmass := massEncoded r b d m hcone
  exact source_depth_le8_mod256 (65536*r+12) (65536*r+19)
    m b d w z alpha t k c hmass hoff hscaled (by omega)
    (by omega) (nodes_no256 r m z hmem) hi

private theorem source_c_ge_two (r b d m t k c : Nat) (hr : 1≤r)
    (hcone : OddCone (rootB r) 3 b d m)
    (hmod : b%4=0)
    (hi : inverseAt b d t=some (k,c)) : 2≤c := by
  have ht := source_depth r b d m t k c hr hcone hmod hi
  have hscale : 2^t≤256 := by
    have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) ht
    simpa only [show (2:Nat)^8=256 by decide] using hh
  by_cases hc : c≤1
  · have hc4 : c+3≤4 := by omega
    have hupper : 2^t*(c+3)≤256*4 := Nat.mul_le_mul hscale hc4
    have hshift := inverseAt_power b d t k c hi
    have hsum : b+d≤2048 := by omega
    have hmass := massEncoded r b d m hcone
    have hm := authentic_n14_sparse_odd_cone_cost r b d m hr (by simpa [rootB,nn] using hcone) hmod
    have hp := large_pow (65536*r+12) (by omega)
    have hp56 := Nat.mul_le_mul_left 56 hp
    omega
  · omega

private theorem source_even_gap
    (r b d m t k c j : Nat) (hr : 1≤r)
    (hcone : OddCone (rootB r) 3 b d m)
    (hb : 8≤b) (hmod : b%4=0) (hd : d%2=1)
    (hi : inverseAt b d t=some (k,c)) (hceven : c%2=0) :
    2*k+8≠14*2^j := by
  intro he
  have hm := authentic_n14_sparse_odd_cone_cost r b d m hr (by simpa [rootB,nn] using hcone) hmod
  have hc := source_c_ge_two r b d m t k c hr hcone hmod hi
  have hp := inverseAt_power b d t k c hi
  have him := inverseAt_exact_mass b d t k c (by omega) hmod hd hi
  have hlin : 2*k+c+2*t+1=b+d := by omega
  have hmass := massPower r b d m hcone
  have hsharp := critical_root_even_exit_sharp_budget (nn r)
    b d m t k c j (by dsimp [nn]; omega) hmass hmod hp hceven hc hlin he
  rcases hsharp with hcost | ⟨_,_,hwall⟩
  · exact (big_cost_impossible (nn r) m (by dsimp [nn]; omega) hm) hcost
  · have hgap := source_wall_gap r b d m hr hcone hmod
    omega

private theorem root_blocked (r : Nat) (hr : 1≤r) :
    Blocked (rootB r) 3 := by
  have hform := start_form r hr
  apply blocked_of_uniform_cone_exit_budget 8 (rootB r) 3
  · intro b d m hcone hmod
    exact authentic_n14_sparse_odd_cone_cost r b d m hr (by simpa [rootB,nn] using hcone) hmod
  · intro b d m hcone hmod
    have hg := source_wall_gap r b d m hr hcone hmod
    have hn : 14≤nn r := by dsimp [nn]; omega
    omega
  · intro b d m t k hcone hmod hi
    have hc := source_c_ge_two r b d m t k 1 hr hcone hmod hi
    omega
  · intro b d m t k c j hcone hb hmod hd hi hc
    exact source_even_gap r b d m t k c j hr hcone hb hmod hd hi hc
  · exact hform.2
  · decide

/-- The original blank-entry P1 critical gateway is unreachable, for every
    n=65536*r+14 with r≥1. -/
theorem authentic_n14_sparse_critical_unreachable
    (r : Nat) (hr : 1≤r) :
    ¬BB6.Agent1.Reach 2
      (14*2^(65536*r+14)-2*(65536*r+14)-10) := by
  intro hreach
  let target := 14*2^(nn r)-2*(nn r)-10
  have hroot := rootPower r
  have hform := start_form r hr
  have htlarge : 10≤target := by
    dsimp [target]
    omega
  have hn : nn r=65536*r+14 := rfl
  have hpow4 : (2:Nat)^(nn r) % 4=0 := by
    have hp : (2:Nat)^2 ∣ 2^(nn r) := Nat.pow_dvd_pow 2 (by dsimp [nn]; omega)
    exact Nat.dvd_iff_mod_eq_zero.mp (by simpa using hp)
  have htmod : target%4=2 := by
    dsimp [target,nn,rootB] at *
    omega
  have htarget : BB6.Agent1.Reach 2 target := by simpa [target,nn] using hreach
  have hh := critical_target_implies_three target htlarge htmod htarget
  have heq : target-6=rootB r := by
    dsimp [target]
    omega
  exact (blocked_no_reach (rootB r) 3 (root_blocked r hr)) (by simpa only [heq] using hh)

#print axioms root_blocked
#print axioms authentic_n14_sparse_critical_unreachable
end Agent23N14
