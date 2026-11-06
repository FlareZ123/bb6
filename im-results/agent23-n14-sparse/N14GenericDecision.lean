import N14GenericSource
import N14Bounds
import GenericBudgetBlocked
import RootWallSharpArithmetic
import P1Gate

namespace Agent23N14Generic
open BB6.Agent1Quarter BB6.Agent47P1 BB6.Shadow BB6.Agent23RootWall
open BB6.Agent1ShortCone BB6.Agent9Budget BB6.Agent4Cone BB6.Agent50P1
open Agent23N14

private def nn (q : Nat) : Nat := 16*q+14
private def rootB (q : Nat) : Nat := 14*2^(nn q)-2*(nn q)-16

structure Certificate (q : Nat) where
  nodes : List (Nat×Nat)
  root : (0,8*q+8)∈nodes
  closed : ∀ m z t v zp, (m,z)∈nodes →
      z=2^t*v → 2*zp+1=16*q+19+m+t+v →
      (m+t+1,zp)∈nodes
  small : ∀ m z, (m,z)∈nodes → m≤8
  nodiv : ∀ m z, (m,z)∈nodes → ¬256∣z

private theorem rootPower (q : Nat) :
    rootB q + 2*(nn q)+16=14*2^(nn q) := by
  have hn : 14≤nn q := by dsimp [nn]; omega
  have hp := large_pow (nn q) hn
  have hp14 := Nat.mul_le_mul_left 14 hp
  dsimp [rootB]
  omega

private theorem massPower (q b d m : Nat)
    (hcone : OddCone (rootB q) 3 b d m) :
    b+d+2*m+2*(nn q)+13=14*2^(nn q) := by
  have hr := rootPower q
  have hm := odd_cone_mass (rootB q) 3 b d m hcone
  omega

private theorem massEncoded (q b d m : Nat)
    (hcone : OddCone (rootB q) 3 b d m) :
    b+d+2*m+2*(16*q+19)+3=56*2^(16*q+12) := by
  have hm := massPower q b d m hcone
  have he : nn q=16*q+12+2 := by
    change 16*q+14=16*q+12+2
    omega
  have hp : (2:Nat)^(nn q)=4*2^(16*q+12) := by
    rw [he,Nat.pow_add]
    simp [Nat.mul_comm]
  rw [hp] at hm
  dsimp [nn] at hm
  omega

private theorem start_form (q : Nat) (hq : 1≤q) :
    8≤rootB q ∧ rootB q%4=0 := by
  have hroot := rootPower q
  have hn : nn q = 16*q+14 := rfl
  have hn2 : 2≤nn q := by omega
  have hpow4 : 4 ∣ 2^(nn q) := by
    have hp : 2^2 ∣ (2:Nat)^(nn q) := Nat.pow_dvd_pow 2 hn2
    simpa using hp
  have hmod : 2^(nn q)%4=0 := Nat.dvd_iff_mod_eq_zero.mp hpow4
  have hp := large_pow (nn q) (by omega)
  have hlarge := Nat.mul_le_mul_left 14 hp
  dsimp [rootB,nn] at *
  constructor <;> omega

private theorem hub_cost (q b d m : Nat) (hq : 1≤q)
    (cfg : Certificate q) (hcone : OddCone (rootB q) 3 b d m)
    (hmod : b%4=0) : m≤8 := by
  obtain ⟨w,z,alpha,hmem,_,_,_,_⟩ :=
    cone_encoded q hq cfg.nodes cfg.root cfg.closed cfg.small cfg.nodiv
      b d m (by simpa [rootB,nn] using hcone) hmod
  exact cfg.small m z hmem

private theorem source_wall_gap (q b d m : Nat) (hq : 1≤q)
    (cfg : Certificate q) (hcone : OddCone (rootB q) 3 b d m)
    (hmod : b%4=0) : 4*(nn q+m)<b := by
  have hm := hub_cost q b d m hq cfg hcone hmod
  have hl := odd_cone_left_bound (rootB q) 3 b d m hcone
  exact wall_impossible (nn q) (rootB q) b m (by dsimp [nn]; omega)
    hm (rootPower q) hl

private theorem source_depth (q b d m t k c : Nat) (hq : 1≤q)
    (cfg : Certificate q) (hcone : OddCone (rootB q) 3 b d m)
    (hmod : b%4=0) (hi : inverseAt b d t=some (k,c)) : t≤8 := by
  obtain ⟨w,z,alpha,hmem,hz,hw,hoff,hscaled⟩ :=
    cone_encoded q hq cfg.nodes cfg.root cfg.closed cfg.small cfg.nodiv
      b d m (by simpa [rootB,nn] using hcone) hmod
  have hm := cfg.small m z hmem
  have hmass := massEncoded q b d m hcone
  exact source_depth_le8_mod256 (16*q+12) (16*q+19)
    m b d w z alpha t k c hmass hoff hscaled (by omega)
    (by omega) (cfg.nodiv m z hmem) hi

private theorem source_c_ge_two (q b d m t k c : Nat) (hq : 1≤q)
    (cfg : Certificate q) (hcone : OddCone (rootB q) 3 b d m)
    (hmod : b%4=0) (hi : inverseAt b d t=some (k,c)) : 2≤c := by
  have ht := source_depth q b d m t k c hq cfg hcone hmod hi
  have hscale : 2^t≤256 := by
    have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) ht
    simpa only [show (2:Nat)^8=256 by decide] using hh
  by_cases hc : c≤1
  · have hc4 : c+3≤4 := by omega
    have hupper : 2^t*(c+3)≤256*4 := Nat.mul_le_mul hscale hc4
    have hshift := inverseAt_power b d t k c hi
    have hsum : b+d≤2048 := by omega
    have hmass := massEncoded q b d m hcone
    have hm := hub_cost q b d m hq cfg hcone hmod
    have hp := large_pow (16*q+12) (by omega)
    have hp56 := Nat.mul_le_mul_left 56 hp
    omega
  · omega

private theorem source_even_gap (q b d m t k c j : Nat) (hq : 1≤q)
    (cfg : Certificate q) (hcone : OddCone (rootB q) 3 b d m)
    (hb : 8≤b) (hmod : b%4=0) (hd : d%2=1)
    (hi : inverseAt b d t=some (k,c)) (hceven : c%2=0) :
    2*k+8≠14*2^j := by
  intro he
  have hm := hub_cost q b d m hq cfg hcone hmod
  have hc := source_c_ge_two q b d m t k c hq cfg hcone hmod hi
  have hp := inverseAt_power b d t k c hi
  have him := inverseAt_exact_mass b d t k c (by omega) hmod hd hi
  have hlin : 2*k+c+2*t+1=b+d := by omega
  have hmass := massPower q b d m hcone
  have hsharp := critical_root_even_exit_sharp_budget (nn q)
    b d m t k c j (by dsimp [nn]; omega) hmass hmod hp hceven hc hlin he
  rcases hsharp with hcost | ⟨_,_,hwall⟩
  · exact (big_cost_impossible (nn q) m (by dsimp [nn]; omega) hm) hcost
  · have hgap := source_wall_gap q b d m hq cfg hcone hmod
    omega

private theorem root_blocked (q : Nat) (hq : 1≤q)
    (cfg : Certificate q) : Blocked (rootB q) 3 := by
  have hform := start_form q hq
  apply blocked_of_uniform_cone_exit_budget 8 (rootB q) 3
  · intro b d m hcone hmod
    exact hub_cost q b d m hq cfg hcone hmod
  · intro b d m hcone hmod
    have hg := source_wall_gap q b d m hq cfg hcone hmod
    have hn : 14≤nn q := by dsimp [nn]; omega
    omega
  · intro b d m t k hcone hmod hi
    have hc := source_c_ge_two q b d m t k 1 hq cfg hcone hmod hi
    omega
  · intro b d m t k c j hcone hb hmod hd hi hc
    exact source_even_gap q b d m t k c j hq cfg hcone hb hmod hd hi hc
  · exact hform.2
  · decide

/-- Any closed finite cost-eight scalar graph excludes a genuine P1
    n=16q+14 critical gateway, uniformly in q≥1. -/
theorem critical_unreachable_of_certificate
    (q : Nat) (hq : 1≤q) (cfg : Certificate q) :
    ¬BB6.Agent1.Reach 2
      (14*2^(16*q+14)-2*(16*q+14)-10) := by
  intro hreach
  let target := 14*2^(nn q)-2*(nn q)-10
  have hroot := rootPower q
  have hform := start_form q hq
  have htlarge : 10≤target := by
    dsimp [target]
    omega
  have hn : nn q=16*q+14 := rfl
  have hpow4 : (2:Nat)^(nn q)%4=0 := by
    have hp : (2:Nat)^2 ∣ 2^(nn q) := Nat.pow_dvd_pow 2 (by dsimp [nn]; omega)
    exact Nat.dvd_iff_mod_eq_zero.mp (by simpa using hp)
  have htmod : target%4=2 := by
    dsimp [target,nn,rootB] at *
    omega
  have htarget : BB6.Agent1.Reach 2 target := by simpa [target,nn] using hreach
  have hh := critical_target_implies_three target htlarge htmod htarget
  have heq : target-6=rootB q := by
    dsimp [target]
    omega
  exact (blocked_no_reach (rootB q) 3 (root_blocked q hq cfg)) (by simpa only [heq] using hh)

#print axioms critical_unreachable_of_certificate
end Agent23N14Generic
