import M8OddTowerPrior
import Lean.Elab.Tactic.Omega
namespace BB6.Agent15Research
open BB6.Agent29Depth

/-- Tower height one is precisely the formerly isolated deep family. -/
theorem tower_level_one_index (m t : Nat) :
    towerIndex m 1 t=deepIndex m t := by
  have hB := allOdd_BQ m
  have hQ := m8Geom4_mod_four (m+1) (by omega)
  have hQpos : 1≤allOddQ m := by
    have hh : allOddQ m%4=1 := by simpa [allOddQ] using hQ
    omega
  have hB3 : 3≤allOddB m := by omega
  have hr : towerR m 1=allOddB m-3 := by
    dsimp [towerR,towerS,towerSum]
    omega
  have hs : towerS m 1=1 := rfl
  have hx : towerX m 1=allOddB m := by
    dsimp [towerX]
    simp
  dsimp [towerIndex,deepIndex]
  rw [hr,hx,hs]
  simp

theorem tower_level_one_k (m t : Nat) :
    towerK m 1 t=deepK m t := by
  dsimp [towerK,towerX,deepK]
  simp

/-- Every tower level contains an infinite arithmetic progression of
    forbidden high stopping indices. -/
theorem tower_index_step (m r t : Nat) :
    towerIndex m r (t+1)=towerIndex m r t+
      towerX m r*(if m%4=1 then 16 else 8) := by
  by_cases hm : m%4=1
  · dsimp [towerIndex,deepTail]
    simp only [hm,ite_true,Nat.mul_add,Nat.mul_one]
    ac_rfl
  · dsimp [towerIndex,deepTail]
    simp only [hm,ite_false,Nat.mul_add,Nat.mul_one]
    ac_rfl

/-- For fixed odd m the exact normalized depth grows strictly with the
    tower level, proving distinct disjoint layer configurations. -/
theorem tower_depth_increases (m r t : Nat) (hm : m%2=1) :
    BB6.Agent15.oddDepth (towerK m r t) <
      BB6.Agent15.oddDepth (towerK m (r+1) t) := by
  rw [tower_odd_depth m r t hm, tower_odd_depth m (r+1) t hm]
  have he : (2*m+2)*(r+1)=(2*m+2)*r+(2*m+2) := by
    simp only [Nat.mul_add,Nat.mul_one]
  rw [he]
  by_cases hh : m%4=1
  · simp only [hh,ite_true]
    omega
  · simp only [hh,ite_false]
    omega

/-- No two distinct tower heights can encode the same source stopping
    right coordinate. -/
theorem tower_disjoint_levels (m r s t u : Nat)
    (hm : m%2=1) (hne : r≠s) :
    towerK m r t≠towerK m s u := by
  intro heq
  have hdepth := congrArg BB6.Agent15.oddDepth heq
  rw [tower_odd_depth m r t hm,tower_odd_depth m s u hm] at hdepth
  have hfactor : 0<2*m+2 := by omega
  have hh : (2*m+2)*r=(2*m+2)*s := by
    by_cases hmod : m%4=1
    · simp only [hmod,ite_true] at hdepth
      omega
    · simp only [hmod,ite_false] at hdepth
      omega
  exact hne (Nat.eq_of_mul_eq_mul_left hfactor hh)

#print axioms tower_level_one_index
#print axioms tower_index_step
#print axioms tower_depth_increases
#print axioms tower_disjoint_levels
end BB6.Agent15Research

