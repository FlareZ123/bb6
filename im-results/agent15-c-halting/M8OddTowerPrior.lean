import M8OddTower
import Lean.Elab.Tactic.Omega
namespace BB6.Agent15Research

/-- Rearrange the tower index equation to display divisibility by its
    bottom exponential 2^(2m+2). -/
theorem tower_index_rearranged (m r t : Nat) (hr : 1≤r) :
    towerIndex m r t+3*m+3+3*m*(towerS m r-1)=
      towerX m r*(m+deepTail m t+1) := by
  let S := towerS m r
  let X := towerX m r
  let R := towerR m r
  let T := deepTail m t
  let J := towerIndex m r t
  have hSpos : 1≤S := by
    simpa [S,towerS] using towerSum_nonzero (allOddB m) r hr
  have hSsub : S-1+1=S := by omega
  have hRS : R+3*S=X := towerR_plus m r hr
  have hmul : R*(m+1)+3*S*(m+1)=X*(m+1) := by
    calc
      R*(m+1)+3*S*(m+1)=(R+3*S)*(m+1) :=
        (Nat.add_mul R (3*S) (m+1)).symm
      _=X*(m+1) := by rw [hRS]
  have hprod : 3*S*(m+1)=3*m*S+3*S := by
    simp only [Nat.mul_add,Nat.mul_one]
    ac_rfl
  have hJ : J+3+3*m*S=X*(m+T+1) := by
    calc
      J+3+3*m*S=R*(m+1)+3*S*(m+1)+X*T := by
        change (R*(m+1)+X*T+3*(S-1))+3+3*m*S =
          R*(m+1)+3*S*(m+1)+X*T
        have hh : 3*(S-1)+3=3*S := by omega
        omega
      _=X*(m+1)+X*T := by rw [hmul]
      _=X*(m+T+1) := by
        rw [show m+T+1=(m+1)+T by omega]
        simp only [Nat.mul_add]
  have hsplit : 3*m*S=3*m*(S-1)+3*m := by
    calc
      3*m*S=3*m*((S-1)+1) := by rw [hSsub]
      _=3*m*(S-1)+3*m := by
        simp only [Nat.mul_add,Nat.mul_one]
  change J+3*m+3+3*m*(S-1)=X*(m+T+1)
  omega

/-- Each positive tower level retains the bottom 2^(2m+2) divisibility
    of the prior dyadic-sieve test index. -/
theorem tower_prior_divisible (m r t : Nat) (hr : 1≤r) :
    allOddB m ∣ towerIndex m r t+3*m+3 := by
  have hJ := tower_index_rearranged m r t hr
  have hx : allOddB m ∣ towerX m r := by
    cases r with
    | zero => omega
    | succ r =>
        refine ⟨allOddB m^r,?_⟩
        dsimp [towerX]
        rw [Nat.pow_succ]
        ac_rfl
  have hs : allOddB m ∣ towerS m r-1 := by
    cases r with
    | zero => omega
    | succ r =>
        refine ⟨towerSum (allOddB m) r,?_⟩
        change (allOddB m*towerSum (allOddB m) r+1)-1 =
          allOddB m*towerSum (allOddB m) r
        omega
  have hright : allOddB m ∣
      towerX m r*(m+deepTail m t+1) := by
    rcases hx with ⟨x,hx⟩
    refine ⟨x*(m+deepTail m t+1),?_⟩
    rw [hx]
    ac_rfl
  have hleft : allOddB m ∣ 3*m*(towerS m r-1) := by
    rcases hs with ⟨x,hx⟩
    refine ⟨3*m*x,?_⟩
    rw [hx]
    ac_rfl
  have htotal : allOddB m ∣
      (towerIndex m r t+3*m+3)+(3*m*(towerS m r-1)) := by
    rw [hJ]
    exact hright
  exact (Nat.dvd_add_iff_left hleft).mpr htotal

/-- The old all-depth tower forbids residue 2^(n+2), whereas every
    present tower level has the ZERO residue for all admissible n. -/
theorem tower_prior_zero (m r t n : Nat)
    (hr : 1≤r) (hn : n+4≤2*m+2) :
    (towerIndex m r t+3*m+3)%2^(n+4)=0 := by
  have hdvd : 2^(n+4)∣allOddB m := by
    obtain ⟨q,hq⟩ : ∃q,2*m+2=n+4+q :=
      ⟨2*m+2-(n+4),by omega⟩
    refine ⟨2^q,?_⟩
    dsimp [allOddB]
    rw [hq,Nat.pow_add]
  exact Nat.mod_eq_zero_of_dvd
    (Nat.dvd_trans hdvd (tower_prior_divisible m r t hr))

theorem tower_prior_avoided (m r t n : Nat)
    (hr : 1≤r) (hn : n+4≤2*m+2) :
    ¬((towerIndex m r t+3*m+3)%2^(n+4)=2^(n+2)) := by
  have hz := tower_prior_zero m r t n hr hn
  have hp : 0<2^(n+2) := Nat.pow_pos (by decide)
  omega

#print axioms tower_prior_avoided
end BB6.Agent15Research

