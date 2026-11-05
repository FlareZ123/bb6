import FirstFork

namespace CascadeFirstFork
open CascadeResetInverse CascadeUniformFatal CascadeManyShield

private theorem pow_at_least_16 (n:Nat) (hn:4≤n) : 16 ≤ 2^n := by
  have hp:2^4≤2^n:=Nat.pow_le_pow_right (by decide) hn
  exact hp

private theorem two_n_le_pow (n:Nat) (hn:4≤n) : 2*n ≤ 2^n := by
  have h:∀ k:Nat, 2*(k+4)≤2^(k+4):=by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      rw [show k+1+4=k+4+1 by omega,Nat.pow_succ]
      omega
  have he:n=(n-4)+4:=by omega
  rw [he]
  exact h (n-4)

private theorem odd_band_scale_unique (v k j:Nat)
    (hb:6*2^k+1≤v ∧ v≤8*2^k-1)
    (hj:6*2^j+1≤v ∧ v≤8*2^j-1) : k=j := by
  by_cases heq:k=j
  · exact heq
  by_cases hlt:k<j
  · have hpow:2^(k+1)≤2^j:=Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (by omega)
    have he:2^(k+1)=2*2^k:=by rw [Nat.pow_succ];omega
    rw [he] at hpow
    omega
  · have hpow:2^(j+1)≤2^k:=Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (by omega)
    have he:2^(j+1)=2*2^j:=by rw [Nat.pow_succ];omega
    rw [he] at hpow
    omega

private theorem odd_tzero_in_dyadic_gap (n u:Nat) (hn:4≤n)
    (hl:3*2^n≤u) (hu:u≤4*2^n) :
    ¬ ∃ k d, (6*2^k+1≤d ∧ d≤8*2^k-1) ∧ 2*u+5=3*d := by
  rintro ⟨k,d,⟨hlo,hhi⟩,heq⟩
  have hp := pow_at_least_16 n hn
  have hdlo : 2*2^n < d := by omega
  have hdhi : d < 3*2^n := by omega
  by_cases hk : k+2≤n
  · have hpow:2^(k+2)≤2^n := Nat.pow_le_pow_right (by decide:0<(2:Nat)) hk
    have he:2^(k+2)=4*2^k := by rw [Nat.pow_add];omega
    rw [he] at hpow
    omega
  · have hnk : n≤k+1 := by omega
    have hpow:2^n≤2^(k+1) := Nat.pow_le_pow_right (by decide:0<(2:Nat)) hnk
    have he:2^(k+1)=2*2^k := by rw [Nat.pow_succ];omega
    rw [he] at hpow
    omega

/-- If the odd parameter has exactly 3-adic valuation two, the
    near-top target has precisely two source first-reset parents. -/
theorem near_top_exact_two (n u A q:Nat) (hn:4≤n)
    (hA:3≤A) (hclose:u+A=4*2^n)
    (hsize:8*A≤5*2^n)
    (hdiv9:(2*u+5)%9=0) (hnot27:(2*u+5)%27≠0) :
    ResetParent q u ↔ q=oddPre n u ∨ q=evenPre n A := by
  have ho := odd_parent_near_top n u A hn hclose hsize hdiv9
  have he := even_parent_near_top n u A hn hA hclose hsize
  have hpow2 : 2^n=2*2^(n-1) := by
    have hh:2^n=2^((n-1)+1):=congrArg (fun m:Nat=>2^m) (by omega)
    rw [Nat.pow_succ] at hh
    omega
  have hbandE : 6*2^(n-1)-1≤u ∧ u≤8*2^(n-1)-3 := by omega
  have heveneq : 2*u=8*2^(n-1)+evenPre n A+(n-1) := by
    have hh:=two_n_le_pow n hn
    dsimp [evenPre]
    omega
  have hbiglo:3*2^n≤u := by omega
  have hbighi:u≤4*2^n := by omega
  let d0 := (2*u+5)/9
  have hd0:9*d0=2*u+5 := by
    have hm:=Nat.mod_add_div (2*u+5) 9
    dsimp [d0]
    omega
  have hpow4:2^n=4*2^(n-2) := by
    have hh:2^n=2^((n-2)+2):=congrArg (fun m:Nat=>2^m) (by omega)
    rw [Nat.pow_add] at hh
    omega
  have hlarge : 4 ≤ 2^(n-2) := by
    have hp := pow_at_least_16 n hn
    omega
  have odd_band : 6*2^(n-2)+1≤2*d0 ∧ 2*d0≤8*2^(n-2)-1 := by
    constructor <;> omega
  have hlinear : n+3 ≤ 4*2^(n-2) := by
    have hp := n_plus_three_le_pow n hn
    omega
  have odd_eq:2*(2*d0)=8*2^(n-2)+oddPre n u+(n-2)+5 := by
    dsimp [oddPre,d0]
    omega
  constructor
  · intro hp
    rcases hp with ⟨k,hband,heq⟩|⟨k,t,d,hd,hband,hout,heq⟩
    · have hk : k=n-1 := even_band_scale_unique u k (n-1) hband hbandE
      right
      rw [hk] at heq
      omega
    · by_cases ht:t=0
      · subst t
        have hprod : 2*u+5=3*d := by simpa using hout
        exact False.elim (odd_tzero_in_dyadic_gap n u hn hbiglo hbighi
          ⟨k,d,by simpa using hband,hprod⟩)
      · have ht1 : t=1 := by
          by_cases hte:t=1
          · exact hte
          have ht2 : 2≤t := by omega
          have he:t+1=3+(t-2) := by omega
          have hp:3^(t+1)%27=0 := by
            rw [he,Nat.pow_add]
            simp
          have hu:(2*u+5)%27=0 := by
            rw [hout,Nat.mul_mod,hp]
            simp
          exact False.elim (hnot27 hu)
        subst t
        have hdd:d=d0 := by
          have hp:3^(1+1)=9 := by decide
          rw [hp] at hout
          omega
        have hk : k=n-2 := odd_band_scale_unique (2*d0) k (n-2)
          (by simpa [hdd] using hband) odd_band
        left
        rw [hdd,hk] at heq
        omega
  · rintro (rfl|rfl)
    · exact ho
    · exact he

#print axioms near_top_exact_two


/-
private theorem pow_period_eighteen (n : Nat) :
    2^(n+18)%27=2^n%27 := by
  rw [Nat.pow_add]
  simp [Nat.mul_mod]

private theorem pow_mod_eighteen (n : Nat) :
    2^n%27=2^(n%18)%27 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn:n<18
    · simp [Nat.mod_eq_of_lt hn]
    · have hm:n-18<n:=by omega
      have he:n=(n-18)+18:=by omega
      rw [he,pow_period_eighteen]
      rw [ih (n-18) hm]
      have hmod:((n-18)+18)%18=(n-18)%18:=by omega
      rw [hmod]

/-- Four mod54 fatal subclasses have precisely v3(2fatal(n)+5)=2. -/
theorem fatal_not_div27 (n:Nat) (hn:4≤n)
    (hres:n%54=4 ∨ n%54=23 ∨ n%54=40 ∨ n%54=41) :
    (2*fatal n+5)%27≠0 := by
  have hf:=fatal_close n hn
  have hp:=pow_mod_eighteen n
  rcases hres with h|h|h|h
  · have hm:n%18=4:=by omega
    have hm27:2^n%27=2^4%27:=by rw [hp,hm]
    omega
  · have hm:n%18=5:=by omega
    have hm27:2^n%27=2^5%27:=by rw [hp,hm]
    omega
  · have hm:n%18=4:=by omega
    have hm27:2^n%27=2^4%27:=by rw [hp,hm]
    omega
  · have hm:n%18=5:=by omega
    have hm27:2^n%27=2^5%27:=by rw [hp,hm]
    omega

/-- Four mod54 second-predecessor subclasses have exactly two factors 3. -/
theorem second_not_div27 (n:Nat) (hn:10≤n)
    (hres:n%54=11 ∨ n%54=34 ∨ n%54=47 ∨ n%54=52) :
    (2*secondPred n+5)%27≠0 := by
  have hf:=second_close n hn
  have hp:=pow_mod_eighteen n
  rcases hres with h|h|h|h
  · have hm:n%18=11:=by omega
    have hm27:2^n%27=2^11%27:=by rw [hp,hm]
    omega
  · have hm:n%18=16:=by omega
    have hm27:2^n%27=2^16%27:=by rw [hp,hm]
    omega
  · have hm:n%18=11:=by omega
    have hm27:2^n%27=2^11%27:=by rw [hp,hm]
    omega
  · have hm:n%18=16:=by omega
    have hm27:2^n%27=2^16%27:=by rw [hp,hm]
    omega

theorem fatal_parents_exactly_two (q n:Nat) (hn:4≤n)
    (hres:n%54=4 ∨ n%54=23 ∨ n%54=40 ∨ n%54=41) :
    ResetParent q (fatal n) ↔
      q=oddPre n (fatal n) ∨ q=evenPre n (n+4) := by
  have h18:n%18=4 ∨ n%18=5:=by omega
  exact near_top_exact_two n (fatal n) (n+4) q hn (by omega)
    (fatal_close n hn) (fatal_size n hn) (fatal_divnine n hn h18)
    (fatal_not_div27 n hn hres)

theorem second_parents_exactly_two (q n:Nat) (hn:10≤n)
    (hres:n%54=11 ∨ n%54=34 ∨ n%54=47 ∨ n%54=52) :
    ResetParent q (secondPred n) ↔
      q=oddPre n (secondPred n) ∨ q=evenPre n (7*n+13) := by
  have h18:n%18=11 ∨ n%18=16:=by omega
  exact near_top_exact_two n (secondPred n) (7*n+13) q (by omega)
    (by omega) (second_close n hn) (second_size n hn)
    (second_divnine n hn h18) (second_not_div27 n hn hres)

/-- Every reached nonroot reset has a last source-certified edge. -/
theorem rooted_two_parents (u a b:Nat) (hu:u≠2)
    (ha:ResetParent a u) (hb:ResetParent b u)
    (hall:∀ q, ResetParent q u ↔ q=a∨q=b) :
    CascadeSweep.ReachC (2,0) (u,0) ↔
      CascadeSweep.ReachC (2,0) (a,0) ∨ CascadeSweep.ReachC (2,0) (b,0) := by
  constructor
  · intro hroot
    have hc:ResetChain 2 u := (root_reset_chain_iff u).mp hroot
    obtain ⟨q,hchain,hparent⟩:=reset_chain_last hc hu
    rcases (hall q).mp hparent with h|h
    · left
      rw [h] at hchain
      exact (root_reset_chain_iff a).mpr hchain
    · right
      rw [h] at hchain
      exact (root_reset_chain_iff b).mpr hchain
  · intro h
    rcases h with h|h
    · have hc:ResetChain 2 a := (root_reset_chain_iff a).mp h
      exact (root_reset_chain_iff u).mpr (hc.append ha)
    · have hc:ResetChain 2 b := (root_reset_chain_iff b).mp h
      exact (root_reset_chain_iff u).mpr (hc.append hb)

STAGED_SECOND_PHASE
-/
end CascadeFirstFork
