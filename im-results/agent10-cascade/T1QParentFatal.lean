import LevelDeficitDynamics
import ResetChain

/-!
# Exact source connection: t=1 Q-parent implies a fatal reset hit

The Q-parent equation is combined with the exact first-reset source grammar.
The odd-offset bound is used explicitly to keep the child above the fatal
height at level K+1; this is the nonfatal guard needed before taking any
even reset. The resulting even chain has exactly j resets and reaches
F_(K+2). This is a source-C reset-chain theorem, not an all-time exclusion.
-/

namespace Agent10T1Fatal

open CascadeSource CascadeResetInverse CascadeLevelDeficit CascadeSweep

def fatalHeight (n : Nat) : Nat := 4*2^n-n-4

def fatalDeficit (n : Nat) : Nat := 4*2^n+2*n+4

private theorem k_add_five_le_eight_pow (k : Nat) :
    k+5 ≤ 8*2^k := by
  induction k with
  | zero => decide
  | succ k ih =>
      rw [Nat.pow_succ]
      have hp : 1 ≤ 2^k := Nat.one_le_pow k 2 (by decide)
      omega

private theorem k_add_four_le_four_pow (k : Nat) :
    k+4 ≤ 4*2^k := by
  induction k with
  | zero => decide
  | succ k ih =>
      have hb := k_add_five_le_eight_pow k
      rw [Nat.pow_succ]
      omega

theorem fatalHeight_succ (k : Nat) :
    fatalHeight (k+1) = 8*2^k-k-5 := by
  dsimp [fatalHeight]
  rw [Nat.pow_succ]
  have hb := k_add_five_le_eight_pow k
  omega

theorem fatalHeight_add (n : Nat) :
    fatalHeight n+n+4 = 4*2^n := by
  have hb := k_add_four_le_four_pow n
  dsimp [fatalHeight]
  omega

theorem fatal_deficit (n : Nat) :
    deficit (fatalHeight n) n = fatalDeficit n := by
  have hb := fatalHeight_add n
  dsimp [deficit, fatalDeficit]
  omega

theorem fatal_deficit_succ (k : Nat) :
    fatalDeficit (k+1) = 8*2^k+2*k+6 := by
  dsimp [fatalDeficit]
  rw [Nat.pow_succ]
  omega

/-- The t=1 Q equation fixes the child deficit at c*2^j and, using the
source odd-offset bound, proves that the child is strictly above the
fatal height at level K+1. -/
theorem t1_child_deficit (h k d a j : Nat)
    (hg : ∀ i, i<k → 8*2^i≤h+i+5)
    (hhigh : h+k+5<8*2^k)
    (hpar : (h+k)%2=1)
    (hfactor : oddParameter h k=2*d)
    (hd : d%2=1)
    (ha : oddOffset h k=2*a)
    (hQ : 9*a+2*k+7-2^(k+2)=(2*k+7)*2^(j+1)) :
    deficit (oddOutput 1 d) (k+1)=(2*k+7)*2^j ∧
    deficit (oddOutput 1 d) (k+1)<fatalDeficit (k+1) := by
  have houtput0 := odd_output_equation_deficit h k 1 d hg hhigh hpar hfactor hd
  have houtput : 2*oddOutput 1 d+5=9*d := by
    simpa [Nat.pow_succ] using houtput0.1
  have hparam : 8*2^k-2*d=2*a := by
    have hx := ha
    change 8*2^k-oddParameter h k=2*a at hx
    rw [hfactor] at hx
    exact hx
  have hsum : a+d=4*2^k := by omega
  have hpowK2 : 2^(k+2)=4*2^k := by
    rw [Nat.pow_add]
    simp
    ac_rfl
  have hQ' := hQ
  rw [hpowK2] at hQ'
  have hQeq : 9*a+(2*k+7)=4*2^k+(2*k+7)*2^(j+1) := by omega
  have hpK1 : 2^(k+1)=2*2^k := by rw [Nat.pow_succ]
  have hpj : 2^(j+1)=2*2^j := by rw [Nat.pow_succ]
  have hapos : 1≤2^(j+1) := Nat.one_le_pow (j+1) 2 (by decide)
  have hc : 1≤2*k+7 := by omega
  have hcpow : (2*k+7)≤(2*k+7)*2^(j+1) :=
    Nat.mul_le_mul_left (2*k+7) hapos
  have haLower : 4*2^k≤9*a := by omega
  have hdUpper : 9*d≤32*2^k := by omega
  have huUpper : oddOutput 1 d≤16*2^k := by omega
  have hD2 : 2*deficit (oddOutput 1 d) (k+1)=(2*k+7)*2^(j+1) := by
    dsimp [deficit]
    rw [hpK1]
    omega
  have hD : deficit (oddOutput 1 d) (k+1)=(2*k+7)*2^j := by
    have hmul :
        2*((2*k+7)*2^j)=2*deficit (oddOutput 1 d) (k+1) := by
      calc
        2*((2*k+7)*2^j)=(2*k+7)*(2*2^j) := by ac_rfl
        _=(2*k+7)*2^(j+1) := by rw [←hpj]
        _=2*deficit (oddOutput 1 d) (k+1) := hD2.symm
    omega
  have hA := (odd_offset_bounds h k hg hhigh hpar).2
  rw [ha] at hA
  rw [hpK1] at hA
  have habound : a≤2^k-1 := by omega
  have hD2bound :
      2*deficit (oddOutput 1 d) (k+1)≤5*2^k+(2*k+7)-9 := by
    rw [hD2]
    omega
  have hfd : fatalDeficit (k+1)=8*2^k+(2*k+7)-1 := by
    rw [fatal_deficit_succ]
    omega
  have hp : 1≤2^k := Nat.one_le_pow k 2 (by decide)
  constructor
  · exact hD
  · rw [hfd]
    omega

/-- From deficit c*2^j at level K+1, a nonfatal state reaches F_(K+2)
through exactly j genuine even first-reset edges. The strict bound below
the level-(K+1) fatal deficit is preserved by halving. -/
theorem even_reset_chain_to_fatal (K j h : Nat)
    (hg : ∀ i, i<K+1 → 8*2^i≤h+i+5)
    (hhigh : h+(K+1)+5<8*2^(K+1))
    (hD : deficit h (K+1)=(2*K+7)*2^j)
    (hbelow : deficit h (K+1)<fatalDeficit (K+1)) :
    ResetChain h (fatalHeight (K+2)) := by
  induction j generalizing h with
  | zero =>
      have hD0 : deficit h (K+1)=2*K+7 := by simpa using hD
      have hpK1 : 2^(K+1)=2*2^K := by rw [Nat.pow_succ]
      have hpK2 : 2^(K+2)=4*2^K := by
        rw [Nat.pow_add]
        simp
        ac_rfl
      have hbound : K+6≤16*2^K := by
        have hb := k_add_four_le_four_pow (K+2)
        rw [hpK2] at hb
        omega
      have hval : h=fatalHeight (K+2) := by
        dsimp [deficit] at hD0
        rw [hpK1] at hD0
        dsimp [fatalHeight]
        rw [hpK2]
        omega
      rw [hval]
      exact ResetChain.root
  | succ j ih =>
      have hsum : 8*2^(K+1)+(K+1)=h+(2*K+7)*2^(j+1) := by
        dsimp [deficit] at hD
        omega
      have hpowEven : (8*2^(K+1))%2=0 := by simp
      have hdefEven : ((2*K+7)*2^(j+1))%2=0 := by
        have hp : 2^(j+1)=2*2^j := by rw [Nat.pow_succ]
        rw [hp]
        simp [Nat.mul_mod]
      have hpar : (h+(K+1))%2=0 := by omega
      have hlow : 4*2^(K+1)≤h+(K+1)+4 := by
        have hguard := hg K (by omega)
        simpa [Nat.pow_succ] using hguard
      have hFdef := fatal_deficit (K+1)
      have hgt : fatalHeight (K+1)<h := by
        have hbelow' := hbelow
        rw [←hFdef] at hbelow'
        dsimp [deficit] at hbelow'
        omega
      have hnot : h+(K+1)+4≠4*2^(K+1) := by
        intro heq
        have hb := k_add_four_le_four_pow (K+1)
        have hval : h=fatalHeight (K+1) := by
          dsimp [fatalHeight]
          omega
        exact (Nat.ne_of_lt hgt) hval.symm
      have hout : Outcome (h,0) (some (evenOutput h (K+1))) := by
        simpa [evenOutput] using
          even_outcome h (K+1) hg hlow hhigh hnot hpar
      have hparent : ResetParent h (evenOutput h (K+1)) :=
        (reset_parent_iff h (evenOutput h (K+1))).mp hout
      by_cases hj : j=0
      · subst j
        have hD0 : deficit h (K+1)=2*(2*K+7) := by simpa using hD
        have hF : fatalHeight (K+2)=8*2^(K+1)-(K+1)-5 :=
          fatalHeight_succ (K+1)
        have hu : evenOutput h (K+1)=fatalHeight (K+2) := by
          rw [hF]
          have hdiv : h+(K+1)=2*((h+(K+1))/2) := by omega
          dsimp [evenOutput, deficit] at hD0 ⊢
          have hb := k_add_five_le_eight_pow (K+1)
          omega
        rw [hu] at hparent
        exact ResetChain.append ResetChain.root hparent
      · have hjpos : 1≤j := by omega
        have hpj : 2≤2^j := by
          cases j with
          | zero => omega
          | succ j => simp [Nat.pow_succ]
        have hDgt : deficit h (K+1)>4*(K+1)+10 := by
          rw [hD]
          have hpplus : 2≤2^(j+1) := by
            have hp : 1≤2^j := Nat.one_le_pow j 2 (by decide)
            rw [Nat.pow_succ]
            omega
          have hmul : 2*(2*K+7)≤(2*K+7)*2^(j+1) :=
            Nat.mul_le_mul_left (2*K+7) hpplus
          omega
        have hlevel := even_level_criterion h (K+1) hg hhigh hpar
        have hg' := hlevel.1
        have hhigh' := hlevel.2.mpr hDgt
        have hhalf := even_deficit_halves h (K+1) hpar
        have hD' :
            deficit (evenOutput h (K+1)) (K+1)=(2*K+7)*2^j := by
          have hmul :
              2*((2*K+7)*2^j)=
                2*deficit (evenOutput h (K+1)) (K+1) := by
            calc
              2*((2*K+7)*2^j)=(2*K+7)*(2*2^j) := by ac_rfl
              _=(2*K+7)*2^(j+1) := by rw [←hpj]
              _=deficit h (K+1) := hD.symm
              _=2*deficit (evenOutput h (K+1)) (K+1) := hhalf
          omega
        have hbelow' :
            deficit (evenOutput h (K+1)) (K+1)<fatalDeficit (K+1) := by
          rw [hD'] 
          rw [hD] at hbelow
          have hpowlt : 2^j<2^(j+1) := by
            rw [Nat.pow_succ]
            have hp : 1≤2^j := Nat.one_le_pow j 2 (by decide)
            omega
          have hmul :
              (2*K+7)*2^j<(2*K+7)*2^(j+1) :=
            Nat.mul_lt_mul_of_pos_left hpowlt (by omega)
          omega
        have hrec := ih (evenOutput h (K+1)) hg' hhigh' hD' hbelow'
        exact ResetChain.append (ResetChain.append ResetChain.root hparent) hrec

/-- Any genuine blank-root source state satisfying the exact t=1 Q-parent
identity reaches the fatal reset height F_(K+2). The theorem includes the
nonfatal offset bound needed for every intermediate even reset. -/
theorem root_t1_q_parent_fatal (h k d a j : Nat)
    (hroot : ReachC (2,0) (h,0))
    (hg : ∀ i, i<k → 8*2^i≤h+i+5)
    (hhigh : h+k+5<8*2^k)
    (hnot : h+k+4≠4*2^k)
    (hpar : (h+k)%2=1)
    (hfactor : oddParameter h k=2*d)
    (hd : d%2=1)
    (ha : oddOffset h k=2*a)
    (hQ : 9*a+2*k+7-2^(k+2)=(2*k+7)*2^(j+1)) :
    ReachC (2,0) (fatalHeight (k+2),0) := by
  have hlow := first_low h k hg
  have hout : Outcome (h,0) (some (oddOutput 1 d)) := by
    simpa [oddOutput] using
      odd_outcome h k 1 d hg hlow hhigh hnot hpar hfactor hd
  have hparent : ResetParent h (oddOutput 1 d) :=
    (reset_parent_iff h (oddOutput 1 d)).mp hout
  have hchain : ResetChain 2 h := (root_reset_chain_iff h).mp hroot
  have hchain1 := ResetChain.append hchain hparent
  have hchild := t1_child_deficit h k d a j hg hhigh hpar hfactor hd ha hQ
  by_cases hj : j=0
  · have hD0 : deficit (oddOutput 1 d) (k+1)=2*k+7 := by
      rw [hchild.1, hj]
      simp
    have hpowK2 : 2^(k+2)=4*2^k := by
      rw [Nat.pow_add]
      simp
      ac_rfl
    have hbound : k+6≤16*2^k := by
      have hb := k_add_four_le_four_pow (k+2)
      rw [hpowK2] at hb
      omega
    have hu : oddOutput 1 d=fatalHeight (k+2) := by
      dsimp [deficit] at hD0
      rw [hpK1] at hD0
      dsimp [fatalHeight]
      rw [hpowK2]
      omega
    rw [hu] at hchain1
    exact (root_reset_chain_iff _).mpr hchain1
  · have hguardsChild := odd_reset_guards h k 1 d hg hhigh hpar hd hfactor
    have hg' : ∀ i, i<k+1 → 8*2^i≤oddOutput 1 d+i+5 := by
      intro i hi
      exact hguardsChild i (by omega)
    have hDgt : deficit (oddOutput 1 d) (k+1)>2*k+7 := by
      rw [hchild.1]
      have hjpos : 1≤j := by omega
      have hpj : 2≤2^j := by
        cases j with
        | zero => omega
        | succ m =>
            rw [Nat.pow_succ]
            have hp : 1≤2^m := Nat.one_le_pow m 2 (by decide)
            omega
      have hmul : 2*(2*k+7)≤(2*k+7)*2^j :=
        Nat.mul_le_mul_left (2*k+7) hpj
      omega
    have hhigh' :
        oddOutput 1 d+(k+1)+5<8*2^(k+1) := by
      dsimp [deficit] at hDgt
      omega
    have heven := even_reset_chain_to_fatal k j (oddOutput 1 d)
      hg' hhigh' hchild.1 hchild.2
    have hchain2 := ResetChain.append hchain1 heven
    exact (root_reset_chain_iff _).mpr hchain2

#print axioms t1_child_deficit
#print axioms even_reset_chain_to_fatal
#print axioms root_t1_q_parent_fatal

end Agent10T1Fatal
