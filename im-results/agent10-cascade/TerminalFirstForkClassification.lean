import RootConeComposition

set_option maxHeartbeats 0

namespace CascadeTerminalFirstForkClassification
open CascadeResetInverse CascadeUniformFatal CascadeSweep
open CascadeTerminalFirstFork CascadeTerminalHighBand CascadeRootConeComposition

/-- Dyadic odd-source bands, just like even-return target bands,
    have disjoint scales. The shift by 2 translates their endpoint
    inequalities directly into the kernel-checked even-band lemma. -/
theorem odd_source_scale_unique (w k j : Nat)
    (hk : 6*2^k+1≤w ∧ w≤8*2^k-1)
    (hj : 6*2^j+1≤w ∧ w≤8*2^j-1) : k=j := by
  have hpos : 2≤w := by
    have hp : 1≤2^k := Nat.one_le_pow k 2 (by decide)
    omega
  apply even_band_scale_unique (w-2) k j
  · constructor <;> omega
  · constructor <;> omega

/-- Source-first-reset parent classification for one nonterminal
    canonical-ray step, under the two exact dyadic source bands and
    the v_3(2*v+5)=2 certificate. Both the even and the unique odd t=1
    parent are retained. All other odd valuations are excluded. -/
theorem middle_band_exact_two_parent_coverage
    (n v w h d : Nat) (hn : 4≤n)
    (hband : 6*2^(n-1)-1≤v ∧ v≤8*2^(n-1)-3)
    (heven : 2*v=8*2^(n-1)+w+(n-1))
    (hoddBand : 6*2^(n-2)+1≤2*d ∧ 2*d≤8*2^(n-2)-1)
    (hoddOutput : 2*v+5=9*d)
    (hoddParent : 4*d=8*2^(n-2)+h+(n-2)+5)
    (h27 : (2*v+5)%27=9)
    (q : Nat) (hq : ResetParent q v) :
    q=w ∨ q=h := by
  rcases hq with ⟨k,hb,heq⟩ | ⟨k,t,e,he,hb,hout,heq⟩
  · have hk : k=n-1 :=
      even_band_scale_unique v k (n-1) hb hband
    subst k
    left
    omega
  · by_cases ht0 : t=0
    · subst t
      have heout : 2*v+5=3*e := by simpa using hout
      have hpow : 2^(n+1)=4*2^(n-1) := by
        have heq : n+1=(n-1)+2 := by omega
        rw [heq,Nat.pow_add]
        omega
      have hpowbig : 2≤2^(n-1) := by
        have heq : 1≤n-1 := by omega
        have hp := Nat.pow_le_pow_right
          (by decide : 0<(2:Nat)) heq
        simpa using hp
      have hlow : 2^(n+1)<e := by omega
      have hhigh : 2*e+2<3*2^(n+1) := by omega
      exact False.elim
        ((gap_avoids_odd_images (n+1) e hlow hhigh)
          k (by simpa using hb))
    · by_cases ht1 : t=1
      · subst t
        have heout : 2*v+5=9*e := by simpa using hout
        have hd : e=d := by omega
        subst e
        have hk : k=n-2 :=
          odd_source_scale_unique (2*d) k (n-2)
            (by simpa using hb) hoddBand
        subst k
        right
        omega
      · have ht2 : 2≤t := by omega
        have hsplit : t+1=3+(t-2) := by omega
        have hzero : 3^(t+1)%27=0 := by
          rw [hsplit,Nat.pow_add]
          simp
        have hbad : (2*v+5)%27=0 := by
          rw [hout,Nat.mul_mod,hzero]
          simp
        omega

/-- Exact universal one-parent classification when the next
    canonical-ray state lies in a dyadic even-target band and its
    residue prevents all odd-valued first-return ancestors. -/
theorem middle_band_unique_even_parent
    (n w z : Nat)
    (hband : 6*2^(n-1)-1≤w ∧ w≤8*2^(n-1)-3)
    (heq : 2*w=8*2^(n-1)+z+(n-1))
    (hmod : w%3≠2)
    (q : Nat) (hq : ResetParent q w) : q=z := by
  exact any_parent_equals_even w (n-1) z q hband heq hmod hq

/-- A genuinely source-rooted nonterminal fork is now closed
    using source-algebraic band proofs rather than axiomatizing
    either universal parent-coverage proposition. The remaining
    hypotheses are arithmetical, with no ResetParent quantifiers. -/
theorem ray_nonterminal_four_node_from_bands
    (n p q Q u v w z h d s : Nat)
    (hn : 257≤n)
    (hp : p=2^n)
    (hpbig : n+16<p)
    (hhigh : 7*p<4*q)
    (hqbound : q<2*p)
    (hqfour : q=4*Q)
    (hvlin : v+Q+1=4*p+n)
    (hwlin : w+2*Q+1=4*p+n)
    (hXd : 2*v+5=9*d)
    (hdmod : d%3=1)
    (hhlin : h+2*p+n+3=4*d)
    (hsector : (2*p+n)%3=0)
    (hzlin : z+q+1=4*p+n)
    (hhighstrong : 7*p+4*s≤4*q)
    (hs : n+5≤s)
    (hzmod : (2*z+5)%9≠0)
    (hvband : 6*2^(n-1)-1≤v ∧ v≤8*2^(n-1)-3)
    (hwband : 6*2^(n-1)-1≤w ∧ w≤8*2^(n-1)-3)
    (hoddBand : 6*2^(n-2)+1≤2*d ∧ 2*d≤8*2^(n-2)-1)
    (hwmod : w%3≠2)
    (hvne : v≠2) (hwne : w≠2) :
    ¬ReachC (2,0) (v,0) := by
  have hpEven : 2^n=2*2^(n-1) := by
    have hidx : n=(n-1)+1 := by omega
    rw [hidx,Nat.pow_succ]
    omega
  have hpOdd : 2^n=4*2^(n-2) := by
    have hidx : n=(n-2)+2 := by omega
    rw [hidx,Nat.pow_add]
    omega
  have hevenV : 2*v=8*2^(n-1)+w+(n-1) := by omega
  have hevenW : 2*w=8*2^(n-1)+z+(n-1) := by omega
  have hoddEq : 4*d=8*2^(n-2)+h+(n-2)+5 := by omega
  have h27 : (2*v+5)%27=9 := by
    rw [hXd]
    omega
  have hparentV : ∀ r, ResetParent r v → r=w ∨ r=h := by
    intro r hr
    exact middle_band_exact_two_parent_coverage n v w h d
      (by omega) hvband hevenV hoddBand hXd hoddEq h27 r hr
  have hparentW : ∀ r, ResetParent r w → r=z := by
    intro r hr
    exact middle_band_unique_even_parent n w z hwband hevenW
      hwmod r hr
  exact ray_nonterminal_fork_closed n p q Q u v w z h d s
    hn hp hpbig hhigh hqbound hqfour hvlin hXd hdmod hhlin
    hsector hzlin hhighstrong hs hzmod hvne hwne
    hparentV hparentW

#print axioms odd_source_scale_unique
#print axioms middle_band_exact_two_parent_coverage
#print axioms middle_band_unique_even_parent
#print axioms ray_nonterminal_four_node_from_bands
end CascadeTerminalFirstForkClassification
