import F418NormalReturn
import F418HighTail

namespace BB6.Agent32F418.ReturnBounds
open Arithmetic EventSystem State
namespace Prefix

theorem prefix_has_even (b : Prefix) (Q : Nat) :
    (b.value Q).testBit (b.L-1)=true := by
  induction b with
  | last r =>
    simp only [value,L_last,Nat.add_sub_cancel]
    rw [Nat.mul_comm,Nat.testBit_mul_two_pow]
    simp [Nat.testBit_eq_decide_div_mod_eq]
  | more r t ih =>
    have ht : 0 < t.L := by simp [L]
    simp only [value,L_more]
    rw [Nat.mul_comm,Nat.testBit_mul_two_pow]
    have hle : 2*r+1 ≤ 2*r+2+t.L-1 := by omega
    simp only [show decide (2*r+1 ≤ 2*r+2+t.L-1)=true by simp [hle],Bool.true_and]
    rw [show 2*r+2+t.L-1-(2*r+1)=(t.L-1)+1 by omega,Nat.testBit_add_one]
    have h : (2*t.value Q+1)/2=t.value Q := by omega
    rwa [h]

theorem prefix_not_noEven (b : Prefix) (Q : Nat) : ¬NoEven (b.value Q) := by
  intro hn
  have h := prefix_has_even b Q
  rw [hn (b.L-1) (by simp [L])] at h
  contradiction

theorem oddChain_noEven {N last : Nat} (hc : OddChain N last) : NoEven N := by
  induction hc with
  | last j hj =>
    intro i hi
    exact Nat.testBit_two_pow_of_ne (by omega)
  | more j Q last hj hQ hc ih =>
    intro i hi
    rw [Nat.mul_comm,Nat.testBit_mul_two_pow]
    by_cases h : j ≤ i
    · simp only [show decide (j≤i)=true by simp [h],Bool.true_and]
      have he : i-j=(i-j-1)+1 := by omega
      rw [he,Nat.testBit_add_one,show (2*Q+1)/2=Q by omega]
      exact ih _ (by omega)
    · simp [h]

theorem prefix_or_oddChain (N : Nat) (hN : 0 < N) :
    (∃ (b : Prefix) (Q : Nat), N=b.value Q) ∨ (∃ last, OddChain N last) := by
  induction N using Nat.strongRecOn with
  | ind N ih =>
    have hf := splitOdd_spec N hN
    have hlt := splitOdd_tail_lt N hN
    rcases he : splitOdd N with ⟨j,Q⟩
    rw [he] at hf hlt
    dsimp at hf hlt
    by_cases hj : j%2=0
    · left
      refine ⟨Prefix.last (j/2),Q,?_⟩
      simp only [value]
      rwa [show 2*(j/2)=j by omega]
    · have hodd : j%2=1 := by omega
      by_cases hQ : Q=0
      · right
        refine ⟨j,?_⟩
        rw [hf,hQ]
        simp only [Nat.mul_zero,Nat.zero_add,Nat.mul_one]
        exact OddChain.last j hodd
      · have hpos : 0<Q := by omega
        rcases ih Q hlt hpos with ⟨b,R,hr⟩ | ⟨last,hc⟩
        · left
          refine ⟨Prefix.more (j/2) b,R,?_⟩
          simp only [value]
          rw [show 2*(j/2)+1=j by omega,←hr]
          exact hf
        · right
          exact ⟨last,hf ▸ OddChain.more j Q last hodd hpos hc⟩

theorem noEven_iff_oddChain {N : Nat} (hN : 0<N) :
    NoEven N ↔ ∃ last, OddChain N last := by
  constructor
  · intro hn
    rcases prefix_or_oddChain N hN with ⟨b,Q,h⟩ | h
    · exact False.elim (prefix_not_noEven b Q (h ▸ hn))
    · exact h
  · rintro ⟨last,h⟩
    exact oddChain_noEven h

theorem singleton_fatal {r : Nat} (hr : r%2=1) :
    ∃ last, OddChain ((Prefix.last r).next 0 (2*r+1)) last ∧ last%4=3 := by
  have hodd : (2*r+1)%2=1 := by omega
  have h5 : (5*r)%2=1 := by omega
  have hpos : 0<2^(2*r+1) := Nat.two_pow_pos _
  refine ⟨2*r+1,?_,by omega⟩
  rw [singleton_next,show 2^(2*r+2)=2*2^(2*r+1) by rw [show 2*r+2=(2*r+1)+1 by omega,Nat.pow_succ,Nat.mul_comm]]
  exact OddChain.more (5*r) (2^(2*r+1)) (2*r+1) h5 hpos (OddChain.last _ hodd)

/-- A pure-power alignment-2, phase-1 event state. -/
def pure (N W : Nat) : State := shift2 N 1 (2^W) (W+1)

inductive NormalPath : Nat → Nat → Prop where
  | seed : NormalPath 268311341 29
  | step {b : Prefix} {Q W : Nat} :
      NormalPath (b.value Q) W →
      NormalPath (b.next Q W) (W+b.E+1)

theorem normalPath_reaches {N W : Nat} (h : NormalPath N W) :
    Reaches EventSystem.seed (pure N W) := by
  induction h with
  | seed =>
    exact reaches_iff.mpr ⟨4,seed_to_pure⟩
  | @step b Q W h ih =>
    have hsafe := reaches_safe ih
    have hwidth : b.value Q < 2^W := hsafe.2.2.2.1
    apply reaches_trans ih
    exact reaches_iff.mpr ⟨b.steps+1,normal_return_exact b Q W hwidth⟩

theorem normalPath_safe {N W : Nat} (h : NormalPath N W) :
    0<N ∧ N<2^W := by
  have hs := reaches_safe (normalPath_reaches h)
  exact ⟨hs.1,hs.2.2.2.1⟩

theorem none_after_some {s t : State} {k l : Nat}
    (hn : iterate k s = none) (hs : iterate l s=some t) :
    l≤k ∧ iterate (k-l) t=none := by
  have hle : l≤k := by
    by_cases h : l≤k
    · exact h
    · rw [show l=k+(l-k) by omega,iterate_add,hn] at hs
      simp at hs
  refine ⟨hle,?_⟩
  rw [show k=l+(k-l) by omega,iterate_add,hs] at hn
  exact hn

/-- Before any arithmetic termination there is an actual pure checkpoint
    whose register has no even-position set bit. -/
theorem normalPath_none_has_gate {k N W : Nat} (hp : NormalPath N W)
    (hn : iterate k (pure N W)=none) :
    ∃ N' W', NormalPath N' W' ∧ NoEven N' := by
  induction k using Nat.strongRecOn generalizing N W with
  | ind k ih =>
    by_cases h : NoEven N
    · exact ⟨N,W,hp,h⟩
    · obtain ⟨hpos,hwidth⟩ := normalPath_safe hp
      rcases prefix_or_oddChain N hpos with ⟨b,Q,hb⟩ | ⟨last,ho⟩
      · subst N
        have hnext := normal_return_exact b Q W hwidth
        obtain ⟨h_le,h_none⟩ := none_after_some hn hnext
        have hlt : k-(b.steps+1)<k := by omega
        exact ih _ hlt (NormalPath.step hp) h_none
      · exact False.elim (h (oddChain_noEven ho))

theorem seed_none_has_gate (h : ∃ k, iterate k EventSystem.seed=none) :
    ∃ N W, NormalPath N W ∧ NoEven N := by
  obtain ⟨k,hk⟩ := h
  obtain ⟨_,hn⟩ := none_after_some hk seed_to_pure
  exact normalPath_none_has_gate NormalPath.seed hn

/-- Explicit necessary predecessor conditions for a first pure odd-only
    checkpoint, reached only through genuine normal returns. -/
theorem seed_none_has_restricted_predecessor
    (h : ∃ k, iterate k EventSystem.seed=none) :
    ∃ (b : Prefix) (Q W : Nat), NormalPath (b.value Q) W ∧
      NoEven (b.next Q W) ∧
      ((∃ r, b=Prefix.last r ∧ W=2*r+1 ∧ Q=0 ∧ r%2=1) ∨
        (b.C≤Q ∧ (W+b.p)%2=1 ∧ (0<b.p → 7*b.p+4≤W) ∧
          ∀ i, i%2=1 → 9*b.p+5≤i → (b.value Q).testBit i=false)) := by
  obtain ⟨N,W,hp,hn⟩ := seed_none_has_gate h
  cases hp with
  | seed =>
    have hh := hn 0 (by decide)
    contradiction
  | @step b Q W hp =>
    refine ⟨b,Q,W,hp,hn,?_⟩
    have hw := (normalPath_safe hp).2
    by_cases hb : Q<b.C
    · exact Or.inl (oddOnly_borrow_predecessor hw hb hn)
    · have hc : b.C≤Q := by omega
      obtain ⟨hpar,hsize⟩ := oddOnly_noBorrow_predecessor hw hc hn
      right
      refine ⟨hc,hpar,hsize,?_⟩
      intro i hi hi'
      apply noBorrow_high_odd_exclusion hw hc hn hi
      simp [L,E]
      omega

#print axioms normalPath_reaches
#print axioms seed_none_has_gate
#print axioms seed_none_has_restricted_predecessor

#print axioms prefix_has_even
#print axioms oddChain_noEven
#print axioms prefix_or_oddChain
#print axioms noEven_iff_oddChain
#print axioms singleton_fatal

end Prefix
end BB6.Agent32F418.ReturnBounds
