import BlankGateBridge
import Lean.Elab.Tactic.Omega

namespace BB6.Agent49

theorem pow_two_even (m : Nat) : 2^(2*m)=4^m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      have hn : 2*(m+1)=2*m+1+1 := by omega
      rw [hn, Nat.pow_succ, Nat.pow_succ, ih, Nat.pow_succ]
      omega

theorem pow_two_odd (m : Nat) : 2^(2*m+1)=2*4^m := by
  calc
    2^(2*m+1)=2^(2*m)*2 := by simp only [Nat.pow_succ]
    _=4^m*2 := by rw [pow_two_even]
    _=2*4^m := by omega

theorem pow_two_even_two (m : Nat) : 2^(2*m+2)=4*4^m := by
  calc
    2^(2*m+2)=2^(2*m)*4 := by
      have he : 2*m+2=2*m+1+1 := by omega
      rw [he, Nat.pow_succ, Nat.pow_succ]
      omega
    _=4^m*4 := by rw [pow_two_even]
    _=4*4^m := by omega

theorem one_gate_parity (k n : Nat)
    (h : 2*k+8+3*n=8*2^(n+1)) : n%2=0 := by
  have hrhs : 8*2^(n+1)=2*(4*2^(n+1)) := by omega
  rw [hrhs] at h
  omega

theorem one_gate_base4 (k : Nat) :
    (∃ n : Nat, 2*k+8+3*n=8*2^(n+1)) ↔
      (∃ m : Nat, k+4+3*m=8*4^m) := by
  constructor
  · rintro ⟨n,hn⟩
    have hp := one_gate_parity k n hn
    obtain ⟨m,hm⟩ : ∃ m, n=2*m := ⟨n/2,by omega⟩
    subst n
    refine ⟨m,?_⟩
    rw [pow_two_odd] at hn
    omega
  · rintro ⟨m,hm⟩
    refine ⟨2*m,?_⟩
    rw [pow_two_odd]
    omega

theorem odd_gate_parity (a k n : Nat) (ha : a%2=1)
    (h : 2*k+a+4+3*n=(a+3)*2^(n+1)) : n%2=1 := by
  have hrhs : (a+3)*2^(n+1)=2*((a+3)*2^n) := by
    simp only [Nat.pow_succ]
    ac_rfl
  rw [hrhs] at h
  omega

theorem odd_gate_base4 (a k : Nat) (ha : a%2=1) :
    (∃ n : Nat, 2*k+a+4+3*n=(a+3)*2^(n+1)) ↔
      (∃ m : Nat, 2*k+a+7+6*m=4*(a+3)*4^m) := by
  constructor
  · rintro ⟨n,hn⟩
    have hp := odd_gate_parity a k n ha hn
    obtain ⟨m,hm⟩ : ∃ m, n=2*m+1 := ⟨n/2,by omega⟩
    subst n
    refine ⟨m,?_⟩
    have he : 2^(2*m+1+1)=4*4^m := by
      rw [show 2*m+1+1=2*m+2 by omega]
      exact pow_two_even_two m
    rw [he] at hn
    have hmul : (a+3)*(4*4^m)=4*(a+3)*4^m := by ac_rfl
    rw [hmul] at hn
    omega
  · rintro ⟨m,hm⟩
    refine ⟨2*m+1,?_⟩
    have he : 2^(2*m+1+1)=4*4^m := by
      rw [show 2*m+1+1=2*m+2 by omega]
      exact pow_two_even_two m
    rw [he]
    have hmul : (a+3)*(4*4^m)=4*(a+3)*4^m := by ac_rfl
    rw [hmul]
    omega

def SectionGate4 (a k : Nat) : Prop :=
  (a=0 ∧ k=0) ∨
  (a=1 ∧ 4≤k ∧ ∃ m : Nat, k+4+3*m=8*4^m) ∨
  (2≤a ∧ a<2*k ∧ a%2=1 ∧
    ∃ m : Nat, 2*k+a+7+6*m=4*(a+3)*4^m)

theorem section_gate_base4_iff (a k : Nat) :
    SectionGate a k ↔ SectionGate4 a k := by
  unfold SectionGate SectionGate4
  constructor
  · intro h
    rcases h with h0 | h1 | h2
    · exact Or.inl h0
    · rcases h1 with ⟨ha,hk,hex⟩
      exact Or.inr (Or.inl ⟨ha,hk,(one_gate_base4 k).mp hex⟩)
    · rcases h2 with ⟨ha,hs,ho,hex⟩
      exact Or.inr (Or.inr ⟨ha,hs,ho,(odd_gate_base4 a k ho).mp hex⟩)
  · intro h
    rcases h with h0 | h1 | h2
    · exact Or.inl h0
    · rcases h1 with ⟨ha,hk,hex⟩
      exact Or.inr (Or.inl ⟨ha,hk,(one_gate_base4 k).mpr hex⟩)
    · rcases h2 with ⟨ha,hs,ho,hex⟩
      exact Or.inr (Or.inr ⟨ha,hs,ho,(odd_gate_base4 a k ho).mpr hex⟩)

theorem source_section_base4_gate_iff (a k : Nat) :
    BB6.Agent46.secNext (a,k)=none ↔ SectionGate4 a k :=
  (source_section_gate_iff a k).trans (section_gate_base4_iff a k)

theorem blank_halts_iff_reachable_base4_gate :
    BB6.CReachBridge.RunHalts ↔
      ∃ s : Pair, SecReach s ∧ SectionGate4 s.1 s.2 := by
  rw [blank_halts_iff_reachable_power_gate]
  constructor
  · rintro ⟨s,hr,hg⟩
    exact ⟨s,hr,(section_gate_base4_iff s.1 s.2).mp hg⟩
  · rintro ⟨s,hr,hg⟩
    exact ⟨s,hr,(section_gate_base4_iff s.1 s.2).mpr hg⟩

#print axioms source_section_base4_gate_iff
#print axioms blank_halts_iff_reachable_base4_gate
#print axioms pow_two_even
#print axioms pow_two_odd
#print axioms pow_two_even_two
end BB6.Agent49
