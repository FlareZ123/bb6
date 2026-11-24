import PeriodicRigidity
namespace CascadePeriodic

/-- Exact arithmetic grammar from FirstInverseComplete.ResetParent, reproduced
    here without importing the upstream TM library. -/
def Grammar (h u : Nat) : Prop :=
  (∃k, (6*2^k-1≤u ∧ u≤8*2^k-3) ∧ 2*u=8*2^k+h+k) ∨
  (∃k t d, d%2=1 ∧
    (6*2^k+1≤2^t*d ∧ 2^t*d≤8*2^k-1) ∧
    2*u+5=3^(t+1)*d ∧
    2*(2^t*d)=8*2^k+h+k+5)

def Valid (h k : Nat) : Prop :=
  4*2^k < h+k+4 ∧ h+k+5 < 8*2^k

def Unified (h u k a : Nat) : Prop :=
  Valid h k ∧ 2^(a+1)*(2*u+5)=3^a*((2*h+5)+16*2^k+2*k+5)

theorem cancel_two_pow_odd (a M X S : Nat) (hm : M%2=1)
    (he : 2^a*X=M*S) : ∃d, S=2^a*d ∧ X=M*d := by
  induction a generalizing S with
  | zero =>
    refine ⟨S,by simp,?_⟩
    simpa using he
  | succ a ih =>
    have hs : S%2=0 := by
      have hmod := congrArg (fun z : Nat => z%2) he
      change (2^(a+1)*X)%2=(M*S)%2 at hmod
      rw [Nat.pow_succ,show (2^a*2)*X=2*(2^a*X) by ac_rfl] at hmod
      rw [Nat.mul_mod M,hm] at hmod
      simpa using hmod.symm
    have hS : S=2*(S/2) := by omega
    have he' : 2^a*X=M*(S/2) := by
      rw [Nat.pow_succ,show (2^a*2)*X=2*(2^a*X) by ac_rfl] at he
      have he'' : 2*(2^a*X)=2*(M*(S/2)) := by
        calc
          2*(2^a*X)=M*S := he
          _ = M*(2*(S/2)) := by rw [←hS]
          _ = 2*(M*(S/2)) := by ac_rfl
      omega
    obtain ⟨d,hd,hx⟩ := ih (S/2) he'
    refine ⟨d,?_,hx⟩
    calc
      S=2*(S/2) := hS
      _=2*(2^a*d) := by rw [hd]
      _=2^(a+1)*d := by rw [Nat.pow_succ]; ac_rfl

private theorem three_odd (a : Nat) : (3^a)%2=1 := by
  induction a with
  | zero => decide
  | succ a ih => rw [Nat.pow_succ, Nat.mul_mod, ih]

theorem grammar_iff_unified (h u : Nat) : Grammar h u ↔ ∃ k a, Unified h u k a := by
  constructor
  · intro he
    rcases he with ⟨k,⟨hl,hh⟩,hq⟩ | ⟨k,t,d,hd,⟨hl,hh⟩,hout,hq⟩
    · have hp : 1≤2^k := Nat.one_le_pow k 2 (by decide)
      refine ⟨k,0,⟨?_,?_⟩,?_⟩
      · omega
      · omega
      · simp only [Nat.pow_zero,Nat.zero_add,Nat.pow_one,Nat.one_mul]
        omega
    · refine ⟨k,t+1,⟨?_,?_⟩,?_⟩
      · omega
      · omega
      · have hq' : (2*h+5)+16*2^k+2*k+5=2^(t+1+1)*d := by
          rw [Nat.pow_succ,Nat.pow_succ]
          have hmul : (2^t*2*2)*d=4*(2^t*d) := by grind
          rw [hmul]
          omega
        rw [hq',hout]
        ac_rfl
  · rintro ⟨k,a,hv,he⟩
    rcases hv with ⟨hl,hh⟩
    cases a with
    | zero =>
      simp only [Nat.zero_add,Nat.pow_one,Nat.pow_zero,Nat.one_mul] at he
      have hq : 2*u=8*2^k+h+k := by omega
      exact Or.inl ⟨k,⟨by omega,by omega⟩,hq⟩
    | succ t =>
      obtain ⟨d,hd,hout⟩ := cancel_two_pow_odd (t+1+1) (3^(t+1)) (2*u+5)
        ((2*h+5)+16*2^k+2*k+5) (three_odd _) he
      have hodd : d%2=1 := by
        have hm := congrArg (fun z : Nat => z%2) hout
        change (2*u+5)%2=(3^(t+1)*d)%2 at hm
        rw [Nat.mul_mod (3^(t+1)),three_odd] at hm
        omega
      have hq : 2*(2^t*d)=8*2^k+h+k+5 := by
        rw [Nat.pow_succ,Nat.pow_succ] at hd
        have hm : (2^t*2*2)*d=4*(2^t*d) := by grind
        rw [hm] at hd
        omega
      exact Or.inr ⟨k,t,d,hodd,⟨by omega,by omega⟩,hout,hq⟩

#print axioms cancel_two_pow_odd
#print axioms grammar_iff_unified
end CascadePeriodic
