import CInverseDepth
import Lean.Elab.Tactic.Omega

namespace BB6.Agent8Compat
open BB6.Agent8Depth

/-- The reachable-state odd-middle zero-right residue necessary condition. -/
def admissible (a k : Nat) : Prop :=
  a % 2 = 1 ∧
  (5 ≤ k → k % 2 = 1 → (a+k) % 4 = 0 ∨ (a+k) % 4 = 3)

/-- A reverse certificate all of whose c=0 checkpoints satisfy the existing
    global odd-k modulo-four necessary condition. -/
inductive CompatibleLong : Nat → Nat → Nat → Prop where
 | zero (a k : Nat) (hg : admissible a k) : CompatibleLong 0 a k
 | succ (n a k : Nat) (hk : 1 ≤ k) (hg : admissible a (2*k+2))
    (h : CompatibleLong n (a+2*k) k) : CompatibleLong (n+1) a (2*k+2)

theorem compatible_implies_long {n a k : Nat} (h : CompatibleLong n a k) :
    LongAnc n a k := by
  induction h with
  | zero a k hg => exact .zero a k
  | succ n a k hk hg h ih => exact .succ n a k hk ih

/-- For the initial odd k == 1 mod4, or every later even k, the universal
    modular obstruction is satisfied when the weighted c=0 rank is 1 mod4. -/
theorem admissible_of_rank (a k : Nat)
    (hr : (a+2*k)%4=1) (hk : k%2=0 ∨ k%4=1) :
    admissible a k := by
  constructor
  · omega
  · intro h5 hodd
    rcases hk with he | he
    · omega
    · left
      omega

/-- The base odd counter is 1 mod4; all later reverse middle counters are even. -/
theorem K_good_mod (n t : Nat) :
    K n (12*t+13)%2=0 ∨ K n (12*t+13)%4=1 := by
  cases n with
  | zero =>
      right
      simp only [K]
      omega
  | succ n =>
      left
      change (2*K n (12*t+13)+2)%2=0
      omega

/-- Construct a whole n-long-return inverse chain satisfying the globally
    necessary c=0 modulo-four rule at every displayed section checkpoint. -/
theorem compatible_chain (n a t : Nat)
    (hr : (a+2*K n (12*t+13))%4=1) :
    CompatibleLong n a (K n (12*t+13)) := by
  induction n generalizing a with
  | zero =>
      apply CompatibleLong.zero
      exact admissible_of_rank a (12*t+13) hr (K_good_mod 0 t)
  | succ n ih =>
      change CompatibleLong (n+1) a (2*K n (12*t+13)+2)
      apply CompatibleLong.succ n a (K n (12*t+13))
      · exact K_positive n (12*t+13) (by omega)
      · apply admissible_of_rank a (2*K n (12*t+13)+2)
        · exact hr
        · left
          omega
      · apply ih (a+2*K n (12*t+13))
        change (a+2*(2*K n (12*t+13)+2))%4=1 at hr
        omega

/-- A 3-mod4 base parameter makes every c=0 state in arbitrarily long
    exact predecessor chains satisfy the known global range-hole invariant. -/
theorem all_depth_admissible_gate (n t : Nat) :
    CompatibleLong n (2*J n (4*t+3)+1) (3*J n (4*t+3)+4) := by
  rw [← K_at_reset n (4*t+3)]
  have hr : ((2*J n (4*t+3)+1)+2*K n (3*(4*t+3)+4))%4=1 := by
    rw [K_at_reset]
    omega
  have he : 3*(4*t+3)+4=12*t+13 := by omega
  rw [he] at hr ⊢
  exact compatible_chain n (2*J n (4*t+3)+1) t hr

/-- Unbounded indices with arbitrarily deep exact predecessors, and all c=0
    section checkpoints satisfy the known blank-necessary odd-middle hole. -/
theorem unbounded_compatible_depth (n lower : Nat) :
    ∃ j : Nat, lower < j ∧
       CompatibleLong n (2*j+1) (3*j+4) ∧
       ∃ aa kk time : Nat, n ≤ time ∧
           BB6.CReachBridge.runN time (some (aa,kk,0)) = some (2*j+1,3*j+4,0) := by
  refine ⟨J n (4*(lower+1)+3), ?_, ?_, ?_⟩
  · have h := J_ge n (4*(lower+1)+3)
    omega
  · exact all_depth_admissible_gate n (lower+1)
  · exact arbitrarily_deep_reset_traces n (4*(lower+1)+3)

#print axioms unbounded_compatible_depth
#print axioms all_depth_admissible_gate
end BB6.Agent8Compat
