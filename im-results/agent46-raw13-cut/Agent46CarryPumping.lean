import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Carry
open BB6Coverage Agent31Pump

/-- Exact cost of a two-cell carry, when a carry at depth k first traverses
    2*k cells and invokes every smaller carry once. -/
def cost (base : Nat) : Nat → Nat
  | 0 => base
  | n+1 => 2*cost base n+2

def prefixCost (base : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => prefixCost base n+cost base n

theorem cost_prefix (base k : Nat) : cost base k = 2*k+base+prefixCost base k := by
  induction k with
  | zero => simp [cost,prefixCost]
  | succ k ih => simp only [cost,prefixCost]; omega

theorem cost_closed (base k : Nat) : cost base k+2=(base+2)*2^k := by
  induction k with
  | zero => simp [cost]
  | succ k ih => rw [Nat.pow_succ,← Nat.mul_assoc,← ih]; simp only [cost]; omega

theorem cost_pos (base k : Nat) (h : 0<base) : 0<cost base k := by
  cases k <;> simp only [cost] <;> omega

/-- All smaller carries remove a repeated pair from the left, while growing
    the right-side counter. No condition on the untouched left suffix. -/
theorem drain (p : PartialMachine) (q : Fin 6) (Z : List Bool) (R : Nat → List Bool)
    (base k : Nat) (h : ∀ j<k, ∀ L, run0 p (cost base j) ⟨q,Z++L,R j⟩ = some ⟨q,L,R (j+1)⟩)
    (L : List Bool) : run0 p (prefixCost base k) ⟨q,rep Z k++L,R 0⟩ = some ⟨q,L,R k⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    have h0 := ih (fun j hj => h j (by omega)) (Z++L)
    have h1 := h k (by omega) L
    have he : rep Z (k+1)++L=rep Z k++(Z++L) := by
      rw [rep,← rep_snoc Z k,List.append_assoc]
    rw [he,prefixCost]
    exact join0 h0 h1

/-- A generic nested carry induction. The prepare segment replaces the
    leading pair by a marker preceded by k fresh pairs; the finish segment
    consumes the marker after all smaller carries have run. -/
theorem advance (p : PartialMachine) (q : Fin 6) (Z M : List Bool) (R : Nat → List Bool)
    (prep fin : Nat)
    (prepare : ∀ k L, run0 p (2*k+prep) ⟨q,Z++L,R k⟩ = some ⟨q,rep Z k++(M++L),R 0⟩)
    (finish : ∀ k L, run0 p fin ⟨q,M++L,R k⟩ = some ⟨q,L,R (k+1)⟩)
    (k : Nat) (L : List Bool) :
    run0 p (cost (prep+fin) k) ⟨q,Z++L,R k⟩ = some ⟨q,L,R (k+1)⟩ := by
  have bounded : ∀ n, ∀ j<n, ∀ L, run0 p (cost (prep+fin) j) ⟨q,Z++L,R j⟩ = some ⟨q,L,R (j+1)⟩ := by
    intro n
    induction n with
    | zero => intro j hj; omega
    | succ n ih =>
      intro j hj L
      by_cases he : j=n
      · subst j
        have h := join0 (join0 (prepare n L) (drain p q Z R (prep+fin) n ih (M++L))) (finish n L)
        rw [cost_prefix]
        have ht : 2*n+(prep+fin)+prefixCost (prep+fin) n=2*n+prep+prefixCost (prep+fin) n+fin := by omega
        rw [ht]
        exact h
      · exact ih j (by omega) L
  exact bounded (k+1) k (by omega) L

theorem blank (p : PartialMachine) (q : Fin 6) (Z M N : List Bool) (R : Nat → List Bool)
    (prep fin : Nat)
    (prepare : ∀ k L, run0 p (2*k+prep) ⟨q,Z++L,R k⟩ = some ⟨q,rep Z k++(M++L),R 0⟩)
    (finish : ∀ k L, run0 p fin ⟨q,M++L,R k⟩ = some ⟨q,L,R (k+1)⟩)
    (prepareBlank : ∀ k, run0 p (2*k+prep) ⟨q,[],R k⟩ = some ⟨q,rep Z k++N,R 0⟩)
    (finishBlank : ∀ k, run0 p fin ⟨q,N,R k⟩ = some ⟨q,[],R (k+1)⟩)
    (k : Nat) : run0 p (cost (prep+fin) k) ⟨q,[],R k⟩ = some ⟨q,[],R (k+1)⟩ := by
  have h := join0 (join0 (prepareBlank k) (drain p q Z R (prep+fin) k
    (fun j _ L => advance p q Z M R prep fin prepare finish j L) N)) (finishBlank k)
  rw [cost_prefix]
  have ht : 2*k+(prep+fin)+prefixCost (prep+fin) k=2*k+prep+prefixCost (prep+fin) k+fin := by omega
  rw [ht]
  exact h

#print axioms cost_closed
#print axioms advance
#print axioms blank
end BB6Coverage.Agent31Pump.Carry
