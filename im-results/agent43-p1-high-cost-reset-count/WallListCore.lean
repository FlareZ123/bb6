import Lean

namespace BB6.Agent43WallListCore

def costPowSum : List Nat → Nat
  | [] => 0
  | s :: A => 2^s + costPowSum A

def costWeightedSum (n : Nat) : List Nat → Nat
  | [] => 0
  | s :: A => (n+3+s)*2^s + costWeightedSum n A

def CostWitness (n d m : Nat) : Prop :=
  ∃ A : List Nat, A.Nodup ∧ (∀ s ∈ A, s < m) ∧
    (0 < m → 0 ∈ A) ∧
    2+14*2^n*costPowSum A = 2^m*(d-1)+2*costWeightedSum n A

theorem witness_root (n : Nat) : CostWitness n 3 0 := by
  refine ⟨[], ?_, ?_, ?_, ?_⟩
  · exact List.nodup_nil
  · simp
  · intro h; omega
  · simp [costPowSum, costWeightedSum]

theorem witness_step (n d m e D : Nat) (he : 0 < e)
    (h : CostWitness n d m)
    (hrec : (d-1)+14*2^n = 2^e*(D-1)+2*(m+n+3)) :
    CostWitness n D (m+e) := by
  obtain ⟨A, hnd, hlt, hstart, hInv⟩ := h
  have hnot : m ∉ A := by
    intro hm
    have := hlt m hm
    omega
  refine ⟨m::A, List.nodup_cons.mpr ⟨hnot,hnd⟩, ?_, ?_, ?_⟩
  · intro s hs
    rcases List.mem_cons.mp hs with hsm | hsA
    · omega
    · have := hlt s hsA
      omega
  · intro _
    by_cases hm : m=0
    · simp [hm]
    · exact List.mem_cons_of_mem _ (hstart (by omega))
  · have hrecMul := congrArg (fun x : Nat => 2^m*x) hrec
    change 2^m*((d-1)+14*2^n) = 2^m*(2^e*(D-1)+2*(m+n+3)) at hrecMul
    rw [Nat.mul_add, Nat.mul_add] at hrecMul
    have h1 : 2^m*(2^e*(D-1)) = 2^(m+e)*(D-1) := by
      rw [← Nat.mul_assoc, ← Nat.pow_add]
    have h2 : 2^m*(2*(m+n+3)) = 2*((n+3+m)*2^m) := by
      have heq : m+n+3=n+3+m := by omega
      rw [heq]
      ac_rfl
    have h3 : 2^m*(14*2^n) = 14*2^n*2^m := by ac_rfl
    rw [h1,h2,h3] at hrecMul
    simp only [costPowSum, costWeightedSum]
    rw [Nat.mul_add (14*2^n), Nat.mul_add 2]
    omega

theorem wall_from_witness (n d m : Nat) (h : CostWitness n d m)
    (hd : d=2*2^n+2*m+2*n+7) :
    ∃ A : List Nat, A.Nodup ∧ (∀ s ∈ A, s < m) ∧
      (0 < m → 0 ∈ A) ∧
      1+7*2^n*costPowSum A =
        2^n*2^m+costWeightedSum n A+(n+3+m)*2^m := by
  obtain ⟨A,hnd,hlt,hstart,hInv⟩ := h
  refine ⟨A,hnd,hlt,hstart,?_⟩
  have hd' : d-1=2*(2^n+(n+3+m)) := by omega
  have hR : 2^m*(d-1)=2*(2^n*2^m+(n+3+m)*2^m) := by
    rw [hd']
    calc
      _ = 2*((2^n+(n+3+m))*2^m) := by ac_rfl
      _ = _ := by rw [Nat.add_mul]
  rw [hR] at hInv
  have h1 : 14*2^n*costPowSum A=2*(7*2^n*costPowSum A) := by
    calc
      _ = (2*7)*2^n*costPowSum A := rfl
      _ = _ := by ac_rfl
  rw [h1] at hInv
  omega

#print axioms witness_root
#print axioms witness_step
#print axioms wall_from_witness
end BB6.Agent43WallListCore
