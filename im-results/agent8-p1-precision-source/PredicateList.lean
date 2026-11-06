import Lean

namespace BB6.Agent8FiniteBridge

def rect (M Z : Nat) : List (Nat × Nat) :=
  (List.range (M+1)).flatMap fun m =>
    (List.range (Z+1)).map fun z => (m,z)

theorem mem_rect (M Z m z : Nat) : (m,z) ∈ rect M Z ↔ m ≤ M ∧ z ≤ Z := by
  simp [rect, List.mem_flatMap]
  omega

noncomputable def listed (M Z : Nat) (S : Nat → Nat → Prop) : List (Nat × Nat) := by
  classical
  exact (rect M Z).filter fun p => decide (S p.1 p.2)

theorem mem_listed (M Z m z : Nat) (S : Nat → Nat → Prop) :
    (m,z) ∈ listed M Z S ↔ m ≤ M ∧ z ≤ Z ∧ S m z := by
  classical
  simp [listed, mem_rect, and_assoc]

/-- Constructive finite rectangle with classical filtering. A successor staying
in the cost bound also stays inside the shadow z-bound L+M. -/
theorem listed_closed (L M : Nat) (S : Nat → Nat → Prop)
    (hsmall : ∀ m z, S m z → m ≤ M)
    (hclosed : ∀ m z t v zp, S m z → z=2^t*v →
       2*zp+1=L+m+t+v → S (m+t+1) zp)
    (m z t v zp : Nat)
    (hm : (m,z) ∈ listed M (L+M) S)
    (hd : z=2^t*v)
    (hn : 2*zp+1=L+m+t+v) :
    (m+t+1,zp) ∈ listed M (L+M) S := by
  classical
  obtain ⟨_,hz,hs⟩ := (mem_listed M (L+M) m z S).mp hm
  have hchild := hclosed m z t v zp hs hd hn
  have hmchild := hsmall (m+t+1) zp hchild
  have hpow : 1 ≤ (2:Nat)^t := Nat.one_le_pow t 2 (by decide)
  have hv : v ≤ z := by
    rw [hd]
    simpa using Nat.mul_le_mul_right v hpow
  have hzchild : zp ≤ L+M := by omega
  exact (mem_listed M (L+M) (m+t+1) zp S).mpr ⟨hmchild,hzchild,hchild⟩

theorem listed_bounds (K L M : Nat) (S : Nat → Nat → Prop)
    (hsmall : ∀ m z, S m z → m ≤ M)
    (hnodiv : ∀ m z, S m z → ¬2^K∣z)
    (m z : Nat) (hm : (m,z)∈listed M (L+M) S) :
    m≤M ∧ ¬2^K∣z := by
  rcases (mem_listed M (L+M) m z S).mp hm with ⟨_,_,hs⟩
  exact ⟨hsmall m z hs, hnodiv m z hs⟩

#print axioms listed_closed
#print axioms listed_bounds
#print axioms mem_listed
end BB6.Agent8FiniteBridge
