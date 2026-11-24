import Lean
namespace BB6.Agent28Delay

/-- The delay window is the previous n selection bits, oldest bit at bit zero. -/
def windowStep (P W b : Nat) : Nat := W/2+(P/2)*b

theorem window_step_identity (P W b : Nat) (hP : P%2=0) :
    2*windowStep P W b+W%2=W+P*b := by
  unfold windowStep
  rw [Nat.mul_add, ← Nat.mul_assoc]
  have hp : 2*(P/2)=P := by omega
  rw [hp]
  omega

theorem window_step_bound (P W b : Nat) (hP : P%2=0) (hW : W<P) (hb : b≤1) :
    windowStep P W b<P := by
  have he := window_step_identity P W b hP
  have h : b=0 ∨ b=1 := by omega
  rcases h with rfl|rfl <;> simp at he <;> omega

def projection (W : Nat) (s : Int) : Int := 7*(W:Int)+s

/-- Exact signed convolution. The giant coefficient 7P-C appears only in the
    projection. The evolving signed carry uses the delayed low bit of W. -/
theorem delayed_step_iff (P W b : Nat) (C s s' : Int) (hP : P%2=0) :
    2*projection (windowStep P W b) s' = projection W s+(7*(P:Int)-C)*(b:Int) ↔
    2*s'=s+7*(W%2:Nat)-C*(b:Int) := by
  have h := window_step_identity P W b hP
  have hz : 2*(windowStep P W b:Int)+(W%2:Nat)=(W:Int)+(P:Int)*(b:Int) := by exact_mod_cast h
  unfold projection
  rw [Int.sub_mul,Int.mul_assoc]
  omega

theorem signed_bounds (n j : Nat) (s s' d b : Int)
    (hs : -(n:Int)-(j:Int)-1≤s ∧ s≤7) (hd : 0≤d ∧ d≤1) (hb : 0≤b ∧ b≤1)
    (h : 2*s'=s+7*d-((n:Int)+(j:Int)+3)*b) :
    -(n:Int)-(j+1:Nat)-1≤s' ∧ s'≤7 := by
  have he : b=0 ∨ b=1 := by omega
  rcases he with rfl|rfl <;> simp at h <;> omega

/-- A group with fixed delayed bits has a small integer anchor u. Its
    carry lies in an interval of width C, so reverse reconstruction is unique. -/
theorem anchor_step (u s s' d C b : Int)
    (hC : 0<C) (hs : u-C<s ∧ s≤u) (hb : 0≤b ∧ b≤1)
    (h : 2*s'=s+7*d-C*b) :
    (u+7*d)/2-(C+1)<s' ∧ s'≤(u+7*d)/2 := by
  have he : b=0 ∨ b=1 := by omega
  rcases he with rfl|rfl <;> simp at h <;> omega

theorem anchor_reconstruct (u s s' d C b : Int) (_hC : 0<C)
    (hs : u-C<s ∧ s≤u) (hb : 0≤b ∧ b≤1)
    (h : 2*s'=s+7*d-C*b) :
    (b=1 ↔ 2*s'-7*d≤u-C) ∧ s=2*s'-7*d+C*b := by
  have he : b=0 ∨ b=1 := by omega
  rcases he with rfl|rfl <;> simp at h ⊢ <;> omega

/-- Offset p=u-s supports an exact small nonnegative carry bitset. -/
theorem offset_step (u s s' d C b : Int) (h : 2*s'=s+7*d-C*b) :
    2*((u+7*d)/2-s')=(u-s)+C*b-(u+7*d)%2 := by omega

theorem offset_reconstruct (p p' e C b : Int) (_hC : 0<C)
    (hp : 0≤p ∧ p<C) (hb : 0≤b ∧ b≤1) (h : 2*p'+e=p+C*b) :
    (b=1 ↔ C≤2*p'+e) ∧ p=2*p'+e-C*b := by
  have he : b=0 ∨ b=1 := by omega
  rcases he with rfl|rfl <;> simp at h ⊢ <;> omega

/-- A high selected and high omitted window bit imply both full margins. -/
theorem window_margin (P W n j L M : Nat) (s : Int)
    (hW : W<P) (hs : -(n:Int)-(j:Int)-1≤s ∧ s≤7)
    (hlo : M≤W) (hhi : M≤P-1-W) (hM : L+n+j+1≤7*M) :
    (L:Int)≤projection W s ∧ (L:Int)≤7*(P:Int)-(n:Int)-(j:Int)-1-projection W s := by
  unfold projection
  have hhi' : M+W+1≤P := by omega
  omega

#print axioms delayed_step_iff
#print axioms signed_bounds
#print axioms anchor_reconstruct
#print axioms offset_step
#print axioms offset_reconstruct
#print axioms window_margin
end BB6.Agent28Delay
