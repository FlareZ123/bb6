import Lean
set_option maxRecDepth 16384
namespace BB6.Agent9Heaps

/-- Universal two-pile transfer. An even left pile is halved and the
    removed half, together with one new unit, is passed to the right. -/
def moveL (u e : Nat) : Nat × Nat := (u/2, e+u/2+1)

/-- Symmetric transfer, available when the right pile is even. -/
def moveR (u e : Nat) : Nat × Nat := (u+e/2+1, e/2)

theorem moveL_sum (u e : Nat) (h : u%2=0) :
    (moveL u e).1 + (moveL u e).2 = u+e+1 := by
  simp [moveL]
  omega

theorem moveR_sum (u e : Nat) (h : e%2=0) :
    (moveR u e).1 + (moveR u e).2 = u+e+1 := by
  simp [moveR]
  omega

/-- Exactly t consecutive legal transfers of the right pile. -/
inductive RightRun : Nat → Nat → Nat → Nat → Nat → Prop where
  | zero (u e : Nat) : RightRun 0 u e u e
  | step (t u e u' e' : Nat) (heven : e%2=0)
      (tail : RightRun t (u+e/2+1) (e/2) u' e') :
      RightRun (t+1) u e u' e'

/-- The right-pile transfer iterates collapse to exact dyadic division. -/
theorem right_run_closed (t u z v : Nat)
    (h : z=2^t*v) :
    RightRun t u z (u+z-v+t) v := by
  induction t generalizing u z with
  | zero =>
      simp at h
      subst z
      simp
      exact RightRun.zero u v
  | succ t ih =>
      have hdouble : z=2*(2^t*v) := by
        calc
          z = 2^(t+1)*v := h
          _ = 2*(2^t*v) := by rw [Nat.pow_succ]; ac_rfl
      have heven : z%2=0 := by omega
      have hz : z/2=2^t*v := by omega
      have hvle : v≤z/2 := by
        rw [hz]
        exact Nat.le_mul_of_pos_left v (Nat.pow_pos (by decide))
      have htail := ih (u+z/2+1) (z/2) hz
      have htwo : z=2*(z/2) := by omega
      have htarget : (u+z/2+1)+(z/2)-v+t = u+z-v+(t+1) := by omega
      rw [←htarget]
      exact RightRun.step t u z _ v heven htail

/-- Every right-only transfer segment has its exact power-of-two quotient. -/
theorem right_run_quotient (t u z un v : Nat)
    (h : RightRun t u z un v) :
    z=2^t*v ∧ un=u+z-v+t := by
  induction h with
  | zero a b =>
      simp
  | step k a b c d heven tail ih =>
      rcases ih with ⟨hp,hb⟩
      have htwice : b=2*(b/2) := by omega
      have hvle : d≤b/2 := by
        rw [hp]
        exact Nat.le_mul_of_pos_left d (Nat.pow_pos (by decide))
      constructor
      · calc
          b = 2*(b/2) := htwice
          _ = 2*(2^k*d) := by rw [hp]
          _ = 2^(k+1)*d := by rw [Nat.pow_succ]; ac_rfl
      · omega

/-- The exact shadow coordinates are recovered at any legal left-pile
    transfer boundary. -/
def Represents (L m z u e : Nat) : Prop :=
  u%2=0 ∧ L+m=u+e+4 ∧ z=e+u/2+1

/-- A single exact inverse-shadow edge transports the two-pile coding.
    The new left pile is the result of one left transfer followed by
    t right transfers, once 2^t divides the old z coordinate. -/
theorem shadow_step_coding (L m z t v zp u e : Nat)
    (hrep : Represents L m z u e)
    (hquot : v≤z)
    (hstep : 2*zp+1=L+m+t+v) :
    ∃ un, Represents L (m+t+1) zp un v ∧
      un = u/2+(z-v)+t := by
  rcases hrep with ⟨hu,hs,hz⟩
  let un := u/2+(z-v)+t
  refine ⟨un, ?_, rfl⟩
  change un%2=0 ∧ L+(m+t+1)=un+v+4 ∧ zp=v+un/2+1
  have hm : u=2*(u/2) := by omega
  have hsub : z-v+v=z := by omega
  constructor
  · omega
  constructor
  · omega
  · omega

/-- Conversely, a legal encoded transfer block determines the exact
    odd-output shadow equation without any model approximation. -/
theorem heap_block_to_shadow (L m z t v zp u e un : Nat)
    (hrep : Represents L m z u e)
    (hrep' : Represents L (m+t+1) zp un v)
    (hblock : un=u/2+(z-v)+t) :
    2*zp+1=L+m+t+v := by
  rcases hrep with ⟨hu,hs,hz⟩
  rcases hrep' with ⟨hu',hs',hz'⟩
  omega

/-- One exact scalar source edge is equivalent to one legal transfer of
    the left pile and then exactly t legal transfers of the right pile. -/
theorem shadow_step_realized_by_heap (L m z t v zp u e : Nat)
    (hrep : Represents L m z u e)
    (hd : z=2^t*v)
    (hnext : 2*zp+1=L+m+t+v) :
    ∃ un, Represents L (m+t+1) zp un v ∧
      RightRun t (moveL u e).1 (moveL u e).2 un v := by
  have hvle : v≤z := by
    rw [hd]
    exact Nat.le_mul_of_pos_left v (Nat.pow_pos (by decide))
  obtain ⟨un,hrep',heq⟩ := shadow_step_coding L m z t v zp u e hrep hvle hnext
  refine ⟨un,hrep',?_⟩
  have hz : (moveL u e).2=z := by
    rcases hrep with ⟨_,_,hr⟩
    simp [moveL,hr]
  have hu : (moveL u e).1=u/2 := rfl
  rw [hz,hu,heq]
  have hrewrite : u/2+z-v+t = u/2+(z-v)+t := by omega
  simpa only [hrewrite] using right_run_closed t (u/2) z v hd

/-- The transfer-block converse reconstructs the authentic scalar edge;
    it does not infer a machine edge merely from an arithmetic resemblance. -/
theorem heap_block_is_shadow (L m z t zp u e un v : Nat)
    (hrep : Represents L m z u e)
    (hrep' : Represents L (m+t+1) zp un v)
    (hrun : RightRun t (moveL u e).1 (moveL u e).2 un v) :
    z=2^t*v ∧ 2*zp+1=L+m+t+v := by
  have hz : (moveL u e).2=z := by
    rcases hrep with ⟨_,_,hr⟩
    simp [moveL,hr]
  have hu : (moveL u e).1=u/2 := rfl
  rw [hz,hu] at hrun
  obtain ⟨hd,hblock⟩ := right_run_quotient t (u/2) z un v hrun
  have hvle : v≤z := by
    rw [hd]
    exact Nat.le_mul_of_pos_left v (Nat.pow_pos (by decide))
  refine ⟨hd,?_⟩
  have hb : un=u/2+(z-v)+t := by omega
  exact heap_block_to_shadow L m z t v zp u e un hrep hrep' hb

/-- The two authentic P1 feeder roots become explicit universal heap seeds. -/
theorem first_root (q : Nat) :
    Represents (16*q+8) 0 (12*q+4) (8*q+2) (8*q+2) := by
  unfold Represents
  constructor
  · omega
  constructor
  · omega
  · omega

theorem second_root (q : Nat) :
    Represents (16*q+9) 0 (10*q+4) (12*q+4) (4*q+1) := by
  unfold Represents
  constructor
  · omega
  constructor
  · omega
  · omega

/-- A left transfer always lands strictly below the pile-swap diagonal. -/
theorem left_image_right_dominant (u e : Nat) :
    (moveL u e).1 < (moveL u e).2 := by
  simp only [moveL, Prod.fst, Prod.snd]
  omega

/-- A right transfer always lands strictly above the pile-swap diagonal. -/
theorem right_image_left_dominant (u e : Nat) :
    (moveR u e).2 < (moveR u e).1 := by
  simp only [moveR, Prod.fst, Prod.snd]
  omega

/-- The destination of a left move determines its entire legal predecessor. -/
theorem left_predecessor (u e U E : Nat)
    (heven : u%2=0) (h : moveL u e = (U,E)) :
    u=2*U ∧ e+U+1=E := by
  have hu : u=2*(u/2) := by omega
  have hU : u/2=U := (Prod.mk.inj h).1
  have hE : e+u/2+1=E := (Prod.mk.inj h).2
  omega

/-- The destination of a right move determines its entire legal predecessor. -/
theorem right_predecessor (u e U E : Nat)
    (heven : e%2=0) (h : moveR u e = (U,E)) :
    e=2*E ∧ u+E+1=U := by
  have he : e=2*(e/2) := by omega
  have hU : u+e/2+1=U := (Prod.mk.inj h).1
  have hE : e/2=E := (Prod.mk.inj h).2
  omega

/-- Legal single-transfer predecessors are unique, even when one pile is zero.
    The strict inequalities of left and right output regions exclude cross-types. -/
def HeapEdge (x z : Nat×Nat) : Prop :=
  (x.1%2=0 ∧ z=moveL x.1 x.2) ∨
  (x.2%2=0 ∧ z=moveR x.1 x.2)

theorem heap_edge_predecessor_unique (x y z : Nat×Nat)
    (hx : HeapEdge x z) (hy : HeapEdge y z) : x=y := by
  rcases x with ⟨u,e⟩
  rcases y with ⟨a,b⟩
  rcases z with ⟨U,E⟩
  dsimp [HeapEdge] at hx hy
  rcases hx with ⟨hue,hx⟩ | ⟨hee,hx⟩
  · rcases hy with ⟨ha,hy⟩ | ⟨hb,hy⟩
    · have hxp := left_predecessor u e U E hue hx.symm
      have hyp := left_predecessor a b U E ha hy.symm
      simp only [Prod.mk.injEq]
      omega
    · have hl := left_image_right_dominant u e
      have hr := right_image_left_dominant a b
      rw [←hx] at hl
      rw [←hy] at hr
      omega
  · rcases hy with ⟨ha,hy⟩ | ⟨hb,hy⟩
    · have hl := left_image_right_dominant a b
      have hr := right_image_left_dominant u e
      rw [←hy] at hl
      rw [←hx] at hr
      omega
    · have hxp := right_predecessor u e U E hee hx.symm
      have hyp := right_predecessor a b U E hb hy.symm
      simp only [Prod.mk.injEq]
      omega

/-- The two P1 feeder seeds are sibling-origin coordinates in one
    universal heap tree: the second is the right child of the first,
    and the left child is its mirror image. -/
theorem feeder_siblings (q : Nat) :
    moveL (8*q+2) (8*q+2) = (4*q+1,12*q+4) ∧
    moveR (8*q+2) (8*q+2) = (12*q+4,4*q+1) := by
  simp only [moveL, moveR, Prod.mk.injEq]
  omega

/-- Equal-pile nodes are all genuine roots of the universal transfer forest. -/
theorem diagonal_no_predecessor (a : Nat) (x : Nat×Nat) :
    ¬ HeapEdge x (a,a) := by
  rcases x with ⟨u,e⟩
  intro h
  dsimp [HeapEdge] at h
  rcases h with ⟨_,hl⟩ | ⟨_,hr⟩
  · have hs := left_image_right_dominant u e
    rw [←hl] at hs
    omega
  · have hs := right_image_left_dominant u e
    rw [←hr] at hs
    omega

#print axioms feeder_siblings
#print axioms diagonal_no_predecessor

#print axioms heap_edge_predecessor_unique
#print axioms right_run_closed
#print axioms right_run_quotient
#print axioms shadow_step_realized_by_heap
#print axioms heap_block_is_shadow
#print axioms shadow_step_coding
#print axioms heap_block_to_shadow
#print axioms first_root
#print axioms second_root
end BB6.Agent9Heaps
