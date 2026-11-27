import Std

namespace BB6.Agent43Matrix64

/-- The six masks from Agent9's exact plane_reverse.cpp. -/
def mask : Nat → Nat
  | 0 => 0x5555555555555555
  | 1 => 0x3333333333333333
  | 2 => 0x0f0f0f0f0f0f0f0f
  | 3 => 0x00ff00ff00ff00ff
  | 4 => 0x0000ffff0000ffff
  | 5 => 0x00000000ffffffff
  | _ => 0

abbrev Rows := Nat → Nat

/-- The exact pairwise XOR-swap butterfly. Each low/high row pair is updated
    from its common pre-stage inputs; pairs within a stage are disjoint. -/
def stage (h : Nat) (a : Rows) (r : Nat) : Nat :=
  let d := 2^h
  if r.testBit h then
    let t := ((a (r-d) >>> d) ^^^ a r) &&& mask h
    a r ^^^ t
  else
    let t := ((a r >>> d) ^^^ a (r+d)) &&& mask h
    a r ^^^ (t <<< d)

/-- Swap the h-th binary coordinate bit between row and column. -/
def swapR (h r c : Nat) : Nat :=
  if r.testBit h then if c.testBit h then r else r-2^h
  else if c.testBit h then r+2^h else r

def swapC (h r c : Nat) : Nat := swapR h c r

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem mask_fin : ∀ h : Fin 6, ∀ c : Fin 64,
    (mask h.val).testBit c.val = !(c.val.testBit h.val) := by decide +kernel

theorem mask_bit (h c : Nat) (hh : h<6) (hc : c<64) :
    (mask h).testBit c = !(c.testBit h) := mask_fin ⟨h,hh⟩ ⟨c,hc⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem shift_fin : ∀ h : Fin 6, ∀ c : Fin 64,
    (c.val.testBit h.val=true → 2^h.val≤c.val) ∧
    (2^h.val≤c.val → (c.val-2^h.val).testBit h.val = !(c.val.testBit h.val)) := by decide +kernel

theorem shift_bit (h c : Nat) (hh : h<6) (hc : c<64) :
    (c.testBit h=true → 2^h≤c) ∧
    (2^h≤c → (c-2^h).testBit h = !(c.testBit h)) := shift_fin ⟨h,hh⟩ ⟨c,hc⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem swap_fin : ∀ h : Fin 6, ∀ r : Fin 64, ∀ c : Fin 64,
    swapR h.val r.val c.val<64 ∧ swapC h.val r.val c.val<64 := by decide +kernel

theorem swap_bound (h r c : Nat) (hh : h<6) (hr : r<64) (hc : c<64) :
    swapR h r c<64 ∧ swapC h r c<64 := swap_fin ⟨h,hh⟩ ⟨r,hr⟩ ⟨c,hc⟩

/-- Bitwise semantics of one butterfly, for arbitrary input words. The
    finitely checked mask/index facts above do not depend on input data. -/
theorem stage_bit (h r c : Nat) (a : Rows) (hh : h<6) (hr : r<64) (hc : c<64) :
    (stage h a r).testBit c = (a (swapR h r c)).testBit (swapC h r c) := by
  have hm := mask_bit h c hh hc
  have hs := shift_bit h c hh hc
  cases hrb : r.testBit h <;> cases hcb : c.testBit h
  · simp only [stage,swapC,swapR,hrb,hcb, Bool.false_eq_true,ite_false,Nat.testBit_xor,Nat.testBit_shiftLeft]
    by_cases hd : 2^h≤c
    · have hm' := mask_bit h (c-2^h) hh (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hc)
      rw [hs.2 hd,hcb] at hm'
      simp [hd,Nat.testBit_and,hm']
    · simp [hd]
  · have hd := hs.1 hcb
    have hm' := mask_bit h (c-2^h) hh (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hc)
    rw [hs.2 hd,hcb] at hm'
    simp only [stage,swapC,swapR,hrb,hcb,Bool.false_eq_true,ite_false,ite_true,Nat.testBit_xor,Nat.testBit_shiftLeft]
    simp [hd,Nat.testBit_and,Nat.testBit_xor,Nat.testBit_shiftRight,hm',show 2^h+(c-2^h)=c by omega]
  · simp [stage,swapC,swapR,hrb,hcb,Nat.testBit_xor,Nat.testBit_and,Nat.testBit_shiftRight,hm,Nat.add_comm (2^h) c]
    cases (a r).testBit c <;> cases (a (r-2^h)).testBit (c+2^h) <;> rfl
  · simp [stage,swapC,swapR,hrb,hcb,Nat.testBit_xor,Nat.testBit_and,hm]

private theorem mask_bound_fin : ∀ h : Fin 6, mask h.val<2^(64-2^h.val) := by decide +kernel

/-- Every XOR-swap operation is a genuine 64-bit word operation: the
    shift in the low row cannot discard a set high bit. -/
theorem stage_bound (h r : Nat) (a : Rows) (hh : h<6) (ha : ∀ i, a i<2^64) :
    stage h a r<2^64 := by
  have hm := mask_bound_fin ⟨h,hh⟩
  change mask h<2^(64-2^h) at hm
  have hd : 2^h≤64 := Nat.pow_le_pow_right (by decide : 0<2) (show h≤6 by omega)
  unfold stage
  split
  · apply Nat.xor_lt_two_pow (ha r)
    exact Nat.lt_of_le_of_lt Nat.and_le_right (Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide : 0<2) (Nat.sub_le 64 (2^h))))
  · apply Nat.xor_lt_two_pow (ha r)
    rw [Nat.shiftLeft_eq,←show (64-2^h)+2^h=64 by omega,Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right (Nat.lt_of_le_of_lt Nat.and_le_right hm) (Nat.two_pow_pos _)

/-- Apply the stages in exactly the order of the C++ implementation. -/
def stages : Nat → Rows → Rows
  | 0,a => a
  | n+1,a => stage n (stages n a)

def coords : Nat → Nat → Nat → Nat × Nat
  | 0,r,c => (r,c)
  | n+1,r,c => coords n (swapR n r c) (swapC n r c)

theorem stages_bit (n r c : Nat) (a : Rows) (hn : n≤6) (hr : r<64) (hc : c<64) :
    (stages n a r).testBit c = (a (coords n r c).1).testBit (coords n r c).2 := by
  induction n generalizing r c with
  | zero => rfl
  | succ n ih =>
    have hb := swap_bound n r c (by omega) hr hc
    rw [stages,stage_bit n r c (stages n a) (by omega) hr hc]
    exact ih _ _ (by omega) hb.1 hb.2

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem coords_fin : ∀ r : Fin 64, ∀ c : Fin 64,
    coords 6 r.val c.val = (c.val,r.val) := by decide +kernel

/-- Fully symbolic verification of the 64×64 packed transpose on every
    possible input matrix, not merely a test on basis matrices. -/
theorem transpose_bit (r c : Nat) (a : Rows) (hr : r<64) (hc : c<64) :
    (stages 6 a r).testBit c = (a c).testBit r := by
  rw [stages_bit 6 r c a (by decide) hr hc,coords_fin ⟨r,hr⟩ ⟨c,hc⟩]

#print axioms stage_bound
#print axioms stage_bit
#print axioms transpose_bit
end BB6.Agent43Matrix64
