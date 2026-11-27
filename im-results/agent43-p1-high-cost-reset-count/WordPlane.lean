import Matrix64

namespace BB6.Agent43WordPlane
open BB6.Agent43Matrix64 (Rows stages transpose_bit)

def WordMem (a : Rows) (i : Nat) : Prop := (a (i/64)).testBit (i%64)=true

def Words64 (a : Rows) : Prop := ∀ i, a i<2^64

/-- A word-aligned or unaligned 64-bit read, with zero extension supplied
    by the caller's word function. -/
def read64 (a : Rows) (i : Nat) : Nat :=
  ((a (i/64)+2^64*a (i/64+1)) >>> (i%64)) % 2^64

theorem read64_bit (a : Rows) (i j : Nat) (ha : Words64 a) (hj : j<64) :
    (read64 a i).testBit j = (a ((i+j)/64)).testBit ((i+j)%64) := by
  unfold read64
  rw [Nat.testBit_mod_two_pow,Nat.testBit_shiftRight,Nat.add_comm (a (i/64)),Nat.testBit_two_pow_mul_add _ (ha (i/64))]
  simp only [decide_eq_true hj,Bool.true_and]
  have hi := Nat.div_add_mod i 64
  have hij := Nat.div_add_mod (i+j) 64
  have hm := Nat.mod_lt i (by decide : 0<64)
  have hmj := Nat.mod_lt (i+j) (by decide : 0<64)
  by_cases h : i%64+j<64
  · rw [if_pos h,show (i+j)/64=i/64 by omega,show (i+j)%64=i%64+j by omega]
  · rw [if_neg h,show (i+j)/64=i/64+1 by omega,show (i+j)%64=i%64+j-64 by omega]

/-- Local inclusion test for all valid bits in one source interval. -/
def TileOK (ends out : Rows) (start count b : Nat) : Prop :=
  let X := read64 ends (start+64*b) &&& (2^(min 64 (count-64*b))-1)
  X &&& out b = X

instance (ends out : Rows) (start count b : Nat) : Decidable (TileOK ends out start count b) := by
  unfold TileOK; infer_instance

/-- No element of an interval is lost by the word-local tile checks. In
    particular a partial final tile cannot justify any out-of-range bit. -/
theorem tile_cover (ends out : Rows) (start count : Nat) (ha : Words64 ends)
    (h : ∀ b, 64*b<count → TileOK ends out start count b)
    (t : Nat) (ht : t<count) (he : WordMem ends (start+t)) :
    (out (t/64)).testBit (t%64)=true := by
  let b := t/64
  let j := t%64
  have hdecomp : 64*b+j=t := Nat.div_add_mod _ _
  have hj : j<64 := Nat.mod_lt _ (by decide)
  have hb : 64*b<count := by omega
  have hlim : j<min 64 (count-64*b) := by omega
  have hcheck := h b hb
  unfold TileOK at hcheck
  have hbit := congrArg (fun x : Nat => x.testBit j) hcheck
  rw [Nat.testBit_and,Nat.testBit_and,Nat.testBit_two_pow_sub_one,read64_bit _ _ _ ha hj] at hbit
  have heq : start+64*b+j=start+t := by omega
  simp only [heq,show (ends ((start+t)/64)).testBit ((start+t)%64)=true from he,decide_eq_true hlim,Bool.true_and] at hbit
  exact hbit

/-- Lane r contains all quotient indices t whose original carry is r+M*t. -/
def PlaneMem (M : Nat) (lane : Nat → Rows) (c : Nat) : Prop :=
  WordMem (lane (c%M)) (c/M)

/-- Match the C++ output layout: each 64×64 lane tile is transposed to
    64 consecutive quotient rows and one group of 64 residue bits. -/
def flatten (S : Nat) (lane : Nat → Rows) (j : Nat) : Nat :=
  let row := j/S
  let colBlock := j%S
  stages 6 (fun r => lane (64*colBlock+r) (row/64)) (row%64)

theorem flatten_bit (S c : Nat) (lane : Nat → Rows) (hS : 0<S) :
    WordMem (flatten S lane) c ↔ PlaneMem (64*S) lane c := by
  unfold WordMem PlaneMem flatten
  have hM : 0<64*S := Nat.mul_pos (by decide) hS
  have hdiv : c/64/S=c/(64*S) := Nat.div_div_eq_div_mul _ _ _
  have hcol : c/64%S=c%(64*S)/64 := (Nat.mod_mul_right_div_self _ _ _).symm
  have hmod : c%(64*S)%64=c%64 := Nat.mod_mod_of_dvd _ ⟨S,rfl⟩
  have hrow : c/64/S%64<64 := Nat.mod_lt _ (by decide)
  have hbit : c%64<64 := Nat.mod_lt _ (by decide)
  change (stages 6 (fun r => lane (64*(c/64%S)+r) (c/64/S/64)) (c/64/S%64)).testBit (c%64)=true ↔ (lane (c%(64*S)) (c/(64*S)/64)).testBit (c/(64*S)%64)=true
  rw [transpose_bit _ _ _ hrow hbit,hdiv,hcol,←hmod]
  have he := Nat.div_add_mod (c%(64*S)) 64
  rw [he]

#print axioms read64_bit
#print axioms tile_cover
#print axioms flatten_bit
end BB6.Agent43WordPlane
