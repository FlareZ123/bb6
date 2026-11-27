import JumpResidueReduced
import LongBlockCover

namespace BB6.Agent45PackedJump

open BB6.Agent23ResiduePeriod (Rep)
open BB6.Agent9JumpResidue
open BB6.Agent9ReverseBlock (JumpMember walk_mem_jump)
open BB6.Agent45ReverseBlock
open BB6.Agent45LongBlock

/-- Rotate a finite modular support in a packed natural integer. -/
def rotate (M s bits : Nat) : Nat :=
  let t := s%M
  ((bits <<< t) ||| (bits >>> (M-t))) &&& (2^M-1)

theorem rotate_sound (M s bits x : Nat) (hM : 0<M) (hx : x<M)
    (hb : bits.testBit x=true) : (rotate M s bits).testBit ((x+s)%M)=true := by
  let t := s%M
  have ht : t<M := Nat.mod_lt _ hM
  have he : (x+s)%M=(x+t)%M := by
    rw [Nat.add_mod,Nat.mod_eq_of_lt hx]
  rw [he]
  unfold rotate
  change (((bits <<< t) ||| (bits >>> (M-t))) &&& (2^M-1)).testBit ((x+t)%M)=true
  simp only [Nat.testBit_and,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_shiftRight,Nat.testBit_two_pow_sub_one,decide_eq_true (Nat.mod_lt _ hM),Bool.and_true]
  by_cases h : x+t<M
  · rw [Nat.mod_eq_of_lt h]
    have h1 : x+t≥t := by omega
    have h2 : x+t-t=x := by omega
    simp [h1,h2,hb]
  · have h1 : (x+t)%M=x+t-M := by
      rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
    have h2 : M-t+(x+t-M)=x := by omega
    rw [h1,h2,hb]
    simp

def packedNeg (M : Nat) : List Int → Nat
  | [] => 1
  | w::ws => let b := packedNeg M ws; b ||| rotate M ((-w)%(M:Int)).toNat b

theorem emod_lt (M : Nat) (hM : 0<M) (x : Int) : (x%(M:Int)).toNat<M := by
  have hp : (0:Int)<(M:Int) := by omega
  have hn := Int.emod_nonneg x (by omega : (M:Int)≠0)
  exact (Int.toNat_lt hn).2 (Int.emod_lt_of_pos x hp)

theorem residue_add (M : Nat) (hM : 0<M) (x y : Int) :
    (((x%(M:Int)).toNat+(y%(M:Int)).toNat)%M) = ((x+y)%(M:Int)).toNat := by
  have hn : (M:Int)≠0 := by omega
  apply Int.ofNat_inj.mp
  rw [Int.natCast_emod,Int.natCast_add,Int.toNat_of_nonneg (Int.emod_nonneg x hn),Int.toNat_of_nonneg (Int.emod_nonneg y hn),Int.toNat_of_nonneg (Int.emod_nonneg (x+y) hn)]
  exact (Int.add_emod x y (M:Int)).symm

theorem packedNeg_sound (M : Nat) (hM : 0<M) (ws : List Int) (x : Int)
    (h : Rep (M:Int) x ws) : (packedNeg M ws).testBit ((-x)%(M:Int)).toNat=true := by
  induction ws generalizing x with
  | nil =>
    obtain ⟨a,ha⟩ := h
    rw [ha,← Int.mul_neg,Int.mul_emod_right]
    simp [packedNeg]
  | cons w ws ih =>
    rcases h with h|h
    · simp [packedNeg,Nat.testBit_or,ih x h]
    · have hb := ih (x-w) h
      have hr := rotate_sound M ((-w)%(M:Int)).toNat (packedNeg M ws)
        ((-(x-w))%(M:Int)).toNat hM (emod_lt M hM _) hb
      rw [residue_add M hM,show -(x-w)+ -w = -x by omega] at hr
      simp [packedNeg,Nat.testBit_or,hr]

/-- Double the number of residue blocks on every recursion. -/
def repeatBlocks (M bits : Nat) : Nat → Nat
  | 0 => bits
  | t+1 => let b := repeatBlocks M bits t; b ||| (b <<< (M*2^t))

theorem repeatBlocks_sound (M bits t j r : Nat) (hj : j<2^t)
    (hr : bits.testBit r=true) : (repeatBlocks M bits t).testBit (j*M+r)=true := by
  induction t generalizing j with
  | zero =>
    have he : j=0 := by simp at hj; omega
    simpa [repeatBlocks,he] using hr
  | succ t ih =>
    simp only [repeatBlocks,Nat.testBit_or,Nat.testBit_shiftLeft]
    by_cases h : j<2^t
    · simp [ih j h]
    · have hj' : j-2^t<2^t := by rw [Nat.pow_succ] at hj; omega
      have h := ih (j-2^t) hj'
      have he : j*M=(j-2^t)*M+M*2^t := by
        have hEq : j=(j-2^t)+2^t := by omega
        calc
          j*M = ((j-2^t)+2^t)*M := congrArg (·*M) hEq
          _ = _ := by rw [Nat.add_mul,Nat.mul_comm (2^t) M]
      have hle : j*M+r≥M*2^t := by omega
      have hsub : j*M+r-M*2^t=(j-2^t)*M+r := by omega
      simp [hle,hsub,h]

def packedLift (q M bits : Nat) : Nat :=
  (repeatBlocks M bits ((q/M).log2+1)) &&& (2^q-1)

theorem packedLift_sound (q M bits c : Nat) (hc : c<q)
    (hb : bits.testBit (c%M)=true) : (packedLift q M bits).testBit c=true := by
  have hj : c/M<2^((q/M).log2+1) := by
    have hq : q/M<2^((q/M).log2+1) := by
      by_cases h : q/M=0
      · simp [h]
      · exact (Nat.log2_lt h).mp (by omega)
    exact Nat.lt_of_le_of_lt (Nat.div_le_div_right (by omega : c≤q)) hq
  have hr := repeatBlocks_sound M bits ((q/M).log2+1) (c/M) (c%M) hj hb
  rw [Nat.mul_comm (c/M) M,Nat.div_add_mod] at hr
  simp [packedLift,hc,hr]

def packedReducedJump (q k Y : Nat) : Nat :=
  let M := reducedModulus q k
  packedLift q M (rotate M Y (packedNeg M (reducedWeights q k)))

theorem packedReduced_sound (q k Y c : Nat) (h : JumpMember (q+k) k Y c) :
    (packedReducedJump q k Y).testBit c=true := by
  let M := reducedModulus q k
  have hM : 0<M := Nat.two_pow_pos (reducedExponent q k)
  obtain ⟨hc,hRep⟩ := (jump_member_iff_reduced q k Y c).mp h
  have hb := packedNeg_sound M hM (reducedWeights q k) ((Y:Int)-(c:Int)) hRep
  have hr := rotate_sound M Y (packedNeg M (reducedWeights q k))
      ((-((Y:Int)-(c:Int)))%(M:Int)).toNat hM (emod_lt M hM _) hb
  have he : (((-((Y:Int)-(c:Int)))%(M:Int)).toNat+Y)%M=c%M := by
    have hy : ((Y:Int)%(M:Int)).toNat=Y%M := by rw [←Int.natCast_emod,Int.toNat_natCast]
    rw [Nat.add_mod,Nat.mod_eq_of_lt (emod_lt M hM _),←hy,residue_add M hM,
      show -((Y:Int)-(c:Int))+(Y:Int)=(c:Int) by omega,←Int.natCast_emod,Int.toNat_natCast]
  rw [he] at hr
  exact packedLift_sound q M _ c hc hr

/-- Start a long-block certificate directly from the exact modular jump. -/
theorem live_bits_jump (n B s k : Nat) :
    LiveBits n B s k (packedReducedJump (n+s+3) k (targetDigits n s B k)) := by
  intro z c hw
  have h := walk_mem_jump (n+s+k+3) z (targetWord n s B k) c hw
  rw [targetWord_length,digits_targetWord] at h
  apply packedReduced_sound
  simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

#print axioms rotate_sound
#print axioms packedNeg_sound
#print axioms packedLift_sound
#print axioms packedReduced_sound
#print axioms live_bits_jump

end BB6.Agent45PackedJump
