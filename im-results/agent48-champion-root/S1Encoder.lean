import ChampionRootBridge
import Lean.Elab.Tactic.Omega

/-!
General physical encoder for the published BusyCoq TM63 S1 section.

The source uses BinDec d0 d1 len n = BinaryCounter d0 d1
(2^(len+1)-1-n). Here width=len+1 is the number of three-cell blocks.
The recursive binary digits are low-bit-first; the physical left word is
far-to-near, so this file reverses the fixed-width bit vector before
expanding each bit to d0 or d1.

This is an exact finite-support transcription of the source S1 words, not a
new BB(6) bound. The main theorem exposes the arbitrary carry suffix needed
by the counted TM63 micro-step proof.
-/

namespace BB6Coverage.Agent48S1Encoder

open BB6Coverage

/-- A recursively defined power of two. -/
def twoPow : Nat → Nat
  | 0 => 1
  | n+1 => 2 * twoPow n

theorem twoPow_pos (n : Nat) : 0 < twoPow n := by
  induction n with
  | zero => simp [twoPow]
  | succ n ih =>
      simp [twoPow]
      omega

theorem twoPow_add (a b : Nat) :
    twoPow (a+b) = twoPow a * twoPow b := by
  induction b with
  | zero =>
      simp [twoPow]
  | succ b ih =>
      simp only [Nat.add_succ, twoPow]
      rw [ih]
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem twoPow_lt_succ (n : Nat) : twoPow n < twoPow (n+1) := by
  have hp := twoPow_pos n
  simp [twoPow]
  omega

/-- The low-bit-first fixed-width binary expansion. -/
def bitsLE : Nat → Nat → List Bool
  | 0, _ => []
  | k+1, n => decide (n % 2 = 1) :: bitsLE k (n / 2)

theorem bitsLE_even (k n : Nat) :
    bitsLE (k+1) (2*n) = false :: bitsLE k n := by
  have hm : (2*n) % 2 = 0 := by omega
  have hd : (2*n) / 2 = n := by omega
  simp [bitsLE, hm, hd]

theorem bitsLE_odd (k n : Nat) :
    bitsLE (k+1) (2*n+1) = true :: bitsLE k n := by
  have hm : (2*n+1) % 2 = 1 := by omega
  have hd : (2*n+1) / 2 = n := by omega
  simp [bitsLE, hm, hd]

/-- If u is odd, the low r bits of 2^r*u are zero and bit r is one. -/
theorem bitsLE_pow2_odd (k r u : Nat) (hr : r < k) (hu : u % 2 = 1) :
    bitsLE k (twoPow r * u) =
      List.replicate r false ++ [true] ++
        bitsLE (k-r-1) ((u-1)/2) := by
  induction r generalizing k u with
  | zero =>
      have hk : k = (k-1)+1 := by omega
      have huRep : u = 2*((u-1)/2)+1 := by omega
      conv_lhs => rw [show twoPow 0 = 1 by rfl]
      conv_lhs => rw [hk]
      rw [huRep, bitsLE_odd]
      simp
  | succ r ih =>
      have hk : k = (k-1)+1 := by omega
      have hpow : twoPow (r+1)*u = 2*(twoPow r*u) := by
        simp [twoPow, Nat.mul_assoc]
      conv_lhs => rw [hk]
      rw [hpow, bitsLE_even]
      have hrec := ih (k-1) u (by omega) hu
      rw [hrec]
      have heq : (k-1)-r-1 = k-(r+1)-1 := by omega
      rw [heq]
      simp [List.replicate_succ, List.append_assoc]

/-- If u is odd, 2^r*u-1 has r low one-bits followed by a zero. -/
theorem bitsLE_pow2_sub_one (k r u : Nat) (hr : r < k) (hu : u % 2 = 1) :
    bitsLE k (twoPow r * u - 1) =
      List.replicate r true ++ [false] ++
        bitsLE (k-r-1) ((u-1)/2) := by
  induction r generalizing k u with
  | zero =>
      have hk : k = (k-1)+1 := by omega
      have huRep : u-1 = 2*((u-1)/2) := by omega
      conv_lhs => rw [show twoPow 0 = 1 by rfl]
      conv_lhs => rw [hk]
      rw [huRep, bitsLE_even]
      simp
  | succ r ih =>
      have hk : k = (k-1)+1 := by omega
      have huPos : 0 < u := by omega
      have hA : 0 < twoPow r * u :=
        Nat.mul_pos (twoPow_pos r) huPos
      have hmul : twoPow (r+1)*u = 2*(twoPow r*u) := by
        simp [twoPow, Nat.mul_assoc]
      have hpow : twoPow (r+1)*u - 1 =
          2*(twoPow r*u - 1)+1 := by omega
      conv_lhs => rw [hk]
      rw [hpow, bitsLE_odd]
      have hrec := ih (k-1) u (by omega) hu
      rw [hrec]
      have heq : (k-1)-r-1 = k-(r+1)-1 := by omega
      rw [heq]
      simp [List.replicate_succ, List.append_assoc]

/-- The all-ones counter has exactly width d1 blocks. -/
theorem bitsLE_max (width : Nat) :
    bitsLE width (twoPow width - 1) = List.replicate width true := by
  induction width with
  | zero => rfl
  | succ width ih =>
      have hp := twoPow_pos width
      have hpow : twoPow (width+1)-1 =
          2*(twoPow width-1)+1 := by
        simp [twoPow]
        omega
      rw [hpow, bitsLE_odd, ih]
      simp [List.replicate_succ, List.append_assoc]

/-- Source TM63 blocks: d0=100 and d1=111. -/
def d0 : List Bool := [true,false,false]
def d1 : List Bool := [true,true,true]

def block (b : Bool) : List Bool := if b then d1 else d0

def blockWord : List Bool → List Bool
  | [] => []
  | b::bs => block b ++ blockWord bs

@[simp] theorem blockWord_append (xs ys : List Bool) :
    blockWord (xs ++ ys) = blockWord xs ++ blockWord ys := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      simp [blockWord, ih, List.append_assoc]

/-- r copies of one three-cell source block. -/
def repeatBlock (b : Bool) (r : Nat) : List Bool :=
  blockWord (List.replicate r b)

def binDecWord (width n : Nat) : List Bool :=
  blockWord ((bitsLE width (twoPow width - 1 - n)).reverse)

theorem replicate_append_singleton (n : Nat) (b : Bool) :
    List.replicate n b ++ [b] = List.replicate (n+1) b := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [List.replicate_succ, ih, List.append_assoc]

theorem reverse_replicate (n : Nat) (b : Bool) :
    (List.replicate n b).reverse = List.replicate n b := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (b :: List.replicate n b).reverse =
        List.replicate (n+1) b
      rw [List.reverse_cons, ih]
      exact replicate_append_singleton n b

theorem binDecWord_zero (width : Nat) :
    binDecWord width 0 = repeatBlock true width := by
  unfold binDecWord
  simp only [Nat.sub_zero]
  rw [bitsLE_max, reverse_replicate]
  rfl

/-- The universal binary decrement interface. If n+1=2^r*u and u is odd,
    and the complementary high quotient v is odd, then the published
    BinDec word changes by exactly d0;d1^r -> d1;d0^r. The same prefix
    occurs on both sides. -/
theorem binDec_carry_suffix
    (width n r u v : Nat)
    (hr : r < width)
    (hfactor : n+1 = twoPow r * u)
    (hu : u % 2 = 1)
    (hcomplement : twoPow (width-r) = u+v)
    (hv : v % 2 = 1) :
    ∃ prefix : List Bool,
      binDecWord width (n+1) =
        prefix ++ d0 ++ repeatBlock true r ∧
      binDecWord width n =
        prefix ++ d1 ++ repeatBlock false r := by
  have hsum : r + (width-r) = width := by omega
  have hpow : twoPow width = twoPow r * (u+v) := by
    calc
      twoPow width = twoPow (r+(width-r)) := by rw [← hsum]
      _ = twoPow r * twoPow (width-r) := twoPow_add r (width-r)
      _ = twoPow r * (u+v) := by rw [hcomplement]
  have hpow' : twoPow width = twoPow r*u + twoPow r*v := by
    calc
      twoPow width = twoPow r * (u+v) := hpow
      _ = twoPow r*u + twoPow r*v := by rw [Nat.mul_add]
  have huPos : 0 < u := by omega
  have hvPos : 0 < v := by omega
  have hA : 0 < twoPow r*u := Nat.mul_pos (twoPow_pos r) huPos
  have hB : 0 < twoPow r*v := Nat.mul_pos (twoPow_pos r) hvPos
  have hcounterIn :
      twoPow width - 1 - (n+1) = twoPow r*v - 1 := by omega
  have hcounterOut :
      twoPow width - 1 - n = twoPow r*v := by omega
  let tail := bitsLE (width-r-1) ((v-1)/2)
  have hbitsIn :
      bitsLE width (twoPow width - 1 - (n+1)) =
        List.replicate r true ++ [false] ++ tail := by
    rw [hcounterIn]
    simpa [tail] using bitsLE_pow2_sub_one width r v hr hv
  have hbitsOut :
      bitsLE width (twoPow width - 1 - n) =
        List.replicate r false ++ [true] ++ tail := by
    rw [hcounterOut]
    simpa [tail] using bitsLE_pow2_odd width r v hr hv
  have hrevIn :
      (List.replicate r true ++ [false] ++ tail).reverse =
        tail.reverse ++ [false] ++ List.replicate r true := by
    simp [List.reverse_append, reverse_replicate, List.append_assoc]
  have hrevOut :
      (List.replicate r false ++ [true] ++ tail).reverse =
        tail.reverse ++ [true] ++ List.replicate r false := by
    simp [List.reverse_append, reverse_replicate, List.append_assoc]
  refine ⟨blockWord tail.reverse, ?_, ?_⟩
  · unfold binDecWord
    rw [hbitsIn, hrevIn]
    simp [blockWord, block, d0, d1, repeatBlock, List.append_assoc]
  · unfold binDecWord
    rw [hbitsOut, hrevOut]
    simp [blockWord, block, d0, d1, repeatBlock, List.append_assoc]

/-- The source S1 left word, parameterized by block counts
    width0=len0+1 and width1=len1+1. The head is the last cell. -/
def s1LeftWord (width0 a0 : Nat) (marker : List Bool)
    (width1 a1 : Nat) : List Bool :=
  [true,true,true,false,true,true] ++
    binDecWord width0 a0 ++ d0 ++ marker ++ binDecWord width1 a1

/-- The cells to the right of the S1 head: 0,11100,(111)^(b+1). -/
def s1RightWord (b : Nat) : List Bool :=
  [false,true,true,true,false,false] ++ List.replicate (3*(b+1)) true

/-- The arbitrary-parameter S1 source word inherits the exact same
    arbitrary-r carry suffix; all earlier sections are absorbed into prefix. -/
theorem s1LeftWord_carry
    (width0 a0 : Nat) (marker : List Bool)
    (width1 n r u v : Nat)
    (hr : r < width1)
    (hfactor : n+1 = twoPow r*u)
    (hu : u%2=1)
    (hcomplement : twoPow (width1-r)=u+v)
    (hv : v%2=1) :
    ∃ prefix : List Bool,
      s1LeftWord width0 a0 marker width1 (n+1) =
        prefix ++ d0 ++ repeatBlock true r ∧
      s1LeftWord width0 a0 marker width1 n =
        prefix ++ d1 ++ repeatBlock false r := by
  obtain ⟨p,hIn,hOut⟩ :=
    binDec_carry_suffix width1 n r u v hr hfactor hu hcomplement hv
  refine ⟨[true,true,true,false,true,true] ++
    binDecWord width0 a0 ++ d0 ++ marker ++ p, ?_, ?_⟩
  · simp [s1LeftWord, hIn, List.append_assoc]
  · simp [s1LeftWord, hOut, List.append_assoc]

/-- The source m0 marker. -/
def m0 : List Bool := [true,false]

/-- The terminal S1(L,0,m0,a,0,b) word is the all-one special case. -/
theorem s1LeftWord_zero (L a : Nat) :
    s1LeftWord L 0 m0 a 0 =
      [true,true,true,false,true,true] ++
        repeatBlock true L ++
        [true,false,false,true,false] ++
        repeatBlock true a := by
  simp [s1LeftWord, m0, binDecWord_zero, d0, List.append_assoc]

/-- Read a finite word from its nearest cell outward, with zero padding. -/
def sideBit : List Bool → Nat → Bool
  | [], _ => false
  | h::_, 0 => h
  | _::tail, n+1 => sideBit tail n

/-- Convert far-to-near left cells and near-to-far right cells into the
    original two-sided infinite-tape configuration. Coordinate 0 is the
    last bit of left; coordinate +1 is the first bit of right. -/
def configFromWords (left right : List Bool) : Config :=
  { state := ⟨3, by decide⟩
    head := 0
    tape := fun x =>
      if x < 0 then sideBit left.reverse x.natAbs
      else if x = 0 then sideBit left.reverse 0
      else sideBit right (x.toNat - 1) }

/-- The general source S1 configuration in the original Config model.
    State 3 is D; the head is on the last bit of the left S1 word. -/
def s1Config (width0 a0 : Nat) (marker : List Bool)
    (width1 a1 b : Nat) : Config :=
  configFromWords (s1LeftWord width0 a0 marker width1 a1) (s1RightWord b)

theorem s1Config_state (width0 a0 : Nat) (marker : List Bool)
    (width1 a1 b : Nat) :
    (s1Config width0 a0 marker width1 a1 b).state = ⟨3, by decide⟩ := rfl

theorem s1Config_head (width0 a0 : Nat) (marker : List Bool)
    (width1 a1 b : Nat) :
    (s1Config width0 a0 marker width1 a1 b).head = 0 := rfl

theorem s1Config_right_first (width0 a0 : Nat) (marker : List Bool)
    (width1 a1 b : Nat) :
    (s1Config width0 a0 marker width1 a1 b).tape 1 = false := by
  simp [s1Config, configFromWords, s1RightWord, sideBit]

#print axioms binDec_carry_suffix
#print axioms s1LeftWord_carry
#print axioms s1Config_right_first

end BB6Coverage.Agent48S1Encoder
