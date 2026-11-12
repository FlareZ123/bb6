import ChampionRootBridge
import Lean.Elab.Tactic.Omega

/-!
# Source-exact S0/S1 physical encoder for TM63

This mirrors the pinned BusyCoq definitions in verify/Helper.v,
verify/BinaryCounter.v, verify/BinaryCounter_v2.v, and verify/SOBCv5.v.

Important orientation convention: Coq's l <* xs is Str_app xs l,
so xs is prepended to the head-facing left stream. Coq's <[x;y;z]
reverses the displayed physical block. Thus d0 and d1 below are in
head-facing order, not left-to-right physical order.
-/

namespace BB6Coverage.Agent8S1Encoder

open BB6Coverage.Agent48Champion

/-- Coq <[1;0;0], in head-facing list order. -/
def d0 : List Bool := [false,false,true]

/-- Coq <[1;1;1]; this block is palindromic. -/
def d1 : List Bool := [true,true,true]

/-- The head-facing marker words m0, m1 and m2. -/
def markerWord (m : Nat) : List Bool :=
  if m % 3 = 0 then [false,true]
  else if m % 3 = 1 then [true,false,true]
  else [true,true,false,true]

/-- The fixed left-history word lh, in head-facing order. -/
def lh : List Bool := [true,true]

/-- Repetition of the source zero-digit block. -/
def d1pow : Nat → List Bool
  | 0 => []
  | n+1 => d1 ++ d1pow n

/-- A fuelled transcription of BusyCoq's positive BinaryCounter.
The fuel is the declared number of counter digits; on the source domain
n < 2^len, the complemented positive integer reaches its xH base
exactly when the fuel is exhausted. -/
def binaryCounterFuel : Nat → Nat → List Bool
  | 0, _ => []
  | fuel+1, p =>
      if p ≤ 1 then []
      else if p % 2 = 0 then d0 ++ binaryCounterFuel fuel (p / 2)
      else d1 ++ binaryCounterFuel fuel (p / 2)

/-- The finite block prefix of source BinDec d0 d1 len n tail, with
the arbitrary source tail omitted. The complemented integer is exactly
the one in BinaryCounter_v2.v: 2^(len+1)-1-n. -/
def binDec (len n : Nat) : List Bool :=
  binaryCounterFuel len (2^(len+1)-1-n)

private theorem binaryCounterFuel_even (fuel n : Nat) (hn : 0 < n) :
    binaryCounterFuel (fuel+1) (2*n) =
      d0 ++ binaryCounterFuel fuel n := by
  have hp : ¬ 2*n ≤ 1 := by omega
  have hd : (2*n) / 2 = n := by omega
  rw [binaryCounterFuel]
  simp [hp,hd]

private theorem binaryCounterFuel_odd (fuel n : Nat) (hn : 0 < n) :
    binaryCounterFuel (fuel+1) (2*n+1) =
      d1 ++ binaryCounterFuel fuel n := by
  have hp : ¬ (2*n+1) ≤ 1 := by omega
  have hm : (2*n+1) % 2 ≠ 0 := by omega
  have hd : (2*n+1) / 2 = n := by omega
  rw [binaryCounterFuel]
  simp [hp,hm,hd]

/-- Source BinDec_mul2: an even counter value prefixes d1. -/
theorem binDec_even (len n : Nat) (hn : n < 2^len) :
    binDec (len+1) (2*n) = d1 ++ binDec len n := by
  unfold binDec
  have hpow : 2^(len+2) = 2*2^(len+1) := by
    rw [show len+2 = (len+1)+1 by omega, Nat.pow_succ]
    ac_rfl
  have harg :
      2^(len+2)-1-2*n =
        2*(2^(len+1)-1-n)+1 := by omega
  have hpos : 0 < 2^(len+1)-1-n := by
    have hpow' : 2^len ≤ 2^(len+1) := by
      rw [Nat.pow_succ]
      omega
    omega
  rw [harg]
  exact binaryCounterFuel_odd len (2^(len+1)-1-n) hpos

/-- Source BinDec_mul2add1: an odd counter value prefixes d0. -/
theorem binDec_odd (len n : Nat) (hn : n < 2^len) :
    binDec (len+1) (2*n+1) = d0 ++ binDec len n := by
  unfold binDec
  have hpow : 2^(len+2) = 2*2^(len+1) := by
    rw [show len+2 = (len+1)+1 by omega, Nat.pow_succ]
    ac_rfl
  have harg :
      2^(len+2)-1-(2*n+1) =
        2*(2^(len+1)-1-n) := by omega
  have hpos : 0 < 2^(len+1)-1-n := by
    have hpow' : 2^len ≤ 2^(len+1) := by
      rw [Nat.pow_succ]
      omega
    omega
  rw [harg]
  exact binaryCounterFuel_even len (2^(len+1)-1-n) hpos

/-- Repeated source BinDec_mul2: low zero bits are d1 blocks at the
actual head-facing boundary. -/
theorem binDec_mulpow2 (len n i : Nat) (hn : n < 2^len) :
    binDec (len+i) (n*2^i) =
      d1pow i ++ binDec len n := by
  induction i with
  | zero =>
      simp [binDec,d1pow]
  | succ i ih =>
      have hpow : 2^(len+i) = 2^len * 2^i := by
        rw [Nat.pow_add]
      have hpos : 0 < 2^i := Nat.pow_pos (by decide)
      have hbound : n*2^i < 2^(len+i) := by
        rw [hpow]
        exact Nat.mul_lt_mul_of_pos_right hn hpos
      have hlen : len+(i+1) = (len+i)+1 := by omega
      have hnum : n*2^(i+1) = 2*(n*2^i) := by
        rw [Nat.pow_succ]
        ac_rfl
      rw [hlen,hnum,binDec_even (len+i) (n*2^i) hbound,ih]
      simp [d1pow,List.append_assoc]

/-- Exact source carry-prefix expansion. If the counter value has odd
part 2*q+1 and 2-adic exponent r, its head-facing BinDec word is
d1^r ++ d0 ++ BinDec(q). -/
theorem binDec_carryPrefix (len q r : Nat) (hq : q < 2^len) :
    binDec (len+1+r) ((2*q+1)*2^r) =
      d1pow r ++ d0 ++ binDec len q := by
  have hpow : 2^(len+1) = 2*2^len := by
    rw [Nat.pow_succ]
    ac_rfl
  have hbound : 2*q+1 < 2^(len+1) := by omega
  rw [binDec_mulpow2 (len+1) (2*q+1) r hbound]
  rw [binDec_odd len q hq]
  simp [List.append_assoc]

/-- Every positive natural has an odd-part/power-of-two factorization.
Uniqueness is not needed by the encoder theorem. -/
theorem exists_odd_factor (z : Nat) (hz : 0 < z) :
    ∃ q r, z = (2*q+1)*2^r := by
  induction z using Nat.strongRecOn with
  | ind z ih =>
      by_cases hod : z % 2 = 1
      · refine ⟨z/2,0,?_⟩
        have hdecomp : z = 2*(z/2)+1 := by omega
        simpa using hdecomp
      · have hmod : z % 2 = 0 := by omega
        let m := z/2
        have hmEq : 2*m = z := by dsimp [m]; omega
        have hmpos : 0 < m := by dsimp [m]; omega
        have hmlt : m < z := by dsimp [m]; omega
        obtain ⟨q,r,hr⟩ := ih m hmlt hmpos
        refine ⟨q,r+1,?_⟩
        have hh : z = 2*((2*q+1)*2^r) := by rw [← hmEq,hr]
        rw [hh,Nat.pow_succ]
        ac_rfl


/-- A valid length-bounded source counter has the matching residual
odd-part length: if 0<z<2^a and z=(2q+1)2^r, then a=len+1+r
for len=a-r-1 and q<2^len. This closes the range side-condition needed
to instantiate the carry-prefix theorem for every valid S0/S1 input. -/
theorem exists_odd_factor_bounded (a z : Nat)
    (hz : 0 < z) (hzlt : z < 2^a) :
    ∃ q r len, z = (2*q+1)*2^r ∧ a = len+1+r ∧ q < 2^len := by
  obtain ⟨q,r,hr⟩ := exists_odd_factor z hz
  have hodd : 1 ≤ 2*q+1 := by omega
  have hmul := Nat.mul_le_mul_left (2^r) hodd
  have hpowle : 2^r ≤ z := by
    simpa [Nat.mul_comm,hr] using hmul
  have hpowlt : 2^r < 2^a := lt_of_le_of_lt hpowle hzlt
  have hra : r < a := by
    by_contra hnot
    have har : a ≤ r := by omega
    have hp := Nat.pow_le_pow_right (show 0 < 2 by decide) har
    omega
  let len := a-r-1
  have ha : a = len+1+r := by dsimp [len]; omega
  have hpowadd : 2^a = 2^(len+1)*2^r := by
    calc
      2^a = 2^(len+1+r) := by rw [ha]
      _ = 2^(len+1)*2^r := by rw [Nat.pow_add]
  have hq : q < 2^len := by
    by_contra hqnot
    have hqge : 2^len ≤ q := by omega
    have hlargeOdd : 2^(len+1) < 2*q+1 := by
      rw [Nat.pow_succ]
      omega
    have hlarge :
        2^(len+1)*2^r < (2*q+1)*2^r :=
      Nat.mul_lt_mul_of_pos_right hlargeOdd (Nat.pow_pos (by decide))
    have hsmall : (2*q+1)*2^r < 2^(len+1)*2^r := by
      simpa [hr,hpowadd] using hzlt
    omega
  exact ⟨q,r,len,hr,ha,hq⟩

/-- The source zero counter is exactly a repetition of d1. -/
theorem binDec_zero (len : Nat) : binDec len 0 = d1pow len := by
  induction len with
  | zero =>
      simp [binDec,binaryCounterFuel,d1pow]
  | succ len ih =>
      have hbound : 0 < 2^len := Nat.pow_pos (by decide)
      calc
        binDec (len+1) 0 = d1 ++ binDec len 0 := by
          simpa using binDec_even len 0 hbound
        _ = d1pow (len+1) := by simp [d1pow,ih]

/-- The repeated d1 word is invariant under reversal. -/
private theorem d1pow_append_d1 (n : Nat) :
    d1pow n ++ d1 = d1 ++ d1pow n := by
  induction n with
  | zero => simp [d1pow]
  | succ n ih =>
      calc
        d1pow (n+1) ++ d1 = d1 ++ (d1pow n ++ d1) := by
          simp [d1pow,List.append_assoc]
        _ = d1 ++ (d1 ++ d1pow n) := by rw [ih]
        _ = d1 ++ d1pow (n+1) := by simp [d1pow]

theorem d1pow_reverse (n : Nat) : (d1pow n).reverse = d1pow n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        (d1pow (n+1)).reverse =
            (d1pow n).reverse ++ d1 := by
              simp [d1pow,List.reverse_append,d1]
        _ = d1pow n ++ d1 := by rw [ih]
        _ = d1 ++ d1pow n := d1pow_append_d1 n
        _ = d1pow (n+1) := by simp [d1pow]

/-- Length of the physical block word on the valid source domain. -/
theorem d1pow_length (n : Nat) : (d1pow n).length = 3*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [d1pow,d1,ih,Nat.mul_succ]

theorem binDec_length (len n : Nat) (hn : n < 2^len) :
    (binDec len n).length = 3*len := by
  induction len generalizing n with
  | zero =>
      have hn0 : n = 0 := by omega
      subst n
      simp [binDec,binaryCounterFuel]
  | succ len ih =>
      have hpow : 2^(len+1) = 2*2^len := by
        rw [Nat.pow_succ]
        ac_rfl
      by_cases he : n % 2 = 0
      · let k := n/2
        have hnEq : n = 2*k := by dsimp [k]; omega
        have hk : k < 2^len := by dsimp [k]; omega
        rw [hnEq,binDec_even len k hk]
        simp [d1,ih k hk]
        omega
      · have hmod : n % 2 < 2 := Nat.mod_lt n (by decide)
        have ho : n % 2 = 1 := by omega
        let k := n/2
        have hnEq : n = 2*k+1 := by dsimp [k]; omega
        have hk : k < 2^len := by dsimp [k]; omega
        rw [hnEq,binDec_odd len k hk]
        simp [d0,ih k hk]
        omega

/-- Head-facing S0 left stream: BinDec is prepended to its arbitrary
left context, exactly as l <* xs is defined in Helper.v. -/
def s0LeftFacing (l : List Bool) (a z : Nat) : List Bool :=
  binDec a z ++ l

/-- The physical S0 left word, from far left to the D-head cell. -/
def s0PhysicalLeft (l : List Bool) (a z : Nat) : List Bool :=
  (s0LeftFacing l a z).reverse

/-- The right-facing S0 suffix includes the separator zero before RC. -/
def s0RightFacing (b : Nat) : List Bool :=
  [false,true,true,true,false,false] ++ d1pow (b+1)

/-- The physical right word following the D-head cell. -/
def s0PhysicalRight (b : Nat) : List Bool := s0RightFacing b

/-- Zero-padded lookup from a nearest-first physical side. -/
def sideBit : List Bool → Nat → Bool
  | [], _ => false
  | h::_, 0 => h
  | _::t, n+1 => sideBit t n

/-- The complete original-source S0 tape, with absolute head coordinate h.
For x≤h, index zero is the cell under the head and subsequent indices
run left; for x>h, index zero is the first cell to the right. -/
def s0Tape (l : List Bool) (a z b : Nat) (h x : Int) : Bool :=
  if x ≤ h then
    sideBit (s0LeftFacing l a z) (Int.toNat (h-x))
  else
    sideBit (s0RightFacing b) (Int.toNat (x-h-1))

/-- The actual original-source S0 configuration, in BB6Coverage.Config. -/
def s0Config (l : List Bool) (a z b : Nat) (h : Int) : BB6Coverage.Config :=
  ⟨(3 : Fin 6),h,s0Tape l a z b h⟩

@[simp] theorem s0Config_state (l : List Bool) (a z b : Nat) (h : Int) :
    (s0Config l a z b h).state = (3 : Fin 6) := rfl

@[simp] theorem s0Config_head (l : List Bool) (a z b : Nat) (h : Int) :
    (s0Config l a z b h).head = h := rfl

/-- Exact physical cell lookup to the left of the genuine D head. -/
theorem s0Config_left_cell (l : List Bool) (a z b : Nat)
    (h : Int) (i : Nat) :
    (s0Config l a z b h).tape (h-(i:Int)) =
      sideBit (s0LeftFacing l a z) i := by
  unfold s0Config s0Tape
  have hle : h-(i:Int) ≤ h := by omega
  have hdiff : h-(h-(i:Int)) = (i:Int) := by omega
  simp [hle,hdiff]

/-- Exact physical cell lookup to the right of the genuine D head. -/
theorem s0Config_right_cell (l : List Bool) (a z b : Nat)
    (h : Int) (i : Nat) :
    (s0Config l a z b h).tape (h+1+(i:Int)) =
      sideBit (s0RightFacing b) i := by
  unfold s0Config s0Tape
  have hgt : ¬ h+1+(i:Int) ≤ h := by omega
  have hdiff : h+1+(i:Int)-h-1 = (i:Int) := by omega
  simp [hgt,hdiff]

/-- The universal S0 carry boundary in head-facing order. -/
theorem s0LeftFacing_carryPrefix (l : List Bool) (len q r : Nat)
    (hq : q < 2^len) :
    s0LeftFacing l (len+1+r) ((2*q+1)*2^r) =
      d1pow r ++ d0 ++ binDec len q ++ l := by
  unfold s0LeftFacing
  rw [binDec_carryPrefix len q r hq]

/-- Physical left-to-right form of the S0 boundary: the exact suffix
immediately before the head is d0 ++ d1^r. -/
theorem s0PhysicalLeft_carrySuffix (l : List Bool) (len q r : Nat)
    (hq : q < 2^len) :
    s0PhysicalLeft l (len+1+r) ((2*q+1)*2^r) =
      (binDec len q ++ l).reverse ++ d0.reverse ++ d1pow r := by
  unfold s0PhysicalLeft
  rw [s0LeftFacing_carryPrefix l len q r hq]
  simp [List.reverse_append,d1pow_reverse,List.append_assoc]

/-- The full left-facing S1 stream, obtained by the source's nested
S0 (LC ... <* d0 <* m) definition. -/
def s1LeftFacing (L n m a z : Nat) : List Bool :=
  binDec a z ++ markerWord m ++ d0 ++ binDec L n ++ lh

/-- The literal physical left-to-right S1 word. -/
def s1PhysicalLeft (L n m a z : Nat) : List Bool :=
  (s1LeftFacing L n m a z).reverse

/-- The literal physical right word following the D-head cell. -/
def s1PhysicalRight (b : Nat) : List Bool := s0PhysicalRight b

/-- The actual original-source S1 configuration. -/
def s1Config (L n m a z b : Nat) (h : Int) : BB6Coverage.Config :=
  s0Config (markerWord m ++ d0 ++ binDec L n ++ lh) a z b h

@[simp] theorem s1Config_state (L n m a z b : Nat) (h : Int) :
    (s1Config L n m a z b h).state = (3 : Fin 6) := rfl

@[simp] theorem s1Config_head (L n m a z b : Nat) (h : Int) :
    (s1Config L n m a z b h).head = h := rfl

/-- Exact cell lookup for the S1 head-facing left stream. -/
theorem s1Config_left_cell (L n m a z b : Nat) (h : Int) (i : Nat) :
    (s1Config L n m a z b h).tape (h-(i:Int)) =
      sideBit (s1LeftFacing L n m a z) i := by
  simpa [s1Config,s1LeftFacing,s0LeftFacing,List.append_assoc] using
    s0Config_left_cell
      (markerWord m ++ d0 ++ binDec L n ++ lh) a z b h i

/-- Exact cell lookup for the S1 right-facing suffix. -/
theorem s1Config_right_cell (L n m a z b : Nat) (h : Int) (i : Nat) :
    (s1Config L n m a z b h).tape (h+1+(i:Int)) =
      sideBit (s1PhysicalRight b) i := by
  simpa [s1Config,s1PhysicalRight,s0PhysicalRight] using
    s0Config_right_cell
      (markerWord m ++ d0 ++ binDec L n ++ lh) a z b h i

/-- The universal S1 carry boundary at the actual D-head position. -/
theorem s1LeftFacing_carryPrefix (L n m len q r : Nat)
    (hq : q < 2^len) :
    s1LeftFacing L n m (len+1+r) ((2*q+1)*2^r) =
      d1pow r ++ d0 ++ binDec len q ++
        markerWord m ++ d0 ++ binDec L n ++ lh := by
  unfold s1LeftFacing
  rw [binDec_carryPrefix len q r hq]

/-- The actual S1 tape exposes the entire carry prefix at its D head. -/
theorem s1Config_left_carryCells (L n m len q r b : Nat)
    (h : Int) (i : Nat) (hq : q < 2^len) :
    (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape (h-(i:Int)) =
      sideBit
        (d1pow r ++ d0 ++ binDec len q ++
          markerWord m ++ d0 ++ binDec L n ++ lh) i := by
  rw [s1Config_left_cell]
  rw [s1LeftFacing_carryPrefix L n m len q r hq]


/-- Turn an arbitrary valid positive S1 counter directly into the exact
carry-window tape required by the counted local macro. No residual-range
obligation remains for the caller. -/
theorem s1Config_anyPositive_carry (L n m a z b : Nat) (h : Int)
    (hz : 0 < z) (hzlt : z < 2^a) :
    ∃ q r len, z = (2*q+1)*2^r ∧ a = len+1+r ∧ q < 2^len ∧
      ∀ i, (s1Config L n m a z b h).tape (h-(i:Int)) =
        sideBit
          (d1pow r ++ d0 ++ binDec len q ++
            markerWord m ++ d0 ++ binDec L n ++ lh) i := by
  obtain ⟨q,r,len,hr,ha,hq⟩ :=
    exists_odd_factor_bounded a z hz hzlt
  refine ⟨q,r,len,hr,ha,hq,?_⟩
  intro i
  have hcfg : s1Config L n m a z b h =
      s1Config L n m (len+1+r) ((2*q+1)*2^r) b h := by
    rw [ha,hr]
  rw [hcfg]
  exact s1Config_left_carryCells L n m len q r b h i hq

/-- Physical left-to-right form of the S1 boundary: immediately before
the head-facing end, the exact suffix is d0 ++ d1^r. -/
theorem s1PhysicalLeft_carrySuffix (L n m len q r : Nat)
    (hq : q < 2^len) :
    s1PhysicalLeft L n m (len+1+r) ((2*q+1)*2^r) =
      (binDec len q ++ markerWord m ++ d0 ++ binDec L n ++ lh).reverse
        ++ d0.reverse ++ d1pow r := by
  unfold s1PhysicalLeft
  rw [s1LeftFacing_carryPrefix L n m len q r hq]
  simp [List.reverse_append,d1pow_reverse,List.append_assoc]

/-- Source m0/zero-counter specialization: the known terminal physical
left word 11 ++ 111^L ++ 100 ++ 10 ++ 111^a. -/
theorem s1PhysicalLeft_m0_zero (L a : Nat) :
    s1PhysicalLeft L 0 0 a 0 =
      [true,true] ++ d1pow L ++
        [true,false,false] ++ [true,false] ++ d1pow a := by
  unfold s1PhysicalLeft s1LeftFacing
  rw [binDec_zero a,binDec_zero L]
  simp [markerWord,d0,lh,List.reverse_append,d1pow_reverse,List.append_assoc]

/-- Source right word 0 ++ 11100 ++ 111^(1+b). -/
theorem s1PhysicalRight_source (b : Nat) :
    s1PhysicalRight b =
      [false,true,true,true,false,false] ++ d1pow (b+1) := rfl

#print axioms binDec_even
#print axioms binDec_odd
#print axioms binDec_mulpow2
#print axioms binDec_carryPrefix
#print axioms exists_odd_factor
#print axioms binDec_length
#print axioms s0Config_left_cell
#print axioms s1Config_left_cell
#print axioms s1LeftFacing_carryPrefix
#print axioms s1Config_left_carryCells
#print axioms s0PhysicalLeft_carrySuffix
#print axioms s1PhysicalLeft_carrySuffix
#print axioms s1PhysicalLeft_m0_zero

end BB6Coverage.Agent8S1Encoder
