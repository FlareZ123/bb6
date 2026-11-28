import ZipAuditCore

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent16PackedZip
open BB6Coverage BB6Coverage.Agent50Zipper BB6Coverage.Agent10ZipAudit BB6Coverage.Agent50SideCycle BB6Coverage.Agent31Pump

/-- Little-endian, zero-padded binary stack. -/
def bits : List Bool → Nat
  | [] => 0
  | b::bs => b.toNat + 2 * bits bs

theorem bits_head (xs : List Bool) : bits xs % 2 = (xs.headD false).toNat := by
  cases xs with
  | nil => rfl
  | cons b bs =>
    cases b <;> simp [bits, Nat.add_mul_mod_self_left]

theorem bits_tail (xs : List Bool) : bits xs / 2 = bits xs.tail := by
  cases xs with
  | nil => rfl
  | cons b bs =>
    cases b <;> simp [bits, Nat.add_mul_div_left]

theorem all_zero_bits (xs : List Bool) : xs.all (!·) = decide (bits xs = 0) := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    rw [List.all_cons,ih]
    cases b <;> simp [bits] <;> omega

/-- Numeric equality is precisely equality under infinite zero padding. -/
theorem padEq_bits (xs ys : List Bool) : padEq xs ys = decide (bits xs = bits ys) := by
  induction xs generalizing ys with
  | nil =>
    rw [padEq, all_zero_bits, bits]
    by_cases hz : bits ys = 0
    · simp [hz]
    · have hz' : 0 ≠ bits ys := Ne.symm hz
      simp [hz,hz']
  | cons a as ih =>
    cases ys with
    | nil =>
      rw [padEq,ih]
      cases a <;> simp [bits]
      by_cases hz : bits as = 0
      · simp [hz]
      · have hz' : 2 * bits as ≠ 0 := by omega
        simp [hz,hz']
    | cons b bs =>
      rw [padEq,ih]
      cases a <;> cases b <;> simp [bits] <;> omega

/-- A finite prefix of a stack is its low n bits. -/
theorem bits_take (xs : List Bool) (n : Nat) : bits (xs.take n) = bits xs % 2^n := by
  induction n generalizing xs with
  | zero => simp [bits,Nat.mod_one]
  | succ n ih =>
    cases xs with
    | nil => simp [bits]
    | cons a as =>
      rw [List.take_succ_cons,bits,ih,bits,Nat.pow_succ]
      have hd : 0 < 2^n := Nat.pow_pos (by decide)
      have hlt : bits as % 2^n < 2^n := Nat.mod_lt _ hd
      have hb : a.toNat < 2 := Bool.toNat_lt a
      have he : a.toNat + 2 * bits as = (a.toNat + 2 * (bits as % 2^n)) + (2^n*2) * (bits as / 2^n) := by
        rw [Nat.mul_comm (2^n) 2, Nat.mul_assoc]
        have hh := Nat.mod_add_div (bits as) (2^n)
        omega
      rw [he,Nat.add_mul_mod_self_left]
      exact (Nat.mod_eq_of_lt (by omega)).symm

structure Packed where
  q : Fin 6
  h : Int
  l : Nat
  r : Nat
  deriving DecidableEq, Repr

def pack (z : Z) : Packed := ⟨z.q,z.h,bits z.l,bits z.r⟩

def read (z : Packed) : Slot := (z.q,z.l % 2 == 1)

theorem read_pack (z : Z) : read (pack z) = (z.q,z.l.headD false) := by
  simp only [read,pack,bits_head]
  cases z.l.headD false <;> rfl

def pmove (mv : Move) (z : Packed) : Packed :=
  if mv.right then ⟨mv.next,z.h+1,z.r%2 + 2*mv.write.toNat + 4*(z.l/2),z.r/2⟩
  else ⟨mv.next,z.h-1,z.l/2,mv.write.toNat+2*z.r⟩

theorem pack_move (mv : Move) (z : Z) : pmove mv (pack z) = pack (move mv z) := by
  cases hr : mv.right <;> simp [pmove,pack,move,hr,bits,bits_head,bits_tail] <;> omega

def pstep (p : PartialMachine) (z : Packed) : Option Packed :=
  ((p (read z)).bind id).map (fun mv => pmove mv z)

theorem pack_step (p : PartialMachine) (z : Z) : pstep p (pack z) = (step p z).map pack := by
  rw [pstep,read_pack,step]
  cases h : (p (z.q,z.l.headD false)).bind id with
  | none => rfl
  | some mv => simp [pack_move]

def prun (p : PartialMachine) : Nat → Packed → Option Packed
  | 0,z => some z
  | n+1,z => (pstep p z).bind (prun p n)

theorem pack_run (p : PartialMachine) (n : Nat) (z : Z) :
    prun p n (pack z) = (zrun p n z).map pack := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    rw [prun,pack_step,zrun]
    cases hz : step p z with
    | none => rfl
    | some t => exact ih t

def pwindow (p : PartialMachine) (right : Bool) (boundary : Int) : Nat → Packed → Option Packed
  | 0,z => some z
  | n+1,z => if side right boundary z.h then (pstep p z).bind (pwindow p right boundary n) else none

theorem pack_window (p : PartialMachine) (right : Bool) (boundary : Int) (n : Nat) (z : Z) :
    pwindow p right boundary n (pack z) = (zipWindow p right boundary n z).map pack := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    rw [pwindow,zipWindow]
    change (if side right boundary z.h then (pstep p (pack z)).bind (pwindow p right boundary n) else none) = _
    by_cases hs : side right boundary z.h
    · rw [if_pos hs,if_pos hs,pack_step]
      cases hz : step p z with
      | none => rfl
      | some t => exact ih t
    · rw [if_neg hs,if_neg hs]; rfl

def ptailEq (right : Bool) (boundary : Int) (c d : Packed) : Bool :=
  decide (c.q = d.q) && decide (side right 0 (d.h-c.h)) &&
    if right then decide (c.l % 2^((c.h-boundary).toNat+1) = d.l % 2^((c.h-boundary).toNat+1)) && decide (c.r = d.r)
    else decide (c.l = d.l) && decide (c.r % 2^((boundary-c.h).toNat) = d.r % 2^((boundary-c.h).toNat))

theorem pack_tailEq (right : Bool) (boundary : Int) (c d : Z) :
    ptailEq right boundary (pack c) (pack d) = zipTailEq right boundary c d := by
  simp only [ptailEq,zipTailEq,pack,padEq_bits,bits_take]
  rfl

def pread (p : PartialMachine) (n : Nat) : Option Slot := (prun p n (pack start)).map read

theorem pread_eq (p : PartialMachine) (n : Nat) : pread p n = zipRead p n := by
  rw [pread,pack_run,zipRead]
  cases zrun p n start <;> simp [read_pack]

def pcycle (p : PartialMachine) (entry period : Nat) (right : Bool) (boundary : Int) : Bool :=
  match prun p entry (pack start) with
  | none => false
  | some c => match pwindow p right boundary period c with
    | none => false
    | some d => ptailEq right boundary c d

theorem pcycle_eq (p : PartialMachine) (entry period : Nat) (right : Bool) (boundary : Int) :
    pcycle p entry period right boundary = zipCycle p entry period right boundary := by
  rw [pcycle,pack_run,zipCycle]
  cases hz : zrun p entry start with
  | none => rfl
  | some c =>
    simp only [Option.map_some]
    rw [pack_window]
    cases zipWindow p right boundary period c <;> simp [pack_tailEq]

#print axioms pread_eq
#print axioms pcycle_eq
end BB6.Agent16PackedZip
