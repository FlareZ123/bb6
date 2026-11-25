import ZipAuditCore
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent16Packed
open BB6Coverage Agent50Zipper Agent10ZipAudit

def packWord : List Bool → Nat
  | [] => 0
  | b::bs => b.toNat + 2 * packWord bs
theorem packWord_tail (l : List Bool) : packWord l.tail = packWord l / 2 := by
  cases l with
  | nil => rfl
  | cons b bs => cases b <;> simp [packWord, Bool.toNat] <;> omega
theorem packWord_head (l : List Bool) : l.headD false = (packWord l % 2 == 1) := by
  cases l with
  | nil => rfl
  | cons b bs => cases b <;> simp [packWord, Bool.toNat]
structure P where
  q : Fin 6
  l : Nat
  r : Nat
  deriving DecidableEq, Repr
def pack (z : Z) : P := ⟨z.q,packWord z.l,packWord z.r⟩
def pmove (mv : Move) (z : P) : P :=
  if mv.right then
    ⟨mv.next,z.r % 2 + 2 * (mv.write.toNat + 2 * (z.l/2)),z.r/2⟩
  else
    ⟨mv.next,z.l/2,mv.write.toNat+2*z.r⟩
def pstep (p : PartialMachine) (z : P) : Option P :=
  ((p (z.q,z.l%2 == 1)).bind id).map (fun mv => pmove mv z)
def prun (p : PartialMachine) : Nat → P → Option P
  | 0,z => some z
  | n+1,z => (pstep p z).bind (prun p n)
theorem packWord_headNat (l : List Bool) : (l.headD false).toNat = packWord l % 2 := by
  cases l with
  | nil => rfl
  | cons b bs => cases b <;> simp [packWord,Bool.toNat]
theorem pack_move (mv : Move) (z : Z) : pack (move mv z) = pmove mv (pack z) := by
  cases hd : mv.right
  · simp [move,pmove,pack,hd,packWord,packWord_tail]
  · have h := packWord_headNat z.r
    simp only [List.headD_eq_head?_getD] at h
    simp [move,pmove,pack,hd,packWord,packWord_tail,h]
theorem pack_step (p : PartialMachine) (z : Z) : (step p z).map pack = pstep p (pack z) := by
  unfold step pstep
  rw [packWord_head z.l]
  change (((p (z.q,packWord z.l % 2 == 1)).bind id).map (fun mv => move mv z)).map pack =
    ((p (z.q,packWord z.l % 2 == 1)).bind id).map (fun mv => pmove mv (pack z))
  cases h : (p (z.q,packWord z.l % 2 == 1)).bind id with
  | none => rfl
  | some mv => exact congrArg some (pack_move mv z)
theorem pack_run (p : PartialMachine) (n : Nat) (z : Z) : (zrun p n z).map pack = prun p n (pack z) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    rw [zrun,prun,←pack_step]
    cases h : step p z with
    | none => rfl
    | some t => simpa only [h,Option.bind_some,Option.map_some] using ih t
theorem prun_add (p : PartialMachine) (n k : Nat) (z : P) :
    prun p (n+k) z = (prun p n z).bind (prun p k) := by
  induction n generalizing z with
  | zero => simp [prun]
  | succ n ih =>
    rw [show n+1+k=n+k+1 by omega]
    simp only [prun]
    cases pstep p z with
    | none => rfl
    | some t => exact ih t
theorem prun_join {p : PartialMachine} {n k : Nat} {a b c : P}
    (h : prun p n a = some b) (g : prun p k b = some c) :
    prun p (n+k) a = some c := by rw [prun_add,h]; exact g
def packedRead (p : PartialMachine) (n : Nat) : Option Slot :=
  (prun p n (pack start)).map fun z => (z.q,z.l % 2 == 1)
theorem packedRead_eq (p : PartialMachine) (n : Nat) : packedRead p n = zipRead p n := by
  rw [packedRead, ← pack_run]
  cases h : zrun p n start with
  | none => simp [zipRead,h]
  | some z => simp only [Option.map_some,zipRead,h,pack,← packWord_head]

def pushN (b : Bool) (n x : Nat) : Nat := 2^n*x + (if b then 2^n-1 else 0)
theorem pushN_zero (b : Bool) (x : Nat) : pushN b 0 x = x := by cases b <;> simp [pushN]
theorem pushN_succ (b : Bool) (n x : Nat) :
    pushN b (n+1) x = b.toNat + 2*pushN b n x := by
  have h : 0 < 2^n := Nat.pow_pos (by decide)
  cases b <;> simp [pushN,Nat.pow_succ,Bool.toNat]
  · rw [Nat.mul_comm (2^n) 2, Nat.mul_assoc]
  · rw [Nat.mul_comm (2^n) 2, Nat.mul_assoc, Nat.mul_add]
    omega
theorem pushN_succ_tail (b : Bool) (n x : Nat) :
    pushN b (n+1) x = pushN b n (b.toNat+2*x) := by
  induction n with
  | zero => rw [pushN_succ,pushN_zero,pushN_zero]
  | succ n ih => rw [pushN_succ b (n+1),pushN_succ b n (b.toNat+2*x),←ih]
theorem digit_mod (b : Bool) (x : Nat) : (b.toNat+2*x)%2 = b.toNat := by cases b <;> simp [Bool.toNat]
theorem digit_div (b : Bool) (x : Nat) : (b.toNat+2*x)/2 = x := by cases b <;> simp [Bool.toNat] <;> omega
theorem digit_read (b : Bool) (x : Nat) : ((b.toNat+2*x)%2 == 1) = b := by rw [digit_mod]; cases b <;> rfl
theorem leftSweep (p : PartialMachine) (q : Fin 6) (b w : Bool)
    (hm : p (q,b) = some (some ⟨w,false,q⟩)) (k x r : Nat) :
    prun p k ⟨q,pushN b k x,r⟩ = some ⟨q,x,pushN w k r⟩ := by
  induction k generalizing r with
  | zero => simp [prun,pushN_zero]
  | succ k ih =>
    rw [pushN_succ,prun]
    have hs : pstep p ⟨q,b.toNat+2*pushN b k x,r⟩ = some ⟨q,pushN b k x,w.toNat+2*r⟩ := by
      simp only [pstep,digit_read,hm,Option.bind_some,id_eq,Option.map_some,pmove,Bool.false_eq_true,ite_false,digit_div]
    rw [hs,Option.bind_some,ih,←pushN_succ_tail]
theorem rightSweep (p : PartialMachine) (q : Fin 6) (b w : Bool)
    (hm : p (q,b) = some (some ⟨w,true,q⟩)) (k l r : Nat) :
    prun p (k+1) ⟨q,b.toNat+2*l,pushN b k r⟩ =
      some ⟨q,r%2+2*pushN w (k+1) l,r/2⟩ := by
  induction k generalizing l with
  | zero => simp only [pushN_zero,prun,pstep,digit_read,hm,Option.bind_some,id_eq,Option.map_some,pmove,ite_true,digit_div,pushN_succ]
  | succ k ih =>
    rw [pushN_succ,prun]
    have hs : pstep p ⟨q,b.toNat+2*l,b.toNat+2*pushN b k r⟩ = some ⟨q,b.toNat+2*(w.toNat+2*l),pushN b k r⟩ := by
      have hb : (b.toNat == 1) = b := by cases b <;> rfl
      simp only [pstep,digit_read,hm,Option.bind_some,id_eq,Option.map_some,pmove,ite_true,digit_div,digit_mod,hb]
    rw [hs,Option.bind_some,ih,←pushN_succ_tail]

inductive Instr where
  | ordinary (n : Nat)
  | left (k : Nat)
  | right (k : Nat)
def Instr.cost : Instr → Nat
  | .ordinary n => n
  | .left k => k
  | .right k => k+1
def execute (p : PartialMachine) : Instr → P → Option P
  | .ordinary n,z => prun p n z
  | .left k,z =>
    let b := z.l % 2 == 1
    let x := z.l / 2^k
    match p (z.q,b) with
    | some (some mv) =>
      if mv.next = z.q ∧ mv.right = false ∧ z.l = pushN b k x then
        some ⟨z.q,x,pushN mv.write k z.r⟩
      else none
    | _ => none
  | .right k,z =>
    let b := z.l % 2 == 1
    let l := z.l / 2
    let r := z.r / 2^k
    match p (z.q,b) with
    | some (some mv) =>
      if mv.next = z.q ∧ mv.right = true ∧ z.l = b.toNat+2*l ∧ z.r = pushN b k r then
        some ⟨z.q,r%2+2*pushN mv.write (k+1) l,r/2⟩
      else none
    | _ => none
theorem execute_sound (p : PartialMachine) (i : Instr) (z t : P)
    (h : execute p i z = some t) : prun p i.cost z = some t := by
  cases i with
  | ordinary n => exact h
  | left k =>
    rcases z with ⟨q,l,r⟩
    simp only [execute] at h
    cases hp : p (q,l%2 == 1) with
    | none => simp [hp] at h
    | some opt =>
      cases opt with
      | none => simp [hp] at h
      | some mv =>
        simp only [hp] at h
        by_cases hg : mv.next = q ∧ mv.right = false ∧ l = pushN (l%2 == 1) k (l/2^k)
        · simp only [if_pos hg] at h
          simp only [Option.some.injEq] at h
          subst t
          rcases mv with ⟨w,d,s⟩
          rcases hg with ⟨hs,hd,hl⟩
          simp only at hs hd hl
          subst s; subst d
          have hh := leftSweep p q (l%2 == 1) w hp k (l/2^k) r
          rw [←hl] at hh
          exact hh
        · simp [hg] at h
  | right k =>
    rcases z with ⟨q,l,r⟩
    simp only [execute] at h
    cases hp : p (q,l%2 == 1) with
    | none => simp [hp] at h
    | some opt =>
      cases opt with
      | none => simp [hp] at h
      | some mv =>
        simp only [hp] at h
        by_cases hg : mv.next = q ∧ mv.right = true ∧ l = (l%2 == 1).toNat+2*(l/2) ∧ r = pushN (l%2 == 1) k (r/2^k)
        · simp only [if_pos hg] at h
          simp only [Option.some.injEq] at h
          subst t
          rcases mv with ⟨w,d,s⟩
          rcases hg with ⟨hs,hd,hl,hr⟩
          simp only at hs hd hl hr
          subst s; subst d
          have hh := rightSweep p q (l%2 == 1) w hp k (l/2) (r/2^k)
          rw [←hl,←hr] at hh
          exact hh
        · simp [hg] at h
def execList (p : PartialMachine) : List Instr → P → Option P
  | [],z => some z
  | i::xs,z => (execute p i z).bind (execList p xs)
def totalCost : List Instr → Nat
  | [] => 0
  | i::xs => i.cost + totalCost xs
theorem execList_sound (p : PartialMachine) (xs : List Instr) (z t : P)
    (h : execList p xs z = some t) : prun p (totalCost xs) z = some t := by
  induction xs generalizing z with
  | nil => simpa [execList,totalCost,prun] using h
  | cons i xs ih =>
    simp only [execList] at h
    cases he : execute p i z with
    | none => simp [he] at h
    | some u =>
      have hh : execList p xs u = some t := by simpa [he] using h
      exact prun_join (execute_sound p i z u he) (ih u hh)

#print axioms packedRead_eq
#print axioms execList_sound
end BB6Coverage.Agent16Packed
