import Raw13Coupled6OneRAReplay
namespace BB6Coverage.Agent31Pump.Raw13Coupled6OneRAReplay
open BB6Coverage Agent31Pump Raw13Coupled6OneRAHierarchy Raw13Coupled6OneRACost Raw13Coupled6OneRABatch
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pack : List Bool → Nat
 | [] => 0
 | b::bs => bv b + 2*pack bs

def unpack : Nat → Nat → List Bool
 | 0,_ => []
 | n+1,v => (v%2==1)::unpack n (v/2)

def decode (v : Nat) : List Bool := if v=0 then [] else unpack (v.log2+1) v

theorem bv_lt (b : Bool) : bv b < 2 := by cases b <;> decide

theorem pack_bound (l : List Bool) : pack l < 2^l.length := by
  induction l with
  | nil => decide
  | cons b l ih =>
    have := bv_lt b
    simp only [pack,List.length_cons,Nat.pow_succ]
    omega

theorem pack_unpack (n v : Nat) (hv : v<2^n) : pack (unpack n v)=v := by
  induction n generalizing v with
  | zero => simp at hv; simp [unpack,pack]; omega
  | succ n ih =>
    have h : v/2 < 2^n := by rw [Nat.pow_succ] at hv; omega
    simp only [unpack,pack,ih _ h]
    have hm : v%2 < 2 := Nat.mod_lt _ (by decide)
    have he : bv (v%2==1)=v%2 := by
      by_cases h : v%2=1 <;> simp [h,bv] <;> omega
    rw [he]; omega

theorem pack_decode (v : Nat) : pack (decode v)=v := by
  unfold decode
  split
  · simp_all [pack]
  · exact pack_unpack _ _ (Nat.lt_log2_self)

theorem pack_append (l r : List Bool) : pack (l++r)=pack l+2^l.length*pack r := by
  induction l with
  | nil => simp [pack]
  | cons b l ih =>
    simp only [List.cons_append,pack,List.length_cons,Nat.pow_succ,ih]
    rw [Nat.mul_comm (2^l.length) 2,Nat.mul_assoc]
    omega

theorem pack_head (l : List Bool) : (pack l % 2 == 1)=l.headD false := by
  cases l with
  | nil => rfl
  | cons b bs => cases b <;> simp [pack,bv,Nat.add_mod]

theorem pack_tail (l : List Bool) : pack l /2=pack l.tail := by
  cases l with
  | nil => rfl
  | cons b bs => have := bv_lt b; simp only [pack,List.tail_cons]; omega

theorem pack_rep_one (n : Nat) : pack (rep one n)=2^n-1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp := Nat.two_pow_pos n
    change 1+2*pack (rep one n)=2^(n+1)-1
    rw [ih,Nat.pow_succ]; omega

theorem pack_rep_zero (n : Nat) : pack (rep zero n)=0 := by
  induction n with
  | zero => rfl
  | succ n ih => change 0+2*pack (rep zero n)=0; rw [ih]

theorem length_rep_one (n : Nat) : (rep one n).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => change (rep one n).length+1=n+1; rw [ih]

theorem length_rep_zero (n : Nat) : (rep zero n).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => change (rep zero n).length+1=n+1; rw [ih]

theorem pack_tape (l : List Bool) (i : Nat) : (pack l).testBit i = l.getD i false := by
  induction l generalizing i with
  | nil => simp [pack]
  | cons b bs ih =>
    cases i with
    | zero => rw [Nat.testBit_zero]; change (pack (b::bs)%2==1)=(b::bs).headD false; exact pack_head _
    | succ i => rw [Nat.testBit_succ,pack_tail]; exact ih i

theorem pack_eq_tape {l r : List Bool} (h : pack l=pack r) : TapeEq l r := by
  intro i; rw [←pack_tape,←pack_tape,h]

theorem tape_eq_pack {l r : List Bool} (h : TapeEq l r) : pack l=pack r := by
  apply Nat.eq_of_testBit_eq
  intro i; rw [pack_tape,pack_tape]; exact h i

structure PZ where
 q : Fin 6
 l : Nat
 r : Nat
 deriving DecidableEq, Repr

def packZ (z : Z0) : PZ := ⟨z.q,pack z.l,pack z.r⟩
def decodeZ (z : PZ) : Z0 := ⟨z.q,decode z.l,decode z.r⟩
theorem pack_decodeZ (z : PZ) : packZ (decodeZ z)=z := by cases z; simp [packZ,decodeZ,pack_decode]
theorem packZ_eq {a b : Z0} (h : packZ a=packZ b) : ZEq a b := by
  have hq := congrArg PZ.q h
  have hl := congrArg PZ.l h
  have hr := congrArg PZ.r h
  exact ⟨hq,pack_eq_tape hl,pack_eq_tape hr⟩

def moveP (mv : Move) (z : PZ) : PZ :=
 if mv.right then ⟨mv.next,z.r%2+2*(bv mv.write+2*(z.l/2)),z.r/2⟩
 else ⟨mv.next,z.l/2,bv mv.write+2*z.r⟩

theorem bv_mod (l : List Bool) : bv (l.headD false)=pack l%2 := by
  cases l with
  | nil => rfl
  | cons b bs => cases b <;> simp [pack,bv,Nat.add_mod]

theorem moveP_correct (mv : Move) (z : Z0) : moveP mv (packZ z)=packZ (move0 mv z) := by
  cases hr : mv.right with
  | false => simp [moveP,move0,hr,packZ,pack,pack_tail]
  | true => simp only [moveP,move0,hr,ite_true,packZ,pack,bv_mod,pack_tail]

def stepP (z : PZ) : Option PZ := ((p (z.q,z.l%2==1)).bind id).map (fun mv => moveP mv z)

theorem stepP_correct (z : Z0) : stepP (packZ z)=(step0 p z).map packZ := by
  unfold stepP step0
  simp only [packZ,pack_head]
  cases h : (p (z.q,z.l.headD false)).bind id with
  | none => rfl
  | some mv => exact congrArg some (moveP_correct mv z)

def runP : Nat → PZ → Option PZ
 | 0,z => some z
 | n+1,z => (stepP z).bind (runP n)

theorem runP_correct (n : Nat) (z : Z0) : runP n (packZ z)=(run0 p n z).map packZ := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    simp only [runP,run0,stepP_correct]
    cases h : step0 p z with
    | none => rfl
    | some u => exact ih u

/-- Exact assigned primitive run up to implicit-zero padding. -/
def PackedOK (z : PZ) (n : Nat) (out : PZ) : Prop := ∀ a : Z0, packZ a=z → ∃ b, run0 p n a=some b ∧ packZ b=out

theorem packed_join {z u v : PZ} {n m : Nat} (h : PackedOK z n u) (g : PackedOK u m v) : PackedOK z (n+m) v := by
  intro a ha
  obtain ⟨b,hb,he⟩ := h a ha
  obtain ⟨c,hc,hf⟩ := g b he
  exact ⟨c,join0 hb hc,hf⟩

theorem packed_raw {z out : PZ} {n : Nat} (h : runP n z=some out) : PackedOK z n out := by
  intro a ha
  rw [←ha,runP_correct] at h
  cases hr : run0 p n a with
  | none => simp [hr] at h
  | some b => exact ⟨b,rfl,Option.some.inj (by simpa [hr] using h)⟩

theorem packed_of_run {a b : Z0} {n : Nat} (h : run0 p n a=some b) : PackedOK (packZ a) n (packZ b) := by
  intro z hz
  obtain ⟨w,hw,he⟩ := run_eq n (zsymm (packZ_eq hz)) h
  exact ⟨w,hw,by have hq := he.1; have hl:=tape_eq_pack he.2.1; have hr:=tape_eq_pack he.2.2; simp [packZ,hq,hl,hr]⟩

#print axioms packed_of_run
end BB6Coverage.Agent31Pump.Raw13Coupled6OneRAReplay
