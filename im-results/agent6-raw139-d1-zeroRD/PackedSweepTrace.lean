import CheckedSweepTrace
import ZipThreeHoleAudit
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6Coverage.Agent6PackedSweep
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent6SweepTrace

structure Word where
  len : Nat
  val : Nat
  deriving DecidableEq, Repr

def bit (b : Bool) : Nat := if b then 1 else 0
def empty : Word := ⟨0,0⟩
def cons (b : Bool) (x : Word) : Word := ⟨x.len+1,bit b+2*x.val⟩
def enc : List Bool → Word
  | [] => empty
  | b::l => cons b (enc l)
def head (x : Word) : Bool := x.val % 2 == 1
def tail (x : Word) : Word := ⟨x.len-1,x.val/2⟩
def cat (x y : Word) : Word := ⟨x.len+y.len,x.val+2^x.len*y.val⟩

theorem enc_len (l : List Bool) : (enc l).len = l.length := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [enc,cons,ih]

theorem head_enc (l : List Bool) : head (enc l) = l.headD false := by
  cases l with
  | nil => rfl
  | cons b l => cases b <;> simp [enc,cons,head,bit,Nat.add_mul_mod_self_left]

theorem tail_enc (l : List Bool) : tail (enc l) = enc l.tail := by
  cases l with
  | nil => rfl
  | cons b l =>
    cases h : enc l with
    | mk len val => cases b <;> simp [enc,cons,tail,bit,h] <;> omega

theorem enc_cat (l r : List Bool) : enc (l++r) = cat (enc l) (enc r) := by
  induction l with
  | nil => simp [enc,empty,cat]
  | cons b l ih =>
    simp only [List.cons_append,enc,ih,cons,cat,Nat.pow_succ]
    congr 1
    · omega
    · simp only [Nat.mul_add,Nat.mul_assoc,Nat.add_assoc]
      simp [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]

theorem enc_bound (l : List Bool) : (enc l).val < 2^(enc l).len := by
  induction l with
  | nil => decide
  | cons b l ih => cases b <;> simp only [enc,cons,bit,ite_false,ite_true,Bool.false_eq_true,Nat.pow_succ] <;> omega

theorem enc_injective {l r : List Bool} (h : enc l = enc r) : l = r := by
  induction l generalizing r with
  | nil =>
    cases r with
    | nil => rfl
    | cons b r => have hlen := congrArg Word.len h; simp [enc_len] at hlen
  | cons b l ih =>
    cases r with
    | nil => have hlen := congrArg Word.len h; simp [enc_len] at hlen
    | cons c r =>
      have hhead := congrArg head h
      have htail := congrArg tail h
      simp only [head_enc,tail_enc,List.headD_cons,List.tail_cons] at hhead htail
      rw [hhead,ih htail]

theorem rep_cat (P : List Bool) (n m : Nat) : rep P (n+m) = rep P n ++ rep P m := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp [rep,Nat.succ_add,ih,List.append_assoc]

/-- Structural fuel recursion halves the repetition count at every iteration.
    Kernel reduction uses only logarithmically many packed concatenations. -/
def repeatAux (x : Word) : Nat → Nat → Word
  | 0,_ => empty
  | f+1,n => if n=0 then empty else
      let h := repeatAux x f (n/2)
      let d := cat h h
      if n%2=0 then d else cat x d

def repeatFast (x : Word) (n : Nat) := repeatAux x n n

theorem repeatAux_enc (P : List Bool) (f n : Nat) (h : n ≤ f) :
    repeatAux (enc P) f n = enc (rep P n) := by
  induction f generalizing n with
  | zero =>
    have hn : n=0 := by omega
    subst n
    rfl
  | succ f ih =>
    by_cases hn : n=0
    · subst n; rfl
    · have hh : n/2 ≤ f := by omega
      simp only [repeatAux,hn,if_false,ih (n/2) hh,← enc_cat,← rep_cat]
      split
      next hp => rw [show n/2+n/2=n by omega]
      next hp =>
        calc
          enc (P ++ rep P (n/2+n/2)) = enc (rep P (n/2+n/2+1)) := rfl
          _ = enc (rep P n) := by rw [show n/2+n/2+1=n by omega]

theorem repeat_enc (P : List Bool) (n : Nat) : repeatFast (enc P) n = enc (rep P n) :=
  repeatAux_enc P n n (by omega)

def strip (pre x : Word) : Option Word :=
  if pre.len ≤ x.len ∧ x.val % (2^pre.len) = pre.val then
    some ⟨x.len-pre.len,x.val / (2^pre.len)⟩
  else none

theorem strip_enc (pre xs : List Bool) : strip (enc pre) (enc xs) =
    (removePrefix pre xs).map enc := by
  by_cases hl : pre.length ≤ xs.length
  · let a := xs.take pre.length
    let b := xs.drop pre.length
    have hab : a++b = xs := List.take_append_drop _ _
    have hal : a.length = pre.length := by simp [a,List.length_take,Nat.min_eq_left hl]
    have hbl : b.length = xs.length-pre.length := List.length_drop
    have henc : enc xs = cat (enc a) (enc b) := by rw [← hab,enc_cat]
    have hmod : (enc xs).val % 2^(enc pre).len = (enc a).val := by
      rw [henc]
      simp only [cat,enc_len,hal,Nat.add_mul_mod_self_left]
      apply Nat.mod_eq_of_lt
      simpa only [enc_len,hal] using enc_bound a
    have hdiv : (enc xs).val / 2^(enc pre).len = (enc b).val := by
      rw [henc]
      simp only [cat,enc_len,hal]
      rw [Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide : 0 < 2))]
      have hb : (enc a).val < 2^pre.length := by simpa only [enc_len,hal] using enc_bound a
      rw [Nat.div_eq_of_lt hb,Nat.zero_add]
    have heq : (enc a).val = (enc pre).val ↔ a = pre := by
      constructor
      · intro hv
        apply enc_injective
        cases ha : enc a with
        | mk la va =>
          cases hp : enc pre with
          | mk lp vp =>
            have H : (enc a).len = (enc pre).len := by simp [enc_len,hal]
            simp [ha,hp] at H hv
            subst lp; subst vp; rfl
      · intro h; rw [h]
    unfold strip removePrefix
    simp only [enc_len] at hmod hdiv
    simp only [hmod,hdiv,heq,enc_len,hl,true_and]
    change (if a=pre then some ⟨xs.length-pre.length,(enc b).val⟩ else none) =
      (if a=pre then some b else none).map enc
    split
    · congr 1
      cases hb : enc b with
      | mk lb vb => have hlen := enc_len b; simp [hb,hbl] at hlen; simp [hlen]
    · rfl
  · have hne : xs.take pre.length ≠ pre := by
      intro h
      have H := congrArg List.length h
      simp [List.length_take,Nat.min_eq_right (by omega : xs.length ≤ pre.length)] at H
      omega
    simp [strip,removePrefix,enc_len,hl,hne]

structure PZ where
  q : Fin 6
  l : Word
  r : Word
  deriving DecidableEq, Repr

def encZ (z : Z0) : PZ := ⟨z.q,enc z.l,enc z.r⟩
def pstep (p : PartialMachine) (z : PZ) : Option PZ :=
  ((p (z.q,head z.l)).bind id).map fun mv =>
    if mv.right then ⟨mv.next,cons (head z.r) (cons mv.write (tail z.l)),tail z.r⟩
    else ⟨mv.next,tail z.l,cons mv.write z.r⟩

theorem pstep_enc (p : PartialMachine) (z : Z0) : pstep p (encZ z) = (step0 p z).map encZ := by
  simp only [pstep,encZ,head_enc,tail_enc,step0]
  cases h : (p (z.q,z.l.headD false)).bind id with
  | none => rfl
  | some mv => cases hr : mv.right <;> simp [move0,hr,encZ,enc,head_enc,tail_enc]

def prun (p : PartialMachine) : Nat → PZ → Option PZ
  | 0,z => some z
  | n+1,z => (pstep p z).bind (prun p n)

theorem prun_enc (p : PartialMachine) (n : Nat) (z : Z0) :
    prun p n (encZ z) = (run0 p n z).map encZ := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    rw [prun,pstep_enc,run0]
    cases hs : step0 p z with
    | none => rfl
    | some t => exact ih t


def papply (p : PartialMachine) (z : PZ) : Action → Option (Nat × PZ)
  | .raw k => (prun p k z).map fun u => (k,u)
  | .left lp rp I O k n =>
    if strictRun p k ⟨z.q,lp++I,rp⟩ = some ⟨z.q,lp,rp++O⟩ then
      match strip (cat (enc lp) (repeatFast (enc I) n)) z.l, strip (enc rp) z.r with
      | some L, some R => some (k*n,⟨z.q,cat (enc lp) L,cat (enc rp) (cat (repeatFast (enc O) n) R)⟩)
      | _,_ => none
    else none
  | .right lp rp I O k n =>
    if strictRun p k ⟨z.q,lp,rp++I⟩ = some ⟨z.q,lp++O,rp⟩ then
      match strip (enc lp) z.l, strip (cat (enc rp) (repeatFast (enc I) n)) z.r with
      | some L,some R => some (k*n,⟨z.q,cat (enc lp) (cat (repeatFast (enc O) n) L),cat (enc rp) R⟩)
      | _,_ => none
    else none

theorem papply_enc (p : PartialMachine) (z : Z0) (a : Action) :
    papply p (encZ z) a = (applyAction p z a).map (fun (n,u) => (n,encZ u)) := by
  cases a with
  | raw k =>
    simp only [papply,applyAction,prun_enc]
    cases run0 p k z <;> rfl
  | left lp rp I O k n =>
    simp only [papply,applyAction,encZ,repeat_enc,← enc_cat,strip_enc]
    split
    · cases removePrefix (lp++rep I n) z.l <;> cases removePrefix rp z.r <;> simp [← enc_cat,List.append_assoc]
    · rfl
  | right lp rp I O k n =>
    simp only [papply,applyAction,encZ,repeat_enc,← enc_cat,strip_enc]
    split
    · cases removePrefix lp z.l <;> cases removePrefix (rp++rep I n) z.r <;> simp [← enc_cat,List.append_assoc]
    · rfl

def peval (p : PartialMachine) : List Action → PZ → Option (Nat × PZ)
  | [],z => some (0,z)
  | a::as,z => match papply p z a with
    | none => none
    | some (n,t) => (peval p as t).map fun (m,u) => (n+m,u)

theorem peval_enc (p : PartialMachine) (as : List Action) (z : Z0) :
    peval p as (encZ z) = (eval p as z).map (fun (n,u) => (n,encZ u)) := by
  induction as generalizing z with
  | nil => rfl
  | cons a as ih =>
    simp only [peval,eval,papply_enc]
    cases ha : applyAction p z a with
    | none => rfl
    | some v =>
      rcases v with ⟨n,t⟩
      simp only [Option.map_some,ih]
      cases eval p as t <;> rfl

def Reach (p : PartialMachine) (n : Nat) (b : PZ) : Prop :=
  ∃ z, run0 p n ⟨0,[],[]⟩ = some z ∧ encZ z = b

theorem reach0 (p : PartialMachine) : Reach p 0 ⟨0,empty,empty⟩ := ⟨_,rfl,rfl⟩

theorem reach_extend {p : PartialMachine} {n k : Nat} {a b : PZ} (as : List Action)
    (h : Reach p n a) (hh : peval p as a = some (k,b)) : Reach p (n+k) b := by
  obtain ⟨z,hz,rfl⟩ := h
  rw [peval_enc] at hh
  cases he : eval p as z with
  | none => simp [he] at hh
  | some v =>
    rcases v with ⟨m,u⟩
    simp [he] at hh
    obtain ⟨rfl,rfl⟩ := hh
    exact ⟨u,join0 hz (eval_sound p as z u m he),rfl⟩

#print axioms reach_extend
end BB6Coverage.Agent6PackedSweep

namespace BB6Coverage.Agent6PackedSweep
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper
open BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6Coverage.Agent10ZipAudit

theorem reach_read (p : PartialMachine) (n : Nat) (b : PZ) (h : Reach p n b) :
    (knownRun p n).map readSlot = some (b.q,head b.l) := by
  obtain ⟨z,hz,hb⟩ := h
  have H : (zrun p n start).map project = some z := (run_project p n start).trans hz
  rw [knownRun_zip]
  cases hq : zrun p n start with
  | none => simp [hq] at H
  | some u =>
    have hu : project u = z := Option.some.inj (by simpa only [hq,Option.map_some] using H)
    rw [← hb,← hu]
    simp [read_embed,project,encZ,head_enc]

#print axioms reach_read
end BB6Coverage.Agent6PackedSweep
