import F421EpochWords

namespace BB6Coverage.Agent41F421.Compressed
open Agent31Pump
open Regular (repAdd)

structure Bits where
  first : Bool
  second : Bool
  deriving DecidableEq, Repr

def Bits.word (p : Bits) : List Bool := [p.first,p.second]
def Bits.flip (p : Bits) : Bits := ⟨p.second,p.first⟩

abbrev Runs := List (Bits × Nat)
def decode : Runs → List Bool
  | [] => []
  | (p,n)::ws => rep p.word n ++ decode ws

def push (p : Bits) : Nat → Runs → Runs
  | 0,ws => ws
  | n,[] => [(p,n)]
  | n,(q,k)::ws => if p=q then (p,k+n)::ws else (p,n)::(q,k)::ws

theorem decodePush (p : Bits) (n : Nat) (ws : Runs) :
    decode (push p n ws) = rep p.word n ++ decode ws := by
  cases n with
  | zero => rfl
  | succ n =>
    cases ws with
    | nil => simp [push,decode]
    | cons row ws =>
      obtain ⟨q,k⟩ := row
      by_cases hp : p=q
      · subst q
        simp only [push,ite_true,decode]
        rw [Nat.add_comm k (n+1), repAdd,List.append_assoc]
      · simp only [push,ite_eq_right hp,decode]

/-- Rephase a repeated two-bit word by placing its last bit at the front. -/
theorem rotate (p : Bits) (n : Nat) :
    p.second :: rep p.word n = rep p.flip.word n ++ [p.second] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change p.second :: p.first :: p.second :: rep p.word n =
      p.second :: p.first :: (rep p.flip.word n ++ [p.second])
    rw [ih]

inductive Piece where
  | bit (b : Bool)
  | run (p : Bits) (n : Nat)
  deriving Repr

def Piece.word : Piece → List Bool
  | .bit b => [b]
  | .run p n => rep p.word n

def spell (ps : List Piece) : List Bool := ps.flatMap Piece.word

/-- The open bit is at the left. Fold from the right so each insertion is
    at the head, including when an odd-length fragment changes pair phase. -/
structure Packed where
  lead : Option Bool
  runs : Runs
  deriving DecidableEq, Repr

def Packed.word (w : Packed) : List Bool := w.lead.toList ++ decode w.runs

def prependBit (b : Bool) : Packed → Packed
  | ⟨none,ws⟩ => ⟨some b,ws⟩
  | ⟨some c,ws⟩ => ⟨none,push ⟨b,c⟩ 1 ws⟩

def prependRun (p : Bits) (n : Nat) (w : Packed) : Packed :=
  match n,w with
  | 0,_ => w
  | m+1,⟨none,ws⟩ => ⟨none,push p (m+1) ws⟩
  | m+1,⟨some b,ws⟩ => ⟨some p.first,push p.flip m (push ⟨p.second,b⟩ 1 ws)⟩

theorem prependBitWord (b : Bool) (w : Packed) : (prependBit b w).word = b :: w.word := by
  rcases w with ⟨_ | c,ws⟩
  · rfl
  · simp only [prependBit,Packed.word,Option.toList,List.nil_append,decodePush]
    rfl

theorem prependRunWord (p : Bits) (n : Nat) (w : Packed) :
    (prependRun p n w).word = rep p.word n ++ w.word := by
  cases n with
  | zero => rfl
  | succ n =>
    rcases w with ⟨_ | b,ws⟩
    · simp only [prependRun,Packed.word,Option.toList,List.nil_append,decodePush]
    · simp only [prependRun,Packed.word,Option.toList,List.cons_append,List.nil_append,decodePush]
      have hr := congrArg (· ++ (b :: decode ws)) (rotate p n)
      simp only [List.append_assoc,List.cons_append,List.nil_append] at hr
      change p.first :: (rep p.flip.word n ++ p.second :: b :: decode ws) =
        p.first :: ((p.second :: rep p.word n) ++ b :: decode ws)
      simpa only [List.cons_append] using congrArg (p.first :: ·) hr.symm

def pack : List Piece → Packed
  | [] => ⟨none,[]⟩
  | .bit b::ps => prependBit b (pack ps)
  | .run p n::ps => prependRun p n (pack ps)

theorem packWord (ps : List Piece) : (pack ps).word = spell ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    cases p <;> simp only [pack,prependBitWord,prependRunWord,ih] <;> rfl

theorem eqOfPack {ps qs : List Piece} (h : pack ps = pack qs) : spell ps = spell qs := by
  rw [←packWord,←packWord,h]

#print axioms eqOfPack
end BB6Coverage.Agent41F421.Compressed
