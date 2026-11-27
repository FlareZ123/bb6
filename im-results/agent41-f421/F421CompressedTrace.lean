import F421CompressedReturn

namespace BB6Coverage.Agent41F421.Compressed
open Agent31Pump EpochWords F421DrainPlan

def pRun (n : Nat) : Piece := .run ⟨true,false⟩ n
def qRun (n : Nat) : Piece := .run ⟨false,true⟩ n
def zeroPair : Piece := .run ⟨false,false⟩ 1

def rowPieces (c : Row) : List Piece :=
  [pRun c.p] ++ (if c.mark then [zeroPair] else []) ++ [qRun c.q]

theorem rowPiecesWord (c : Row) : spell (rowPieces c) = GeneralDrain.rowWord c := by
  rcases c with ⟨p,q,mark⟩
  cases mark <;> simp [rowPieces,GeneralDrain.rowWord,spell,Piece.word,pRun,qRun,
    zeroPair,Regular.P,Regular.Q,Regular.Z,Bits.word,rep,List.append_assoc]

theorem rowsPiecesWord (cs : List Row) :
    spell (cs.flatMap rowPieces) = GeneralDrain.nearWord cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.flatMap_cons,spellAppend,rowPiecesWord,ih,GeneralDrain.nearWord]

structure Drain where
  a : Nat
  b : Nat
  rows : List Row
  suffix : List Piece

def Drain.before (d : Drain) : List Piece :=
  [pRun d.a,qRun d.b] ++ d.rows.reverse.flatMap rowPieces ++ d.suffix

def Drain.after (d : Drain) : List Piece :=
  let k := count 0 d.rows
  [pRun (d.a+2*k),qRun (d.b+k)] ++ (F421DrainPlan.finish 0 d.rows).reverse.flatMap rowPieces ++ d.suffix

def rowOK (h : Nat) (c : Row) : Bool :=
  decide (2 ≤ c.q ∧ (c.mark = true → 1 ≤ c.p) ∧
    (c.p ≤ 2*h+bit c → c.p%2=bit c))

def drainOK (h : Nat) : List Row → Bool
  | [] => true
  | c::cs => rowOK h c && drainOK (nextH h c) cs

theorem drainOKSound {h : Nat} {cs : List Row} (hg : drainOK h cs = true) : F421DrainPlan.good h cs := by
  induction cs generalizing h with
  | nil => trivial
  | cons c cs ih =>
    rw [drainOK,Bool.and_eq_true] at hg
    refine ⟨?_, ih hg.2⟩
    unfold goodRow
    exact of_decide_eq_true hg.1

theorem Drain.sound (d : Drain) (hb : 2 ≤ d.b) (hg : drainOK 0 d.rows = true) :
    reaches (count 0 d.rows) (spell d.before) (spell d.after) := by
  have h := GeneralDrain.generalDrain d.rows d.a d.b (spell d.suffix) hb (drainOKSound hg)
  unfold Drain.before Drain.after
  simp only [spellAppend,rowsPiecesWord]
  have pairWord (a b : Nat) : spell [pRun a,qRun b] = rep Regular.P a ++ rep Regular.Q b := by
    simp [spell,Piece.word,pRun,qRun,Regular.P,Regular.Q,Bits.word]
  simpa only [reaches,pairWord,GeneralDrain.farWord,List.append_assoc] using h

inductive Edge where
  | single (w : Return)
  | drain (d : Drain)

def Edge.before : Edge → List Piece
  | .single w => w.before
  | .drain d => d.before

def Edge.after : Edge → List Piece
  | .single w => w.after
  | .drain d => d.after

def Edge.bound : Edge → Nat
  | .single w => w.cost
  | .drain d => count 0 d.rows

def Edge.ok : Edge → Bool
  | .single w => decide (pack w.leftStream = pack w.rightStream)
  | .drain d => decide (2 ≤ d.b) && drainOK 0 d.rows

theorem Edge.sound (e : Edge) (he : e.ok = true) :
    reaches e.bound (spell e.before) (spell e.after) := by
  cases e with
  | single w => exact ⟨w.cost, Nat.le_refl _, w.sound (of_decide_eq_true he)⟩
  | drain d =>
    change (_ && _) = true at he
    rw [Bool.and_eq_true] at he
    exact d.sound (of_decide_eq_true he.1) he.2

/-- Check word and local preconditions before accepting each edge. The total
    is a primitive-step lower bound because the drain lemma is existential. -/
def trace (u : Packed) (k : Nat) : List Edge → Option (Packed × Nat)
  | [] => some (u,k)
  | e::es => if (u == pack e.before) && e.ok then trace (pack e.after) (k+e.bound) es else none

theorem traceSound {u v : Packed} {k l : Nat} {es : List Edge}
    (h : trace u k es = some (v,l)) : reaches (l-k) u.word v.word := by
  induction es generalizing u k with
  | nil =>
    simp only [trace,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    exact ⟨0, by omega, rfl⟩
  | cons e es ih =>
    simp only [trace] at h
    split at h
    · rename_i ht
      rw [Bool.and_eq_true,beq_iff_eq] at ht
      have hfirst := e.sound ht.2
      have hrest := ih h
      rw [packWord] at hrest
      rw [ht.1,packWord]
      exact reachesWeak (by omega) (reachesTrans hfirst hrest)
    · contradiction

#print axioms traceSound
end BB6Coverage.Agent41F421.Compressed
