import Frontier

namespace BB6.Agent32SourceEncoding
open BB6Coverage

def stateChar (q : Fin 6) : Char :=
  match q.val with
  | 0 => 'A' | 1 => 'B' | 2 => 'C' | 3 => 'D' | 4 => 'E' | _ => 'F'

def charState (c : Char) : Option (Fin 6) :=
  if c == 'A' then some 0 else if c == 'B' then some 1 else
  if c == 'C' then some 2 else if c == 'D' then some 3 else
  if c == 'E' then some 4 else if c == 'F' then some 5 else none

theorem charState_stateChar (q : Fin 6) : charState (stateChar q) = some q := by
  have h : ∀ q : Fin 6, charState (stateChar q) = some q := by decide
  exact h q

def writeChar (t : Option Move) : Char :=
  match t with | none => '-' | some m => if m.write then '1' else '0'

def dirChar (t : Option Move) : Char :=
  match t with | none => '-' | some m => if m.right then 'R' else 'L'

def nextChar (t : Option Move) : Char :=
  match t with | none => '-' | some m => stateChar m.next

def encodeTransition (t : Option Move) : List Char := [writeChar t, dirChar t, nextChar t]

def decodeTransition (cs : List Char) : Option Move :=
  match cs with
  | [w,d,q] =>
    if (w == '0' || w == '1') && (d == 'L' || d == 'R') then
      (charState q).map (fun s => ⟨w == '1', d == 'R', s⟩)
    else none
  | _ => none

theorem decodeTransition_encode (t : Option Move) : decodeTransition (encodeTransition t) = t := by
  cases t with
  | none => rfl
  | some m =>
    rcases m with ⟨w,d,q⟩
    cases w <;> cases d <;>
      simp [decodeTransition,encodeTransition,writeChar,dirChar,nextChar,charState_stateChar]

def encodeRow (tm : Machine) (q : Fin 6) : List Char :=
  encodeTransition (tm (q,false)) ++ encodeTransition (tm (q,true))

def encodeTable (tm : Machine) : List Char :=
  encodeRow tm 0 ++ ['_'] ++ encodeRow tm 1 ++ ['_'] ++ encodeRow tm 2 ++ ['_'] ++
  encodeRow tm 3 ++ ['_'] ++ encodeRow tm 4 ++ ['_'] ++ encodeRow tm 5

def decodeTable (cs : List Char) : Machine := fun s =>
  decodeTransition ((cs.drop (7*s.1.val + if s.2 then 3 else 0)).take 3)

theorem decodeTable_encode (tm : Machine) : decodeTable (encodeTable tm) = tm := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    exact (by decide : ∀ q : Fin 6, q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5) q
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;>
    first | exact decodeTransition_encode _ | (simp [decodeTable,encodeTable,encodeRow,encodeTransition]; exact decodeTransition_encode _)

theorem encodeTable_injective : Function.Injective encodeTable := by
  intro a b h
  rw [← decodeTable_encode a, ← decodeTable_encode b, h]

#print axioms decodeTable_encode
#print axioms encodeTable_injective
end BB6.Agent32SourceEncoding
