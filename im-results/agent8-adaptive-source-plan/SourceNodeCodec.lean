import Enumerate62Adapter
import SourceTableEncoding

namespace BB6.Agent8SourceNodeCodec
open BB6Coverage BB6.Agent5Enumerate62 BB6.Agent32SourceEncoding

/-- Erasing one hole is exactly filtering out its key, even in a list whose
predicate selects other elements. The no-duplicates premise is essential. -/
theorem filter_erase_eq {α : Type} [DecidableEq α] (xs : List α)
    (p : α → Bool) (a : α) (hn : xs.Nodup) :
    xs.filter (fun x => if x = a then false else p x) = (xs.filter p).erase a := by
  rw [List.erase_filter]
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    obtain ⟨hb, hxs⟩ := List.nodup_cons.mp hn
    by_cases he : b = a
    · subst b
      have hp : ∀ x ∈ xs, (if x = a then false else p x) = p x := by
        intro x hx
        have hne : x ≠ a := by
          intro h; subst x; exact hb hx
        simp [hne]
      rw [List.filter_cons]
      simp only [List.erase_cons_head]
      exact List.filter_congr hp
    · rw [List.filter_cons]
      simp only [ite_eq_right he, List.erase_cons_tail (show ¬(b == a) = true by simp [he]), List.filter_cons, ih hxs]

def canonicalHoles (tm : SourceTM) : List Slot :=
  sourceAllSlots.filter (fun s => (tm s).isNone)

theorem canonicalHoles_child (x : SourceNode) (s : Slot) (mv : Move) :
    canonicalHoles (sourceChild x s mv).tm = (canonicalHoles x.tm).erase s := by
  unfold canonicalHoles
  rw [← filter_erase_eq sourceAllSlots (fun a => (x.tm a).isNone) s sourceAllSlots_nodup]
  apply List.filter_congr
  intro a _
  by_cases he : a = s <;> simp [sourceChild, sourceUpdate, he]

theorem reachable_canonicalHoles {x : SourceNode} (h : SourceReachable x) :
    canonicalHoles x.tm = x.holes := by
  induction h with
  | root => decide
  | @child x slot mv hp hh hs hd ih =>
      rw [canonicalHoles_child, ih]
      rfl

/-- Same three fields as the actual Coq packed_node, with a character list
instead of a Coq string. The ghost hole list is reconstructed in slot order. -/
structure PackedNode where
  table : List Char
  holes : Nat
  cut : Nat
  deriving DecidableEq, Repr

def packNode (x : SourceNode) : PackedNode :=
  ⟨encodeTable x.tm,x.holes.length,x.fresh⟩

def unpackNode (p : PackedNode) : SourceNode :=
  let tm := decodeTable p.table
  ⟨tm,canonicalHoles tm,p.cut⟩

/-- Reject noncanonical strings and inconsistent counts by exact re-encoding.
A successful read checks representation, not semantic reachability. -/
def readNode (p : PackedNode) : Option SourceNode :=
  if packNode (unpackNode p) = p then some (unpackNode p) else none

theorem unpack_pack_reachable {x : SourceNode} (h : SourceReachable x) :
    unpackNode (packNode x) = x := by
  have hh := reachable_canonicalHoles h
  cases x with
  | mk tm holes fresh =>
      simp only [unpackNode,packNode,decodeTable_encode] at *
      rw [hh]

theorem read_pack_reachable {x : SourceNode} (h : SourceReachable x) :
    readNode (packNode x) = some x := by
  simp [readNode,unpack_pack_reachable h]

theorem readNode_exact {p : PackedNode} {x : SourceNode} (h : readNode p = some x) :
    packNode x = p := by
  unfold readNode at h
  split at h
  · rename_i he
    cases h
    exact he
  · contradiction

theorem packNode_injective_reachable {x y : SourceNode} (hx : SourceReachable x) (hy : SourceReachable y)
    (h : packNode x = packNode y) : x = y := by
  have he := congrArg unpackNode h
  simpa [unpack_pack_reachable hx,unpack_pack_reachable hy] using he

#print axioms reachable_canonicalHoles
#print axioms unpack_pack_reachable
#print axioms readNode_exact
#print axioms packNode_injective_reachable

end BB6.Agent8SourceNodeCodec
