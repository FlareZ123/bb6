import PartialAudit

set_option maxHeartbeats 0

namespace BB6.Agent32Raw59PackedQuery
open BB6Coverage BB6Coverage.Agent50Zipper BB6Coverage.Agent31Pump BB6Coverage.Agent10ZipAudit
open BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot
open BB6.Agent10ZipAudit BB6.Agent47PartialAudit

/-- Length-bearing, little-endian word representation (as in Raw590LB190Packed). -/
structure W where
  len : Nat
  bits : Nat
  deriving DecidableEq, Repr

def dec : Nat → Nat → List Bool
  | 0,_ => []
  | n+1,x => (x%2 == 1)::dec n (x/2)

def W.decode (w : W) : List Bool := dec w.len w.bits
def W.head (w : W) : Bool := w.len != 0 && w.bits % 2 == 1
def W.tail (w : W) : W := ⟨w.len-1,w.bits/2⟩
def W.push (w : W) (b : Bool) : W := ⟨w.len+1,b.toNat+2*w.bits⟩

theorem W.head_decode (w : W) : w.decode.headD false = w.head := by
  cases w with
  | mk n x => cases n <;> simp [W.decode,W.head,dec]
theorem W.tail_decode (w : W) : w.decode.tail = w.tail.decode := by
  cases w with
  | mk n x => cases n <;> rfl
theorem W.push_decode (w : W) (b : Bool) : (w.push b).decode = b::w.decode := by
  cases w with
  | mk n x =>
    cases b <;> simp [W.push,W.decode,dec,Nat.add_mul_mod_self_left,Nat.add_mul_div_left _ _ (by decide : 0<2)]

structure BZ where
  q : Fin 6
  l : W
  r : W
  deriving DecidableEq, Repr

def BZ.decode (z : BZ) : Z0 := ⟨z.q,z.l.decode,z.r.decode⟩
def bstep (p : BB6Coverage.PartialMachine) (z : BZ) : Option BZ :=
  ((p (z.q,z.l.head)).bind id).map fun mv =>
    if mv.right then ⟨mv.next,(z.l.tail.push mv.write).push z.r.head,z.r.tail⟩
    else ⟨mv.next,z.l.tail,z.r.push mv.write⟩

def brun (p : BB6Coverage.PartialMachine) : Nat → BZ → Option BZ
  | 0,z => some z
  | n+1,z => (bstep p z).bind (brun p n)

theorem bstep_decode (p : BB6Coverage.PartialMachine) (z : BZ) :
    (bstep p z).map BZ.decode = step0 p z.decode := by
  unfold bstep step0
  simp only [BZ.decode,W.head_decode]
  cases h : (p (z.q,z.l.head)).bind id with
  | none => rfl
  | some mv =>
    cases hd : mv.right <;> simp [hd,BZ.decode,move0,W.push_decode,W.tail_decode,W.head_decode]
    cases z.r with
    | mk n x => cases n <;> simp [W.head,W.decode,dec]

theorem brun_decode (p : BB6Coverage.PartialMachine) (n : Nat) (z : BZ) :
    (brun p n z).map BZ.decode = run0 p n z.decode := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    simp only [brun,run0,← bstep_decode]
    cases h : bstep p z with
    | none => rfl
    | some t => exact ih t

/-- A list of independently checked finite trace segments. -/
abbrev Chunk := Nat × BZ

def chunkCost : List Chunk → Nat
  | [] => 0
  | x::xs => x.1 + chunkCost xs

def chunkCheck (p : BB6Coverage.PartialMachine) (z : BZ) : List Chunk → Bool
  | [] => true
  | x::xs => decide (brun p x.1 z = some x.2) && chunkCheck p x.2 xs

def chunkEnd (z : BZ) : List Chunk → BZ
  | [] => z
  | x::xs => chunkEnd x.2 xs

theorem chunk_sound (p : BB6Coverage.PartialMachine) (z : BZ) (xs : List Chunk)
    (h : chunkCheck p z xs = true) :
    run0 p (chunkCost xs) z.decode = some (chunkEnd z xs).decode := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
    simp only [chunkCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    have h1 := (brun_decode p x.1 z).symm
    rw [h.1] at h1
    exact join0 h1 (ih x.2 h.2)

def startB : BZ := ⟨0,⟨0,0⟩,⟨0,0⟩⟩

theorem read_of_run (p : BB6Coverage.PartialMachine) (n : Nat) (zB : BZ) (s : Slot)
    (hr : run0 p n startB.decode = some zB.decode)
    (hs : (zB.q,zB.l.head) = s) : zipRead p n = some s := by
  have h := (run_project p n start).trans hr
  unfold zipRead
  cases he : zrun p n start with
  | none => simp [he] at h
  | some z =>
    have h' : project z = zB.decode := by
      simpa only [he,Option.map_some,Option.some.injEq] using h
    have hslot : (z.q,z.l.headD false) = s := by
      change ((project z).q,(project z).l.headD false) = _
      rw [h']
      simpa only [BZ.decode,W.head_decode] using hs
    exact congrArg some hslot

theorem read_of_chunks (p : BB6Coverage.PartialMachine) (xs : List Chunk)
    (n : Nat) (s : Slot) (hc : chunkCheck p startB xs = true)
    (hn : chunkCost xs = n)
    (hs : ((chunkEnd startB xs).q,(chunkEnd startB xs).l.head) = s) :
    zipRead p n = some s := by
  have hr := chunk_sound p startB xs hc
  rw [hn] at hr
  exact read_of_run p n _ s hr hs

theorem weight_of_margin (p : BB6Coverage.PartialMachine) (s : Slot) (n B : Nat)
    (h : n + 6 ≤ B) : weightOK p s n B = true := by
  unfold weightOK possibleDelays
  rw [List.all_eq_true]
  intro d hd
  have hd' := List.mem_range.mp (List.mem_filter.mp hd).1
  apply decide_eq_true
  omega

theorem query_of_read (B : Nat) (p : BB6Coverage.PartialMachine) (n : Nat) (s : Slot)
    (hread : zipRead p n = some s) (hhole : p s = none)
    (hmargin : n + 6 ≤ B) : zipQueryOK B p n s = true := by
  simp only [zipQueryOK,hread,hhole,decide_true,weight_of_margin p s n B hmargin,Bool.and_self]

theorem last_of_query (B : Nat) (p : BB6Coverage.PartialMachine) (n : Nat) (s : Slot)
    (hq : zipQueryOK B p n s = true) (hrest : restOK p s = true) :
    partialCheck B p (.closed (.last n s)) = true := by
  simp only [partialCheck,zipCheck,hq,hrest,Bool.and_self]

#print axioms chunk_sound
#print axioms read_of_chunks
#print axioms query_of_read
#print axioms last_of_query
end BB6.Agent32Raw59PackedQuery
