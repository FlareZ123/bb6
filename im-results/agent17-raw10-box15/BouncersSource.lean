import Bouncers
import BlockFARBridge
import Box15Source
import WeightedTNF

namespace BB6.Agent17Box15
open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent17Raw10BoxFar

def mapMove (mv : Box15.Move) : BB6BlockFAR.Move :=
  ⟨mv.write,mv.right,mv.next⟩

def mapTable (M : Box15.Table) : BB6BlockFAR.Table :=
  fun q b => (M q b).map mapMove

def mapPrim (x : Box15.Prim) : BB6BlockFAR.Prim := ⟨x.q,x.l,x.r⟩

theorem step_map (M : Box15.Table) (x : Box15.Prim) :
    (Box15.step M x).map mapPrim =
      BB6BlockFAR.primStep (mapTable M) (mapPrim x) := by
  cases h : M x.q (x.r 0) with
  | none => simp [Box15.step,BB6BlockFAR.primStep,mapTable,mapPrim,h]
  | some mv =>
    cases hd : mv.right <;>
      simp [Box15.step,BB6BlockFAR.primStep,mapTable,mapPrim,mapMove,h,hd] <;> rfl

theorem run_map (M : Box15.Table) (n : Nat) (x : Box15.Prim) :
    (Box15.run M n x).map mapPrim =
      BB6BlockFAR.run (mapTable M) n (mapPrim x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Box15.run,BB6BlockFAR.run,←step_map]
    cases h : Box15.step M x with
    | none => rfl
    | some y => exact ih y

def tab (i : Fin 9) : Box15.Table :=
  [Box15.m1,Box15.m2,Box15.m3,Box15.m4,Box15.m5,Box15.m6,
    Box15.m7,Box15.m8,Box15.m9][i.val]!

theorem local_never (i : Fin 9) : ∀ n, ∃ c, Box15.run (tab i) n Box15.init = some c := by
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact Box15.never1
  · exact Box15.never2
  · exact Box15.never3
  · exact Box15.never4
  · exact Box15.never5
  · exact Box15.never6
  · exact Box15.never7
  · exact Box15.never8
  · exact Box15.never9

def rows : List (List Nat) := [
  [8,19,11,6,17,13,11,21,4,20,0,11],
  [8,19,11,6,17,13,11,23,4,20,0,10],
  [8,20,11,6,17,13,11,21,4,20,0,11],
  [8,20,11,6,17,13,11,23,4,20,0,10],
  [8,4,11,6,17,13,11,19,24,11,3,0],
  [8,4,11,6,17,13,11,19,24,11,4,0],
  [8,10,11,6,17,13,11,19,24,10,4,0],
  [8,12,11,6,17,13,11,19,24,10,4,0],
  [8,24,11,6,17,13,11,19,24,10,4,0]]

/-- In this partial table, zero means unassigned. The soundness theorem
    therefore covers every possible completion, including the halt child. -/
def row (i : Fin 9) : PartialMachine := fun s =>
  let v := rows[i.val]![2*s.1.val+s.2.toNat]!
  if v=0 then none else some (decodeCode (Fin.ofNat 25 v))

theorem row_exact (i : Fin 9) (s : Slot) :
    BB6BlockFAR.partialTable (mapTable (tab i)) s = row i s := by
  rcases s with ⟨q,b⟩
  revert i q b
  decide

theorem row_never (i : Fin 9) (m : Machine) (hm : compatible (row i) m) :
    NeverHalts m := by
  apply BB6BlockFAR.transfer_never (mapTable (tab i)) m
  · intro s t ht
    exact hm s t ((row_exact i s).symm ▸ ht)
  · intro n
    obtain ⟨c,hc⟩ := local_never i n
    refine ⟨mapPrim c,?_⟩
    have he := run_map (tab i) n Box15.init
    rw [hc] at he
    exact he.symm

theorem row_weighted (B : Nat) (i : Fin 9) (m : Machine)
    (hm : compatible (row i) m) : WeightedBound B m :=
  weighted_never B m (row_never i m hm)

#print axioms step_map
#print axioms run_map
#print axioms row_exact
#print axioms row_never
#print axioms row_weighted
end BB6.Agent17Box15
