import FastRegularRay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent29ChunkRegularRay
open BB6Coverage BB6.Agent29FastRegularRay

def checkBlock (c : Certificate) (p : PartialMachine) (q : Fin 6) (lo width : Nat) : Bool :=
  (List.range width).all fun i => (c.base.row q (lo+i)).all fun r => c.closedAt p q (lo+i) r

def blocks (c : Certificate) (p : PartialMachine) (q : Fin 6) (width count : Nat) : Bool :=
  (List.range count).all fun k => checkBlock c p q (k*width) width

theorem soundBlocks (c : Certificate) (p : PartialMachine) (width count : Nat)
    (hsize : c.base.left.trans.size ≤ width*count) (hw : 0<width)
    (hl : c.base.left.valid = true) (hr : c.base.right.valid = true)
    (hpl : c.leftPred.valid c.base.left = true) (hpr : c.rightPred.valid c.base.right = true)
    (h0 : c.base.mem 0 0 0 = true)
    (hb : (List.finRange 6).all (fun q => blocks c p q width count) = true) :
    ∀ m, compatible p m → NeverHalts m := by
  apply c.sound p
  simp only [Certificate.check,Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨hl,hr⟩,hpl⟩,hpr⟩,h0⟩,?_⟩
  apply List.all_eq_true.mpr
  intro q hq
  apply List.all_eq_true.mpr
  intro l hl
  let k := l/width
  let i := l%width
  have hk : k<count := by
    apply (Nat.div_lt_iff_lt_mul hw).mpr
    have h := List.mem_range.mp hl
    simpa only [Nat.mul_comm count width] using Nat.lt_of_lt_of_le h hsize
  have hi : i<width := Nat.mod_lt _ hw
  have he : k*width+i=l := Nat.div_add_mod' _ _
  have hq' := List.all_eq_true.mp hb q hq
  have hb' := List.all_eq_true.mp hq' k (List.mem_range.mpr hk)
  have hi' := List.all_eq_true.mp hb' i (List.mem_range.mpr hi)
  simpa only [he] using hi'
#print axioms soundBlocks
end BB6.Agent29ChunkRegularRay
