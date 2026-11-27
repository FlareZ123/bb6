import MarkerCarry
import Wrap
set_option maxRecDepth 100000
set_option maxHeartbeats 500000
namespace F197.MarkerCarry
open JCarry MixedCarry

def kPQ (v : Bool) : Token := if v then .q else .p

theorem markerUniform (g : Bool) (ks : List Token) (v : Bool) (l y : Tape)
    (hl : l 0 = true) (hy : y 0 = true) (he : t y = inputs ks (src v [] l))
    (r : Tape) (hr : r 0 = true) :
    run (279 + 10*bit g + 68*ks.length + 14*(countFlags ks + bit v))
      (b (input (kPQ g) (p (p (j y)))) r) =
    some (b (j (jprefix (firstFlag ks v) (outputs ks v l))) (x (dcode g r))) := by
  have hcost := midCost_formula ks v
  have hsc : sc (kPQ g) = 36+10*bit g := by cases g <;> rfl
  have hpush : push (kPQ g) r = u (dcode g r) := by cases g <;> rfl
  have hdf : dcode g r 0 = true := by cases g <;> rfl
  have h1 : run (sc (kPQ g)) (b (input (kPQ g) (p (p (j y)))) r) =
      some (b (p (p (j y))) (u (dcode g r))) := by
    simpa only [hpush] using consume (kPQ g) (p (p (j y))) r (by rfl) hr
  have h2 := ppj y (u (dcode g r)) hy (by rfl)
  have h3 : run (midCost ks v) (b (t y) (rmark (u (dcode g r)))) =
      some (b (j (outputs ks v l)) (x (dcode (firstFlag ks v) (rmark (u (dcode g r)))))) := by
    simpa only [he] using sandwich ks v l (rmark (u (dcode g r))) hl (by rfl)
  have h4 := marker_step (firstFlag ks v) (outputs ks v l) (dcode g r) (outputs_first ks v l hl) hdf
  have heq : 279 + 10*bit g + 68*ks.length + 14*(countFlags ks + bit v) =
    sc (kPQ g) + (141 + (midCost ks v + (55+4*bit (firstFlag ks v)))) := by omega
  rw [heq]
  simp only [run_add, h1, h2, h3, h4, Option.bind_some]

#print axioms markerUniform
end F197.MarkerCarry
