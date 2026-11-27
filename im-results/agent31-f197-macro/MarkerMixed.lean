import MarkerUniform
set_option maxRecDepth 100000
set_option maxHeartbeats 500000
namespace F197.MarkerCarry
open JCarry MixedCarry

theorem descentMixed (ws : List Token) (g : Bool) (ks : List Token) (v : Bool) (l y : Tape)
    (hl : l 0 = true) (hy : y 0 = true) (he : t y = inputs ks (src v [] l)) :
    run (306 + 68*(ws.length+ks.length) + 14*(countFlags ws + countFlags ks + bit g + bit v))
      (b (inputs ws (input (kPQ g) (p (p (j y))))) e) =
    some (b (a (h (firstFlag ws g) (outputs ws g (jprefix (firstFlag ks v) (outputs ks v l))))) e) := by
  have hc := wrapCost_formula ws g
  have hw := wrap ws g (input (kPQ g) (p (p (j y))))
    (jprefix (firstFlag ks v) (outputs ks v l))
    (279 + 10*bit g + 68*ks.length + 14*(countFlags ks + bit v))
    (by cases g <;> rfl) (by rfl) (markerUniform g ks v l y hl hy he) e (by rfl)
  rw [show 306 + 68*(ws.length+ks.length) + 14*(countFlags ws + countFlags ks + bit g + bit v) =
    (wrapCost ws g + (279 + 10*bit g + 68*ks.length + 14*(countFlags ks + bit v))) +
      (27+4*bit (firstFlag ws g)) by omega]
  rw [run_add, hw]
  simp only [Option.bind_some]
  exact finish _ _ (outputs_first ws g _ (by rfl))

theorem descentBase (ks : List Token) (v : Bool) (l y : Tape)
    (hl : l 0 = true) (hy : y 0 = true) (he : t y = inputs ks (src v [] l)) :
    run (238 + 68*ks.length + 14*(countFlags ks + bit v))
      (b (p (p (j y))) e) = some (b (jprefix (firstFlag ks v) (outputs ks v l)) e) := by
  have hc := midCost_formula ks v
  rw [show 238 + 68*ks.length + 14*(countFlags ks + bit v) =
    141 + midCost ks v + (50+4*bit (firstFlag ks v)) by omega]
  rw [run_add, run_add, ppj y e hy (by rfl)]
  simp only [Option.bind_some]
  rw [he, sandwich ks v l _ hl (by rfl)]
  simp only [Option.bind_some]
  exact marker_base _ _ (outputs_first ks v l hl)

#print axioms descentMixed
#print axioms descentBase
end F197.MarkerCarry
