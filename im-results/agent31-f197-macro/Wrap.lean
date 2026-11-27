import MixedCarry
set_option maxRecDepth 100000
set_option maxHeartbeats 300000
namespace F197.MixedCarry
open JCarry

def wrapCost : List Token → Bool → Nat
  | [], _ => 0
  | k::ks,v => sc k + wrapCost ks v + dc k (firstFlag ks v)

theorem wrapCost_formula (ks : List Token) (v : Bool) :
    wrapCost ks v + 4 * bit (firstFlag ks v) = 68 * ks.length + 14 * countFlags ks + 4 * bit v := by
  induction ks with
  | nil => rfl
  | cons k ks ih => cases k <;> simp [wrapCost, sc, dc, flag, firstFlag, countFlags, bit] at * <;> omega

theorem wrap (ks : List Token) (v : Bool) (l m : Tape) (n : Nat) (hl : l 0 = true) (hm : m 0 = true)
    (base : ∀ r : Tape, r 0 = true → run n (b l r) = some (b (j m) (x (dcode v r))))
    (r : Tape) (hr : r 0 = true) :
    run (wrapCost ks v + n) (b (inputs ks l) r) =
    some (b (j (outputs ks v m)) (x (dcode (firstFlag ks v) r))) := by
  induction ks generalizing r with
  | nil => simpa [wrapCost, inputs, outputs, firstFlag] using base r hr
  | cons k ks ih =>
    have hc : wrapCost (k::ks) v + n = sc k + (wrapCost ks v + n) + dc k (firstFlag ks v) := by simp [wrapCost]; omega
    rw [hc, run_add, run_add]
    change ((run (sc k) (b (input k (inputs ks l)) r)).bind (run (wrapCost ks v+n))).bind (run (dc k (firstFlag ks v))) = _
    rw [consume k _ _ (inputs_first ks l hl) hr]
    simp only [Option.bind_some]
    rw [ih (push k r) (pushed_first k r)]
    simp only [Option.bind_some]
    exact unpush k (firstFlag ks v) (outputs ks v m) r (outputs_first ks v m hm) hr

#print axioms wrap
#print axioms wrapCost_formula
end F197.MixedCarry
