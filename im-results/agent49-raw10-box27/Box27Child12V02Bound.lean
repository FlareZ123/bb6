import Box27Child12V02Source

namespace BB6.Agent49.Box27Child12V02
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent13.Box17

theorem source_bound (m : Machine) (hm : BB6.Agent49.Box27CanonicalFrontier.child 12 2 m) : WeightedBound 255 m := by
  rcases hm with ⟨hf,hd,hv⟩
  apply bound m
  unfold base
  change m (slot 7) = decode 2 at hv
  rw [← hv]
  exact compatible_refine _ m _ (BB6.Agent49.Box27EarlyTerminal.base_compatible 12 m hf hd)

#print axioms source_bound
end BB6.Agent49.Box27Child12V02
