import Raw14042ArithmeticInvariant
namespace Raw14042ArithmeticGrowth
open Raw14042ArithmeticInvariant

theorem terminal_p_gt (b : Bank) (p n s : Nat) (hp : 24≤p) (he : p%2=0)
    (hn : n<2) (hs : s<6) : p < (terminal b p n s).p := by
  have hN : n=0 ∨ n=1 := by omega
  have hS : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hN with rfl|rfl <;> rcases hS with rfl|rfl|rfl|rfl|rfl|rfl <;>
    cases b <;> simp [terminal,d,cc,a0,b0,bs,next,carry] <;>
      (try split) <;> (try simp [cc,d,bs,carry,next]) <;> omega

theorem step_p_gt (x : Section) (hx : good x) : x.p < (step x).p := by
  rcases hx with ⟨hp,he,hs⟩
  unfold step
  by_cases hn : 2≤x.n
  · simp only [hn,drainStep]
    omega
  · simp only [hn]
    exact terminal_p_gt x.kind x.p x.n x.s hp he (by omega) hs

#print axioms terminal_p_gt
#print axioms step_p_gt
end Raw14042ArithmeticGrowth
