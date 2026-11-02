import RankC

namespace BB6Rank

 def runForward {α : Type} (f : α → Option α) : Nat → α → Option α
  | 0, s => some s
  | n + 1, s => (f s).bind (runForward f n)

theorem nextC_sweep (q a k c : Nat) (ha : q ≤ a) (hc : q + 3 ≤ c) :
    runForward nextC q (a, k, c) = some (a - q, k + q, c - q) := by
  induction q generalizing a k c with
  | zero => simp [runForward]
  | succ q ih =>
      have ha1 : 1 ≤ a := by omega
      have hc4 : 4 ≤ c := by omega
      obtain ⟨a', rfl⟩ : ∃ a' : Nat, a = a' + 1 := ⟨a - 1, by omega⟩
      obtain ⟨d, rfl⟩ : ∃ d : Nat, c = d + 4 := ⟨c - 4, by omega⟩
      have hstep : nextC (a' + 1, k, d + 4) = some (a', k + 1, d + 3) := rfl
      simp only [runForward, hstep, Option.bind_some]
      have hs : q ≤ a' := by omega
      have ht : q + 3 ≤ d + 3 := by omega
      rw [ih a' (k + 1) (d + 3) hs ht]
      simp only [Option.some.injEq, Prod.mk.injEq]
      omega

end BB6Rank
