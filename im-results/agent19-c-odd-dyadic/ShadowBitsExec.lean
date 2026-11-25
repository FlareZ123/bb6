import ShadowBits

namespace BB6.Agent19ShadowBits
set_option maxHeartbeats 200000

/-- Tail-recursive, absorbing-empty implementation. No powers or word histories
    are evaluated by the search itself. -/
def advance : Nat → Nat → List Node → List Node
  | _,0,Q => Q
  | n,f+1,Q => if Q.isEmpty then [] else advance (n+1) f (Q.flatMap (child n))

theorem frontier_empty_later (m x n f : Nat) (he : frontier m x n=[]) :
    frontier m x (n+f)=[] := by
  induction f with
  | zero => simpa using he
  | succ f ih =>
    rw [Nat.add_succ,frontier,ih]
    rfl

theorem advance_correct (m x n f : Nat) :
    advance n f (frontier m x n)=frontier m x (n+f) := by
  induction f generalizing n with
  | zero => rfl
  | succ f ih =>
    simp only [advance]
    split
    · rename_i he
      have h0 : frontier m x n=[] := List.isEmpty_iff.mp he
      exact (frontier_empty_later m x n (f+1) h0).symm
    · change advance (n+1) f (frontier m x (n+1))=frontier m x (n+(f+1))
      rw [ih,show n+1+f=n+(f+1) by omega]

def check (m x n : Nat) : Bool := (advance 0 n [.c m x]).isEmpty

theorem check_iff (m x n : Nat) :
    check m x n=true ↔ frontier m x n=[] := by
  unfold check
  change (advance 0 n (frontier m x 0)).isEmpty=true ↔ _
  rw [advance_correct,Nat.zero_add,List.isEmpty_iff]

theorem check_sound (m x n : Nat) (h : check m x n=true) :
    ∀ f, ∀ a b, ¬Full m x (n+f) a b := by
  intro f a b hf
  have he := frontier_empty_later m x n f ((check_iff m x n).mp h)
  have hm := (valid_frontier m x (n+f) (.c a b)).mpr hf
  rw [he] at hm
  simp at hm

#print axioms advance_correct
#print axioms check_sound
end BB6.Agent19ShadowBits
