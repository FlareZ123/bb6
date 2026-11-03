import SeededHalt
set_option maxHeartbeats 2000000
namespace BB6.Row262.Window
open BB6.Row262

/-- First-return closure implies closure under ANY A-to-A interval, with no
    halting-path assumption beyond its state-A destination. -/
private theorem first_closed_propagates (k : Nat) (P : List Bool → Bool → List Bool → Prop)
    (hfirst : FirstWindowClosed k P) :
    ∀ (n : Nat) (c : Cfg), c.st = 0 →
      P (windowLeft k c.left) c.head (trimRight c.right) →
      (run n c).st = 0 →
      P (windowLeft k (run n c).left) (run n c).head
        (trimRight (run n c).right) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro c hA hp hEnd
      by_cases hn : n = 0
      · subst n
        simpa [run] using hp
      · have hpos : 0 < n := by omega
        have hc : c = ⟨0,c.left,c.head,c.right⟩ := by
          cases c with
          | mk st ls hd rs =>
            simp only at hA ⊢
            subst st
            rfl
        by_cases hprev : ∃ m : Nat, 0 < m ∧ m < n ∧ (run m c).st = 0
        · obtain ⟨m, hmpos, hmlt, hmid⟩ := hprev
          have hpMid := ih m hmlt c hA hp hmid
          let c1 := run m c
          have hsplit : run n c = run (n-m) c1 := by
            have hnat : m+(n-m)=n := by omega
            calc
              run n c = run (m+(n-m)) c := by rw [hnat]
              _ = run (n-m) (run m c) := run_add m (n-m) c
          have hfinal : (run (n-m) c1).st = 0 := by simpa [hsplit] using hEnd
          have hpFinal := ih (n-m) (by omega) c1 hmid hpMid hfinal
          simpa [hsplit] using hpFinal
        · have hFirst : FirstAReturn c.left c.head c.right n := by
            unfold FirstAReturn
            rw [← hc]
            refine ⟨hpos,hEnd,?_⟩
            intro m hm0 hmn hmEnd
            exact hprev ⟨m,hm0,hmn,hmEnd⟩
          have hP := hfirst c.left c.head c.right n hp hFirst
          rw [← hc] at hP
          exact hP

/-- First-return closure propagates across arbitrarily many first returns. -/
theorem first_window_implies_all (k : Nat)
    (P : List Bool → Bool → List Bool → Prop)
    (hfirst : FirstWindowClosed k P) : AllWindowClosed k P := by
  intro ls h rs n hp hEnd
  exact first_closed_propagates k P hfirst n ⟨0,ls,h,rs⟩ rfl hp hEnd

/-- A literal finite nonblank halting witness refutes every ten-left-cell
    universal first-return invariant containing blank and forbidding A0/right11. -/
theorem no_safe_ten_window_first_return
    (P : List Bool → Bool → List Bool → Prop)
    (hblank : P (windowLeft 10 []) false [])
    (hfirst : FirstWindowClosed 10 P)
    (hsafe : ∀ ls rs, ¬ P ls false (true :: true :: rs)) : False := by
  exact no_safe_ten_window_all_return P hblank (first_window_implies_all 10 P hfirst) hsafe

end BB6.Row262.Window
#print axioms BB6.Row262.Window.first_window_implies_all
#print axioms BB6.Row262.Window.no_safe_ten_window_first_return
