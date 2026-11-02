import PosEvenForm
namespace BB6.P1Rank
open BB6.Agent1

/-- Exact 40-step blank-entry certificate. The full affine line d=b+13
    is NOT disjoint from Reach, even though the sparse critical subfamily
    from Agent45 may still be disjoint. -/
theorem reach_line0_32_45 : Reach 32 45 := by
  have h0 : Reach 2 1 := Reach.init
  have h1 : Reach 4 0 := Reach.next 2 1 4 0 h0 (by simp [T,G])
  have h2 : Reach 2 5 := Reach.next 4 0 2 5 h1 (by simp [T,G])
  have h3 : Reach 5 3 := Reach.next 2 5 5 3 h2 (by simp [T,G])
  have h4 : Reach 8 1 := Reach.next 5 3 8 1 h3 (by simp [T,G])
  have h5 : Reach 10 0 := Reach.next 8 1 10 0 h4 (by simp [T,G])
  have h6 : Reach 2 11 := Reach.next 10 0 2 11 h5 (by simp [T,G])
  have h7 : Reach 5 9 := Reach.next 2 11 5 9 h6 (by simp [T,G])
  have h8 : Reach 0 17 := Reach.next 5 9 0 17 h7 (by simp [T,G])
  have h9 : Reach 3 15 := Reach.next 0 17 3 15 h8 (by simp [T,G])
  have h10 : Reach 12 7 := Reach.next 3 15 12 7 h9 (by simp [T,G])
  have h11 : Reach 15 5 := Reach.next 12 7 15 5 h10 (by simp [T,G])
  have h12 : Reach 8 17 := Reach.next 15 5 8 17 h11 (by simp [T,G])
  have h13 : Reach 11 15 := Reach.next 8 17 11 15 h12 (by simp [T,G])
  have h14 : Reach 0 29 := Reach.next 11 15 0 29 h13 (by simp [T,G])
  have h15 : Reach 3 27 := Reach.next 0 29 3 27 h14 (by simp [T,G])
  have h16 : Reach 12 19 := Reach.next 3 27 12 19 h15 (by simp [T,G])
  have h17 : Reach 15 17 := Reach.next 12 19 15 17 h16 (by simp [T,G])
  have h18 : Reach 4 31 := Reach.next 15 17 4 31 h17 (by simp [T,G])
  have h19 : Reach 7 29 := Reach.next 4 31 7 29 h18 (by simp [T,G])
  have h20 : Reach 20 17 := Reach.next 7 29 20 17 h19 (by simp [T,G])
  have h21 : Reach 23 15 := Reach.next 20 17 23 15 h20 (by simp [T,G])
  have h22 : Reach 24 17 := Reach.next 23 15 24 17 h21 (by simp [T,G])
  have h23 : Reach 27 15 := Reach.next 24 17 27 15 h22 (by simp [T,G])
  have h24 : Reach 32 13 := Reach.next 27 15 32 13 h23 (by simp [T,G])
  have h25 : Reach 35 11 := Reach.next 32 13 35 11 h24 (by simp [T,G])
  have h26 : Reach 12 39 := Reach.next 35 11 12 39 h25 (by simp [T,G])
  have h27 : Reach 15 37 := Reach.next 12 39 15 37 h26 (by simp [T,G])
  have h28 : Reach 36 17 := Reach.next 15 37 36 17 h27 (by simp [T,G])
  have h29 : Reach 39 15 := Reach.next 36 17 39 15 h28 (by simp [T,G])
  have h30 : Reach 56 1 := Reach.next 39 15 56 1 h29 (by simp [T,G])
  have h31 : Reach 58 0 := Reach.next 56 1 58 0 h30 (by simp [T,G])
  have h32 : Reach 2 59 := Reach.next 58 0 2 59 h31 (by simp [T,G])
  have h33 : Reach 5 57 := Reach.next 2 59 5 57 h32 (by simp [T,G])
  have h34 : Reach 16 47 := Reach.next 5 57 16 47 h33 (by simp [T,G])
  have h35 : Reach 19 45 := Reach.next 16 47 19 45 h34 (by simp [T,G])
  have h36 : Reach 44 21 := Reach.next 19 45 44 21 h35 (by simp [T,G])
  have h37 : Reach 47 19 := Reach.next 44 21 47 19 h36 (by simp [T,G])
  have h38 : Reach 64 5 := Reach.next 47 19 64 5 h37 (by simp [T,G])
  have h39 : Reach 67 3 := Reach.next 64 5 67 3 h38 (by simp [T,G])
  have h40 : Reach 32 45 := Reach.next 67 3 32 45 h39 (by simp [T,G])
  exact h40

theorem line0_universal_exclusion_is_false :
    ¬(∀ u : Nat, 1≤u → ¬Reach (4*u-4) (4*u+9)) := by
  intro h
  exact h 9 (by decide) (by simpa using reach_line0_32_45)

#print axioms BB6.P1Rank.line0_universal_exclusion_is_false
end BB6.P1Rank
