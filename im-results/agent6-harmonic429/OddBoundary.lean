import ReturnLadder
import Lean.Elab.Tactic.Omega

/-!
Exact seam and overflow transitions for #429's odd-counter, even-difference
sector. These complete a previously unanalysed narrow boundary between the
existing odd-odd return-to-11 theorem and the escaping first-branch branch.

The theorem concerns the source-transcribed BB429.next/run; its universal
hypotheses do not claim authentic blank-root reachability or BB(6) closure.
-/
namespace BB429OddBoundary
open BB429

theorem seam_step_one (u w:Nat) (hu:11≤u) (hw:w%4=3)
    (hseam:3*w=2*u+19):
    next (u,w)=some (u-w/2+7,2*w-4) := by
  have hp:w%2=1:=by omega
  have hlt:w<2*u:=by omega
  have hd:4≤u-w/2:=by omega
  have hw1:w≠1:=by omega
  have h1:¬w≥2*u+3:=by omega
  have h2:w≠2*u+2:=by omega
  have h3:w≠2*u+1:=by omega
  have h4:w≠2*u:=by omega
  unfold next
  simp [h1,h2,h3,h4,show w%2≠0 by omega,
    show u-w/2≠1 by omega,show u-w/2≠2 by omega,
    show (u-w/2)%2=0 by omega, hw1]

theorem seam_step_two (u w:Nat) (hu:11≤u) (hw:w%4=3)
    (hseam:3*w=2*u+19):
    next (u-w/2+7,2*w-4)=some (0,4*w+4) := by
  have heq:2*w-4=2*(u-w/2+7):=by omega
  have heq2:4*(u-w/2+7)+12=4*w+4:=by omega
  simp [next,heq,heq2]

theorem seam_two_step (u w:Nat) (hu:11≤u) (hw:w%4=3)
    (hseam:3*w=2*u+19):
    run 2 (u,w)=some (0,4*w+4) := by
  change (next (u,w)).bind next = _
  rw [seam_step_one u w hu hw hseam]
  simpa only [Option.bind_some] using seam_step_two u w hu hw hseam

theorem overflow_step_one (u w:Nat) (_hu:11≤u) (huodd:u%2=1) (hw:w%4=3)
    (hcap:w+7≤2*u) (_hover:2*u+22≤3*w):
    next (u,w)=some (u-w/2+7,2*w-4) := by
  have hp:w%2=1:=by omega
  have hw3:3≤w:=by omega
  have hlt:w<2*u:=by omega
  have hd:4≤u-w/2:=by omega
  have hw1:w≠1:=by omega
  have h1:¬w≥2*u+3:=by omega
  have h2:w≠2*u+2:=by omega
  have h3:w≠2*u+1:=by omega
  have h4:w≠2*u:=by omega
  unfold next
  simp [h1,h2,h3,h4,show w%2≠0 by omega,
    show u-w/2≠1 by omega,show u-w/2≠2 by omega,
    show (u-w/2)%2=0 by omega, hw1]

theorem overflow_step_two (u w:Nat) (hw:w%4=3)
    (hcap:w+7≤2*u) (hover:2*u+22≤3*w):
    next (u-w/2+7,2*w-4)=some (2*u-w+18,3*w-2*u-22) := by
  have hforward:2*(u-w/2+7)+3≤2*w-4:=by omega
  have hleft:2*(u-w/2+7)+3=2*u-w+18:=by omega
  have hright:(2*w-4)-(2*(u-w/2+7)+3)=3*w-2*u-22:=by omega
  have hform:2*w-4-2*(u-w/2+7)-3=3*w-2*u-22:=by
    calc
      2*w-4-2*(u-w/2+7)-3 = (2*w-4)-(2*(u-w/2+7)+3) := by omega
      _ = 3*w-2*u-22 := hright
  simp only [next,ge_iff_le,if_pos hforward,Option.some.injEq,Prod.mk.injEq]
  exact ⟨hleft,hform⟩

theorem overflow_two_step (u w:Nat) (hu:11≤u) (huodd:u%2=1) (hw:w%4=3)
    (hcap:w+7≤2*u) (hover:2*u+22≤3*w):
    run 2 (u,w)=some (2*u-w+18,3*w-2*u-22) := by
  change (next (u,w)).bind next = _
  rw [overflow_step_one u w hu huodd hw hcap hover]
  simpa only [Option.bind_some] using overflow_step_two u w hw hcap hover

/-- Under odd u and w congruent to 3 modulo 4, the three cases are exhaustive:
the usual return, an exact 2*u+19 seam, and a strictly overflowing burst. -/
theorem odd_seam_overflow_cases (u w:Nat) (hu:u%2=1) (hw:w%4=3):
    3*w≤2*u+15 ∨ 3*w=2*u+19 ∨ 2*u+22≤3*w := by
  omega

/-- Full guarded transition trichotomy. The exact seam resets to U's origin. -/
theorem odd_boundary_trichotomy (u w:Nat) (hu:11≤u) (huodd:u%2=1)
    (hw:w%4=3) (hcap:w+7≤2*u):
    (3*w≤2*u+15 ∧ run 2 (u,w)=some (11,2*u+w+9)) ∨
    (3*w=2*u+19 ∧ run 2 (u,w)=some (0,4*w+4)) ∨
    (2*u+22≤3*w ∧
      run 2 (u,w)=some (2*u-w+18,3*w-2*u-22)) := by
  rcases odd_seam_overflow_cases u w huodd hw with h | h | h
  · exact Or.inl ⟨h,
      BB429ElevenOddExtension.odd_even_two_step u w huodd hu hw h⟩
  · exact Or.inr (Or.inl ⟨h,seam_two_step u w hu hw h⟩)
  · exact Or.inr (Or.inr ⟨h,overflow_two_step u w hu huodd hw hcap h⟩)

#print axioms odd_boundary_trichotomy
#print axioms seam_two_step
#print axioms overflow_two_step

/-- Every U-ray coordinate is divisible by three, including the initial ray. -/
theorem rayU_mod_three (k:Nat): BB429Ladder.rayU k % 3=0 := by
  induction k with
  | zero => decide
  | succ k ih =>
    simp only [BB429Ladder.rayU]
    omega

/-- The exact seam is arithmetically impossible on every U-ray. -/
theorem rayU_odd_dichotomy (k w:Nat) (hk:1≤k) (hw:w%4=3):
    3*w≤2*BB429Ladder.rayU k+15 ∨
      2*BB429Ladder.rayU k+22≤3*w := by
  have huodd := BB429Ladder.rayU_odd k hk
  rcases odd_seam_overflow_cases (BB429Ladder.rayU k) w huodd hw with h | h | h
  · exact Or.inl h
  · have hz := rayU_mod_three k
    omega
  · exact Or.inr h

/-- A complete two-outcome transition theorem for the guarded odd U-rays. -/
theorem rayU_odd_boundary (k w:Nat) (hk:3≤k) (hw:w%4=3)
    (hcap:w+7≤2*BB429Ladder.rayU k):
    (3*w≤2*BB429Ladder.rayU k+15 ∧
      run 2 (BB429Ladder.rayU k,w) =
        some (11,2*BB429Ladder.rayU k+w+9)) ∨
    (2*BB429Ladder.rayU k+22≤3*w ∧
      run 2 (BB429Ladder.rayU k,w) =
        some (2*BB429Ladder.rayU k-w+18,
          3*w-2*BB429Ladder.rayU k-22)) := by
  have hlarge:11≤BB429Ladder.rayU k := by
    have hmono : ∀ j:Nat, 11≤BB429Ladder.rayU (j+3) := by
      intro j
      induction j with
      | zero => decide
      | succ j ih =>
        have hr:BB429Ladder.rayU (j+1+3)=
            2*BB429Ladder.rayU (j+3)+3 := by
          have hj:j+1+3=(j+3)+1:=by omega
          rw [hj]
          rfl
        omega
    have hj:k=(k-3)+3:=by omega
    rw [hj]
    exact hmono (k-3)
  have huodd:=BB429Ladder.rayU_odd k (by omega)
  rcases rayU_odd_dichotomy k w (by omega) hw with hg | ho
  · exact Or.inl ⟨hg,BB429ElevenOddExtension.odd_even_two_step
      (BB429Ladder.rayU k) w huodd hlarge hw hg⟩
  · exact Or.inr ⟨ho,overflow_two_step
      (BB429Ladder.rayU k) w hlarge huodd hw hcap ho⟩

#print axioms rayU_mod_three
#print axioms rayU_odd_dichotomy
#print axioms rayU_odd_boundary

end BB429OddBoundary
