import BB429SplitSieve
import Lean.Elab.Tactic.Omega

namespace BB429Distinct
open BB429SplitSieve
set_option maxHeartbeats 30000000
set_option maxRecDepth 32768

/-- A partitioned, kernel-checked uniqueness proof for every residue in the
    673-element inverse sieve, avoiding a costly monolithic quadratic decide. -/
def agg0 : List Nat := part0
theorem agg0_good : agg0.Nodup ∧ ∀ x, x ∈ agg0 → x < 16384 := by
  constructor <;> decide

def agg1 : List Nat := agg0 ++ part1
theorem agg1_good : agg1.Nodup ∧ ∀ x, x ∈ agg1 → x < 32768 := by
  have hl := agg0_good
  have hR : part1.Nodup := by decide
  have hH : ∀ x, x ∈ part1 → 16384 ≤ x := by decide
  have hU : ∀ x, x ∈ part1 → x < 32768 := by decide
  constructor
  · apply List.nodup_append.mpr
    refine ⟨hl.1,hR,?_⟩
    intro a ha b hb
    have ha' := hl.2 a ha
    have hb' := hH b hb
    omega
  · intro x hx
    simp only [agg1, List.mem_append] at hx
    rcases hx with ha | hb
    · have := hl.2 x ha; omega
    · exact hU x hb

def agg2 : List Nat := agg1 ++ part2
theorem agg2_good : agg2.Nodup ∧ ∀ x, x ∈ agg2 → x < 49152 := by
  have hl := agg1_good
  have hR : part2.Nodup := by decide
  have hH : ∀ x, x ∈ part2 → 32768 ≤ x := by decide
  have hU : ∀ x, x ∈ part2 → x < 49152 := by decide
  constructor
  · apply List.nodup_append.mpr
    refine ⟨hl.1,hR,?_⟩
    intro a ha b hb
    have ha' := hl.2 a ha
    have hb' := hH b hb
    omega
  · intro x hx
    simp only [agg2, List.mem_append] at hx
    rcases hx with ha | hb
    · have := hl.2 x ha; omega
    · exact hU x hb

def agg3 : List Nat := agg2 ++ part3
theorem agg3_good : agg3.Nodup ∧ ∀ x, x ∈ agg3 → x < 65536 := by
  have hl := agg2_good
  have hR : part3.Nodup := by decide
  have hH : ∀ x, x ∈ part3 → 49152 ≤ x := by decide
  have hU : ∀ x, x ∈ part3 → x < 65536 := by decide
  constructor
  · apply List.nodup_append.mpr
    refine ⟨hl.1,hR,?_⟩
    intro a ha b hb
    have ha' := hl.2 a ha
    have hb' := hH b hb
    omega
  · intro x hx
    simp only [agg3, List.mem_append] at hx
    rcases hx with ha | hb
    · have := hl.2 x ha; omega
    · exact hU x hb

def agg4 : List Nat := agg3 ++ part4
theorem agg4_good : agg4.Nodup ∧ ∀ x, x ∈ agg4 → x < 81920 := by
  have hl := agg3_good
  have hR : part4.Nodup := by decide
  have hH : ∀ x, x ∈ part4 → 65536 ≤ x := by decide
  have hU : ∀ x, x ∈ part4 → x < 81920 := by decide
  constructor
  · apply List.nodup_append.mpr
    refine ⟨hl.1,hR,?_⟩
    intro a ha b hb
    have ha' := hl.2 a ha
    have hb' := hH b hb
    omega
  · intro x hx
    simp only [agg4, List.mem_append] at hx
    rcases hx with ha | hb
    · have := hl.2 x ha; omega
    · exact hU x hb

def agg5 : List Nat := agg4 ++ part5
theorem agg5_good : agg5.Nodup ∧ ∀ x, x ∈ agg5 → x < 98304 := by
  have hl := agg4_good
  have hR : part5.Nodup := by decide
  have hH : ∀ x, x ∈ part5 → 81920 ≤ x := by decide
  have hU : ∀ x, x ∈ part5 → x < 98304 := by decide
  constructor
  · apply List.nodup_append.mpr
    refine ⟨hl.1,hR,?_⟩
    intro a ha b hb
    have ha' := hl.2 a ha
    have hb' := hH b hb
    omega
  · intro x hx
    simp only [agg5, List.mem_append] at hx
    rcases hx with ha | hb
    · have := hl.2 x ha; omega
    · exact hU x hb

def agg6 : List Nat := agg5 ++ part6
theorem agg6_good : agg6.Nodup ∧ ∀ x, x ∈ agg6 → x < 114688 := by
  have hl := agg5_good
  have hR : part6.Nodup := by decide
  have hH : ∀ x, x ∈ part6 → 98304 ≤ x := by decide
  have hU : ∀ x, x ∈ part6 → x < 114688 := by decide
  constructor
  · apply List.nodup_append.mpr
    refine ⟨hl.1,hR,?_⟩
    intro a ha b hb
    have ha' := hl.2 a ha
    have hb' := hH b hb
    omega
  · intro x hx
    simp only [agg6, List.mem_append] at hx
    rcases hx with ha | hb
    · have := hl.2 x ha; omega
    · exact hU x hb

def agg7 : List Nat := agg6 ++ part7
theorem agg7_good : agg7.Nodup ∧ ∀ x, x ∈ agg7 → x < 131072 := by
  have hl := agg6_good
  have hR : part7.Nodup := by decide
  have hH : ∀ x, x ∈ part7 → 114688 ≤ x := by decide
  have hU : ∀ x, x ∈ part7 → x < 131072 := by decide
  constructor
  · apply List.nodup_append.mpr
    refine ⟨hl.1,hR,?_⟩
    intro a ha b hb
    have ha' := hl.2 a ha
    have hb' := hH b hb
    omega
  · intro x hx
    simp only [agg7, List.mem_append] at hx
    rcases hx with ha | hb
    · have := hl.2 x ha; omega
    · exact hU x hb

def agg8 : List Nat := agg7 ++ part8
theorem agg8_good : agg8.Nodup ∧ ∀ x, x ∈ agg8 → x < 147456 := by
  have hl := agg7_good
  have hR : part8.Nodup := by decide
  have hH : ∀ x, x ∈ part8 → 131072 ≤ x := by decide
  have hU : ∀ x, x ∈ part8 → x < 147456 := by decide
  constructor
  · apply List.nodup_append.mpr
    refine ⟨hl.1,hR,?_⟩
    intro a ha b hb
    have ha' := hl.2 a ha
    have hb' := hH b hb
    omega
  · intro x hx
    simp only [agg8, List.mem_append] at hx
    rcases hx with ha | hb
    · have := hl.2 x ha; omega
    · exact hU x hb

def agg9 : List Nat := agg8 ++ part9
theorem agg9_good : agg9.Nodup ∧ ∀ x, x ∈ agg9 → x < 163840 := by
  have hl := agg8_good
  have hR : part9.Nodup := by decide
  have hH : ∀ x, x ∈ part9 → 147456 ≤ x := by decide
  have hU : ∀ x, x ∈ part9 → x < 163840 := by decide
  constructor
  · apply List.nodup_append.mpr
    refine ⟨hl.1,hR,?_⟩
    intro a ha b hb
    have ha' := hl.2 a ha
    have hb' := hH b hb
    omega
  · intro x hx
    simp only [agg9, List.mem_append] at hx
    rcases hx with ha | hb
    · have := hl.2 x ha; omega
    · exact hU x hb

def agg10 : List Nat := agg9 ++ part10
theorem agg10_good : agg10.Nodup ∧ ∀ x, x ∈ agg10 → x < 180224 := by
  have hl := agg9_good
  have hR : part10.Nodup := by decide
  have hH : ∀ x, x ∈ part10 → 163840 ≤ x := by decide
  have hU : ∀ x, x ∈ part10 → x < 180224 := by decide
  constructor
  · apply List.nodup_append.mpr
    refine ⟨hl.1,hR,?_⟩
    intro a ha b hb
    have ha' := hl.2 a ha
    have hb' := hH b hb
    omega
  · intro x hx
    simp only [agg10, List.mem_append] at hx
    rcases hx with ha | hb
    · have := hl.2 x ha; omega
    · exact hU x hb

def agg11 : List Nat := agg10 ++ part11
theorem agg11_good : agg11.Nodup ∧ ∀ x, x ∈ agg11 → x < 196608 := by
  have hl := agg10_good
  have hR : part11.Nodup := by decide
  have hH : ∀ x, x ∈ part11 → 180224 ≤ x := by decide
  have hU : ∀ x, x ∈ part11 → x < 196608 := by decide
  constructor
  · apply List.nodup_append.mpr
    refine ⟨hl.1,hR,?_⟩
    intro a ha b hb
    have ha' := hl.2 a ha
    have hb' := hH b hb
    omega
  · intro x hx
    simp only [agg11, List.mem_append] at hx
    rcases hx with ha | hb
    · have := hl.2 x ha; omega
    · exact hU x hb

def agg12 : List Nat := agg11 ++ part12
theorem agg12_good : agg12.Nodup ∧ ∀ x, x ∈ agg12 → x < 212992 := by
  have hl := agg11_good
  have hR : part12.Nodup := by decide
  have hH : ∀ x, x ∈ part12 → 196608 ≤ x := by decide
  have hU : ∀ x, x ∈ part12 → x < 212992 := by decide
  constructor
  · apply List.nodup_append.mpr
    refine ⟨hl.1,hR,?_⟩
    intro a ha b hb
    have ha' := hl.2 a ha
    have hb' := hH b hb
    omega
  · intro x hx
    simp only [agg12, List.mem_append] at hx
    rcases hx with ha | hb
    · have := hl.2 x ha; omega
    · exact hU x hb

def agg13 : List Nat := agg12 ++ part13
theorem agg13_good : agg13.Nodup ∧ ∀ x, x ∈ agg13 → x < 229376 := by
  have hl := agg12_good
  have hR : part13.Nodup := by decide
  have hH : ∀ x, x ∈ part13 → 212992 ≤ x := by decide
  have hU : ∀ x, x ∈ part13 → x < 229376 := by decide
  constructor
  · apply List.nodup_append.mpr
    refine ⟨hl.1,hR,?_⟩
    intro a ha b hb
    have ha' := hl.2 a ha
    have hb' := hH b hb
    omega
  · intro x hx
    simp only [agg13, List.mem_append] at hx
    rcases hx with ha | hb
    · have := hl.2 x ha; omega
    · exact hU x hb

def agg14 : List Nat := agg13 ++ part14
theorem agg14_good : agg14.Nodup ∧ ∀ x, x ∈ agg14 → x < 245760 := by
  have hl := agg13_good
  have hR : part14.Nodup := by decide
  have hH : ∀ x, x ∈ part14 → 229376 ≤ x := by decide
  have hU : ∀ x, x ∈ part14 → x < 245760 := by decide
  constructor
  · apply List.nodup_append.mpr
    refine ⟨hl.1,hR,?_⟩
    intro a ha b hb
    have ha' := hl.2 a ha
    have hb' := hH b hb
    omega
  · intro x hx
    simp only [agg14, List.mem_append] at hx
    rcases hx with ha | hb
    · have := hl.2 x ha; omega
    · exact hU x hb

def agg15 : List Nat := agg14 ++ part15
theorem agg15_good : agg15.Nodup ∧ ∀ x, x ∈ agg15 → x < 262144 := by
  have hl := agg14_good
  have hR : part15.Nodup := by decide
  have hH : ∀ x, x ∈ part15 → 245760 ≤ x := by decide
  have hU : ∀ x, x ∈ part15 → x < 262144 := by decide
  constructor
  · apply List.nodup_append.mpr
    refine ⟨hl.1,hR,?_⟩
    intro a ha b hb
    have ha' := hl.2 a ha
    have hb' := hH b hb
    omega
  · intro x hx
    simp only [agg15, List.mem_append] at hx
    rcases hx with ha | hb
    · have := hl.2 x ha; omega
    · exact hU x hb

theorem excluded_nodup : excluded.Nodup := by
  have h := agg15_good.1
  simpa only [excluded, agg15, agg14, agg13, agg12, agg11,
    agg10, agg9, agg8, agg7, agg6, agg5, agg4, agg3, agg2, agg1, agg0,
    List.append_assoc] using h

/-- Together with BB429SplitSieve.excluded_count, precisely 673 distinct
    entire infinite true-root terminal families are certified absent. -/
theorem excluded_exact_cardinality :
    excluded.length = 673 ∧ excluded.Nodup :=
  ⟨excluded_count, excluded_nodup⟩

#print axioms excluded_exact_cardinality
end BB429Distinct
