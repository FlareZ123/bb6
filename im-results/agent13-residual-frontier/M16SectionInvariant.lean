import CLine

namespace BB6Agent13M16
open BB6CLine

def projectC (c : Nat) : Nat := if c < 2 then c else 2 + (c - 2) % 16
def project (s : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (s.1 % 16, s.2.1 % 16, projectC s.2.2)

def repA (a : Nat) : Nat := if a < 16 then a else a % 16 + 16
def repK (k : Nat) : Nat := if k < 16 then k else k % 16 + 16
def repC (c : Nat) : Nat := if c < 18 then c else projectC c + 16
def canonical (s : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (repA s.1, repK s.2.1, repC s.2.2)

def reps (r : Nat) : List Nat := [r, r + 16]
def repsC (r : Nat) : List Nat := if r < 2 then [r] else [r, r + 16]
def absIndex (a k c : Nat) : Nat := 288 * a + 18 * k + c
def index (s : Nat × Nat × Nat) : Nat :=
  absIndex (s.1 % 16) (s.2.1 % 16) (projectC s.2.2)

def abstractSuccessors (a k c : Nat) : List Nat :=
  (reps a).flatMap (fun aa =>
    (reps k).flatMap (fun kk =>
      (repsC c).filterMap (fun cc =>
        (nextC (aa, kk, cc)).map index)))

def reachableWords : Array Nat := #[
  0x2ad1517fbfb9ede9, 0xd5143ffffb7f7d2a,
  0x5173f9fbcbcda2a2, 0x3ffffbfffd2a2ad1,
  0xa8abdfdca2a2d415, 0x0bfffdbfbfd51538,
  0xfcf8e5e751517a8a, 0xfdffffd51538a8a9,
  0xf6f451517a0a8bff, 0xff1fdfda8a885455,
  0xb2f3d8a8ad4506ff, 0xffca8a845457fe7c,
  0x58a8ad0546ffff3f, 0xefed4547efefbb7a,
  0xfc5457a282bfffdf, 0x45452a2abf3e5979,
  0x5782a2bfffdffff9, 0x2a2ab7f7ddbd3c54,
  0x2a91415ffffbf7f5, 0xd5153f9f38bcfd2a,
  0x517ffffbfffda2a2, 0x3bfbfade9d2a2ac1,
  0xa0affffea2a2d515, 0x8bcf9d5e7ed51538,
  0xfffcffff51517a8a, 0xfd6f4fd51530a8ab,
  0xfbfb51517a8a89fd, 0xcf6f3f3a8a8c5057,
  0xbfffd8a8a94544e7, 0xa79a8a8c5453ffff,
  0xd8a8ad4546fefe37, 0x9f9d4547ffffbdfd,
  0xfc5456a2a233e7d7, 0x45472a28bfffdfff,
  0x54a2a23f7f4bd3d5, 0x282abfffdefef854,
  0x2ad15179f3fbcfc9, 0xd5143ffffbfffd2a,
  0x517fbfb9e9eda2a2, 0x3ffffb7f7d2a2ad1,
  0xa8a8f9fca2a2d415, 0x0bfffdffffd51538,
  0xdfdcf4f651517a8a, 0xfdbfbfd51538a8ab,
  0xe7e551517a0a8bff, 0xff7ffffa8a8c5457,
  0xba7b58a8ad4506ff, 0xdfda8a885455efef,
  0xd8a8ad0546ffff1f, 0xfff945457cfeb3f2,
  0xbc5457a282bfffdf, 0x45472a2ab7f7dd3d,
  0x5782a2bfffdfefed, 0x2a2abe7f19f97c54,
  0x2ad1417ffffbfffc, 0xd5153bfbfa9edd2a,
  0x515ffffbf7f5a2a2, 0x3f3f98fcbd2a2a81,
  0xa0abfffca2a25515, 0x89fdfd4f6fd51538,
  0xfffcfbfb51517a8a, 0xcd7e5ed51530a8ab,
  0xffff51517a8a8b9f, 0xfe67b7ba8a8c5057,
  0xbdfdd8a8ad4546fe, 0x2f1a8a8c5453ffff,
  0xd8a8a94544cfe73f, 0xdbdd4547ffffbfff,
  0xf85454a2a23f7f53, 0x45472a28bfffdefe,
  0x56a2a227f3cf9795, 0x282abfffdffffc54
]

def bitsetMember (i : Nat) : Bool :=
  (reachableWords[i / 64]! / 2 ^ (i % 64)) % 2 == 1

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem bitset_closed (a : Fin 16) (k : Fin 16) (c : Fin 18) :
    bitsetMember (absIndex a.val k.val c.val) = true →
    (abstractSuccessors a.val k.val c.val).all bitsetMember = true := by
  decide

theorem list_all_true_iff (xs : List Nat) (f : Nat → Bool) :
    xs.all f = true ↔ ∀ x, x ∈ xs → f x = true := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem project_next_canon (a k c : Nat) :
    (nextC (a, k, c)).map project =
      (nextC (canonical (a, k, c))).map project := by
  rcases c with _ | _ | _ | _ | c
  · rcases a with _ | _ | a
    · by_cases hk : k < 16 <;>
        simp [nextC, canonical, repA, repK, repC, project, projectC, hk] <;> omega
    · rcases k with _ | k
      · simp [nextC, canonical, repA, repK, repC, project, projectC]
      · by_cases hk : k + 1 < 16 <;>
          simp [nextC, canonical, repA, repK, repC, project, projectC, hk] <;> omega
    · by_cases ha : a + 2 < 16 <;> by_cases hk : k < 16 <;>
        simp [nextC, canonical, repA, repK, repC, project, projectC, ha, hk] <;> omega
  · by_cases ha : a < 16 <;> by_cases hk : k < 16 <;>
      simp [nextC, canonical, repA, repK, repC, project, projectC, ha, hk] <;> omega
  · simp [nextC, canonical, repA, repK, repC, project, projectC]
  · by_cases ha : a < 16 <;> by_cases hk : k < 16 <;>
      simp [nextC, canonical, repA, repK, repC, project, projectC, ha, hk] <;> omega
  · rcases a with _ | a
    · by_cases hk : k < 16 <;> by_cases hc : c + 4 < 18 <;>
        simp [nextC, canonical, repA, repK, repC, project, projectC, hk, hc] <;> omega
    · by_cases ha : a + 1 < 16 <;> by_cases hk : k < 16 <;>
        by_cases hc : c + 4 < 18 <;>
        simp [nextC, canonical, repA, repK, repC, project, projectC, ha, hk, hc] <;> omega

theorem canonical_step {a k c t : Nat}
    (h : nextC (a, k, c) = some t) :
    ∃ u, nextC (canonical (a, k, c)) = some u ∧ index u = index t := by
  have hp := project_next_canon a k c
  rw [h] at hp
  cases hn : nextC (canonical (a, k, c)) with
  | none => simp [hn] at hp
  | some u =>
      have hpu : project t = project u := by simpa [hn] using hp
      refine ⟨u, hn, ?_⟩
      cases hpu
      rfl

theorem repA_mem (a : Nat) : repA a ∈ reps (a % 16) := by
  by_cases h : a < 16
  · simp [repA, reps, h, Nat.mod_eq_of_lt h]
  · simp [repA, reps, h]

theorem repK_mem (k : Nat) : repK k ∈ reps (k % 16) := by
  by_cases h : k < 16
  · simp [repK, reps, h, Nat.mod_eq_of_lt h]
  · simp [repK, reps, h]

theorem projectC_eq_self_of_lt18 (c : Nat) (h : c < 18) :
    projectC c = c := by
  by_cases h2 : c < 2
  · simp [projectC, h2]
  · have hmod : c - 2 < 16 := by omega
    simp [projectC, h2, Nat.mod_eq_of_lt hmod]
    omega

theorem repC_mem (c : Nat) : repC c ∈ repsC (projectC c) := by
  by_cases h : c < 18
  · have hp := projectC_eq_self_of_lt18 c h
    simp [repC, repsC, h, hp]
  · have hp : 2 ≤ projectC c := by
      unfold projectC
      split_ifs <;> omega
    simp [repC, repsC, h, show ¬ projectC c < 2 by omega]

theorem canonical_edge_mem {a k c t : Nat}
    (h : nextC (a, k, c) = some t) :
    index t ∈ abstractSuccessors (a % 16) (k % 16) (projectC c) := by
  obtain ⟨u, hu, hidx⟩ := canonical_step h
  unfold abstractSuccessors
  apply List.mem_flatMap.mpr
  refine ⟨repA a, repA_mem a, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨repK k, repK_mem k, ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨repC c, repC_mem c, ?_⟩
  simp [hu, hidx]

theorem bitset_start : bitsetMember (index (5, 0, 1)) = true := by
  decide

theorem reachable_bitset {s : Nat × Nat × Nat} (h : Reach s) :
    bitsetMember (index s) = true := by
  induction h with
  | init => decide
  | @next s t hs hstep ih =>
      rcases s with ⟨a, k, c⟩
      have ha : a % 16 < 16 := Nat.mod_lt _ (by decide)
      have hk : k % 16 < 16 := Nat.mod_lt _ (by decide)
      have hc : projectC c < 18 := by
        unfold projectC
        split_ifs <;> omega
      let qa : Fin 16 := ⟨a % 16, ha⟩
      let qk : Fin 16 := ⟨k % 16, hk⟩
      let qc : Fin 18 := ⟨projectC c, hc⟩
      have hstart : bitsetMember (absIndex qa.val qk.val qc.val) = true := by
        simpa [index, qa, qk, qc, absIndex] using ih
      have hclosed := bitset_closed qa qk qc hstart
      have hedge := canonical_edge_mem hstep
      have hedge' :
          index t ∈ abstractSuccessors qa.val qk.val qc.val := by
        simpa [qa, qk, qc] using hedge
      exact (list_all_true_iff _ _).mp hclosed (index t) hedge'

theorem c0ForbiddenMasks : Array Nat := #[
  0x2222, 0x2323, 0x9c9a, 0x8a88,
  0x222a, 0x2321, 0x98b0, 0xbc98,
  0x2222, 0x2323, 0x9a90, 0x888a,
  0x2a23, 0x2323, 0xb890, 0x9cb8
]

def c0Forbidden (a k : Nat) : Bool :=
  (c0ForbiddenMasks[a % 16]! / 2 ^ (k % 16)) % 2 == 1

theorem bitset_c0_forbidden_disjoint (a : Fin 16) (k : Fin 16) :
    c0Forbidden a.val k.val = true →
    bitsetMember (absIndex a.val k.val 0) = false := by
  decide

theorem reachable_c0_allowed (a k : Nat) (h : Reach (a, k, 0)) :
    c0Forbidden (a % 16) (k % 16) = false := by
  have hr := reachable_bitset h
  cases hf : c0Forbidden (a % 16) (k % 16) with
  | false => rfl
  | true =>
      have ha : a % 16 < 16 := Nat.mod_lt _ (by decide)
      have hk : k % 16 < 16 := Nat.mod_lt _ (by decide)
      let qa : Fin 16 := ⟨a % 16, ha⟩
      let qk : Fin 16 := ⟨k % 16, hk⟩
      have hbad := bitset_c0_forbidden_disjoint qa qk (by simpa [qa, qk] using hf)
      have hgood : bitsetMember (absIndex qa.val qk.val 0) = true := by
        simpa [index, absIndex, projectC, qa, qk] using hr
      rw [hbad] at hgood
      cases hgood

#print axioms project_next_canon
#print axioms bitset_closed
#print axioms reachable_bitset
#print axioms reachable_c0_allowed

end BB6Agent13M16
