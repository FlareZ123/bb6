import NoFirstCFeeder
namespace BB6Agent6.C

def rank (s : Nat × Nat × Nat) : Nat := s.1+2*s.2.1+s.2.2

theorem rank_mono {s t : Nat × Nat × Nat}
    (h : next s = some t) : rank s ≤ rank t := by
  rcases s with ⟨a,k,c⟩
  rcases c with _ | _ | _ | _ | d
  · rcases a with _ | _ | a
    · simp only [next, Option.some.injEq] at h
      subst t
      simp only [rank]
      omega
    · rcases k with _ | k
      · simp only [next, Option.some.injEq] at h
        subst t
        simp only [rank]
        omega
      · simp only [next, Option.some.injEq] at h
        subst t
        simp only [rank]
        omega
    · simp only [next, Option.some.injEq] at h
      subst t
      simp only [rank]
      omega
  · simp only [next, Option.some.injEq] at h
    subst t
    simp only [rank]
    omega
  · simp [next] at h
  · simp only [next, Option.some.injEq] at h
    subst t
    simp only [rank]
    omega
  · rcases a with _ | a
    · dsimp [next] at h
      by_cases hp : k % 2 = 0
      · simp only [hp, ite_true, Option.some.injEq] at h
        subst t
        simp only [rank]
        omega
      · simp only [hp, ite_false, Option.some.injEq] at h
        subst t
        simp only [rank]
        omega
    · simp only [next, Option.some.injEq] at h
      subst t
      simp only [rank]
      omega

/-- A bounded exhaustive predecessor checker, executable in Lean's kernel. -/
def boundedCheck (B : Nat) (S : List (Nat × Nat × Nat)) : Bool :=
  (List.range (B+1)).all fun a =>
    (List.range (B/2+1)).all fun k =>
      (List.range (B+1)).all fun c =>
        if rank (a,k,c) ≤ B then
          match next (a,k,c) with
          | none => true
          | some t => !S.contains t || S.contains (a,k,c)
        else true

def rankCheck (B : Nat) (S : List (Nat × Nat × Nat)) : Bool :=
  S.all (fun t => decide (rank t ≤ B))

theorem rankCheck_sound (B : Nat) (S : List (Nat × Nat × Nat))
    (hr : rankCheck B S = true) (t : Nat × Nat × Nat) (ht : t ∈ S) :
    rank t ≤ B := by
  have hh := (List.all_eq_true.mp hr) t ht
  exact decide_eq_true_iff.mp hh

/-- Finite true-valued checker certifies full unbounded predecessor closure. -/
theorem boundedCheck_backward (B : Nat) (S : List (Nat × Nat × Nat))
    (hchk : boundedCheck B S = true) (hrS : rankCheck B S = true)
    (s t : Nat × Nat × Nat) (h : next s = some t) (ht : t ∈ S) :
    s ∈ S := by
  have hR : rank s ≤ rank t := rank_mono h
  have hb : rank t ≤ B := rankCheck_sound B S hrS t ht
  rcases s with ⟨a,k,c⟩
  have hbound : a+2*k+c ≤ B := by simpa [rank] using (Nat.le_trans hR hb)
  have ha : a < B+1 := by omega
  have hk : k < B/2+1 := by omega
  have hc : c < B+1 := by omega
  have hcheck := hchk
  change (List.range (B+1)).all (fun a =>
    (List.range (B/2+1)).all (fun k =>
      (List.range (B+1)).all (fun c =>
        if rank (a,k,c) ≤ B then
          match next (a,k,c) with
          | none => true
          | some t => !S.contains t || S.contains (a,k,c)
        else true))) = true at hcheck
  have h1 := (List.all_eq_true.mp hcheck) a (List.mem_range.mpr ha)
  have h2 := (List.all_eq_true.mp h1) k (List.mem_range.mpr hk)
  have h3 := (List.all_eq_true.mp h2) c (List.mem_range.mpr hc)
  have htm : S.contains t = true := List.contains_iff_mem.mpr ht
  have htmp : (!S.contains t || S.contains (a,k,c)) = true := by
    simpa only [if_pos, h, show rank (a,k,c) ≤ B from hbound] using h3
  simp only [htm, Bool.not_true, Bool.false_or] at htmp
  exact List.contains_iff_mem.mp htmp

/-- General finite backward-closed certificate excludes every path from blank start. -/
theorem blank_excluded_by_certificate (B : Nat)
    (S : List (Nat × Nat × Nat))
    (hc : boundedCheck B S = true) (hr : rankCheck B S = true)
    (hstart : (5,0,1) ∉ S)
    (n : Nat) (t : Nat × Nat × Nat)
    (ht : t ∈ S) : run n (5,0,1) ≠ some t := by
  have avoid : ∀ m q, run m (5,0,1) = some q → q ∉ S := by
    intro m
    induction m with
    | zero =>
      intro q hq
      simp only [run,Option.some.injEq] at hq
      subst q
      exact hstart
    | succ m ih =>
      intro q hq hmem
      simp only [run] at hq
      cases hprev : run m (5,0,1) with
      | none => simp [hprev] at hq
      | some prev =>
        simp only [hprev,Option.bind_some] at hq
        exact ih prev hprev (boundedCheck_backward B S hc hr prev q hq hmem)
  intro hh
  exact avoid n t hh ht

end BB6Agent6.C
