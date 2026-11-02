import GenericSection
import CPhaseRank
import Lean.Elab.Tactic.Omega

namespace BB6.Agent8TotalC
open BB6.Agent8Section
open BB6.CReachBridge

/-- Embed the two-counter return section c=0 into the exact three-counter map. -/
def embed (p : Nat × Nat) : S := (p.1,p.2,0)

theorem run_eq (n : Nat) (s : Option S) :
    run BB6CLine.nextC n s = runN n s := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (run BB6CLine.nextC n s).bind BB6CLine.nextC =
             (runN n s).bind BB6CLine.nextC
      rw [ih]

/-- Existing phase termination yields an explicit k-dependent time bound
    for an actual section-to-section return or a genuine halt. -/
theorem bounded_exit (p : Nat × Nat) :
    ∃ n : Nat, 1 ≤ n ∧ n ≤ 4*p.2+5 ∧
      ∃ y : Option (Nat × Nat),
        run BB6CLine.nextC n (some (embed p)) = y.map embed := by
  rcases p with ⟨a,k⟩
  obtain ⟨n,hnlo,hnhi,hres⟩ := BB6.CPhaseRank.c0_excursion_bound a k
  refine ⟨n,hnlo,hnhi,?_⟩
  rcases hres with hnone | ⟨a',k',hr⟩
  · refine ⟨none, ?_⟩
    simpa [run_eq,embed] using hnone
  · refine ⟨some (a',k'), ?_⟩
    simpa [run_eq,embed] using hr

noncomputable def time0 (p : Nat × Nat) : Nat :=
  Classical.choose (bounded_exit p)

noncomputable def next0 (p : Nat × Nat) : Option (Nat × Nat) :=
  Classical.choose ((Classical.choose_spec (bounded_exit p)).2.2)

theorem time0_bounds (p : Nat × Nat) :
    1 ≤ time0 p ∧ time0 p ≤ 4*p.2+5 := by
  exact ⟨(Classical.choose_spec (bounded_exit p)).1,
    (Classical.choose_spec (bounded_exit p)).2.1⟩

theorem next0_exact (p : Nat × Nat) :
    run BB6CLine.nextC (time0 p) (some (embed p)) =
      (next0 p).map embed :=
  Classical.choose_spec ((Classical.choose_spec (bounded_exit p)).2.2)

/-- The exact halting problem from any c=0 counter pair reduces to the
    total two-counter section map, with <=4*k+5 calls per section edge. -/
theorem c0_halts_iff_two_counter (p : Nat × Nat) :
    (∃ n, run BB6CLine.nextC n (some (embed p)) = none) ↔
    (∃ m, run next0 m (some p) = none) :=
  section_halts_iff_of_step BB6CLine.nextC embed time0 next0
    (fun s => (time0_bounds s).1) next0_exact p

private theorem start_step :
    BB6CLine.nextC (5,0,1) = some (5,1,0) := rfl

/-- Exact correspondence from the published initial counter state to c=0. -/
theorem blank_halts_iff_c0 :
    BB6.CReachBridge.RunHalts ↔
      ∃ n, run BB6CLine.nextC n (some (embed (5,1))) = none := by
  rw [show (∃ n, run BB6CLine.nextC n (some (embed (5,1))) = none) ↔
      (∃ n, runN n (some (5,1,0)) = none) from by
          constructor
          · rintro ⟨n,hn⟩
            exact ⟨n, by simpa [run_eq,embed] using hn⟩
          · rintro ⟨n,hn⟩
            exact ⟨n, by simpa [run_eq,embed] using hn⟩]
  constructor
  · rintro ⟨n,hn⟩
    cases n with
    | zero => simp [runN] at hn
    | succ n =>
        refine ⟨n, ?_⟩
        have ht := runN_succ_head n (some start)
        rw [ht] at hn
        have he : stepC (some start) = some (5,1,0) := by
          simp [stepC,start,start_step]
        rw [he] at hn
        cases hh : runN n (some (5,1,0)) with
        | none => rfl
        | some s => simp [hh] at hn
  · rintro ⟨n,hn⟩
    refine ⟨n+1, ?_⟩
    have ht := runN_succ_head n (some start)
    rw [ht]
    have he : stepC (some start) = some (5,1,0) := by
      simp [stepC,start,start_step]
    rw [he,hn]
    rfl

/-- Exact original blank-entry accelerated halting iff the two-counter map
    starting at (5,1) eventually produces none. -/
theorem blank_halts_iff_two_counter :
    BB6.CReachBridge.RunHalts ↔ ∃ m, run next0 m (some (5,1)) = none := by
  rw [blank_halts_iff_c0]
  exact c0_halts_iff_two_counter (5,1)

#print axioms c0_halts_iff_two_counter
#print axioms blank_halts_iff_two_counter
#print axioms time0_bounds
end BB6.Agent8TotalC
