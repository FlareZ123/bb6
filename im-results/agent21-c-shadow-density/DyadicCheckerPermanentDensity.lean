import DyadicCheckerMonotone
import DyadicSourceCheckerDensity

namespace BB6.Agent21Duality
open BB6.Agent42ModularCone

/-- Persistent, uniformly dense *executable* Machine C section certificates:
    a single dyadic precision n and at most a 1/d fraction of exceptional
    parameter residues per ray suffice not only at n, but at EVERY larger
    finite checker precision c>=n. Outside the exceptional list the
    source checker returns true; for genuine section counters with its
    arithmetic height precondition, original-source reachability is excluded.
    This is not a proof that the blank orbit does not halt. -/
theorem source_checker_permanent_dense_on_even_odd_rays
    (d : Nat) (hd : 0<d) :
    ∃ n : Nat, ∀ x y a b : Nat, ∃ R : List Int,
      d*R.length≤2^n ∧
      ∀ c t : Nat, n≤c →
        (t:Int)%BB6.Agent21Dyadic.P n∉R →
        excluded c ⟨((x+2*a*t:Nat):Int),((y+(2*b+1)*t:Nat):Int)⟩=true ∧
          (Large n (y+(2*b+1)*t) →
            ¬BB6.Agent3.CReach (x+2*a*t) (y+(2*b+1)*t)) := by
  obtain ⟨n,hn⟩ := checker_dense_on_even_odd_rays d hd
  refine ⟨n,?_⟩
  intro x y a b
  obtain ⟨R,hR,hkeep⟩ := hn x y a b
  refine ⟨R,hR,?_⟩
  intro c t hnc hnot
  let p : Pair :=
    ⟨((x+2*a*t:Nat):Int),((y+(2*b+1)*t:Nat):Int)⟩
  have hbase : excluded n p=true := by
    cases he : excluded n p with
    | true => rfl
    | false =>
        exact False.elim (hnot (hkeep t he))
  have hcert : excluded c p=true :=
    excluded_monotone_le n c hnc p hbase
  refine ⟨hcert,?_⟩
  intro hl
  have hm : Matches n (x+2*a*t) (y+(2*b+1)*t) p := by
    constructor <;> simp [Cong,p]
  exact source_excluded n p hbase _ _ hl hm

#print axioms source_checker_permanent_dense_on_even_odd_rays
end BB6.Agent21Duality
