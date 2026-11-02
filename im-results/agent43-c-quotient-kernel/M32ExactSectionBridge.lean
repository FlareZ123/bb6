import NormalizedGateway
import M32HighSourceBridge
import Lean.Elab.Tactic.Omega

namespace BB6.Agent43
open BB6.Agent15

/-- Agent 15 exact original-source two-counter embedding (copied unchanged
    except namespace to avoid importing unrelated M8/M16 quotient theorems). -/
/-- Every point on the exact two-counter blank section is a genuine
    reachable point of the unchanged original three-counter CLine map. -/
private theorem line_reach_of_run (n : Nat) :
    ∀ {s t : Nat × Nat × Nat},
      BB6CLine.Reach s →
      BB6.Agent8Section.run BB6CLine.nextC n (some s) = some t →
      BB6CLine.Reach t := by
  induction n with
  | zero =>
      intro s t hs hr
      have hst : s=t := by
        simpa [BB6.Agent8Section.run] using hr
      subst t
      exact hs
  | succ n ih =>
      intro s t hs hr
      change
        (BB6.Agent8Section.run BB6CLine.nextC n (some s)).bind
          BB6CLine.nextC = some t at hr
      cases hp : BB6.Agent8Section.run BB6CLine.nextC n (some s) with
      | none =>
          simp [hp] at hr
      | some u =>
          have hu : BB6CLine.Reach u := ih hs hp
          have hstep : BB6CLine.nextC u = some t := by
            simpa [hp] using hr
          exact BB6CLine.Reach.next u t hu hstep

/-- The Agent 46 exact section-return simulation transports every
    Agent 15 section-reachable pair into the original CLine reachability
    relation, preserving the full blank-origin start. -/
theorem section_reach_embeds {a k : Nat} (h : CReach a k) :
    BB6CLine.Reach (a,k,0) := by
  rcases h with ⟨n,hn⟩
  have hstart : BB6CLine.Reach (5,1,0) := by
    exact BB6CLine.Reach.next (5,0,1) (5,1,0)
      BB6CLine.Reach.init (by decide)
  have aux : ∀ n a k,
      BB6.Agent8Section.run BB6.Agent46.secNext n (some (5,1)) = some (a,k) →
      BB6CLine.Reach (a,k,0) := by
    intro n
    induction n with
    | zero =>
        intro a k hr
        simp only [BB6.Agent8Section.run, Option.some.injEq, Prod.mk.injEq] at hr
        rcases hr with ⟨ha,hk⟩
        subst a
        subst k
        exact hstart
    | succ n ih =>
        intro a k hr
        change
          (BB6.Agent8Section.run BB6.Agent46.secNext n (some (5,1))).bind
            BB6.Agent46.secNext = some (a,k) at hr
        cases hp : BB6.Agent8Section.run BB6.Agent46.secNext n (some (5,1)) with
        | none =>
            simp [hp] at hr
        | some p =>
            have hprev : BB6CLine.Reach (p.1,p.2,0) :=
              ih p.1 p.2 hp
            have hstep : BB6.Agent46.secNext p = some (a,k) := by
              simpa [hp] using hr
            have hexact := BB6.Agent46.section_exact p.1 p.2
            rw [hstep] at hexact
            have hrun :
                BB6.Agent8Section.run BB6CLine.nextC
                  (BB6.Agent46.secTime p) (some (p.1,p.2,0)) =
                  some (a,k,0) := by
              rw [BB6.Agent46.run_eq] at hexact
              simpa [BB6.Agent46.embed0] using hexact
            exact line_reach_of_run (BB6.Agent46.secTime p) hprev hrun
  exact aux n a k hn


/-- The certified M32 quotient excludes this entire first-family parameter. -/
theorem blank_no_low_m32_24 (m k : Nat)
    (hm : m%32=24)
    (heq : k+3*m+4=2^(2*m+3)) :
    ¬ CReach 1 k := by
  intro hr
  exact CCert.original_low_parameter_24_absent m k
    (by omega) hm heq (section_reach_embeds hr)

/-- Twenty-four high-family congruences excluded for m≥2, all j. -/
theorem blank_no_high_m32_pairs (j m k : Nat)
    (hm : 2≤m)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hp : (j%32,m%32) ∈ CCert.newHighPairs) :
    ¬ CReach (2*j+3) k := by
  intro hr
  exact CCert.original_high_24_pairs_all_j_unreachable j m k hm heq hp
    (section_reach_embeds hr)

#print axioms section_reach_embeds
#print axioms blank_no_low_m32_24
#print axioms blank_no_high_m32_pairs
end BB6.Agent43
