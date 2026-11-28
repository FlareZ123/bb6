import ValuationEdges

/-!
Kernel-preparation: the exact upper-interval injection and divisibility
in the per-K sharp four-adic valuation capacity theorem. Remaining
weighted-digit bound is in results/2026-11-28-sharp-signed-valuation-packing-agent22.md.
-/
namespace ValuationPacking

/-- For each legal signed inverse edge, retain its highest four-adic
    quotient, rather than packing every lower quotient independently. -/
def upperQuotient {K : Nat} (e : Edge K) : Nat :=
  4^(e.j-1)*e.next

theorem upperQuotient_eq {K : Nat} (e : Edge K) :
    4*upperQuotient e = e.v+K := by
  have hj : e.j=e.j-1+1 := by omega
  have hp : 4^e.j=4*4^(e.j-1) := by
    calc
      4^e.j=4^((e.j-1)+1) := by rw [← hj]
      _=4^(e.j-1)*4 := by rw [Nat.pow_succ]
      _=4*4^(e.j-1) := by omega
  calc
    4*upperQuotient e = (4*4^(e.j-1))*e.next := by
      unfold upperQuotient
      ac_rfl
    _=4^e.j*e.next := by rw [←hp]
    _=e.v+K := e.eqn

theorem upperQuotient_interval {K : Nat} (e : Edge K) :
    K < 4*upperQuotient e ∧ 3*upperQuotient e < K := by
  have hh := upperQuotient_eq e
  have hpos := e.vpos
  have hsmall := e.vsmall
  omega

theorem upperQuotient_sources_injective {K : Nat}
    (e f : Edge K) (h : upperQuotient e=upperQuotient f) :
    e.v=f.v := by
  have he := upperQuotient_eq e
  have hf := upperQuotient_eq f
  rw [h] at he
  omega

theorem upperQuotient_level_divides {K : Nat} (e : Edge K) :
    4^(e.j-1) ∣ upperQuotient e := by
  exact ⟨e.next,rfl⟩

#print axioms upperQuotient_eq
#print axioms upperQuotient_interval
#print axioms upperQuotient_sources_injective
#print axioms upperQuotient_level_divides
end ValuationPacking
