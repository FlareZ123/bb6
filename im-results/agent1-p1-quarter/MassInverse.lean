import P1FiniteInverse
namespace BB6.Agent1Quarter
open BB6.Agent47P1

/-- Exact cost of an inverseAt source: this includes either parity of the
    source right coordinate and is quantified over every inverse depth. -/
theorem inverseAt_exact_mass (b d t k c : Nat)
    (hb : 4≤b) (hb4:b%4=0) (hd:d%2=1)
    (h : inverseAt b d t = some (k,c)) :
    2*k+c+2*t+1+c%2=b+d := by
  induction t generalizing k c with
  | zero =>
    simp only [inverseAt] at h
    rw [if_pos ⟨hb,hb4⟩] at h
    obtain ⟨hk,hc⟩ := Prod.mk.inj (Option.some.inj h)
    rw [←hk,←hc]
    omega
  | succ t ih =>
    simp only [inverseAt] at h
    split at h
    · simp at h
    · next k0 c0 heq =>
      split at h
      · next hcond =>
        obtain ⟨hc3,hodd⟩ := hcond
        have prev := ih k0 c0 heq
        obtain ⟨hk,hc⟩ := Prod.mk.inj (Option.some.inj h)
        omega
      · simp at h

/-- Every positive-odd feeder of a positive-odd output loses exactly 2(t+1)
    additive counter mass across its depth-t full G inversion. -/
theorem inverseAt_odd_cost (b d t k c : Nat)
    (hb : 4≤b) (hb4:b%4=0) (hd:d%2=1)
    (h:inverseAt b d t=some (k,c)) (hc:c%2=1) :
    2*k+c+2*(t+1)=b+d := by
  have hm := inverseAt_exact_mass b d t k c hb hb4 hd h
  omega

#print axioms inverseAt_exact_mass
#print axioms inverseAt_odd_cost
end BB6.Agent1Quarter
