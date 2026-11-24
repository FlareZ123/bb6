import CarryCert

namespace BB6.Agent43CarryCert

/-- A pointwise invariant at every strictly earlier layer of the block. -/
def Good (Q L j c : Nat) : Bool := c != 2 && decide (c+L+j ≤ Q+2)

def marginCheck (Q L j : Nat) (cs ds : List Nat) : Nat → Bool
  | 0 => cs == ds
  | k+1 => cs.all (Good Q L j) && marginCheck Q L (j+1) (step Q j cs) ds k

def MarginSafe (Q L j : Nat) (cs : List Nat) (k : Nat) (ds : List Nat) : Prop :=
  states Q j cs k = ds ∧ ∀ i<k, ∀ c ∈ states Q j cs i, c ≠ 2 ∧ c+L+(j+i) ≤ Q+2

theorem margin_sound (Q L j : Nat) (cs ds : List Nat) (K : Nat)
    (h : marginCheck Q L j cs ds K = true) : MarginSafe Q L j cs K ds := by
  induction K generalizing j cs with
  | zero => simpa [marginCheck, MarginSafe, states] using h
  | succ k ih =>
      simp only [marginCheck, Bool.and_eq_true] at h
      obtain ⟨hgood, htail⟩ := h
      obtain ⟨he, hall⟩ := ih (j+1) (step Q j cs) htail
      refine ⟨he, ?_⟩
      intro i hi c hm
      cases i with
      | zero =>
          have hh := List.all_eq_true.mp hgood c hm
          simpa [Good] using hh
      | succ i =>
          have hh := hall i (by omega) c hm
          simpa only [show j+(i+1)=j+1+i by omega] using hh

theorem MarginSafe.append {Q L j a b : Nat} {cs ds es : List Nat}
    (h : MarginSafe Q L j cs a ds) (h' : MarginSafe Q L (j+a) ds b es) :
    MarginSafe Q L j cs (a+b) es := by
  obtain ⟨he, hn⟩ := h
  obtain ⟨he', hn'⟩ := h'
  refine ⟨?_, ?_⟩
  · rw [states_add, he, he']
  · intro i hi c hc
    by_cases hlt : i<a
    · exact hn i hlt c hc
    · have hi' : i=a+(i-a) := by omega
      have hm : c ∈ states Q (j+a) ds (i-a) := by
        rw [hi', states_add, he] at hc
        exact hc
      have hgood := hn' (i-a) (by omega) c hm
      have heq : j+a+(i-a)=j+i := by omega
      simpa only [heq] using hgood

theorem empty_forever (Q j k : Nat) : states Q j [] k = [] := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih => exact ih (j+1)

theorem MarginSafe.member {Q L K m c : Nat} (h : MarginSafe Q L 0 [1] K [])
    (hc : c ∈ states Q 0 [1] m) : m<K ∧ c≠2 ∧ c+L+m≤Q+2 := by
  obtain ⟨he,hall⟩ := h
  have hlt : m<K := by
    by_cases hn : m<K
    · exact hn
    · have heq : m=K+(m-K) := by omega
      rw [heq,states_add,he,empty_forever] at hc
      simp at hc
  exact ⟨hlt, by simpa using hall m hlt c hc⟩

/-- The left-margin requirement used by the critical blank-root feeder exclusion. -/
def requiredMargin (n K : Nat) := 2*(n+3*K+10)+6

theorem left_from_carry (n K b d m : Nat)
    (hd : d%2=1) (hP : n+3≤7*2^n)
    (hmass : b+d+2*m+2*n+13=14*2^n)
    (hcarry : (d-1)/2+requiredMargin n K+m≤(7*2^n-(n+3))+2) :
    n+3*K+10≤b/4 := by
  unfold requiredMargin at hcarry
  omega

#print axioms margin_sound
#print axioms MarginSafe.append
#print axioms MarginSafe.member
#print axioms left_from_carry
end BB6.Agent43CarryCert
