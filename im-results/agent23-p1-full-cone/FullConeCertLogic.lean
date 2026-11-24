import FullConeCertCore
namespace BB6.Agent23FullCone

theorem states_add (Q j : Nat) (cs : List Nat) (a b : Nat) :
    states Q j cs (a+b) = states Q (j+a) (states Q j cs a) b := by
  induction a generalizing j cs with
  | zero => simp [states]
  | succ a ih =>
      rw [Nat.succ_add, states, ih, states]
      congr 1
      omega

theorem states_empty (Q j k : Nat) : states Q j [] k = [] := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih => simpa [states, step] using ih (j+1)

theorem cert_member (P n Q K m v : Nat)
    (hcert : cert P n Q 0 [1] K = true)
    (hv : v ∈ states Q 0 [1] m) :
    m<K ∧ v≠2 ∧ v+2*m+2*n+3<7*P := by
  obtain ⟨he, hs⟩ := cert_sound P n Q 0 [1] K hcert
  have hm : m<K := by
    by_cases h : m<K
    · exact h
    · exfalso
      have hsum : m=K+(m-K) := by omega
      rw [hsum, states_add, he, states_empty] at hv
      simp at hv
  exact ⟨hm, by simpa using hs m hm v hv⟩

/-- Explicit interface to the already proved source facts. Each field must
    be instantiated from the actual source, not from an assumed axiom. -/
structure ConeFacts (n : Nat) (C : Nat → Nat → Nat → Prop)
    (R : Nat → Nat → Prop) (I : Nat → Nat → Nat → Nat → Nat → Prop) : Prop where
  mass : ∀ b d m, C b d m → b+d+2*m+2*n+13=14*2^n
  evenLeft : ∀ b d m, C b d m → b%2=0
  oddRight : ∀ b d m, C b d m → d%2=1
  endpoint : ∀ b d m, C b d m → (d-1)/2 ∈ states (7*2^n-(n+3)) 0 [1] m
  child : ∀ b d m t k c, C b d m → 8≤b → b%4=0 → d%2=1 → I b d t k c → 2≤k → c%2=1 → C (2*k-4) (c+4) (m+t+1)
  invLower : ∀ b d t k c, I b d t k c → b/4-1≤k
  invEquations : ∀ b d t k c, 4≤b → b%4=0 → d%2=1 → I b d t k c →
    d+b/2+3=2^t*(c+3) ∧ 2*k+c+2*t+1+c%2=b+d
  prevOdd : ∀ b d t k c, I b d (t+1) k c → ∃ k0 c0, I b d t k0 c0 ∧ c0%2=1
  reachableMod4 : ∀ b d, 12≤b → 0<d → b%2=0 → R b d → b%4=0
  feeder : ∀ b d, 12≤b → b%4=0 → 0<d → (∀ t k, ¬ I b d t k 1) → R b d →
    ∃ t k c, I b d t k c ∧ R (2*k-4) (c+4)
  evenPower : ∀ k c, 2≤k → c%2=0 → R (2*k-4) (c+4) → ∃ a, 2*k+8=14*2^a

variable {n : Nat} {C : Nat → Nat → Nat → Prop} {R : Nat → Nat → Prop}
  {I : Nat → Nat → Nat → Nat → Nat → Prop}

theorem cone_margin (F : ConeFacts n C R I) (hn : 14≤n) (K : Nat)
    (hcert : cert (2^n) n (7*2^n-(n+3)) 0 [1] K = true)
    (b d m : Nat) (h : C b d m) :
    m<K ∧ 12≤b ∧ (d-1)/2≠2 ∧ (d-1)/2+2*m+2*n+3<7*2^n := by
  have he := cert_member _ _ _ _ _ _ hcert (F.endpoint b d m h)
  have hd := F.oddRight b d m h
  have hb := safe_left (2^n) n m b d ((d-1)/2) hn (by omega) (F.mass b d m h) he.2.2
  exact ⟨he.1,hb,he.2⟩

theorem cone_no_one (F : ConeFacts n C R I) (hn : 14≤n) (K : Nat)
    (hcert : cert (2^n) n (7*2^n-(n+3)) 0 [1] K = true)
    (b d m : Nat) (h : C b d m) (hb4 : b%4=0) : ∀ t k, ¬ I b d t k 1 := by
  intro t k hi
  have hs := cone_margin F hn K hcert b d m h
  have hk := F.invLower b d t k 1 hi
  have hd := F.oddRight b d m h
  have hchild := F.child b d m t k 1 h (by omega) hb4 hd hi (by omega) (by decide)
  have hc := cone_margin F hn K hcert _ _ _ hchild
  exact hc.2.2.1 (by decide)

theorem cone_no_even (F : ConeFacts n C R I) (hn : 14≤n) (K : Nat)
    (hcert : cert (2^n) n (7*2^n-(n+3)) 0 [1] K = true)
    (b d m t k c : Nat) (h : C b d m) (hb4 : b%4=0)
    (hi : I b d t k c) (hc : c%2=0) : ¬ R (2*k-4) (c+4) := by
  intro hr
  have hs := cone_margin F hn K hcert b d m h
  have hd := F.oddRight b d m h
  have hk := F.invLower b d t k c hi
  have hp := F.invEquations b d t k c (by omega) hb4 hd hi
  have hm := F.mass b d m h
  obtain ⟨a,ha⟩ := F.evenPower k c (by omega) hc hr
  cases t with
  | zero => simp at hp; omega
  | succ t =>
    obtain ⟨k0,c0,hi0,hc0⟩ := F.prevOdd b d t k c hi
    have hk0 := F.invLower b d t k0 c0 hi0
    have hchild := F.child b d m t k0 c0 h (by omega) hb4 hd hi0 (by omega) hc0
    have hs0 := cone_margin F hn K hcert _ _ _ hchild
    have hp0 := F.invEquations b d t k0 c0 (by omega) hb4 hd hi0
    have hy := previous_odd_carry t c c0 (hp.1.symm.trans hp0.1)
    have hgap := safe_even_gap (2^n) n (m+(t+1)) k c ((c0+4-1)/2) hy (by omega) (by omega) hn
    exact no_power n a (2*k+8) (by omega) hgap.1 hgap.2 ha

theorem cone_no_reach (F : ConeFacts n C R I) (hn : 14≤n) (K r : Nat)
    (hcert : cert (2^n) n (7*2^n-(n+3)) 0 [1] K = true) :
    ∀ b d m, K-m=r → C b d m → ¬ R b d := by
  induction r using Nat.strongRecOn with
  | ind r ih =>
    intro b d m hrem h hr
    have hs := cone_margin F hn K hcert b d m h
    have hd := F.oddRight b d m h
    have hb4 := F.reachableMod4 b d hs.2.1 (by omega) (F.evenLeft b d m h) hr
    obtain ⟨t,k,c,hi,hprev⟩ := F.feeder b d hs.2.1 hb4 (by omega) (cone_no_one F hn K hcert b d m h hb4) hr
    by_cases heven : c%2=0
    · exact cone_no_even F hn K hcert b d m t k c h hb4 hi heven hprev
    · have hk := F.invLower b d t k c hi
      have hchild := F.child b d m t k c h (by omega) hb4 hd hi (by omega) (by omega)
      have hnew := cone_margin F hn K hcert _ _ _ hchild
      exact ih (K-(m+t+1)) (by omega) _ _ _ rfl hchild hprev

#print axioms cert_member
#print axioms cone_margin
#print axioms cone_no_one
#print axioms cone_no_even
#print axioms cone_no_reach
end BB6.Agent23FullCone
