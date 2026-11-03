import Lean.Elab.Tactic.Omega
import PacketPaths

namespace BB6.Agent31PacketNormalizer
open BB6.Agent31PacketPaths CryptidBoundary

def next (s : State) : Option (Nat × State) :=
  if s.a % 3 = 2 then
    if s.q = 0 then none
    else
      let k := s.a / 3
      some (12*k*k+49*k+40, ⟨8*k+10, s.q-1, s.p⟩)
  else if s.a % 3 = 1 then
    if s.a < 4 ∨ s.p < 3 then none
    else
      let k := (s.a-4)/3
      some (12*k*k+49*k+58+6*s.q,
        ⟨8*k+9, s.q+2, s.p-3⟩)
  else none

/-- Every executable step is a valid original-machine packet macro. -/
theorem next_edge {s dst : State} {t : Nat}
    (h : next s = some (t, dst)) : Edge s t dst := by
  rcases s with ⟨a,q,p⟩
  unfold next at h
  by_cases ha : a % 3 = 2
  · simp only [ha, ↓reduceIte] at h
    by_cases hq : q = 0
    · simp [hq] at h
    · simp only [hq, ↓reduceIte] at h
      have heqa : a = 3*(a/3)+2 := by omega
      have heqq : q = (q-1)+1 := by omega
      have hpair := Option.some.inj h
      have ht := congrArg Prod.fst hpair
      simp only at ht
      have hd := congrArg Prod.snd hpair
      simp only at hd
      subst t
      subst dst
      simpa only [←heqa, ←heqq] using (Edge.b (a/3) (q-1) p)
  · simp only [ha, ↓reduceIte] at h
    by_cases he : a % 3 = 1
    · simp only [he, ↓reduceIte] at h
      by_cases hp : a < 4 ∨ p < 3
      · simp [hp] at h
      · simp only [hp, ↓reduceIte] at h
        have heqa : a = 3*((a-4)/3)+4 := by omega
        have heqp : p = (p-3)+3 := by omega
        have hpair := Option.some.inj h
        have ht := congrArg Prod.fst hpair
        simp only at ht
        have hd := congrArg Prod.snd hpair
        simp only at hd
        subst t
        subst dst
        simpa only [←heqa, ←heqp] using (Edge.e ((a-4)/3) q (p-3))
    · simp [he] at h

/-- The executable classifier recognizes *every* legal guarded packet edge. -/
theorem edge_next {s dst : State} {t : Nat}
    (h : Edge s t dst) : next s = some (t, dst) := by
  cases h with
  | b k q p =>
    have hdiv : (3*k+2)/3 = k := by omega
    simp [next, hdiv]
  | e k q p =>
    simp [next]

/-- Proof-producing normalization of all maximal guarded B/E phases. -/
structure Certificate (s : State) where
  count : Nat
  cost : Nat
  dst : State
  path : Path s count cost dst
  stop : next dst = none
  terminal : ∀ (t : Nat) (d : State), ¬ Edge dst t d

def normalize (s : State) : Certificate s :=
  match h : next s with
  | none =>
      ⟨0,0,s,Path.nil s,h, by
        intro t d he
        have hh := edge_next he
        rw [h] at hh
        contradiction⟩
  | some (t,d) =>
      let recCert := normalize d
      ⟨recCert.count + 1, t + recCert.cost, recCert.dst,
        Path.cons (next_edge h) recCert.path, recCert.stop, recCert.terminal⟩
termination_by rank s
decreasing_by
  have hr := edge_rank (next_edge h)
  omega

/-- The complete normalized packet is an exact original raw-machine endpoint. -/
theorem normalize_sound (s : State) (ys : List Bool) :
    run (normalize s).cost (physical s ys) = physical (normalize s).dst ys :=
  path_sound (normalize s).path ys

/-- Its number of macro stages has the global q+p bound. -/
theorem normalize_bound (s : State) : (normalize s).count ≤ s.q+s.p :=
  path_count_bound (normalize s).path

#print axioms next_edge
#print axioms edge_next
#print axioms normalize
#print axioms normalize_sound
#print axioms normalize_bound
end BB6.Agent31PacketNormalizer
