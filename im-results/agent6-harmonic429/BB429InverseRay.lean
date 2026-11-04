import BB429Rank
import BB429Burst
import Lean.Elab.Tactic.Omega

namespace BB429InverseRay

/-- A seed selected to have exactly L first-branch successors ending at a
    125-mod-128 terminal feeder. -/
def seedW (L : Nat) : Nat := 512*2^L-(3*L+138)

theorem seedW_bound (L : Nat) : 3*L+138 ≤ 512*2^L := by
  induction L with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ]
    omega

theorem seedW_identity (L : Nat) : seedW L+3*L+138=512*2^L := by
  unfold seedW
  have hb := seedW_bound L
  omega

/-- Uniform exact forward first-branch chain, with arbitrary finite length L,
    ending on the penultimate state of the 125 (mod 128) halting ray. -/
theorem arbitrary_inverse_depth (L : Nat) :
    BB429Burst.firstRun L (61,seedW L) =
      some (64*2^L-3,384*2^L-10) := by
  cases L with
  | zero => decide
  | succ k =>
    have hw := seedW_identity (k+1)
    have hk : 0 < 2^k := Nat.pow_pos (by decide)
    have hpower : 2^(k+1)=2*2^k := by
      rw [Nat.pow_succ]
      omega
    have hguard : 4*((61+3)*2^k) ≤ 2*61+seedW (k+1)+3*k+9 := by
      rw [hpower] at hw
      omega
    obtain ⟨a,b,htrace⟩ := (BB429Burst.prefix_exists_iff 61 (seedW (k+1)) k).mpr hguard
    have ⟨ha,hb⟩ := BB429Burst.prefix_formula 61 (seedW (k+1)) (k+1) a b htrace
    have ha' : a=64*2^(k+1)-3 := by omega
    have hb' : b=384*2^(k+1)-10 := by omega
    simpa [ha',hb'] using htrace

/-- Every successful first-only execution is an execution of the exact
    12-branch arithmetic map, not an abstract syntactic rewrite. -/
theorem firstRun_to_source (n : Nat) (s t : BB429.State)
    (h : BB429Burst.firstRun n s = some t) :
    BB429.run n s = some t := by
  induction n generalizing t with
  | zero => simpa [BB429Burst.firstRun, BB429.run] using h
  | succ n ih =>
    simp only [BB429Burst.firstRun] at h
    cases hs : BB429Burst.firstRun n s with
    | none => simp [hs] at h
    | some p =>
      simp only [hs, Option.bind_some] at h
      obtain ⟨u,w⟩ := p
      have hg : 2*u+3 ≤ w := by
        simp only [BB429Burst.firstStep] at h
        split at h
        · assumption
        · cases h
      have hb : BB429.next (u,w)=some t := by
        simpa [BB429.next, BB429Burst.firstStep, hg] using h
      have hp : BB429.run n s=some (u,w) := ih (u,w) hs
      simpa [BB429.run,hp] using hb

/-- For every requested inverse depth, the full source-shaped map has a
    genuine all-first-branch predecessor path to a 125-mod-128 feeder. -/
theorem source_arbitrary_inverse_depth (L : Nat) :
    BB429.run L (61,seedW L) =
      some (64*2^L-3,384*2^L-10) := by
  exact firstRun_to_source L (61,seedW L) _ (arbitrary_inverse_depth L)

/-- There are parity-compatible synthetic halting traces of unbounded length
    whose terminal first counters are 125 modulo 128. Their chosen seed is
    not asserted to be reachable from the genuine blank start. -/
theorem synthetic_halt_after_arbitrary_depth (L : Nat) :
    ∃ a b, BB429.run (L+1) (61,seedW L) = some (a,b) ∧
      BB429.next (a,b) = none ∧ a%128=125 := by
  let t := 2^L
  have ht : 0<t := Nat.pow_pos (by decide)
  have hr : BB429.run L (61,seedW L) =
      some (64*t-3,384*t-10) := source_arbitrary_inverse_depth L
  have hg : 2*(64*t-3)+3 ≤ 384*t-10 := by omega
  have hs : BB429.next (64*t-3,384*t-10) =
      some (128*t-3,256*t-7) := by
    simp [BB429.next,hg]
    omega
  have hr' : BB429.run (L+1) (61,seedW L) =
      some (128*t-3,256*t-7) := by
    simp only [BB429.run,hr,Option.bind_some]
    exact hs
  refine ⟨128*t-3,256*t-7,hr',?_,?_⟩
  · apply (BB429.next_none_iff_halt_line (128*t-3) (256*t-7)).mpr
    omega
  · have hdiv : 128*t-3 = 128*(t-1)+125 := by omega
    rw [hdiv]
    omega

#print axioms synthetic_halt_after_arbitrary_depth

/-- A successful long first-branch run has a successful prefix of every
    shorter length. -/
theorem firstRun_prefix (s : BB429Burst.State) (n m : Nat)
    (h : ∃ t, BB429Burst.firstRun (n+m) s = some t) :
    ∃ p, BB429Burst.firstRun n s = some p := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
    obtain ⟨t,ht⟩ := h
    rw [Nat.add_succ] at ht
    simp only [BB429Burst.firstRun] at ht
    cases hp : BB429Burst.firstRun (n+m) s with
    | none => simp [hp] at ht
    | some p =>
      exact ih ⟨p,hp⟩

/-- Every intermediate first counter in the arbitrarily deep inverse chain
    is odd, so the positive-even parity invariant cannot close this chain. -/
theorem all_prefixes_odd (L i : Nat) (hi : i ≤ L) :
    ∃ a b, BB429Burst.firstRun i (61,seedW L) = some (a,b) ∧ a%2=1 := by
  have he := arbitrary_inverse_depth L
  obtain ⟨p,hp⟩ := firstRun_prefix (61,seedW L) i (L-i)
    ⟨_,by simpa [show i+(L-i)=L by omega] using he⟩
  obtain ⟨a,b⟩ := p
  have hf := (BB429Burst.prefix_formula 61 (seedW L) i a b hp).1
  refine ⟨a,b,hp,?_⟩
  omega

#print axioms all_prefixes_odd
#print axioms firstRun_to_source
#print axioms source_arbitrary_inverse_depth
#print axioms seedW_bound
#print axioms seedW_identity
#print axioms arbitrary_inverse_depth
end BB429InverseRay
