import F418EventSystem

namespace BB6.Agent32F418.EventSystem
open Arithmetic State

theorem splitOdd_factor (j Q : Nat) : splitOdd (2^j*(2*Q+1)) = (j,Q) := by
  induction j with
  | zero =>
    rw [splitOdd]
    simp
    omega
  | succ j ih =>
    have hpos : 0 < 2^j*(2*Q+1) := Nat.mul_pos (Nat.two_pow_pos j) (by omega)
    have he : 2^(j+1)*(2*Q+1) = 2*(2^j*(2*Q+1)) := by
      rw [Nat.pow_succ]; ac_rfl
    rw [he,splitOdd]
    simp [show 2*(2^j*(2*Q+1)) ≠ 0 by omega,ih]

theorem splitOdd_gap {a n w z e : Nat} (ha : a ≤ 1) (hw : RightWidth n w)
    (hz : z < gap n w) :
    (splitOdd (gap (resetRight a (n+z) e) (w+e+2))).1 = e := by
  rw [reset_gap ha hw hz]
  have h : 4*(gap n w-z)-1-2*a = 2*(2*(gap n w-z)-1-a)+1 := by omega
  rw [h,Nat.mul_comm,splitOdd_factor]

theorem iterate_add (k l : Nat) (s : State) :
    iterate (k+l) s = (iterate k s).bind (iterate l) := by
  induction k generalizing s with
  | zero => simp [iterate]
  | succ k ih =>
    rw [Nat.succ_add,iterate,iterate]
    cases h : advance s <;> simp [ih]

inductive Reaches (s : State) : State → Prop where
  | zero : Reaches s s
  | succ {t u : State} : Reaches s t → advance t = some u → Reaches s u

theorem reaches_iff {s t : State} : Reaches s t ↔ ∃ k, iterate k s = some t := by
  constructor
  · intro h
    induction h with
    | zero => exact ⟨0,rfl⟩
    | succ _ h ih =>
      obtain ⟨k,hk⟩ := ih
      refine ⟨k+1,?_⟩
      rw [iterate_add,hk]
      simp [iterate,h]
  · rintro ⟨k,h⟩
    induction k generalizing t with
    | zero => simp [iterate] at h; subst t; exact .zero
    | succ k ih =>
      rw [iterate_add] at h
      cases he : iterate k s with
      | none => simp [he] at h
      | some u =>
        refine .succ (ih he) ?_
        simp [he,iterate] at h
        exact h

theorem reaches_trans {s t u : State} (h : Reaches s t) (g : Reaches t u) : Reaches s u := by
  obtain ⟨k,hk⟩ := reaches_iff.mp h
  obtain ⟨l,hl⟩ := reaches_iff.mp g
  exact reaches_iff.mpr ⟨k+l,by simp [iterate_add,hk,hl]⟩

theorem reaches_one {s t : State} (h : advance s = some t) : Reaches s t := .succ .zero h

/-- All set bits of N are at odd indices; last is the final relative valuation.
    This is a recursive language on finite binary words. -/
inductive OddChain : Nat → Nat → Prop where
  | last (j : Nat) (hj : j%2=1) : OddChain (2^j) j
  | more (j Q last : Nat) (hj : j%2=1) (hQ : 0 < Q)
      (h : OddChain Q last) : OddChain (2^j*(2*Q+1)) last

theorem oddChain_pos {N last : Nat} (h : OddChain N last) : 0 < N := by
  cases h with
  | last => exact Nat.two_pow_pos _
  | more => exact Nat.mul_pos (Nat.two_pow_pos _) (by omega)

theorem oddChain_odd {N last : Nat} (h : OddChain N last) : last%2=1 := by
  induction h with
  | last _ h => exact h
  | more _ _ _ _ _ _ ih => exact ih

theorem oddChain_split {N j Q last : Nat} (h : OddChain N last)
    (hf : splitOdd N = (j,Q)) : j%2=1 ∧ (Q=0 ∧ last=j ∨ 0<Q ∧ OddChain Q last) := by
  cases h with
  | last k hk =>
    have he := splitOdd_factor last 0
    simp at he
    rw [he] at hf
    simp at hf
    obtain ⟨rfl,rfl⟩ := hf
    exact ⟨hk,Or.inl ⟨rfl,rfl⟩⟩
  | more k q last hk hq hc =>
    rw [splitOdd_factor] at hf
    simp at hf
    obtain ⟨rfl,rfl⟩ := hf
    exact ⟨hk,Or.inr ⟨hq,hc⟩⟩

/-- Odd-only words exit through the ordinary phase-1 state. The final
    relative valuation determines the valuation of its next gap. -/
theorem oddChain_exit {N last a n w : Nat} (hc : OddChain N last)
    (hs : Safe (shift2 N a n w)) :
    ∃ n' w', Reaches (shift2 N a n w) (reg1 n' w') ∧ Safe (reg1 n' w') ∧
      (splitOdd (gap n' w')).1 = (5*last+1)/2 := by
  induction hc generalizing a n w with
  | last j hj =>
    have hs0 := hs
    obtain ⟨hN,ha,hw,hn,ht⟩ := hs0
    let e := (5*j+1)/2
    let n' := resetRight a (n+(2^j-1)) e
    let w' := w+e+2
    have hf : splitOdd (2^j) = (j,0) := by simpa using splitOdd_factor j 0
    have hav : advance (shift2 (2^j) a n w) = some (reg1 n' w') := by
      simp [advance,hf,hj,shift2OrReg1,n',w',e]
    have hz : 2^j-1 < gap n w := by omega
    refine ⟨n',w',reaches_one hav,safe_advance hs hav,?_⟩
    exact splitOdd_gap ha hw hz
  | more j Q last hj hQ hc ih =>
    have hs0 := hs
    obtain ⟨hN,ha,hw,hn,ht⟩ := hs0
    let e := (5*j+1)/2
    let n' := resetRight a (n+(2^j-1)) e
    let w' := w+e+2
    have hav : advance (shift2 (2^j*(2*Q+1)) a n w) = some (shift2 Q 1 n' w') := by
      simp [advance,splitOdd_factor,hj,shift2OrReg1,show Q ≠ 0 by omega,n',w',e]
    obtain ⟨n'',w'',hr,hSafe,hval⟩ := ih (safe_advance hs hav)
    exact ⟨n'',w'',reaches_trans (reaches_one hav) hr,hSafe,hval⟩

/-- Every nonempty alignment-2 episode either reaches ordinary phase 0,
    or is an odd-only word with a certified ordinary phase-1 exit. -/
theorem episode_partition (N a n w : Nat) (hs : Safe (shift2 N a n w)) :
    (∃ last, OddChain N last ∧ ∃ n' w', Reaches (shift2 N a n w) (reg1 n' w') ∧
      Safe (reg1 n' w') ∧ (splitOdd (gap n' w')).1 = (5*last+1)/2) ∨
    ((∀ last, ¬OddChain N last) ∧ ∃ Q n' w', Reaches (shift2 N a n w) (reg0 Q n' w') ∧
      Safe (reg0 Q n' w')) := by
  induction N using Nat.strongRecOn generalizing a n w with
  | ind N ih =>
    have hs0 := hs
    obtain ⟨hN,ha,hw,hn,ht⟩ := hs0
    have hf := splitOdd_spec N hN
    have hlt := splitOdd_tail_lt N hN
    rcases he : splitOdd N with ⟨j,Q⟩
    rw [he] at hf hlt
    dsimp at hf hlt
    let e := (5*j+1)/2
    let n' := resetRight a (n+(2^j-1)) e
    let w' := w+e+2
    by_cases hj : j%2=0
    · right
      have hav : advance (shift2 N a n w) = some (reg0 Q n' w') := by
        simp [advance,he,hj,n',w',e]
      refine ⟨?_,Q,n',w',reaches_one hav,safe_advance hs hav⟩
      intro last hc
      have hh := (oddChain_split hc he).1
      omega
    · have hodd : j%2=1 := by omega
      by_cases hQ : Q=0
      · have hc : OddChain N j := by simpa [hf,hQ] using OddChain.last j hodd
        exact Or.inl ⟨j,hc,oddChain_exit hc hs⟩
      · have hav : advance (shift2 N a n w) = some (shift2 Q 1 n' w') := by
          simp [advance,he,hj,shift2OrReg1,hQ,n',w',e]
        have hs' := safe_advance hs hav
        rcases ih Q hlt 1 n' w' hs' with ⟨last,hc,_⟩ | ⟨hc,R,m,v,hr,hSafe⟩
        · have hc' : OddChain N last := by rw [hf]; exact .more j Q last hodd (by omega) hc
          exact Or.inl ⟨last,hc',oddChain_exit hc' hs⟩
        · right
          refine ⟨?_,R,m,v,reaches_trans (reaches_one hav) hr,hSafe⟩
          intro last hh
          rcases (oddChain_split hh he).2 with ⟨hz,_⟩ | ⟨_,hh'⟩
          · contradiction
          · exact hc last hh'

/-- The exceptional odd-only episode with final relative valuation 3 mod 4
    reaches the genuine arithmetic terminal state after two more events. -/
theorem fatal_episode {N a n w last : Nat} (hc : OddChain N last)
    (hf : last%4=3) (hs : Safe (shift2 N a n w)) :
    ∃ Q n' w', Reaches (shift2 N a n w) (shift1 Q n' w') ∧ Safe (shift1 Q n' w') := by
  obtain ⟨m,v,hr,hSafe,hval⟩ := oddChain_exit hc hs
  let N' := gap m v
  let W' := v-1
  have h1 : advance (reg1 m v) = some (shift4 N' W') := rfl
  have hs' := safe_advance hSafe h1
  rcases he : splitOdd N' with ⟨j,Q⟩
  change (splitOdd N').1 = (5*last+1)/2 at hval
  rw [he] at hval
  have hj : j%2=0 := by dsimp at hval; omega
  let e := (5*j+4)/2
  let n' := resetRight 0 (2^W'+(2^(j+1)-1)) e
  let w' := W'+1+e+2
  have h2 : advance (shift4 N' W') = some (shift1 Q n' w') := by
    simp [advance,he,hj,n',w',e]
  exact ⟨Q,n',w',reaches_trans (reaches_trans hr (reaches_one h1)) (reaches_one h2),safe_advance hs' h2⟩

/-- The other odd-only episode exits safely to alignment 2 phase 0.
    Odd-only alone is not a halting certificate. -/
theorem recoverable_episode {N a n w last : Nat} (hc : OddChain N last)
    (hf : last%4=1) (hs : Safe (shift2 N a n w)) :
    ∃ Q n' w', Reaches (shift2 N a n w) (shift2 Q 0 n' w') ∧ Safe (shift2 Q 0 n' w') := by
  obtain ⟨m,v,hr,hSafe,hval⟩ := oddChain_exit hc hs
  let N' := gap m v
  let W' := v-1
  have h1 : advance (reg1 m v) = some (shift4 N' W') := rfl
  have hs' := safe_advance hSafe h1
  rcases he : splitOdd N' with ⟨j,Q⟩
  change (splitOdd N').1 = (5*last+1)/2 at hval
  rw [he] at hval
  have hj : ¬j%2=0 := by dsimp at hval; omega
  let e := (5*j+4)/2
  let n' := resetRight 0 (2^W'+(2^(j+1)-1)) e
  let w' := W'+1+e+2
  have h2 : advance (shift4 N' W') = some (shift2 Q 0 n' w') := by
    simp [advance,he,hj,n',w',e]
  exact ⟨Q,n',w',reaches_trans (reaches_trans hr (reaches_one h1)) (reaches_one h2),safe_advance hs' h2⟩

/-- Terminal precursor conditions outside the alignment-2 episode. -/
def Gateway : State → Prop
  | reg1 n w => (splitOdd (gap n w)).1%2=0
  | shift4 N _ => (splitOdd N).1%2=0
  | shift1 _ _ _ => True
  | _ => False

def Fatal : State → Prop
  | shift2 N _ _ _ => ∃ last, OddChain N last ∧ last%4=3
  | _ => False

theorem gateway_prev {s t : State} (hs : Safe s) (h : advance s = some t)
    (hg : Gateway t) : Gateway s ∨ Fatal s := by
  cases s with
  | reg0 N n w =>
    simp [advance] at h
    subst t
    exact False.elim hg
  | reg1 n w =>
    simp [advance] at h
    subst t
    exact Or.inl hg
  | shift4 N W =>
    rcases he : splitOdd N with ⟨j,Q⟩
    simp only [advance,he] at h
    split at h
    · rename_i hj
      exact Or.inl (by simp [Gateway,he,hj])
    · simp only [Option.some.injEq] at h
      subst t
      exact False.elim hg
  | shift2 N a n w =>
    obtain ⟨hN,ha,hw,hn,ht⟩ := hs
    have hf := splitOdd_spec N hN
    rcases he : splitOdd N with ⟨j,Q⟩
    rw [he] at hf
    dsimp at hf
    simp only [advance,he] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst t
      exact False.elim hg
    · rename_i hj
      simp only [shift2OrReg1] at h
      split at h
      · rename_i hQ
        simp only [Option.some.injEq] at h
        subst t
        have heq : N=2^j := by simpa [hQ] using hf
        have hz : 2^j-1 < gap n w := by omega
        have hval := splitOdd_gap (e:=(5*j+1)/2) ha hw hz
        change (splitOdd (gap (resetRight a (n+(2^j-1)) ((5*j+1)/2)) (w+(5*j+1)/2+2))).1%2=0 at hg
        rw [hval] at hg
        right
        refine ⟨j,?_,by omega⟩
        rw [heq]
        exact OddChain.last j (by omega)
      · simp only [Option.some.injEq] at h
        subst t
        exact False.elim hg
  | shift1 N n w => simp [advance] at h

theorem reaches_safe {s : State} (h : Reaches seed s) : Safe s := by
  obtain ⟨k,hk⟩ := reaches_iff.mp h
  exact seed_orbit_safe hk

theorem seed_not_gateway : ¬Gateway seed := by
  change ¬(splitOdd (gap 39464 16)).1%2=0
  have he : gap 39464 16 = 2^3*(2*1629+1) := by decide
  rw [he,splitOdd_factor]
  decide

theorem gateway_has_fatal {s : State} (hr : Reaches seed s) (hg : Gateway s) :
    ∃ t, Reaches seed t ∧ Fatal t := by
  induction hr with
  | zero => exact False.elim (seed_not_gateway hg)
  | succ h hstep ih =>
    rcases gateway_prev (reaches_safe h) hstep hg with hg' | hf
    · exact ih hg'
    · exact ⟨_,h,hf⟩

theorem iterate_none_has_terminal {s : State} {k : Nat} (h : iterate k s = none) :
    ∃ t, Reaches s t ∧ advance t = none := by
  induction k with
  | zero => simp [iterate] at h
  | succ k ih =>
    rw [iterate_add] at h
    cases he : iterate k s with
    | none => exact ih he
    | some t =>
      refine ⟨t,reaches_iff.mpr ⟨k,he⟩,?_⟩
      simpa [he,iterate] using h

/-- Exact halting criterion for the arithmetic orbit from the 670-step seed.
    The raw TM bridge is a separate obligation. -/
theorem seed_termination_iff : (∃ k, iterate k seed = none) ↔
    ∃ s, Reaches seed s ∧ Fatal s := by
  constructor
  · rintro ⟨k,h⟩
    obtain ⟨t,hr,ht⟩ := iterate_none_has_terminal h
    obtain ⟨N,n,w,rfl⟩ := (advance_none_iff t).mp ht
    exact gateway_has_fatal hr trivial
  · rintro ⟨s,hr,hf⟩
    cases s with
    | shift2 N a n w =>
      obtain ⟨last,hc,hj⟩ := hf
      obtain ⟨Q,n',w',ht,_⟩ := fatal_episode hc hj (reaches_safe hr)
      obtain ⟨k,hk⟩ := reaches_iff.mp (reaches_trans hr ht)
      refine ⟨k+1,?_⟩
      rw [iterate_add,hk]
      rfl
    | reg0 => contradiction
    | reg1 => contradiction
    | shift4 => contradiction
    | shift1 => contradiction

#print axioms splitOdd_factor
#print axioms reaches_iff
#print axioms episode_partition
#print axioms fatal_episode
#print axioms recoverable_episode
#print axioms seed_termination_iff
end BB6.Agent32F418.EventSystem
