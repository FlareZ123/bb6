import S4TogglePhases
import Lean.Elab.Tactic.Omega

namespace S4TogglePair
open S4Power S4Octet S4Toggle S4ToggleHead S4TogglePhases
set_option maxHeartbeats 0

def step (p : Nat × Nat) : Nat × Nat :=
  match p with
  | (283,b) => (282,h 1023 b)
  | (282,b) => (280,h 281 (h 343 (h 396 b)))
  | (280,b) => (281,h 624 (h 395 b))
  | (281,b) => (283,h 739 b+281)
  | (a,b) => (a,b)

private theorem p283_pair (b : Nat) (S U : List Nat)
    (hp : P (283::b::S) = some U) :
    ∃ V, U=282::h 1023 b::V := by
  rw [p283] at hp
  obtain ⟨V,hV,hU⟩ := Option.map_eq_some_iff.mp hp
  obtain ⟨T,hT⟩ := G_head 1023 b S V hV
  subst V
  subst U
  exact ⟨T,rfl⟩

private theorem p281_pair (b : Nat) (S U : List Nat)
    (hp : P (281::b::S) = some U) :
    ∃ V, U=283::(h 739 b+281)::V := by
  rw [p281] at hp
  obtain ⟨V,hV,hU⟩ := Option.map_eq_some_iff.mp hp
  obtain ⟨T,hT⟩ := G_head 739 b S V hV
  subst V
  subst U
  exact ⟨T,rfl⟩

private theorem p280_pair (b : Nat) (S U : List Nat)
    (hp : P (280::b::S) = some U) :
    ∃ V, U=281::h 624 (h 395 b)::V := by
  rw [p280] at hp
  cases h1 : G 395 (b::S) with
  | none => simp [h1] at hp
  | some X =>
      obtain ⟨T,hX⟩ := G_head 395 b S X h1
      subst X
      cases h2 : G 624 (h 395 b::T) with
      | none => simp [h1,h2] at hp
      | some Y =>
          obtain ⟨V,hY⟩ := G_head 624 (h 395 b) T Y h2
          subst Y
          have hu : U=281::h 624 (h 395 b)::V := by simpa [h1,h2] using hp.symm
          exact ⟨V,hu⟩

private theorem p282_pair (b : Nat) (S U : List Nat)
    (hp : P (282::b::S) = some U) :
    ∃ V, U=280::h 281 (h 343 (h 396 b))::V := by
  rw [p282] at hp
  cases h1 : G 396 (b::S) with
  | none => simp [h1] at hp
  | some X =>
      obtain ⟨T,hX⟩ := G_head 396 b S X h1
      subst X
      cases h2 : G 343 (h 396 b::T) with
      | none => simp [h1,h2] at hp
      | some Y =>
          obtain ⟨V,hY⟩ := G_head 343 (h 396 b) T Y h2
          subst Y
          cases h3 : G 281 (h 343 (h 396 b)::V) with
          | none => simp [h1,h2,h3] at hp
          | some Z =>
              obtain ⟨R,hZ⟩ := G_head 281 (h 343 (h 396 b)) V Z h3
              subst Z
              have hu : U=280::h 281 (h 343 (h 396 b))::R := by
                simpa [h1,h2,h3] using hp.symm
              exact ⟨R,hu⟩

theorem P_pair_step (a b : Nat) (S U : List Nat)
    (ha : a=280 ∨ a=281 ∨ a=282 ∨ a=283)
    (hp : P (a::b::S)=some U) :
    ∃ V, U=(step (a,b)).1::(step (a,b)).2::V := by
  rcases ha with ha | ha | ha | ha
  · subst a
    obtain ⟨V,hV⟩ := p280_pair b S U hp
    exact ⟨V,by simpa [step] using hV⟩
  · subst a
    obtain ⟨V,hV⟩ := p281_pair b S U hp
    exact ⟨V,by simpa [step] using hV⟩
  · subst a
    obtain ⟨V,hV⟩ := p282_pair b S U hp
    exact ⟨V,by simpa [step] using hV⟩
  · subst a
    obtain ⟨V,hV⟩ := p283_pair b S U hp
    exact ⟨V,by simpa [step] using hV⟩

def pairRun : Nat → Nat × Nat
  | 0 => (280,397)
  | n+1 => step (pairRun n)

theorem pairRun_head (n : Nat) :
  (pairRun n).1=280 ∨ (pairRun n).1=281 ∨
  (pairRun n).1=282 ∨ (pairRun n).1=283 := by
  induction n with
  | zero => simp [pairRun]
  | succ n ih =>
      cases hp : pairRun n with
      | mk a b =>
          have ha : a=280 ∨ a=281 ∨ a=282 ∨ a=283 := by
            simpa [hp] using ih
          rcases ha with h0 | h1 | h2 | h3
          · subst a; simp [pairRun,hp,step]
          · subst a; simp [pairRun,hp,step]
          · subst a; simp [pairRun,hp,step]
          · subst a; simp [pairRun,hp,step]

theorem seedSeven :
    prun 7 [301,650,645,322,163,160] =
      some [280,397,1227,3564,1195,2422,323] := by
  set_option maxRecDepth 10000 in
    simp [prun,P,G,H]

private theorem pairRun_sixteen : pairRun 16 = (280,397) := by
  decide

theorem pairRun_period16 (n : Nat) : pairRun (n+16) = pairRun n := by
  induction n with
  | zero => exact pairRun_sixteen
  | succ n ih =>
      change step (pairRun (n+16)) = step (pairRun n)
      rw [ih]

private theorem pairRun_plus_periods (r k : Nat) :
    pairRun (r+16*k) = pairRun r := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc, pairRun_period16, ih]

theorem pairRun_mod16 (n : Nat) : pairRun n = pairRun (n%16) := by
  have hn : n=n%16+16*(n/16) := by omega
  calc
    pairRun n = pairRun (n%16+16*(n/16)) := congrArg pairRun hn
    _ = pairRun (n%16) := pairRun_plus_periods _ _

theorem prun_pair_cycle (n : Nat) (U : List Nat)
    (hr : prun (7+n) [301,650,645,322,163,160]=some U) :
    ∃ T, U=(pairRun n).1::(pairRun n).2::T := by
  induction n generalizing U with
  | zero =>
      rw [show 7+0=7 by omega, seedSeven] at hr
      have hU : U=[280,397,1227,3564,1195,2422,323] := by
        exact Option.some.inj hr.symm
      subst U
      exact ⟨[1227,3564,1195,2422,323],rfl⟩
  | succ n ih =>
      change (prun (7+n) [301,650,645,322,163,160]).bind P=some U at hr
      cases hprev : prun (7+n) [301,650,645,322,163,160] with
      | none => simp [hprev] at hr
      | some V =>
          obtain ⟨T,hV⟩ := ih V hprev
          subst V
          have hp : P ((pairRun n).1::(pairRun n).2::T)=some U := by
            simpa [hprev] using hr
          obtain ⟨Z,hZ⟩ := P_pair_step _ _ T U (pairRun_head n) hp
          have hpair : ((pairRun n).1,(pairRun n).2)=pairRun n := by
            cases pairRun n; rfl
          rw [hpair] at hZ
          exact ⟨Z, by simpa only [pairRun] using hZ⟩

#print axioms P_pair_step
#print axioms seedSeven
#print axioms pairRun_period16
#print axioms prun_pair_cycle
end S4TogglePair
