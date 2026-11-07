import BusyBeaver.BB6.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA
import BB429Burst
import BB429TurnaroundCore
import Lean.Elab.Tactic.Omega

namespace BB429TurnaroundSource
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA
open BB429Burst
open BB429TurnaroundCore

abbrev State := Nat × Nat

def sourceRun (n : Nat) (s : HighLevelState) : Option HighLevelState :=
  match n with
  | 0 => some s
  | k+1 => (sourceRun k s).bind highLevelNext

theorem source_first_step (u w : Nat) (h : 2*u+3 ≤ w) :
    highLevelNext (.J u w) = some (.J (2*u+3) (w-2*u-3)) := by
  simp only [highLevelNext]
  split
  · rfl
  · omega

theorem firstRun_source (u w n a b : Nat)
    (h : firstRun n (u,w) = some (a,b)) :
    sourceRun n (.J u w) = some (.J a b) := by
  induction n generalizing a b with
  | zero =>
    simp only [firstRun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    rfl
  | succ n ih =>
    simp only [firstRun] at h
    cases hp : firstRun n (u,w) with
    | none => simp [hp] at h
    | some p =>
      simp only [hp, Option.bind_some] at h
      simp only [firstStep] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        change (sourceRun n (.J u w)).bind highLevelNext = _
        rw [ih p.1 p.2 hp]
        simp only [Option.bind_some]
        exact source_first_step p.1 p.2 (by assumption)
      · simp at h

theorem source_burst_decomposition (u w : Nat) :
    let r := burstExit u w
    sourceRun (r.2+1) (.J u w) = highLevelNext (.J r.1.1 r.1.2) := by
  let r := burstExit u w
  have hspec := burstExit_spec u w
  dsimp [r] at hspec
  rcases hspec with ⟨hrun,hstop⟩
  have hsource := firstRun_source u w r.2 r.1.1 r.1.2 hrun
  change (sourceRun r.2 (.J u w)).bind highLevelNext = _
  rw [hsource]
  rfl

theorem source_none_iff (u w : Nat) :
    highLevelNext (.J u w) = none ↔ w+1=2*u := by
  constructor
  · intro h
    simp only [highLevelNext] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · split at h
              · cases h
              · split at h
                · cases h
                · cases h
            · split at h
              · omega
              · split at h
                · cases h
                · split at h
                  · split at h
                    · cases h
                    · cases h
                  · cases h
  · intro hl
    have hw : ¬(w ≥ 2*u+3) := by omega
    have hw2 : w ≠ 2*u+2 := by omega
    have hw1 : w ≠ 2*u+1 := by omega
    have hw0 : w ≠ 2*u := by omega
    have hp : w % 2 ≠ 0 := by omega
    have hd : u-w/2=1 := by omega
    simp only [highLevelNext]
    split
    · omega
    · simp [hw2, hw1, hw0, hp, hd]

def sourceTurnAt (u w : Nat) : Option State :=
  match highLevelNext (.J u w) with
  | none => none
  | some (.J a b) => some (a,b)

def sourceTurnaround (u w : Nat) : Option State :=
  let r := burstExit u w
  sourceTurnAt r.1.1 r.1.2

theorem sourceTurnAt_none_iff (u w : Nat) :
    sourceTurnAt u w = none ↔ w+1=2*u := by
  unfold sourceTurnAt
  constructor
  · intro h
    cases hs : highLevelNext (.J u w) with
    | none => exact (source_none_iff u w).mp hs
    | some s => cases s with | J a b => simp [hs] at h
  · intro hw
    have hs := (source_none_iff u w).2 hw
    simp [hs]

theorem sourceTurnaround_none_iff (u w : Nat) :
    sourceTurnaround u w = none ↔
      (burstExit u w).1.2+1 = 2*(burstExit u w).1.1 := by
  simp [sourceTurnaround, sourceTurnAt_none_iff]

theorem sourceTurnaround_none_iff_exponential (u w : Nat) :
    sourceTurnaround u w = none ↔
      2*u+w+3*(burstExit u w).2+13 =
        4*((u+3)*2^(burstExit u w).2) := by
  rw [sourceTurnaround_none_iff]
  have hspec := burstExit_spec u w
  dsimp at hspec
  rcases hspec with ⟨hrun,hstop⟩
  exact (gateway_iff_exponential u w (burstExit u w).2
    (burstExit u w).1.1 (burstExit u w).1.2 hrun)

theorem sourceReturn_run (u w : Nat) :
    sourceRun ((burstExit u w).2+1) (.J u w) =
      (sourceTurnaround u w).map (fun p => HighLevelState.J p.1 p.2) := by
  rw [source_burst_decomposition]
  unfold sourceTurnaround sourceTurnAt
  cases h : highLevelNext (.J (burstExit u w).1.1 (burstExit u w).1.2) with
  | none => simp [h]
  | some s => cases s with | J a b => simp [h]

theorem source_exit_shape (u w a b : Nat) (hexit : w < 2*u+3)
    (hn : highLevelNext (.J u w) = some (.J a b)) :
    b%2=0 ∧ 2≤b ∧ (a=0 → 10≤b) ∧ (a=0 ∨ 6≤a) := by
  simp only [highLevelNext] at hn
  split at hn
  · omega
  · split at hn
    · cases hn
      omega
    · split at hn
      · cases hn
        omega
      · split at hn
        · cases hn
          omega
        · split at hn
          · split at hn
            · cases hn
              omega
            · split at hn
              · cases hn
                omega
              · cases hn
                omega
          · split at hn
            · simp at hn
            · split at hn
              · cases hn
                omega
              · split at hn
                · split at hn
                  · cases hn
                    omega
                  · cases hn
                    omega
                · cases hn
                  omega

theorem even_seed_odd_burst (u w n : Nat) (hw : w%2=0)
    (he : 2*u+w+3*n+13 = 4*((u+3)*2^n)) : n%2=1 := by
  omega

theorem pow_two_odd_mod_six (k : Nat) : 2^(2*k+1)%6=2 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hp : 2^(2*(k+1)+1) = 2^(2*k+1)*4 := by
      rw [show 2*(k+1)+1 = (2*k+1)+2 by omega, Nat.pow_add]
    rw [hp, Nat.mul_mod, ih]

theorem even_gateway_mod_six (u w n : Nat) (hw : w%2=0)
    (he : 2*u+w+3*n+13 = 4*((u+3)*2^n)) : w%6=2 := by
  have hn := even_seed_odd_burst u w n hw he
  have hdecomp : n = 2*(n/2)+1 := by
    have h := Nat.mod_add_div n 2
    omega
  have hpow : 2^n%6=2 := by
    rw [hdecomp]
    exact pow_two_odd_mod_six (n/2)
  have hmod := congrArg (fun z : Nat => z%6) he
  have hrhs : (4*((u+3)*2^n))%6 = (2*u)%6 := by
    simp [Nat.mul_mod, hpow]
    omega
  rw [hrhs] at hmod
  omega

theorem sourceTurnaround_even_seed_mod_six (u w : Nat)
    (hw : w%2=0) (h : sourceTurnaround u w = none) : w%6=2 := by
  have he := (sourceTurnaround_none_iff_exponential u w).mp h
  exact even_gateway_mod_six u w (burstExit u w).2 hw he

theorem sourceTurnaround_even (u w a b : Nat)
    (h : sourceTurnaround u w = some (a,b)) : b%2=0 := by
  let r := burstExit u w
  have hstop : r.1.2 < 2*r.1.1+3 := by
    have hs := burstExit_maximal u w
    dsimp [r] at hs
    omega
  have hturn : sourceTurnAt r.1.1 r.1.2 = some (a,b) := by
    simpa [sourceTurnaround, r] using h
  unfold sourceTurnAt at hturn
  cases hn : highLevelNext (.J r.1.1 r.1.2) with
  | none => simp [hn] at hturn
  | some s =>
    cases s with
    | J x y =>
      have hpair : (x,y)=(a,b) := by simpa [hn] using hturn
      cases hpair
      exact (source_exit_shape r.1.1 r.1.2 a b hstop hn).1

theorem blank_first_return : sourceTurnaround 0 0 = some (0,12) := by
  simp [sourceTurnaround, sourceTurnAt, burstExit, highLevelNext]

theorem blank_second_return : sourceTurnaround 0 12 = some (0,28) := by
  simp [sourceTurnaround, sourceTurnAt, burstExit, highLevelNext]

theorem blank_third_return : sourceTurnaround 0 28 = some (0,44) := by
  simp [sourceTurnaround, sourceTurnAt, burstExit, highLevelNext]

theorem blank_fourth_return : sourceTurnaround 0 44 = some (23,18) := by
  simp [sourceTurnaround, sourceTurnAt, burstExit, highLevelNext]

theorem blank_second_return_not_halt : sourceTurnaround 0 12 ≠ none := by
  intro h
  have hm := sourceTurnaround_even_seed_mod_six 0 12 (by decide) h
  omega

theorem blank_third_return_not_halt : sourceTurnaround 0 28 ≠ none := by
  intro h
  have hm := sourceTurnaround_even_seed_mod_six 0 28 (by decide) h
  omega

theorem sourceTurnaround_shape (u w a b : Nat)
    (h : sourceTurnaround u w = some (a,b)) :
    b%2=0 ∧ 2≤b ∧ (a=0 → 10≤b) ∧ (a=0 ∨ 6≤a) := by
  let r := burstExit u w
  have hstop : r.1.2 < 2*r.1.1+3 := by
    have hs := burstExit_maximal u w
    dsimp [r] at hs
    omega
  have hturn : sourceTurnAt r.1.1 r.1.2 = some (a,b) := by
    simpa [sourceTurnaround, r] using h
  unfold sourceTurnAt at hturn
  cases hn : highLevelNext (.J r.1.1 r.1.2) with
  | none => simp [hn] at hturn
  | some s =>
    cases s with
    | J x y =>
      have hpair : (x,y)=(a,b) := by simpa [hn] using hturn
      cases hpair
      exact source_exit_shape r.1.1 r.1.2 a b hstop hn

#print axioms source_burst_decomposition
#print axioms sourceTurnaround_none_iff_exponential
#print axioms sourceTurnaround_even
#print axioms sourceTurnaround_even_seed_mod_six
#print axioms sourceReturn_run
#print axioms source_exit_shape
#print axioms sourceTurnaround_shape
#print axioms blank_first_return
#print axioms blank_second_return
#print axioms blank_third_return
#print axioms blank_fourth_return
#print axioms blank_second_return_not_halt
#print axioms blank_third_return_not_halt

end BB429TurnaroundSource
