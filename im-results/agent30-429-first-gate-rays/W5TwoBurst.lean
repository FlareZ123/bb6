import FirstGateRays
import BB429Burst
import Lean.Elab.Tactic.Omega

namespace BB429TwoBurst
open BB429FirstGateRays

def kTwo (t : Nat) : Nat := 14*2^(4*t+5)-23-6*t

def qTwo (t : Nat) : Nat := 2^(4*t+5)

theorem q_bound (t : Nat) : 4*t+6 ≤ qTwo t := by
  simpa [qTwo] using two_pow_ge (4*t+5)

theorem kTwo_formula (t : Nat) :
    kTwo t + 23 + 6*t = 14*qTwo t := by
  unfold kTwo qTwo
  have h := q_bound t
  dsimp [qTwo] at h
  omega

theorem pow_two (t : Nat) :
    2^(4*t+6) = 2*qTwo t ∧ 2^(4*t+7) = 4*qTwo t := by
  have h1 : 4*t+6 = (4*t+5)+1 := by omega
  have h2 : 4*t+7 = (4*t+5)+2 := by omega
  constructor
  · rw [h1, Nat.pow_add]
    simp only [show (2:Nat)^1=2 by decide]
    simp [qTwo, Nat.mul_comm]
  · rw [h2, Nat.pow_add]
    simp only [show (2:Nat)^2=4 by decide]
    simp [qTwo, Nat.mul_comm]

theorem first_prefix_two (t : Nat) :
    BB429Burst.firstRun (4*t+7) (3,4*kTwo t+17) =
      some (24*qTwo t-3,8*qTwo t-42-12*t) := by
  have hq := q_bound t
  have hk := kTwo_formula t
  have ⟨hp2,hp4⟩ := pow_two t
  have hg : 4*((3+3)*2^(4*t+6)) ≤
      2*3+(4*kTwo t+17)+3*(4*t+6)+9 := by
    rw [hp2]
    omega
  obtain ⟨a,b,htrace⟩ :=
    (BB429Burst.prefix_exists_iff 3 (4*kTwo t+17) (4*t+6)).mpr hg
  have hab : BB429Burst.firstRun (4*t+7) (3,4*kTwo t+17) = some (a,b) := by
    simpa [show 4*t+6+1=4*t+7 by omega] using htrace
  obtain ⟨ha,hb⟩ := BB429Burst.prefix_formula 3 (4*kTwo t+17) (4*t+7) a b hab
  have ha' : a=24*qTwo t-3 := by rw [hp4] at ha; omega
  have hb' : b=8*qTwo t-42-12*t := by omega
  simpa [ha',hb'] using hab

theorem middle_even_step (t : Nat) :
    BB429.next (24*qTwo t-3,8*qTwo t-42-12*t) =
       some (11,anc 11 (4*t+5)) := by
  have hq := q_bound t
  have ha := anc_formula 11 (4*t+5) (by omega)
  have hbpos : 42+12*t ≤ 8*qTwo t := by omega
  have hapos : 3 ≤ 24*qTwo t := by omega
  have hless : 8*qTwo t-42-12*t < 2*(24*qTwo t-3) := by omega
  have hdiv : (8*qTwo t-42-12*t)/2 = 4*qTwo t-21-6*t := by omega
  have hd : (24*qTwo t-3) - ((8*qTwo t-42-12*t)/2) =
            20*qTwo t+18+6*t := by omega
  have heven : (8*qTwo t-42-12*t)%2=0 := by omega
  have hdeven : ((24*qTwo t-3) - ((8*qTwo t-42-12*t)/2))%2=0 := by omega
  have hdne : (24*qTwo t-3) - ((8*qTwo t-42-12*t)/2) ≠ 1 := by omega
  have hsum : 2*(24*qTwo t-3)+(8*qTwo t-42-12*t)-2 = anc 11 (4*t+5) := by
    dsimp [qTwo] at *
    omega
  have hguard : ¬ (2*(24*qTwo t-3)+3 ≤ 8*qTwo t-42-12*t) := by omega
  have h2 : 8*qTwo t-42-12*t ≠ 2*(24*qTwo t-3)+2 := by omega
  have h1 : 8*qTwo t-42-12*t ≠ 2*(24*qTwo t-3)+1 := by omega
  have h0 : 8*qTwo t-42-12*t ≠ 2*(24*qTwo t-3) := by omega
  simp [BB429.next, hguard, h2, h1, h0, heven, hdeven, hdne, hsum]

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

/-- For every t, a long first-branch burst, one exceptional low-even
    branch, and another long first-branch burst reach the genuine
    12-branch source accelerator's fatal gateway. -/
theorem two_burst_halts (t : Nat) :
    BB429.run (8*t+14) (3,4*kTwo t+17) = none := by
  have hfirst : BB429.run (4*t+7) (3,4*kTwo t+17) =
      some (24*qTwo t-3,8*qTwo t-42-12*t) :=
    firstRun_to_source (4*t+7) _ _ (first_prefix_two t)
  have hmid := middle_even_step t
  have hstep : BB429.run (4*t+8) (3,4*kTwo t+17) =
      some (11,anc 11 (4*t+5)) := by
    have hh : 4*t+8=(4*t+7)+1 := by omega
    rw [hh]
    change (BB429.run (4*t+7) (3,4*kTwo t+17)).bind BB429.next = _
    rw [hfirst]
    simp only [Option.bind_some]
    exact hmid
  have ht : 8*t+14=(4*t+8)+(4*t+6) := by omega
  rw [ht, BB429.run_add (4*t+8) (4*t+6) (3,4*kTwo t+17)]
  rw [hstep]
  simpa only [Option.bind_some, show 4*t+6=(4*t+5)+1 by omega] using
    (ray_halts 11 (4*t+5) (by omega))

#print axioms first_prefix_two
#print axioms middle_even_step
#print axioms two_burst_halts
end BB429TwoBurst
