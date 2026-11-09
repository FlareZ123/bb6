import Agent8DigitChargeSource

/-!
An exact intrinsic joint-mass cocycle for the original Cryptids #623
B-drain. Every successful source drain has mass
a'+d' = a+d+3*b+e, where e is computed by a one-level ternary
transducer. The charge e is the number of reductions plus twice the
number of positive-first-counter residue-one reductions.
No original blank-root decision follows from this local identity.
-/
namespace BB6.Agent8DigitChargeSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

def excessMass (a b : Nat) : Option Nat :=
  if b=0 then some 0
  else if b%3=0 then (excessMass (a+1) (b/3-1)).map (·+1)
  else if b%3=1 then
    if a=0 then none else (excessMass (a-1) (b/3)).map (·+3)
  else if a=0 then (excessMass 0 (b/3)).map (·+1)
  else (excessMass (a-1) (b/3+1)).map (·+1)
termination_by b
decreasing_by all_goals omega

theorem code_mass (b : Nat) :
  ∀ a : Nat, (digitCode a b).map (fun p => p.1+p.2) =
    (excessMass a b).map (fun v => a+v) := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a
    rw [digitCode,excessMass]
    by_cases hz : b=0
    · subst b; simp
    · simp only [if_neg hz]
      have hdiv : b=3*(b/3)+b%3 := by omega
      by_cases h0 : b%3=0
      · simp only [if_pos h0]
        have hs : b/3-1<b := by omega
        have h:=ih (b/3-1) hs (a+1)
        cases hd : digitCode (a+1) (b/3-1) with
        | none =>
          cases he : excessMass (a+1) (b/3-1) with
          | none => simp [hd,he]
          | some v => simp [hd,he] at h
        | some p =>
          rcases p with ⟨aa,c⟩
          cases he : excessMass (a+1) (b/3-1) with
          | none => simp [hd,he] at h
          | some v =>
            simp only [hd,he,Option.map_some,Option.some.injEq] at h ⊢
            omega
      · simp only [if_neg h0]
        by_cases h1 : b%3=1
        · simp only [if_pos h1]
          by_cases ha : a=0
          · simp [ha]
          · simp only [if_neg ha]
            have hs : b/3<b := by omega
            have h:=ih (b/3) hs (a-1)
            cases hd : digitCode (a-1) (b/3) with
            | none =>
              cases he : excessMass (a-1) (b/3) with
              | none => simp [hd,he]
              | some v => simp [hd,he] at h
            | some p =>
              rcases p with ⟨aa,c⟩
              cases he : excessMass (a-1) (b/3) with
              | none => simp [hd,he] at h
              | some v =>
                simp only [hd,he,Option.map_some,Option.some.injEq] at h ⊢
                omega
        · simp only [if_neg h1]
          by_cases ha : a=0
          · subst a
            simp only [if_pos rfl]
            have hs : b/3<b := by omega
            have h:=ih (b/3) hs 0
            cases hd : digitCode 0 (b/3) with
            | none =>
              cases he : excessMass 0 (b/3) with
              | none => simp [hd,he]
              | some v => simp [hd,he] at h
            | some p =>
              rcases p with ⟨aa,c⟩
              cases he : excessMass 0 (b/3) with
              | none => simp [hd,he] at h
              | some v =>
                simp only [hd,he,Option.map_some,Option.some.injEq] at h ⊢
                simp only [ite_true,Option.map_some,Option.some.injEq] at h ⊢
                omega
          · simp only [if_neg ha]
            have hs : b/3+1<b := by omega
            have h:=ih (b/3+1) hs (a-1)
            cases hd : digitCode (a-1) (b/3+1) with
            | none =>
              cases he : excessMass (a-1) (b/3+1) with
              | none => simp [hd,he]
              | some v => simp [hd,he] at h
            | some p =>
              rcases p with ⟨aa,c⟩
              cases he : excessMass (a-1) (b/3+1) with
              | none => simp [hd,he] at h
              | some v =>
                simp only [hd,he,Option.map_some,Option.some.injEq] at h ⊢
                omega

/-- Original-source complete-drain mass equation; the exact excess is
determined solely by the two input counters, irrespective of d. -/
theorem drainB_exact_joint_mass (a b d aa dd : Nat)
    (h : drainB a b d = some (.D aa dd)) :
    ∃ e : Nat, excessMass a b = some e ∧ aa+dd=a+d+3*b+e := by
  obtain ⟨c,hc,hdd⟩ := drainB_charge_witness a b d aa dd h
  have hi := code_mass b a
  rw [hc] at hi
  cases he : excessMass a b with
  | none => simp [he] at hi
  | some e =>
    simp only [he, Option.map_some, Option.some.injEq] at hi
    exact ⟨e,rfl,by omega⟩

#print axioms code_mass
#print axioms drainB_exact_joint_mass
end BB6.Agent8DigitChargeSource
