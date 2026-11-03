import Lean.Elab.Tactic.Omega

namespace BB429Burst

abbrev State := Nat × Nat

def firstStep (s : State) : Option State :=
  if 2*s.1+3 ≤ s.2 then
    some (2*s.1+3, s.2-2*s.1-3)
  else none

def firstRun (n : Nat) (s : State) : Option State :=
  match n with
  | 0 => some s
  | k+1 => (firstRun k s).bind firstStep

/-- Exact source-compatible arithmetic throughout any all-first-branch prefix. -/
theorem prefix_formula (u w n a b : Nat)
    (h : firstRun n (u,w) = some (a,b)) :
    a + 3 = (u+3)*2^n ∧ 2*a+b = 2*u+w+3*n := by
  induction n generalizing a b with
  | zero =>
    simp only [firstRun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    simp
  | succ n ih =>
    simp only [firstRun] at h
    cases hp : firstRun n (u,w) with
    | none => simp [hp] at h
    | some p =>
      simp only [hp, Option.bind_some] at h
      simp only [firstStep] at h
      split at h
      · have hprev := ih p.1 p.2 hp
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨ha,hb⟩ := h
        have hpow : (u+3)*2^(n+1) = 2*((u+3)*2^n) := by
          rw [Nat.pow_succ]
          simp only [Nat.mul_assoc, Nat.mul_comm]
        constructor
        · rw [hpow]
          omega
        · omega
      · simp at h

/-- The exact first-branch guard at the endpoint uses a single exponential comparison. -/
theorem continue_iff_exponential (u w n a b : Nat)
    (h : firstRun n (u,w) = some (a,b)) :
    (2*a+3 ≤ b) ↔ 4*((u+3)*2^n) ≤ 2*u+w+3*n+9 := by
  obtain ⟨ha,hp⟩ := prefix_formula u w n a b h
  omega

/-- Necessary and sufficient exponential equality for an exact halting gateway after a first-branch prefix. -/
theorem gateway_iff_exponential (u w n a b : Nat)
    (h : firstRun n (u,w) = some (a,b)) :
    (b+1=2*a) ↔ 2*u+w+3*n+13 = 4*((u+3)*2^n) := by
  obtain ⟨ha,hp⟩ := prefix_formula u w n a b h
  omega

/-- Exponential guard inequalities are nested: validity of a later first-branch
    attempt implies validity of every earlier attempt. -/
theorem guard_backward (u w n : Nat)
    (h : 4*((u+3)*2^(n+1)) ≤ 2*u+w+3*(n+1)+9) :
    4*((u+3)*2^n) ≤ 2*u+w+3*n+9 := by
  have hpow : 4*((u+3)*2^(n+1)) = 2*(4*((u+3)*2^n)) := by
    rw [Nat.pow_succ]
    simp only [Nat.mul_assoc, Nat.mul_comm]
  have hlarge : 3 ≤ 4*((u+3)*2^n) := by
    have htwo : 0 < 2^n := Nat.pow_pos (by omega)
    have hprod : 0 < (u+3)*2^n := Nat.mul_pos (by omega) htwo
    omega
  rw [hpow] at h
  omega

/-- Exact O(log w) burst membership test: n+1 successful first-branch steps
    are possible precisely when the last exponential guard inequality holds. -/
theorem prefix_exists_iff (u w n : Nat) :
    (∃ a b, firstRun (n+1) (u,w) = some (a,b)) ↔
    4*((u+3)*2^n) ≤ 2*u+w+3*n+9 := by
  induction n with
  | zero =>
    constructor
    · rintro ⟨a,b,h⟩
      change firstStep (u,w) = some (a,b) at h
      simp only [firstStep] at h
      split at h
      · omega
      · simp at h
    · intro hg
      have hf : 2*u+3 ≤ w := by omega
      refine ⟨2*u+3,w-2*u-3,?_⟩
      simp [firstRun,firstStep,hf]
  | succ n ih =>
    constructor
    · rintro ⟨a,b,h⟩
      change (firstRun (n+1) (u,w)).bind firstStep = some (a,b) at h
      cases hp : firstRun (n+1) (u,w) with
      | none => simp [hp] at h
      | some p =>
        simp only [hp, Option.bind_some] at h
        simp only [firstStep] at h
        split at h
        · exact (continue_iff_exponential u w (n+1) p.1 p.2 hp).mp (by assumption)
        · simp at h
    · intro hg
      have hprev := guard_backward u w n hg
      obtain ⟨a,b,hp⟩ := ih.mpr hprev
      have hcont : 2*a+3 ≤ b :=
        (continue_iff_exponential u w (n+1) a b hp).mpr hg
      refine ⟨2*a+3,b-2*a-3,?_⟩
      change (firstRun (n+1) (u,w)).bind firstStep = some (2*a+3,b-2*a-3)
      simp [hp,firstStep,hcont]

/-- Exact sparse exponential parametrization of *every* seed whose
    first-branch burst ends on the halting gateway. -/
theorem burst_gateway_iff (u w : Nat) :
    (∃ n a b, firstRun n (u,w) = some (a,b) ∧ b+1=2*a) ↔
    (∃ n, 2*u+w+3*n+13=4*((u+3)*2^n)) := by
  constructor
  · rintro ⟨n,a,b,hp,hg⟩
    exact ⟨n,(gateway_iff_exponential u w n a b hp).mp hg⟩
  · rintro ⟨n,he⟩
    cases n with
    | zero =>
      have hg : w+1=2*u := by
        simp only [Nat.pow_zero, Nat.mul_one] at he
        omega
      exact ⟨0,u,w,rfl,hg⟩
    | succ k =>
      have hpow : 4*((u+3)*2^(k+1)) = 2*(4*((u+3)*2^k)) := by
        rw [Nat.pow_succ]
        simp only [Nat.mul_assoc, Nat.mul_comm]
      have htwo : 0 < 2^k := Nat.pow_pos (by omega)
      have hprod : 0 < (u+3)*2^k := Nat.mul_pos (by omega) htwo
      have hlarge : 7 ≤ 4*((u+3)*2^k) := by
        omega
      have hguard : 4*((u+3)*2^k) ≤ 2*u+w+3*k+9 := by
        rw [hpow] at he
        omega
      obtain ⟨a,b,hp⟩ := (prefix_exists_iff u w k).mpr hguard
      exact ⟨k+1,a,b,hp,
        (gateway_iff_exponential u w (k+1) a b hp).mpr he⟩

/-- At the gateway all first-branch steps have already ended. -/
theorem gateway_exits (a b : Nat) (h : b+1=2*a) :
    firstStep (a,b) = none := by
  simp [firstStep]
  omega

#print axioms prefix_formula
#print axioms continue_iff_exponential
#print axioms gateway_iff_exponential
#print axioms guard_backward
#print axioms prefix_exists_iff
#print axioms burst_gateway_iff
#print axioms gateway_exits

end BB429Burst
