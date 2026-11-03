import FastSectionDef
import GenericSection
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0
namespace BB6.Agent1M8
open BB6.Agent46

/-- Structural fuel evaluator. At least c+1 fuel is sufficient for each bounce. -/
def bounceFuel : Nat → Nat → Nat → Nat × Option (Nat × Nat)
 | 0, _, _ => (0, none)
 | fuel+1,k,c =>
    if c<4 then (0,none)
    else if k%2=1 then
      if c≤2*k+6 then (c,some (2*k+6-c,c))
      else
        let out := bounceFuel fuel (2*k+3) (c-(2*k+3))
        (2*k+4+out.1,out.2)
    else if c=4 then (2,some (2*k+2,3))
    else if c=5 then (2,none)
    else if c≤2*k+8 then (c-3,some (2*k+8-c,c-1))
    else
      let out := bounceFuel fuel (2*k+4) (c-(2*k+5))
      (2*k+3+out.1,out.2)

/-- The fast evaluator agrees with the original, unmodified well-founded source
    for every input and every positive fuel strictly above c. -/
theorem bounceFuel_eq (k c fuel : Nat) (hc : c<fuel) :
    bounceFuel fuel k c = bounce k c := by
  induction c using Nat.strongRecOn generalizing k fuel with
  | ind c ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [bounce.eq_1]
      simp only [bounceFuel]
      by_cases h4 : c<4
      · simp [h4]
      · simp only [if_neg h4]
        by_cases ho : k%2=1
        · simp only [if_pos ho]
          by_cases hs : c≤2*k+6
          · simp only [if_pos hs]
          · simp only [if_neg hs]
            have hlt : c-(2*k+3)<c := by omega
            have hbound : c-(2*k+3)<fuel := by omega
            rw [ih (c-(2*k+3)) hlt (2*k+3) fuel hbound]
        · simp only [if_neg ho]
          by_cases hc4 : c=4
          · simp only [if_pos hc4]
          · simp only [if_neg hc4]
            by_cases hc5 : c=5
            · simp only [if_pos hc5]
            · simp only [if_neg hc5]
              by_cases hs : c≤2*k+8
              · simp only [if_pos hs]
              · simp only [if_neg hs]
                have hlt : c-(2*k+5)<c := by omega
                have hbound : c-(2*k+5)<fuel := by omega
                rw [ih (c-(2*k+5)) hlt (2*k+4) fuel hbound]

def bounceFast (k c : Nat) : Nat × Option (Nat × Nat) := bounceFuel (c+1) k c
theorem bounceFast_eq_bounce (k c : Nat) : bounceFast k c = bounce k c :=
  bounceFuel_eq k c (c+1) (by omega)

def fastExactSection (p : Nat × Nat) : Nat × Option (Nat × Nat) :=
  let (a,k) := p
  if a=0 then
    if k=0 then (2,none)
    else if k=1 then (4,some (0,4))
    else
      let b := bounceFast 1 (2*k+1)
      (2+b.1,b.2)
  else if a=1 then
    if k=0 then (2,some (5,1))
    else if k=1 then (2,some (2,3))
    else if k=2 then (3,some (2,5))
    else if k=3 then (5,some (0,7))
    else
      let b := bounceFast 4 (2*k-3)
      (3+b.1,b.2)
  else if k=0 then (2,some (a-2,2))
  else if 2*k≤a then (2*k+1,some (a-2*k,2*k+2))
  else
    let b := bounceFast (a-1) (2*k-a+3)
    (a-1+b.1,b.2)


theorem fastExact_eq_original (p : Nat × Nat) :
    fastExactSection p = exactSection p := by
  rcases p with ⟨a,k⟩
  simp only [fastExactSection,exactSection]
  simp only [bounceFast_eq_bounce]

def fastNext (p : Nat × Nat) : Option (Nat × Nat) := (fastExactSection p).2
theorem fastNext_eq_original (p : Nat × Nat) : fastNext p = secNext p := by
  simpa only [fastNext,secNext] using congrArg Prod.snd (fastExact_eq_original p)

/-- An efficient head-recursive runner, definitionally reducible in the kernel. -/
def runFast : Nat → Option (Nat × Nat) → Option (Nat × Nat)
  | 0, s => s
  | n+1, s => runFast n (s.bind fastNext)

theorem runFast_none (n : Nat) : runFast n none = none := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [runFast] using ih

theorem runFast_add (n m : Nat) (s : Option (Nat × Nat)) :
    runFast (n+m) s = runFast m (runFast n s) := by
  induction n generalizing s with
  | zero => simp [runFast]
  | succ n ih =>
      rw [Nat.succ_add]
      change runFast (n+m) (s.bind fastNext) =
        runFast m (runFast n (s.bind fastNext))
      exact ih (s.bind fastNext)

theorem runFast_eq_source (n : Nat) (s : Option (Nat × Nat)) :
    runFast n s = BB6.Agent8Section.run secNext n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      change runFast n (s.bind fastNext) = _
      rw [show fastNext = secNext from funext fastNext_eq_original]
      rw [BB6.Agent8Section.run_succ_head]
      exact ih (s.bind secNext)

def verify : Nat → Option (Nat × Nat) → (Nat × Nat) → Bool × Option (Nat × Nat)
  | 0, s, _ => (true,s)
  | n+1, none, _ => (true,none)
  | n+1, some p, target =>
      let child := verify n (fastNext p) target
      (decide (p ≠ target) && child.1, child.2)

/-- Kernel-checkable safe prefix plus precise endpoint. -/
theorem verify_sound (n : Nat) (s : Option (Nat × Nat)) (target : Nat × Nat)
    (h : (verify n s target).1 = true) :
    (∀ i, i < n → runFast i s ≠ some target) ∧
      (verify n s target).2 = runFast n s := by
  induction n generalizing s with
  | zero =>
      constructor
      · intro i hi; omega
      · simp [verify,runFast]
  | succ n ih =>
      cases s with
      | none =>
          constructor
          · intro i _; simp [runFast_none]
          · simp [verify,runFast_none]
      | some p =>
          have hboth : (decide (p ≠ target) &&
              (verify n (fastNext p) target).1) = true := by
            simpa only [verify] using h
          have hpair : p ≠ target ∧ (verify n (fastNext p) target).1 = true := by
            simpa using hboth
          obtain ⟨hgood, hfinish⟩ := ih (fastNext p) hpair.2
          constructor
          · intro i hi
            cases i with
            | zero =>
                change some p ≠ some target
                intro hp
                exact hpair.1 (Option.some.inj hp)
            | succ j =>
                have hj : j < n := by omega
                simpa only [runFast,Option.bind_some] using hgood j hj
          · simpa only [verify,runFast,Option.bind_some] using hfinish

def chainTotal : List (Nat × (Nat × Nat)) → Nat
  | [] => 0
  | (n,_)::tl => n + chainTotal tl

def chainEnd : List (Nat × (Nat × Nat)) → Option (Nat × Nat) → Option (Nat × Nat)
  | [],s => s
  | (_,p)::tl,_ => chainEnd tl (some p)

def chainCheck : List (Nat × (Nat × Nat)) → Option (Nat × Nat) → (Nat × Nat) → Bool
  | [],_,_ => true
  | (n,p)::tl,s,t =>
      (verify n s t).1 && ((verify n s t).2 == some p) && chainCheck tl (some p) t

theorem chain_sound (steps : List (Nat × (Nat × Nat)))
    (s : Option (Nat × Nat)) (target : Nat × Nat)
    (h : chainCheck steps s target = true) :
    (∀ i, i < chainTotal steps → runFast i s ≠ some target) ∧
      runFast (chainTotal steps) s = chainEnd steps s := by
  induction steps generalizing s with
  | nil =>
      constructor
      · intro i hi; simp [chainTotal] at hi
      · simp [chainTotal,chainEnd,runFast]
  | cons hd tl ih =>
      obtain ⟨n,p⟩ := hd
      have hp : ((verify n s target).1 = true ∧
        (verify n s target).2 = some p) ∧ chainCheck tl (some p) target = true := by
        simpa [chainCheck] using h
      obtain ⟨hseg, hseg_end⟩ := verify_sound n s target hp.1.1
      have hrun : runFast n s = some p := hseg_end.symm.trans hp.1.2
      obtain ⟨htail, htail_end⟩ := ih (some p) hp.2
      constructor
      · intro i hi
        by_cases hsmall : i < n
        · exact hseg i hsmall
        · have hoff : i-n < chainTotal tl := by simp only [chainTotal] at hi; omega
          have hid : i=n+(i-n) := by omega
          rw [hid,runFast_add,hrun]
          exact htail (i-n) hoff
      · simp only [chainTotal,chainEnd]
        rw [runFast_add,hrun]
        exact htail_end

theorem chainEnd_append (xs ys : List (Nat × (Nat × Nat)))
    (s : Option (Nat × Nat)) :
    chainEnd (xs++ys) s = chainEnd ys (chainEnd xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons hd xs ih =>
      rcases hd with ⟨n,p⟩
      simpa only [List.cons_append,chainEnd] using ih (some p)

theorem chainCheck_append (xs ys : List (Nat × (Nat × Nat)))
    (s : Option (Nat × Nat)) (target : Nat × Nat) :
    chainCheck (xs++ys) s target =
      (chainCheck xs s target && chainCheck ys (chainEnd xs s) target) := by
  induction xs generalizing s with
  | nil => rfl
  | cons hd xs ih =>
      rcases hd with ⟨n,p⟩
      simp only [List.cons_append,chainCheck,chainEnd]
      rw [ih]
      simp only [Bool.and_assoc]

#print axioms bounceFuel_eq
#print axioms runFast_eq_source
#print axioms chain_sound
end BB6.Agent1M8
