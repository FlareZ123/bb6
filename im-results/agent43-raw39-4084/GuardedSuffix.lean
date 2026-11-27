import SweepPumping
namespace BB6.Agent43GuardedSuffix
open BB6Coverage BB6Coverage.Agent31Pump
inductive Side where | left | right
  deriving DecidableEq

def active : Side → Z0 → List Bool
  | .left,z => z.l
  | .right,z => z.r

def appendTail : Side → Z0 → List Bool → Z0
  | .left,z,T => { z with l := z.l ++ T }
  | .right,z,T => { z with r := z.r ++ T }

theorem appendTail_assoc (s : Side) (z : Z0) (T U : List Bool) :
    appendTail s (appendTail s z T) U = appendTail s z (T++U) := by
  cases s <;> cases z <;> simp [appendTail,List.append_assoc]

theorem appendTail_nil (s : Side) (z : Z0) : appendTail s z [] = z := by
  cases s <;> cases z <;> simp [appendTail]

theorem step_tail (p : PartialMachine) (s : Side) (z : Z0) (T : List Bool)
    (h : active s z ≠ []) :
    step0 p (appendTail s z T) = (step0 p z).map (fun z' => appendTail s z' T) := by
  cases z with
  | mk q l r =>
    cases s with
    | left =>
      cases l with
      | nil => exact False.elim (h rfl)
      | cons b l =>
        change ((p (q,b)).bind id).map _ = (((p (q,b)).bind id).map _).map _
        cases hv : ((p (q,b)).bind id) with
        | none => rfl
        | some mv =>
          cases hd : mv.right <;> simp [appendTail,move0,hd]
    | right =>
      cases r with
      | nil => exact False.elim (h rfl)
      | cons b r =>
        change ((p (q,l.headD false)).bind id).map _ = (((p (q,l.headD false)).bind id).map _).map _
        cases hv : ((p (q,l.headD false)).bind id) with
        | none => rfl
        | some mv =>
          cases hd : mv.right <;> simp [appendTail,move0,hd]

def guardedRun (p : PartialMachine) (s : Side) : Nat → Z0 → Option Z0
  | 0,z => some z
  | n+1,z => if active s z = [] then none else (step0 p z).bind (guardedRun p s n)

theorem guardedRun_tail (p : PartialMachine) (s : Side) (n : Nat) (z z' : Z0)
    (T : List Bool) (h : guardedRun p s n z = some z') :
    run0 p n (appendTail s z T) = some (appendTail s z' T) := by
  induction n generalizing z with
  | zero =>
    have hz : z = z' := Option.some.inj h
    subst z'; rfl
  | succ n ih =>
    by_cases he : active s z = []
    · simp [guardedRun,he] at h
    · cases hs : step0 p z with
      | none => simp [guardedRun,he,hs] at h
      | some t =>
        have ht : guardedRun p s n t = some z' := by simpa [guardedRun,he,hs] using h
        rw [run0,step_tail p s z T he,hs]
        exact ih t ht

theorem guardedRun_add (p : PartialMachine) (s : Side) (n k : Nat) (z : Z0) :
    guardedRun p s (n+k) z = (guardedRun p s n z).bind (guardedRun p s k) := by
  induction n generalizing z with
  | zero => simp [guardedRun]
  | succ n ih =>
    rw [show n+1+k=n+k+1 by omega]
    by_cases h : active s z = []
    · simp [guardedRun,h]
    · simp only [guardedRun,h,ite_false]
      cases step0 p z with
      | none => rfl
      | some t => exact ih t

theorem guardedJoin {p : PartialMachine} {s : Side} {n k : Nat} {a b c : Z0}
    (h : guardedRun p s n a = some b) (g : guardedRun p s k b = some c) :
    guardedRun p s (n+k) a = some c := by
  rw [guardedRun_add,h]; exact g

/-- A checked finite prefix run can be replayed in front of any suffix. -/
theorem pump_step (p : PartialMachine) (s : Side) (n : Nat) (z : Z0) (Q T : List Bool)
    (h : guardedRun p s n z = some (appendTail s z Q)) (k : Nat) :
    run0 p n (appendTail s z (rep Q k ++ T)) =
      some (appendTail s z (rep Q (k+1) ++ T)) := by
  have hh := guardedRun_tail p s n z (appendTail s z Q) (rep Q k ++ T) h
  simpa only [appendTail_assoc,rep,List.append_assoc] using hh

theorem never_of_guarded_pump (p : PartialMachine) (s : Side) (entry period : Nat)
    (z : Z0) (Q T : List Bool) (hp : 0 < period)
    (hentry : run0 p entry ⟨0,[],[]⟩ = some (appendTail s z T))
    (hcycle : guardedRun p s period z = some (appendTail s z Q))
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply never_of_growth p (fun k => appendTail s z (rep Q k ++ T)) entry (fun _ => period) _ (fun _ => hp) _ m hm
  · simpa only [rep,List.nil_append] using hentry
  · exact pump_step p s period z Q T hcycle

#print axioms guardedRun_tail
#print axioms pump_step
#print axioms never_of_guarded_pump
end BB6.Agent43GuardedSuffix
