import PadGrowth
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent6GuardedTail
open BB6Coverage BB6Coverage.Agent31Pump

def appendL (z : Z0) (tail : List Bool) : Z0 := ⟨z.q,z.l++tail,z.r⟩
def guardedStep (p : PartialMachine) (z : Z0) : Option Z0 :=
  if z.l.isEmpty then none else step0 p z

def guardedRun (p : PartialMachine) : Nat → Z0 → Option Z0
  | 0,z => some z
  | n+1,z => (guardedStep p z).bind (guardedRun p n)

theorem guardedStep_append (p : PartialMachine) {z u : Z0} (tail : List Bool)
    (h : guardedStep p z = some u) : step0 p (appendL z tail) = some (appendL u tail) := by
  rcases z with ⟨q,l,r⟩
  cases l with
  | nil => simp [guardedStep] at h
  | cons a l =>
    simp only [guardedStep,List.isEmpty_cons, Bool.false_eq_true,ite_false] at h
    unfold step0 at h ⊢
    change ((p (q,a)).bind id).map (fun mv => move0 mv ⟨q,a::l,r⟩) = some u at h
    change ((p (q,a)).bind id).map (fun mv => move0 mv ⟨q,a::l++tail,r⟩) = some (appendL u tail)
    cases hm : (p (q,a)).bind id with
    | none => simp [hm] at h
    | some mv =>
      simp only [hm,Option.map_some,Option.some.injEq] at h ⊢
      rw [←h]
      cases hd : mv.right <;> simp [move0,appendL,hd,List.cons_append]

theorem guardedRun_append (p : PartialMachine) (n : Nat) {z u : Z0} (tail : List Bool)
    (h : guardedRun p n z = some u) : run0 p n (appendL z tail) = some (appendL u tail) := by
  induction n generalizing z u with
  | zero => simp only [guardedRun,Option.some.injEq] at h; subst u; rfl
  | succ n ih =>
    rw [guardedRun] at h
    rw [run0.eq_2]
    cases hs : guardedStep p z with
    | none => simp [hs] at h
    | some v =>
      rw [hs,Option.bind_some] at h
      rw [guardedStep_append p tail hs,Option.bind_some]
      exact ih h

theorem guardedJoin {p : PartialMachine} {n k : Nat} {a b c : Z0}
    (h : guardedRun p n a = some b) (g : guardedRun p k b = some c) : guardedRun p (n+k) a = some c := by
  induction n generalizing a with
  | zero => simp only [guardedRun,Option.some.injEq] at h; subst a; simpa using g
  | succ n ih =>
    rw [guardedRun] at h
    rw [Nat.succ_add,guardedRun]
    cases hs : guardedStep p a with
    | none => simp [hs] at h
    | some v =>
      rw [hs,Option.bind_some] at h
      simp only [Option.bind_some]
      exact ih h
#print axioms guardedRun_append
#print axioms guardedJoin
end BB6.Agent6GuardedTail
