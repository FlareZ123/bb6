import TwoSidedGuard
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent6NatTape
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent6PadGrowth BB6.Agent6TwoSidedGuard BB6Coverage.Agent50Zipper BB6Coverage.Agent10ZipAudit

def value : List Bool → Nat
  | [] => 0
  | b::t => b.toNat+2*value t

def head (n : Nat) : Bool := n % 2 == 1
def push (b : Bool) (n : Nat) : Nat := b.toNat+2*n

theorem value_head (l : List Bool) : head (value l) = l.headD false := by
  cases l with
  | nil => rfl
  | cons b t => cases b <;> simp [head,value,Bool.toNat]
theorem value_tail (l : List Bool) : value l / 2 = value l.tail := by
  cases l with
  | nil => rfl
  | cons b t => cases b <;> simp [value,Bool.toNat] <;> omega

structure N1 where
  q : Fin 6
  l : Nat
  r : Nat
  deriving DecidableEq

def encode (z : Z1) : N1 := ⟨z.q,value z.l,value z.r⟩
def moveN (mv : Move) (z : N1) : N1 :=
  if mv.right then ⟨mv.next,push mv.write z.l,z.r/2⟩
  else ⟨mv.next,z.l/2,push (head z.l) (push mv.write (z.r/2))⟩
def stepN (p : PartialMachine) (z : N1) : Option N1 :=
  ((p (z.q,head z.r)).bind id).map (fun mv => moveN mv z)
def runN (p : PartialMachine) : Nat → N1 → Option N1 :=
  Nat.rec (fun z => some z) (fun _ rec z => (stepN p z).bind rec)

theorem move_encode (mv : Move) (z : Z1) : encode (move1 mv z) = moveN mv (encode z) := by
  cases hd : mv.right <;> simp [move1,moveN,hd,encode,push,value,value_head,value_tail]
theorem step_encode (p : PartialMachine) (z : Z1) : stepN p (encode z) = (step1 p z).map encode := by
  unfold stepN step1
  have hhead : head (encode z).r = z.r.headD false := value_head z.r
  rw [hhead]
  change (((p (z.q,z.r.headD false)).bind id).map (fun mv => moveN mv (encode z))) =
    (((p (z.q,z.r.headD false)).bind id).map (fun mv => move1 mv z)).map encode
  cases hm : (p (z.q,z.r.headD false)).bind id with
  | none => rfl
  | some mv => exact congrArg some (move_encode mv z).symm

theorem run_encode (p : PartialMachine) (n : Nat) (z : Z1) : runN p n (encode z) = (run1 p n z).map encode := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    change (stepN p (encode z)).bind (runN p n) = _
    rw [step_encode,run1]
    cases hs : step1 p z with
    | none => rfl
    | some t => exact ih t

theorem runN_join {p : PartialMachine} {n k : Nat} {a b c : N1}
    (h : runN p n a = some b) (g : runN p k b = some c) : runN p (n+k) a = some c := by
  induction n generalizing a with
  | zero => have h' : a = b := Option.some.inj h; subst a; simpa using g
  | succ n ih =>
    change (stepN p a).bind (runN p n) = some b at h
    rw [Nat.succ_add]
    change (stepN p a).bind (runN p (n+k)) = some c
    cases hs : stepN p a with
    | none => simp [hs] at h
    | some t => exact ih (by simpa [hs] using h)

/-- Arbitrarily long successful natural-tape runs imply original nonhalting. -/
theorem never_of_nat_growth (p : PartialMachine) (family : Nat → N1) (entry : Nat) (cost : Nat → Nat)
    (first : runN p entry ⟨0,0,0⟩ = some (family 0)) (positive : ∀ k, 0 < cost k)
    (growth : ∀ k, runN p (cost k) (family k) = some (family (k+1)))
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  have arbitrary (k : Nat) : ∃ t, k ≤ t ∧ runN p t ⟨0,0,0⟩ = some (family k) := by
    induction k with
    | zero => exact ⟨entry,by omega,first⟩
    | succ k ih =>
      obtain ⟨t,ht,hr⟩ := ih
      have hp := positive k
      exact ⟨t+cost k,by omega,runN_join hr (growth k)⟩
  intro n
  obtain ⟨t,ht,hr⟩ := arbitrary n
  have H := run_encode p t ⟨0,[],[]⟩
  change runN p t ⟨0,0,0⟩ = _ at H
  rw [hr] at H
  cases hz : run1 p t ⟨0,[],[]⟩ with
  | none => simp [hz] at H
  | some z =>
    obtain ⟨u,hu,he⟩ := run1_embed p t hz
    have hu' : Reach p t ⟨0,[],[]⟩ (embed1 z) := by
      apply padRun ⟨u,hu,he⟩ _ (eqZ_refl _)
      exact ⟨rfl,by intro i; cases i <;> rfl,fun _ => rfl⟩
    obtain ⟨v,hv,_⟩ := hu'
    have hzz := (run_project p t start).trans hv
    cases h : zrun p t start with
    | none => simp [h] at hzz
    | some zz =>
      have H := zrun_sound p m hm t start zz h
      rw [start_embed] at H
      cases he : run m n blank with
      | none =>
        have H' : run m (n+(t-n)) blank = some (embed zz) := by rwa [show n+(t-n)=t by omega]
        rw [run_append,he] at H'; contradiction
      | some c => rfl

#print axioms never_of_nat_growth
end BB6.Agent6NatTape
