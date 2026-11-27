import Raw40A0RC492Trace
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.A0RC492
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

def paddedStart : BB6Coverage.Agent50Zipper.Z := ⟨0,0,Z 341035,Z 767307⟩

theorem zero_getD (n i : Nat) : (Z n).getD i false = false := by
  rw [List.getD_eq_getElem?_getD]
  change (List.replicate n false)[i]?.getD false = false
  rw [List.getElem?_replicate]
  split <;> rfl

theorem padded_blank : embed paddedStart = blank := by
  unfold embed paddedStart blank
  congr 1
  funext x
  simp only [atCell,zero_getD,ite_self]

def family (k : Nat) : Z0 := ⟨0,[],U (2*(554172+2*k)+1)⟩
def cost (k : Nat) : Nat := 4*(554172+2*k)+9

theorem first : run0 table 497344989939 (project paddedStart) = some (family 0) := by
  have h := join0 entry (oddBlank 554170 [])
  rw [show 497342773250+(4*554170+9)=497344989939 by rfl] at h
  exact h

theorem growth (k : Nat) : run0 table (cost k) (family k) = some (family (k+1)) := by
  simpa only [family,cost,show 2*(554172+2*(k+1))+1=2*(554172+2*k)+5 by omega] using oddBlankEmpty (554172+2*k)

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  have arbitrary : ∀ k, ∃ t, k ≤ t ∧ run0 table t (project paddedStart) = some (family k) := by
    intro k
    induction k with
    | zero => exact ⟨497344989939,by omega,first⟩
    | succ k ih =>
      obtain ⟨t,ht,hr⟩ := ih
      have hp : 0 < cost k := by unfold cost; omega
      exact ⟨t+cost k,by omega,join0 hr (growth k)⟩
  intro n
  obtain ⟨t,ht,hr⟩ := arbitrary n
  have hz : (zrun table t paddedStart).map project = some (family n) :=
    (run_project table t paddedStart).trans hr
  cases h : zrun table t paddedStart with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound table m hm t paddedStart z h
    rw [padded_blank] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms padded_blank
#print axioms first
#print axioms growth
#print axioms never
end BB6.Agent19Raw40.A0RC492
