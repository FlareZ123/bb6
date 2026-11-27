import CrossingBank
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent42Crossing
open BB6Coverage Agent50Zipper

theorem embed_congr (a b : Z) (hq : a.q=b.q) (hh : a.h=b.h)
    (hl : ∀ i, a.l.getD i false = b.l.getD i false)
    (hr : ∀ i, a.r.getD i false = b.r.getD i false) : embed a = embed b := by
  unfold embed
  rw [hq,hh]
  congr 1
  funext x
  simp only [atCell,hh,hl,hr]

def family (c : Certificate) (h : Int) (n : Nat) : Config :=
  embed ⟨0,h,[],(expand n c.right).map Cell.bit⟩

def inputBlank (c : Certificate) : Prop := padEq (c.head.bit::c.left.map Cell.bit) [] = true
instance inputBlankDec (c : Certificate) : Decidable (inputBlank c) := by
  unfold inputBlank; infer_instance

def recOK (c : Certificate) : Prop :=
  match fixedGoal c with
  | none => False
  | some f => f.q=0 ∧ padEq f.l [] = true ∧
      exprEq (normalize Cell.bit 1 [] c.right) (normalize Cell.out 0 f.r c.right)

instance recDec (c : Certificate) : Decidable (recOK c) :=
  match h : fixedGoal c with
  | none => by simp only [recOK,h]; infer_instance
  | some f => by simp only [recOK,h]; infer_instance

def entryOK (p : PartialMachine) (c : Certificate) (entry : Nat) (h : Int) : Prop :=
  match zrun p entry ⟨0,0,[],[]⟩ with
  | none => False
  | some z => z.q=0 ∧ z.h=h ∧ padEq z.l []=true ∧
      padEq z.r ((expand 0 c.right).map Cell.bit)=true

instance entryDec (p : PartialMachine) (c : Certificate) (entry : Nat) (h : Int) : Decidable (entryOK p c entry h) :=
  match he : zrun p entry ⟨0,0,[],[]⟩ with
  | none => by simp only [entryOK,he]; infer_instance
  | some z => by simp only [entryOK,he]; infer_instance

def checked (p : PartialMachine) (c : Certificate) (entry : Nat) (h : Int) : Prop :=
  certOK p c ∧ c.head.events ≠ [] ∧ inputBlank c ∧ recOK c ∧ entryOK p c entry h

instance checkedDec (p : PartialMachine) (c : Certificate) (entry : Nat) (h : Int) : Decidable (checked p c entry h) := by
  unfold checked; infer_instance

theorem view_family (c : Certificate) (hc : inputBlank c) (h : Int) (n : Nat) :
    embed (view (script c h n)) = family c h n := by
  apply embed_congr (view (script c h n)) (⟨0,h,[],(expand n c.right).map Cell.bit⟩ : Z) rfl rfl
  · exact padEq_sound _ _ hc
  · intro i; rfl

theorem entry_sound (p : PartialMachine) (c : Certificate) (entry : Nat) (h : Int)
    (he : entryOK p c entry h) (m : Machine) (hm : compatible p m) :
    run m entry blank = some (family c h 0) := by
  cases hz : zrun p entry ⟨0,0,[],[]⟩ with
  | none => simp [entryOK,hz] at he
  | some z =>
    simp only [entryOK,hz] at he
    have hstart : embed ⟨0,0,[],[]⟩ = blank := by
      unfold embed blank
      congr 1
      funext x
      simp [atCell]
    have hf : embed z = family c h 0 :=
      embed_congr _ _ he.1 he.2.1 (padEq_sound _ _ he.2.2.1) (padEq_sound _ _ he.2.2.2)
    have H := zrun_sound p m hm entry ⟨0,0,[],[]⟩ z hz
    rwa [hstart,hf] at H

theorem recurrence (p : PartialMachine) (c : Certificate) (hc : certOK p c)
    (hn : c.head.events ≠ []) (hb : inputBlank c) (hr : recOK c)
    (m : Machine) (hm : compatible p m) (h : Int) (n : Nat) :
    ∃ k j, 0<k ∧ run m k (family c h n) = some (family c j (n+1)) := by
  cases hf : fixedGoal c with
  | none => simp [recOK,hf] at hr
  | some f =>
    simp only [recOK,hf] at hr
    obtain ⟨k,z,ht,hg,hz⟩ := sound p (script c h n) (script_ok p c hc h n)
    have hp : 0<k := by
      have he : 0<c.head.events.length := by
        cases he : c.head.events with
        | nil => contradiction
        | cons e es => simp
      simp [remaining,script] at ht
      omega
    have hgoal := goal_script c f hf h n
    rw [hgoal] at hg
    have hzeq : z = {f with h := f.h+h, r := f.r ++ (expand n c.right).map Cell.out} :=
      (Option.some.inj hg).symm
    have hw : ∀ i, (f.r ++ (expand n c.right).map Cell.out).getD i false =
        ((expand (n+1) c.right).map Cell.bit).getD i false := by
      intro i
      have H := exprEq_sound _ _ hr.2.2 n i
      rw [normalize_sound,normalize_sound] at H
      simpa [Nat.add_comm] using H.symm
    have hemb : embed z = family c (f.h+h) (n+1) := by
      rw [hzeq]
      exact embed_congr _ _ hr.1 rfl (padEq_sound _ _ hr.2.1) hw
    have H := zrun_sound p m hm k _ z hz
    rw [view_family c hb h n,hemb] at H
    exact ⟨k,f.h+h,hp,H⟩

/-- A finite checked script bank, with exact parametric word identity, proves
    every completion of the sparse table nonhalting from the original blank. -/
theorem never (p : PartialMachine) (c : Certificate) (entry : Nat) (h : Int)
    (hc : checked p c entry h) (m : Machine) (hm : compatible p m) : NeverHalts m := by
  obtain ⟨hcert,hn,hb,hr,he⟩ := hc
  have arbitrarily : ∀ n, ∃ k j, n≤k ∧ run m k blank = some (family c j n) := by
    intro n
    induction n with
    | zero => exact ⟨entry,h,by omega,entry_sound p c entry h he m hm⟩
    | succ n ih =>
      obtain ⟨k,j,hk,h1⟩ := ih
      obtain ⟨cost,j',hp,h2⟩ := recurrence p c hcert hn hb hr m hm j n
      exact ⟨k+cost,j',by omega,by rw [run_append,h1]; exact h2⟩
  intro n
  obtain ⟨k,j,hk,h1⟩ := arbitrarily n
  rw [show k=n+(k-n) by omega,run_append] at h1
  cases hh : run m n blank with
  | none => simp [hh] at h1
  | some z => rfl

#print axioms never
end BB6Coverage.Agent42Crossing
