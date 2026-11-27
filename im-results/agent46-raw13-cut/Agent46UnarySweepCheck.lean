import Agent46AutoPump2

set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Auto2.UnarySweep
open BB6Coverage Agent31Pump Agent50Zipper Auto2
open BB6Coverage.Agent31Pump.Auto (rep_add)

def P : List Bool := [false,true]
def B : List Bool := [false,true,false,true]
def mark : List Bool := [true,true]
def tail (b : Bool) : List Bool := if b then [true,true,true] else [true]
def frame (l : List Bool) (i j : Nat) (b : Bool) : Z0 :=
  ⟨5,l,P ++ rep B i ++ mark ++ rep P j ++ tail b⟩
def moveIn (l : List Bool) (b : Bool) : PZ :=
  ⟨5,.lit l,.periodic P B false (.periodic (mark++P) P true (.lit (tail b)))⟩
def moveOut (l : List Bool) (b : Bool) : PZ :=
  ⟨5,.lit l,.periodic (P++B) B false (.periodic mark P true (.lit (tail b)))⟩
def endIn (l : List Bool) (b : Bool) : PZ :=
  ⟨5,.lit l,.periodic P B false (.lit (mark++tail b))⟩
def endOut (l : List Bool) (b : Bool) : PZ :=
  ⟨5,.lit l,.periodic (P++mark++rep P 3) B false (.lit (tail (!b)))⟩
structure Macro where
  ops : List Action
  a : Nat
  b : Nat
  c : Nat

def macroCert (f g : PZ) (m : Macro) : Auto2.Cert := ⟨f,g,m.ops,m.a,m.b,m.c⟩
structure Cert where
  left : List Bool
  entry : Nat
  seed : Nat
  move : Bool → Macro
  finish : Bool → Macro
structure Checked (p : PartialMachine) (c : Cert) : Prop where
  seed : run0 p c.entry ⟨0,[],[]⟩ = some (frame c.left 0 c.seed false)
  move : ∀ b : Bool, 0 < (c.move b).c ∧ check p (macroCert (moveIn c.left b) (moveOut c.left b) (c.move b)) = true
  finish : ∀ b : Bool, 0 < (c.finish b).c ∧ check p (macroCert (endIn c.left b) (endOut c.left b) (c.finish b)) = true

theorem repB (n : Nat) : rep B n = rep P (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rep,ih,show 2*(n+1)=2+2*n by omega,← rep_add]
    rfl

theorem live (p : PartialMachine) (c : Cert) (h : Checked p c) (i j : Nat) (b : Bool) :
    ∃ t i' j' b', 0<t ∧ run0 p t (frame c.left i j b) = some (frame c.left i' j' b') := by
  cases j with
  | zero =>
    have hr := Auto2.sound p _ (h.finish b).2 i 0
    refine ⟨(c.finish b).a*i+(c.finish b).b*0+(c.finish b).c,0,2*i+3,!b,by have := (h.finish b).1; omega,?_⟩
    simpa [macroCert,endIn,endOut,PZ.eval,Word.eval,frame,repB,rep,List.append_assoc] using hr
  | succ j =>
    have hr := Auto2.sound p _ (h.move b).2 i j
    refine ⟨(c.move b).a*i+(c.move b).b*j+(c.move b).c,i+1,j,b,by have := (h.move b).1; omega,?_⟩
    simpa [macroCert,moveIn,moveOut,PZ.eval,Word.eval,frame,rep,List.append_assoc] using hr

theorem never (p : PartialMachine) (c : Cert) (h : Checked p c)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  have arbitrary : ∀ k : Nat, ∃ t i j b, k ≤ t ∧ run0 p t ⟨0,[],[]⟩ = some (frame c.left i j b) := by
    intro k
    induction k with
    | zero => exact ⟨c.entry,0,c.seed,false,by omega,h.seed⟩
    | succ k ih =>
      obtain ⟨t,i,j,b,ht,hr⟩ := ih
      obtain ⟨d,i',j',b',hd,hs⟩ := live p c h i j b
      exact ⟨t+d,i',j',b',by omega,join0 hr hs⟩
  intro n
  obtain ⟨t,i,j,b,ht,hr⟩ := arbitrary n
  have hz : (zrun p t start).map project = some (frame c.left i j b) := (run_project p t start).trans hr
  cases he : zrun p t start with
  | none => simp [he] at hz
  | some z =>
    have H := zrun_sound p m hm t start z he
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he' : run m n blank with
    | none => simp [he'] at H
    | some c => rfl
#print axioms never
end BB6Coverage.Agent31Pump.Auto2.UnarySweep
