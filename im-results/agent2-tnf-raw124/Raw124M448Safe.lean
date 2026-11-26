import Raw124Transient

import Raw108LBSplit1930Kid0

import Raw108LBSplit1930Kid3

import Raw108LBSplit1930Kid6

import Raw108LBSplit1930Kid7

import Raw108LBSplit1930Kid9

import Raw108LBSplit1930Kid11

import Raw108LBSplit1930Kid12

import Raw108LBSplit1930Kid13

import Raw108LBSplit1930Kid15

import Raw108LBSplit1930Kid17

import Raw108LBSplit1930Kid18

import Raw108LBSplit1930Kid19

import Raw108LBSplit1930Kid21

import Raw108LBSplit1930Kid23

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent4.Raw124M448
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6Coverage.Agent10ZipAudit


open BB6.Agent4.Raw124Transient
def table : PartialMachine := new none
theorem root_read : zipRead table 91502 = some (0,true) :=
  read_transfer none (by simp [safe]) 91502 (0,true) (by decide) (by decide) BB6.Agent10Raw108Long.read_entry
def kid (mv : Move) : PartialMachine := new (some (some mv))
theorem kid_eq (mv : Move) : refine table (0,true) (some mv) = kid mv := by
  funext s; rcases s with ⟨q,b⟩
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
theorem safe_of (mv : Move) (h : mv.next=4 → mv.right=true ∧ mv.write=true) : safe (some (some mv)) := by
  intro x hx; have hx' : mv=x := Option.some.inj (Option.some.inj hx)
  subst x; exact h

def mv0 : Move := ⟨false,false,0⟩

theorem safe0 : safe (some (some mv0)) := safe_of mv0 (by decide)

theorem old_eq0 : old (some (some mv0)) = BB6.Agent10Raw108LBSplit1930Kid0.table := tableOK_sound _ _ (by decide)
theorem never0 (m : Machine) (hm : compatible (kid mv0) m) : NeverHalts m := by
  apply never_transfer _ safe0 _ m hm
  rw [old_eq0]
  exact BB6.Agent10Raw108LBSplit1930Kid0.never

def mv1 : Move := ⟨false,false,1⟩

theorem safe1 : safe (some (some mv1)) := safe_of mv1 (by decide)

theorem read1 : zipRead (kid mv1) 4136170 = some (2,true) :=
  read_transfer _ safe1 4136170 (2,true) (by decide) (by decide) BB6.Agent10Raw108Long.read_kid1
theorem checked1 : zipCheck 4136175 (kid mv1) (.last 4136170 (2,true)) = true := by
  have hh : kid mv1 (2,true) = none := by decide
  have hw : weightOK (kid mv1) (2,true) 4136170 4136175 = true := by decide
  have hr : restOK (kid mv1) (2,true) = true := by decide
  rw [zipCheck.eq_1]
  simp only [zipQueryOK,read1,hh,hw,hr,decide_true,Bool.and_self]

def mv2 : Move := ⟨false,false,2⟩

theorem safe2 : safe (some (some mv2)) := safe_of mv2 (by decide)

theorem read2 : zipRead (kid mv2) 91503 = some (2,true) :=
  read_transfer _ safe2 91503 (2,true) (by decide) (by decide) BB6.Agent10Raw108Long.read_short2
theorem checked2 : zipCheck 4136175 (kid mv2) (.last 91503 (2,true)) = true := by
  have hh : kid mv2 (2,true) = none := by decide
  have hw : weightOK (kid mv2) (2,true) 91503 4136175 = true := by decide
  have hr : restOK (kid mv2) (2,true) = true := by decide
  rw [zipCheck.eq_1]
  simp only [zipQueryOK,read2,hh,hw,hr,decide_true,Bool.and_self]

def mv3 : Move := ⟨false,false,3⟩

theorem safe3 : safe (some (some mv3)) := safe_of mv3 (by decide)

theorem old_eq3 : old (some (some mv3)) = BB6.Agent10Raw108LBSplit1930Kid3.table := tableOK_sound _ _ (by decide)
theorem never3 (m : Machine) (hm : compatible (kid mv3) m) : NeverHalts m := by
  apply never_transfer _ safe3 _ m hm
  rw [old_eq3]
  exact BB6.Agent10Raw108LBSplit1930Kid3.never

def mv4 : Move := ⟨false,false,4⟩

def mv5 : Move := ⟨false,false,5⟩

theorem safe5 : safe (some (some mv5)) := safe_of mv5 (by decide)

theorem read5 : zipRead (kid mv5) 4136170 = some (2,true) :=
  read_transfer _ safe5 4136170 (2,true) (by decide) (by decide) BB6.Agent10Raw108Long.read_kid5
theorem checked5 : zipCheck 4136175 (kid mv5) (.last 4136170 (2,true)) = true := by
  have hh : kid mv5 (2,true) = none := by decide
  have hw : weightOK (kid mv5) (2,true) 4136170 4136175 = true := by decide
  have hr : restOK (kid mv5) (2,true) = true := by decide
  rw [zipCheck.eq_1]
  simp only [zipQueryOK,read5,hh,hw,hr,decide_true,Bool.and_self]

def mv6 : Move := ⟨false,true,0⟩

theorem safe6 : safe (some (some mv6)) := safe_of mv6 (by decide)

theorem old_eq6 : old (some (some mv6)) = BB6.Agent10Raw108LBSplit1930Kid6.table := tableOK_sound _ _ (by decide)
theorem never6 (m : Machine) (hm : compatible (kid mv6) m) : NeverHalts m := by
  apply never_transfer _ safe6 _ m hm
  rw [old_eq6]
  exact BB6.Agent10Raw108LBSplit1930Kid6.never

def mv7 : Move := ⟨false,true,1⟩

theorem safe7 : safe (some (some mv7)) := safe_of mv7 (by decide)

theorem old_eq7 : old (some (some mv7)) = BB6.Agent10Raw108LBSplit1930Kid7.table := tableOK_sound _ _ (by decide)
theorem never7 (m : Machine) (hm : compatible (kid mv7) m) : NeverHalts m := by
  apply never_transfer _ safe7 _ m hm
  rw [old_eq7]
  exact BB6.Agent10Raw108LBSplit1930Kid7.never

def mv8 : Move := ⟨false,true,2⟩

theorem safe8 : safe (some (some mv8)) := safe_of mv8 (by decide)

theorem read8 : zipRead (kid mv8) 91503 = some (2,true) :=
  read_transfer _ safe8 91503 (2,true) (by decide) (by decide) BB6.Agent10Raw108Long.read_short8
theorem checked8 : zipCheck 4136175 (kid mv8) (.last 91503 (2,true)) = true := by
  have hh : kid mv8 (2,true) = none := by decide
  have hw : weightOK (kid mv8) (2,true) 91503 4136175 = true := by decide
  have hr : restOK (kid mv8) (2,true) = true := by decide
  rw [zipCheck.eq_1]
  simp only [zipQueryOK,read8,hh,hw,hr,decide_true,Bool.and_self]

def mv9 : Move := ⟨false,true,3⟩

theorem safe9 : safe (some (some mv9)) := safe_of mv9 (by decide)

theorem old_eq9 : old (some (some mv9)) = BB6.Agent10Raw108LBSplit1930Kid9.table := tableOK_sound _ _ (by decide)
theorem never9 (m : Machine) (hm : compatible (kid mv9) m) : NeverHalts m := by
  apply never_transfer _ safe9 _ m hm
  rw [old_eq9]
  exact BB6.Agent10Raw108LBSplit1930Kid9.never

def mv10 : Move := ⟨false,true,4⟩

def mv11 : Move := ⟨false,true,5⟩

theorem safe11 : safe (some (some mv11)) := safe_of mv11 (by decide)

theorem old_eq11 : old (some (some mv11)) = BB6.Agent10Raw108LBSplit1930Kid11.table := tableOK_sound _ _ (by decide)
theorem never11 (m : Machine) (hm : compatible (kid mv11) m) : NeverHalts m := by
  apply never_transfer _ safe11 _ m hm
  rw [old_eq11]
  exact BB6.Agent10Raw108LBSplit1930Kid11.never

def mv12 : Move := ⟨true,false,0⟩

theorem safe12 : safe (some (some mv12)) := safe_of mv12 (by decide)

theorem old_eq12 : old (some (some mv12)) = BB6.Agent10Raw108LBSplit1930Kid12.table := tableOK_sound _ _ (by decide)
theorem never12 (m : Machine) (hm : compatible (kid mv12) m) : NeverHalts m := by
  apply never_transfer _ safe12 _ m hm
  rw [old_eq12]
  exact BB6.Agent10Raw108LBSplit1930Kid12.never

def mv13 : Move := ⟨true,false,1⟩

theorem safe13 : safe (some (some mv13)) := safe_of mv13 (by decide)

theorem old_eq13 : old (some (some mv13)) = BB6.Agent10Raw108LBSplit1930Kid13.table := tableOK_sound _ _ (by decide)
theorem never13 (m : Machine) (hm : compatible (kid mv13) m) : NeverHalts m := by
  apply never_transfer _ safe13 _ m hm
  rw [old_eq13]
  exact BB6.Agent10Raw108LBSplit1930Kid13.never

def mv14 : Move := ⟨true,false,2⟩

theorem safe14 : safe (some (some mv14)) := safe_of mv14 (by decide)

theorem read14 : zipRead (kid mv14) 91503 = some (2,true) :=
  read_transfer _ safe14 91503 (2,true) (by decide) (by decide) BB6.Agent10Raw108Long.read_short14
theorem checked14 : zipCheck 4136175 (kid mv14) (.last 91503 (2,true)) = true := by
  have hh : kid mv14 (2,true) = none := by decide
  have hw : weightOK (kid mv14) (2,true) 91503 4136175 = true := by decide
  have hr : restOK (kid mv14) (2,true) = true := by decide
  rw [zipCheck.eq_1]
  simp only [zipQueryOK,read14,hh,hw,hr,decide_true,Bool.and_self]

def mv15 : Move := ⟨true,false,3⟩

theorem safe15 : safe (some (some mv15)) := safe_of mv15 (by decide)

theorem old_eq15 : old (some (some mv15)) = BB6.Agent10Raw108LBSplit1930Kid15.table := tableOK_sound _ _ (by decide)
theorem never15 (m : Machine) (hm : compatible (kid mv15) m) : NeverHalts m := by
  apply never_transfer _ safe15 _ m hm
  rw [old_eq15]
  exact BB6.Agent10Raw108LBSplit1930Kid15.never

def mv16 : Move := ⟨true,false,4⟩

def mv17 : Move := ⟨true,false,5⟩

theorem safe17 : safe (some (some mv17)) := safe_of mv17 (by decide)

theorem old_eq17 : old (some (some mv17)) = BB6.Agent10Raw108LBSplit1930Kid17.table := tableOK_sound _ _ (by decide)
theorem never17 (m : Machine) (hm : compatible (kid mv17) m) : NeverHalts m := by
  apply never_transfer _ safe17 _ m hm
  rw [old_eq17]
  exact BB6.Agent10Raw108LBSplit1930Kid17.never

def mv18 : Move := ⟨true,true,0⟩

theorem safe18 : safe (some (some mv18)) := safe_of mv18 (by decide)

theorem old_eq18 : old (some (some mv18)) = BB6.Agent10Raw108LBSplit1930Kid18.table := tableOK_sound _ _ (by decide)
theorem never18 (m : Machine) (hm : compatible (kid mv18) m) : NeverHalts m := by
  apply never_transfer _ safe18 _ m hm
  rw [old_eq18]
  exact BB6.Agent10Raw108LBSplit1930Kid18.never

def mv19 : Move := ⟨true,true,1⟩

theorem safe19 : safe (some (some mv19)) := safe_of mv19 (by decide)

theorem old_eq19 : old (some (some mv19)) = BB6.Agent10Raw108LBSplit1930Kid19.table := tableOK_sound _ _ (by decide)
theorem never19 (m : Machine) (hm : compatible (kid mv19) m) : NeverHalts m := by
  apply never_transfer _ safe19 _ m hm
  rw [old_eq19]
  exact BB6.Agent10Raw108LBSplit1930Kid19.never

def mv20 : Move := ⟨true,true,2⟩

theorem safe20 : safe (some (some mv20)) := safe_of mv20 (by decide)

theorem read20 : zipRead (kid mv20) 91503 = some (2,true) :=
  read_transfer _ safe20 91503 (2,true) (by decide) (by decide) BB6.Agent10Raw108Long.read_short20
theorem checked20 : zipCheck 4136175 (kid mv20) (.last 91503 (2,true)) = true := by
  have hh : kid mv20 (2,true) = none := by decide
  have hw : weightOK (kid mv20) (2,true) 91503 4136175 = true := by decide
  have hr : restOK (kid mv20) (2,true) = true := by decide
  rw [zipCheck.eq_1]
  simp only [zipQueryOK,read20,hh,hw,hr,decide_true,Bool.and_self]

def mv21 : Move := ⟨true,true,3⟩

theorem safe21 : safe (some (some mv21)) := safe_of mv21 (by decide)

theorem old_eq21 : old (some (some mv21)) = BB6.Agent10Raw108LBSplit1930Kid21.table := tableOK_sound _ _ (by decide)
theorem never21 (m : Machine) (hm : compatible (kid mv21) m) : NeverHalts m := by
  apply never_transfer _ safe21 _ m hm
  rw [old_eq21]
  exact BB6.Agent10Raw108LBSplit1930Kid21.never

def mv22 : Move := ⟨true,true,4⟩

theorem safe22 : safe (some (some mv22)) := safe_of mv22 (by decide)

theorem read22 : zipRead (kid mv22) 4136174 = some (2,true) :=
  read_transfer _ safe22 4136174 (2,true) (by decide) (by decide) BB6.Agent10Raw108Long.read_kid22
theorem checked22 : zipCheck 4136175 (kid mv22) (.last 4136174 (2,true)) = true := by
  have hh : kid mv22 (2,true) = none := by decide
  have hw : weightOK (kid mv22) (2,true) 4136174 4136175 = true := by decide
  have hr : restOK (kid mv22) (2,true) = true := by decide
  rw [zipCheck.eq_1]
  simp only [zipQueryOK,read22,hh,hw,hr,decide_true,Bool.and_self]

def mv23 : Move := ⟨true,true,5⟩

theorem safe23 : safe (some (some mv23)) := safe_of mv23 (by decide)

theorem old_eq23 : old (some (some mv23)) = BB6.Agent10Raw108LBSplit1930Kid23.table := tableOK_sound _ _ (by decide)
theorem never23 (m : Machine) (hm : compatible (kid mv23) m) : NeverHalts m := by
  apply never_transfer _ safe23 _ m hm
  rw [old_eq23]
  exact BB6.Agent10Raw108LBSplit1930Kid23.never

#print axioms root_read
#print axioms read22
#print axioms never23
end BB6.Agent4.Raw124M448
