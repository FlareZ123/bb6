import Raw54E1RF47Macro
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.RF47
open BB6Coverage BB6Coverage.Agent31Pump

abbrev LWord := List Nat
abbrev RWord := List (Nat × Nat)
def lw : LWord → List Bool
  | [] => []
  | n::ns => zeros n ++ true::lw ns
def rw : RWord → List Bool
  | [] => []
  | (g,b)::rs => zeros g ++ ones b ++ rw rs
def cfg (l : LWord) (r : RWord) : Z0 := sec (lw l) (rw r)

theorem zeros_add (a b : Nat) : zeros (a+b) = zeros a ++ zeros b := by
  induction a with
  | zero => simp [zeros,rep]
  | succ a ih =>
    rw [show a+1+b=(a+b)+1 by omega]
    change false::zeros (a+b) = false::(zeros a ++ zeros b)
    rw [ih]

theorem ones_add (a b : Nat) : ones (a+b) = ones a ++ ones b := by
  induction a with
  | zero => simp [ones,rep]
  | succ a ih =>
    rw [show a+1+b=(a+b)+1 by omega]
    change true::ones (a+b) = true::(ones a ++ ones b)
    rw [ih]

def decL : LWord → LWord
  | [] => []
  | g::gs => (g-1)::gs

theorem left_dec (l : LWord) (h : l.headD 1 ≠ 0) : padded (lw l) (false::lw (decL l)) := by
  cases l with
  | nil => exact padded_zero
  | cons g gs =>
    cases g with
    | zero => exact False.elim (h rfl)
    | succ g => exact padded_refl _

def addZ : RWord → RWord
  | [] => []
  | (g,b)::rs => (g+1,b)::rs

theorem addZ_rel (r : RWord) : padded (false::rw r) (rw (addZ r)) := by
  cases r with
  | nil => exact padded_symm padded_zero
  | cons p rs => rcases p with ⟨g,b⟩; exact padded_refl _

def addRun (n : Nat) (r : RWord) : RWord := (0,n)::addZ r

theorem addRun_rel (n : Nat) (r : RWord) : padded (ones n++false::rw r) (rw (addRun n r)) :=
  padded_append (ones n) (addZ_rel r)

def leftMerge : LWord → LWord
  | [] => [0]
  | g::gs => 0::(g+1)::gs

theorem leftMerge_rel (l : LWord) : padded (true::false::lw l) (lw (leftMerge l)) := by
  cases l with
  | nil => exact padded_cons (padded_symm padded_zero) true
  | cons g gs => exact padded_refl _

def afterOne (c : Nat) (r : RWord) : RWord := if c=1 then r else (0,c-1)::r

theorem afterOne_eq (c : Nat) (r : RWord) (hc : c>0) : rw (afterOne c r) = ones (c-1) ++ rw r := by
  unfold afterOne
  split
  · rename_i h; subst c; rfl
  · rfl

def afterZero (b g c : Nat) (r : RWord) : RWord :=
  if g=2 then (0,b+2+c)::r else (0,b+2)::(g-2,c)::r

theorem afterZero_eq (b g c : Nat) (r : RWord) (hg : 2 ≤ g) :
    rw (afterZero b g c r) = ones (b+2) ++ zeros (g-2) ++ ones c ++ rw r := by
  unfold afterZero
  split
  · rename_i h; subst g; simp only [rw,zeros,rep,List.nil_append,List.append_nil,Nat.reduceSub,ones_add,List.append_assoc]
  · simp only [rw,zeros,rep,List.nil_append,List.append_assoc]

def stripRun (r : RWord) : Nat × RWord :=
  match r with
  | (0,b)::rs => (b,rs)
  | _ => (0,r)

theorem stripRun_eq (r : RWord) : rw r = ones (stripRun r).1 ++ rw (stripRun r).2 := by
  cases r with
  | nil => rfl
  | cons p rs => rcases p with ⟨g,b⟩; cases g <;> rfl

theorem a0_push (l : LWord) (r rest : RWord) (b c : Nat)
    (hl : l.headD 1 ≠ 0) (hr : stripRun r = (b,(1,c)::rest)) (hc : c>0) :
    goes (cfg l r) (cfg (b::1::decL l) (afterOne c rest)) := by
  have hr' := stripRun_eq r
  rw [hr] at hr'
  have hshape : rw r = ones b ++ false::true::(ones (c-1) ++ rw rest) := by
    rw [hr']; cases c with
    | zero => omega
    | succ c => simp only [rw,zeros,ones,rep,Nat.add_sub_cancel,List.cons_append,List.nil_append,List.append_assoc]
  have h := goes_of_eq (by omega : 0 < b+6) (a0_one b (lw (decL l)) (ones (c-1) ++ rw rest))
  apply goes_congr (a:=sec (false::lw (decL l)) (ones b++false::true::(ones (c-1)++rw rest))) (b:=cfg l r) (c:=sec (zeros b++[true,false,true]++lw (decL l)) (ones (c-1)++rw rest)) (d:=cfg (b::1::decL l) (afterOne c rest)) _ _ h
  · refine ⟨rfl,padded_symm (left_dec l hl),?_⟩
    unfold cfg sec; rw [hshape]; exact padded_refl _
  · refine ⟨rfl,?_,?_⟩
    · change padded (zeros b++[true,false,true]++lw (decL l)) (lw (b::1::decL l))
      simp only [lw,zeros,rep,List.append_assoc,List.cons_append,List.nil_append]; exact padded_refl _
    · unfold cfg sec; rw [afterOne_eq c rest hc]; exact padded_refl _

theorem a0_merge (l : LWord) (r rest : RWord) (b g c : Nat)
    (hl : l.headD 1 ≠ 0) (hr : stripRun r = (b,(g,c)::rest)) (hg : 2 ≤ g) :
    goes (cfg l r) (cfg (0::decL l) (afterZero b g c rest)) := by
  have hr' := stripRun_eq r
  rw [hr] at hr'
  have hshape : rw r = ones b ++ false::false::(zeros (g-2)++ones c++rw rest) := by
    rw [hr']; have h : g = (g-2)+2 := by omega
    change ones b ++ (zeros g ++ ones c ++ rw rest) = _
    have hz : zeros g = false::false::zeros (g-2) := by
      have hh : zeros ((g-2)+2) = false::false::zeros (g-2) := by rfl
      rwa [show (g-2)+2=g by omega] at hh
    rw [hz]; rfl
  have h := goes_of_eq (by omega : 0 < 2*b+8) (a0_zero b (lw (decL l)) (zeros (g-2)++ones c++rw rest))
  apply goes_congr (a:=sec (false::lw (decL l)) (ones b++false::false::(zeros (g-2)++ones c++rw rest))) (b:=cfg l r) (c:=sec (true::lw (decL l)) (ones (b+2)++(zeros (g-2)++ones c++rw rest))) (d:=cfg (0::decL l) (afterZero b g c rest)) _ _ h
  · refine ⟨rfl,padded_symm (left_dec l hl),?_⟩
    unfold cfg sec; rw [hshape]; exact padded_refl _
  · refine ⟨rfl,padded_refl _,?_⟩
    unfold cfg sec; rw [afterZero_eq b g c rest hg]
    simp only [List.append_assoc]; exact padded_refl _

theorem a0_blank (l : LWord) (r : RWord) (b : Nat)
    (hl : l.headD 1 ≠ 0) (hr : stripRun r = (b,[])) :
    goes (cfg l r) (cfg (0::decL l) [(0,b+2)]) := by
  have hr' := stripRun_eq r; rw [hr] at hr'
  have h := goes_of_eq (by omega : 0 < 2*b+8) (a0_zero b (lw (decL l)) [])
  apply goes_congr (a:=sec (false::lw (decL l)) (ones b++[false,false])) (b:=cfg l r) (c:=sec (true::lw (decL l)) (ones (b+2)++[])) (d:=cfg (0::decL l) [(0,b+2)]) _ _ h
  · refine ⟨rfl,padded_symm (left_dec l hl),?_⟩
    unfold cfg sec; rw [hr']; simp only [rw,List.append_nil]
    have H := padded_append (ones b) (padded_symm (padded_zeros 2))
    rw [List.append_nil] at H
    exact padded_append [true,false] H
  · exact ⟨rfl,padded_refl _,padded_refl _⟩

theorem a1_gap1 (l : LWord) (r : RWord) : goes (cfg (0::1::l) r) (cfg (leftMerge l) (addZ r)) := by
  have h := goes_of_eq (by decide : 0 < 7) (a1_one (lw l) (rw r))
  apply goes_congr (a:=sec (true::false::true::lw l) (rw r)) (b:=cfg (0::1::l) r) (c:=sec (true::false::lw l) (false::rw r)) (d:=cfg (leftMerge l) (addZ r)) (zrel_refl _) _ h
  exact ⟨rfl,leftMerge_rel l,padded_append [true,false] (addZ_rel r)⟩

theorem a1_gap2 (l : LWord) (r : RWord) (hl : l.headD 1 ≠ 0) : goes (cfg (0::2::l) r) (cfg (0::l) (addRun 2 r)) := by
  have h := goes_of_eq (by decide : 0 < 13) (a1_two (lw (decL l)) (rw r))
  apply goes_congr (a:=sec (true::false::false::true::false::lw (decL l)) (rw r)) (b:=cfg (0::2::l) r) (c:=sec (true::false::lw (decL l)) ([true,true,false]++rw r)) (d:=cfg (0::l) (addRun 2 r)) _ _ h
  · exact ⟨rfl,padded_append [true,false,false,true] (padded_symm (left_dec l hl)),padded_refl _⟩
  · exact ⟨rfl,padded_cons (padded_symm (left_dec l hl)) true,padded_append [true,false] (addRun_rel 2 r)⟩

theorem a1_gap3 (g : Nat) (l : LWord) (r : RWord) (hg : 3≤g) : goes (cfg (0::g::l) r) (cfg ((g-3)::l) (addRun 3 r)) := by
  have h := goes_of_eq (by decide : 0 < 8) (a1_three (lw ((g-3)::l)) (rw r))
  apply goes_congr (a:=sec (true::false::false::false::lw ((g-3)::l)) (rw r)) (b:=cfg (0::g::l) r) (c:=sec (lw ((g-3)::l)) ([true,true,true,false]++rw r)) (d:=cfg ((g-3)::l) (addRun 3 r)) _ _ h
  · refine ⟨rfl,?_,padded_refl _⟩
    have he : g = (g-3)+3 := by omega
    change padded (true::false::false::false::lw ((g-3)::l)) (true::(zeros g++true::lw l))
    have hz : zeros g = false::false::false::zeros (g-3) := by
      have hh : zeros ((g-3)+3) = false::false::false::zeros (g-3) := by rfl
      rwa [show (g-3)+3=g by omega] at hh
    rw [hz]; exact padded_refl _
  · exact ⟨rfl,padded_refl _,padded_append [true,false] (addRun_rel 3 r)⟩

theorem a1_end (r : RWord) : goes (cfg [0] r) (cfg [] (addRun 3 r)) := by
  have h := goes_of_eq (by decide : 0 < 8) (a1_three [] (rw r))
  apply goes_congr (a:=sec [true,false,false,false] (rw r)) (b:=cfg [0] r) (c:=sec [] ([true,true,true,false]++rw r)) (d:=cfg [] (addRun 3 r)) _ _ h
  · exact ⟨rfl,padded_cons (padded_symm (padded_zeros 3)) true,padded_refl _⟩
  · exact ⟨rfl,padded_refl _,padded_append [true,false] (addRun_rel 3 r)⟩

#print axioms a0_push
#print axioms a0_merge
#print axioms a0_blank
#print axioms a1_gap2
end BB6.Agent8Raw54.RF47
