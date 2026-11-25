import SweepPumping

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent44Row34Stack
open BB6Coverage BB6Coverage.Agent31Pump

/-- The last unassigned F1 is never used. v=true selects F0=1LB,
    v=false selects F0=1LC. -/
def p (v : Bool) : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true  => some (some ⟨true,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true  => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,false,0⟩)
  | 2, true  => some (some ⟨false,true,2⟩)
  | 3, false => some (some ⟨true,false,0⟩)
  | 3, true  => some (some ⟨false,false,1⟩)
  | 4, false => some (some ⟨false,false,5⟩)
  | 4, true  => some (some ⟨true,false,4⟩)
  | 5, false => some (some ⟨true,false,if v then 1 else 2⟩)
  | _, _ => none

def width (v : Bool) : Nat := if v then 3 else 4
def ones (v : Bool) : List Bool := if v then [true,true,true] else [true,true,true,true]
def zeros (v : Bool) : List Bool := if v then [false,false,false] else [false,false,false,false]
def gap (v : Bool) : List Bool := if v then [false,false] else [false,false,false]
def block (v b : Bool) : List Bool := if b then ones v else zeros v

def code (v : Bool) : List Bool → List Bool
  | [] => []
  | b::w => block v b ++ code v w

def left (v : Bool) : Option (List Bool) → List Bool
  | none => []
  | some w => gap v ++ code v w

def stackCfg (v : Bool) (w : Option (List Bool)) (k : Nat) : Z0 :=
  ⟨5, left v w, false :: true :: (rep (ones v) k ++ [false,false])⟩

def prefixCost (v : Bool) : Nat := if v then 6 else 8

theorem openPhase (v : Bool) (w : Option (List Bool)) (k : Nat) :
    run0 (p v) (prefixCost v) (stackCfg v w k) =
      some ⟨2, true :: (ones v ++ code v (w.getD [])),
        rep (ones v) k ++ [false,false]⟩ := by
  cases v <;> cases w <;> rfl

theorem eraseBlocks (v : Bool) (k : Nat) (L : List Bool) :
    run0 (p v) (width v * k) ⟨2, true::L, rep (ones v) k ++ [false,false]⟩ =
      some ⟨2, true :: (rep (zeros v) k ++ L), [false,false]⟩ := by
  simpa only [List.nil_append, List.cons_append, List.append_assoc] using
    (sweepR (p v) 2 [true] [] (ones v) (zeros v) (width v)
      (by intro L R; cases v <;> rfl) k L [false,false])

theorem turnaround (v : Bool) (L : List Bool) :
    run0 (p v) 10 ⟨2,true::L,[false,false]⟩ =
      some ⟨4,true::L,[false,false]⟩ := by
  cases v <;> rfl

def phaseCost (v : Bool) (k : Nat) : Nat := prefixCost v + width v * k + 10

theorem phase (v : Bool) (w : Option (List Bool)) (k : Nat) :
    run0 (p v) (phaseCost v k) (stackCfg v w k) =
      some ⟨4, true :: (rep (zeros v) k ++ ones v ++ code v (w.getD [])),
        [false,false]⟩ := by
  simpa only [phaseCost,List.append_assoc] using
    join0 (join0 (openPhase v w k) (eraseBlocks v k (ones v ++ code v (w.getD []))))
      (turnaround v (rep (zeros v) k ++ (ones v ++ code v (w.getD []))))

theorem code_repeat (v b : Bool) (n : Nat) (w : List Bool) :
    code v (List.replicate n b ++ w) = rep (block v b) n ++ code v w := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, code, rep, ih, List.append_assoc]

theorem pushFinish (v : Bool) (k : Nat) (L : List Bool) :
    run0 (p v) 2
      ⟨4,true :: (rep (zeros v) (k+1) ++ ones v ++ L),[false,false]⟩ =
      some ⟨5,gap v ++ rep (zeros v) k ++ ones v ++ L,[false,true,false,false]⟩ := by
  cases v <;> rfl

theorem push (v : Bool) (w : Option (List Bool)) (k : Nat) :
    run0 (p v) (phaseCost v (k+1)+2) (stackCfg v w (k+1)) =
      some (stackCfg v (some (List.replicate k false ++ true :: w.getD [])) 0) := by
  have H := join0 (phase v w (k+1)) (pushFinish v k (code v (w.getD [])))
  simpa only [stackCfg,left,code_repeat,block,Bool.false_eq_true,ite_false,ite_true,code,rep,List.append_assoc,List.nil_append] using H

/-- Pop a finite run of leading one-blocks, followed by either the
    implicit infinite blank tail or a whole explicit zero-block. -/
def popWord (j : Nat) (tail : Option (List Bool)) : List Bool :=
  List.replicate j true ++ (tail.map (fun w => false::w)).getD []

def stopBlock (v : Bool) (tail : Option (List Bool)) : List Bool :=
  match tail with
  | none => []
  | some w => zeros v ++ code v w

theorem word_split (w : List Bool) : ∃ j tail, w = popWord j tail := by
  induction w with
  | nil => exact ⟨0,none,rfl⟩
  | cons b w ih =>
    cases b with
    | false => exact ⟨0,some w,rfl⟩
    | true =>
      obtain ⟨j,t,h⟩ := ih
      exact ⟨j+1,t,by rw [h]; rfl⟩

theorem code_pop (v : Bool) (j : Nat) (tail : Option (List Bool)) :
    code v (popWord j tail) = rep (ones v) j ++ stopBlock v tail := by
  rw [popWord,code_repeat]
  cases tail <;> rfl

theorem eOne (v : Bool) (L R : List Bool) :
    run0 (p v) 1 ⟨4,true::L,R⟩ = some ⟨4,L,true::R⟩ := by
  cases v <;> rfl

theorem eSweep (v : Bool) (j : Nat) (L : List Bool) :
    run0 (p v) (width v*j) ⟨4,rep (ones v) j ++ L,[true,false,false]⟩ =
      some ⟨4,L,rep (ones v) j ++ [true,false,false]⟩ := by
  simpa only [List.nil_append] using
    (sweepL (p v) 4 [] [] (ones v) (ones v) (width v)
      (by intro L R; cases v <;> rfl) j L [true,false,false])

theorem eExit (v : Bool) (tail : Option (List Bool)) (R : List Bool) :
    run0 (p v) 1 ⟨4,stopBlock v tail,R⟩ = some ⟨5,left v tail,false::R⟩ := by
  cases v <;> cases tail <;> rfl

theorem rep_ones_comm (v : Bool) (j : Nat) :
    rep (ones v) j ++ [true,false,false] = true :: (rep (ones v) j ++ [false,false]) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [rep,List.append_assoc,ih]
    cases v <;> rfl

theorem popFinish (v : Bool) (j : Nat) (tail : Option (List Bool)) :
    run0 (p v) (1+width v*(j+1)+1)
      ⟨4,true :: (ones v ++ code v (popWord j tail)),[false,false]⟩ =
      some (stackCfg v tail (j+1)) := by
  rw [code_pop, ← List.append_assoc]
  change run0 (p v) _ ⟨4,true :: (rep (ones v) (j+1) ++ stopBlock v tail),[false,false]⟩ = _
  have H := join0 (join0 (eOne v (rep (ones v) (j+1) ++ stopBlock v tail) [false,false])
      (eSweep v (j+1) (stopBlock v tail)))
    (eExit v tail (rep (ones v) (j+1) ++ [true,false,false]))
  simpa only [stackCfg,rep_ones_comm] using H

theorem pop (v : Bool) (w : Option (List Bool)) (j : Nat) (tail : Option (List Bool))
    (h : w.getD [] = popWord j tail) :
    run0 (p v) (phaseCost v 0+(1+width v*(j+1)+1)) (stackCfg v w 0) =
      some (stackCfg v tail (j+1)) := by
  have H := phase v w 0
  rw [h] at H
  simp only [rep,List.nil_append] at H
  exact join0 H (popFinish v j tail)

theorem next (v : Bool) (w : Option (List Bool)) (k : Nat) :
    ∃ n w' k', 0 < n ∧ run0 (p v) n (stackCfg v w k) = some (stackCfg v w' k') := by
  cases k with
  | zero =>
    obtain ⟨j,tail,h⟩ := word_split (w.getD [])
    exact ⟨_,tail,j+1,by omega,pop v w j tail h⟩
  | succ k => exact ⟨_,some (List.replicate k false ++ true :: w.getD []),0,by omega,push v w k⟩

theorem entry (v : Bool) : run0 (p v) 10 ⟨0,[],[]⟩ = some (stackCfg v none 0) := by
  cases v <;> rfl

theorem livePrefixes (v : Bool) (n : Nat) :
    ∃ t w k, n ≤ t ∧ run0 (p v) t ⟨0,[],[]⟩ = some (stackCfg v w k) := by
  induction n with
  | zero => exact ⟨10,none,0,by omega,entry v⟩
  | succ n ih =>
    obtain ⟨t,w,k,ht,hr⟩ := ih
    obtain ⟨c,w',k',hc,hs⟩ := next v w k
    exact ⟨t+c,w',k',by omega,join0 hr hs⟩

open BB6Coverage.Agent50Zipper

/-- Original blank-start machine bridge, for every compatible completion. -/
theorem never (v : Bool) (m : Machine) (hm : compatible (p v) m) : NeverHalts m := by
  intro n
  obtain ⟨t,w,k,ht,hr⟩ := livePrefixes v n
  have hz : (zrun (p v) t BB6Coverage.Agent31Pump.start).map project = some (stackCfg v w k) :=
    (run_project (p v) t BB6Coverage.Agent31Pump.start).trans hr
  cases h : zrun (p v) t BB6Coverage.Agent31Pump.start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound (p v) m hm t BB6Coverage.Agent31Pump.start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms livePrefixes
#print axioms never
end BB6.Agent44Row34Stack
