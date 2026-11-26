import PartialAudit
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent6E0ZeroRCRecurrence
open BB6Coverage BB6Coverage.Agent31Pump
open BB6Coverage.Agent50Zipper BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent10ZipAudit BB6.Agent47PartialAudit BB6Coverage.Agent10ZipAudit

def p : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,1⟩)
  | 2,false => some (some ⟨true,false,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,1⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨true,true,2⟩)
  | 5,true => some (some ⟨true,true,4⟩)
  | _,_ => none

def O (n : Nat) : List Bool := rep [true] n
def Q (n : Nat) : List Bool := rep [false,true,true,true] n
@[simp] theorem O_zero : O 0 = [] := rfl
@[simp] theorem O_succ (n : Nat) : O (n+1) = true :: O n := rfl
theorem O_add (n m : Nat) : O (n+m) = O n ++ O m := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.succ_add]; simp [ih]
@[simp] theorem O_one : O 1 = [true] := rfl
@[simp] theorem Q_zero : Q 0 = [] := rfl
@[simp] theorem Q_succ (n : Nat) : Q (n+1) = [false,true,true,true] ++ Q n := rfl

def bcfg (m n : Nat) (L : List Bool) : Z0 := ⟨1, O (m+1) ++ L, O n⟩
def ccfg (n : Nat) (L : List Bool) : Z0 := ⟨2, [false,true] ++ L, O n⟩
theorem b1 (L R : List Bool) : run0 p 1 ⟨1,[true]++L,[true]++R⟩ = some ⟨1,[true]++[true]++L,R⟩ := rfl
theorem c3 (L R : List Bool) : run0 p 3 ⟨2,[false,true]++[true]++L,R⟩ = some ⟨2,[false,true]++L,[true]++R⟩ := rfl
theorem bsweep (m n : Nat) (L : List Bool) :
  run0 p n (bcfg m n L) = some ⟨1,O (n+m+1) ++ L,[]⟩ := by
  have h := sweepR p 1 [true] [] [true] [true] 1 b1 n (O m ++ L) []
  change run0 p (1*n) ⟨1,[true]++(O m++L), []++O n++[]⟩ =
    some ⟨1,[true]++O n++(O m++L), []++[]⟩ at h
  rw [show n+m+1=(n+m)+1 by omega, O_succ, O_add]
  simpa [bcfg,List.append_assoc] using h

theorem turn (k : Nat) (L : List Bool) :
  run0 p 2 ⟨1,O (k+1) ++ L,[]⟩ = some ⟨2,[false,true] ++ O (k+1) ++ L,[]⟩ := by
  rfl

theorem csweep (n : Nat) (L : List Bool) :
  run0 p (3*n) ⟨2,[false,true] ++ O n ++ L,[]⟩ = some (ccfg n L) := by
  have h := sweepL p 2 [false,true] [] [true] [true] 3 c3 n L []
  simpa [ccfg,O,List.append_assoc] using h

theorem bc (m n : Nat) (L : List Bool) :
  run0 p (4*n+3*m+5) (bcfg m n L) = some (ccfg (n+m+1) L) := by
  have h := join0 (join0 (bsweep m n L) (turn (n+m) L)) (csweep (n+m+1) L)
  rw [show 4*n+3*m+5=n+2+3*(n+m+1) by omega]
  exact h

theorem advance (n : Nat) (L : List Bool) :
  run0 p 5 (ccfg n ([false,true] ++ L)) = some (bcfg 0 (n+3) L) := by
  simp only [ccfg,bcfg,O_succ,O_zero,List.cons_append,List.nil_append]
  rfl

theorem loop_one (n : Nat) (L : List Bool) :
  run0 p (4*n+16) (bcfg 2 n ([false,true,true,true]++L)) = some (bcfg 2 (n+6) L) := by
  have h := join0 (bc 2 n ([false,true,true,true]++L)) (advance (n+2+1) ([true,true]++L))
  simpa [bcfg,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem loop_last (n : Nat) :
  run0 p (4*n+16) (bcfg 2 n [false,true]) = some (bcfg 0 (n+6) []) := by
  have h := join0 (bc 2 n [false,true]) (advance (n+2+1) [])
  simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

def innerCost : Nat → Nat → Nat
  | 0,n => 4*n+16
  | j+1,n => 4*n+16 + innerCost j (n+6)
theorem inner (j n : Nat) :
  run0 p (innerCost j n) (bcfg 2 n (Q j ++ [false,true])) = some (bcfg 0 (n+6*(j+1)) []) := by
  induction j generalizing n with
  | zero => simpa [innerCost] using loop_last n
  | succ j ih =>
    have h := join0 (loop_one n (Q j ++ [false,true])) (ih (n+6))
    rw [show n+6*((j+1)+1)=n+6+6*(j+1) by omega]
    simpa [innerCost,List.append_assoc] using h

def P (n : Nat) : List Bool := rep [true,true,true,false] n
@[simp] theorem P_zero : P 0 = [] := rfl
@[simp] theorem P_succ (n : Nat) : P (n+1) = [true,true,true,false] ++ P n := rfl

theorem align (k : Nat) : P (k+1) ++ [true] = [true,true,true] ++ Q k ++ [false,true] := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [P_succ,Q_succ,List.append_assoc] at ih ⊢; rw [ih]; rfl

def peak (n : Nat) : Z0 := ⟨2,[true,true],O n⟩
def after4 (k r : Nat) : Z0 := ⟨2,[true] ++ P k ++ [true],O r⟩
def nextB (j n : Nat) : Z0 := bcfg 2 n (Q j ++ [false,true])

theorem reset (n : Nat) : run0 p 6 (ccfg n []) = some (peak (n+2)) := by rfl

theorem rise (n : Nat) : run0 p (4*n+11) (bcfg 0 n []) = some (peak (n+3)) := by
  have h := join0 (bc 0 n []) (reset (n+1))
  simpa [Nat.add_assoc] using h

theorem c4 (L R : List Bool) :
  run0 p 4 ⟨2,[true]++L,[true,true,true,true]++R⟩ =
    some ⟨2,[true]++[true,true,true,false]++L,R⟩ := rfl

theorem O_block (k r : Nat) : O (4*k+r) = rep [true,true,true,true] k ++ O r := by
  induction k with
  | zero => simp [rep]
  | succ k ih =>
    rw [show 4*(k+1)+r=4+(4*k+r) by omega,O_add,ih]
    rfl

theorem c4sweep (k r : Nat) : run0 p (4*k) (peak (4*k+r)) = some (after4 k r) := by
  have h := sweepR p 2 [true] [] [true,true,true,true] [true,true,true,false] 4 c4 k [true] (O r)
  change run0 p (4*k) ⟨2,[true]++[true],rep [true,true,true,true] k ++ O r⟩ = some ⟨2,[true]++P k++[true],O r⟩ at h
  rw [← O_block] at h
  exact h

theorem bridge0 (k : Nat) : run0 p 11 (after4 (k+1) 0) = some (nextB k 4) := by
  unfold after4 nextB bcfg
  rw [show [true] ++ P (k+1) ++ [true] = [true,true,true,true,false] ++ P k ++ [true] by simp [List.append_assoc]]
  change run0 p 11 ⟨2,[true,true,true,true,false] ++ (P k ++ [true]),[]⟩ = _
  have h (L : List Bool) : run0 p 11 ⟨2,[true,true,true,true,false] ++ L,[]⟩ =
    some ⟨1,[true,true,true,false] ++ L,O 4⟩ := rfl
  rw [h]
  rw [← List.append_assoc,← P_succ,align]
  rfl

theorem bridge3 (k : Nat) : run0 p 15 (after4 (k+1) 3) = some (nextB k 5) := by
  unfold after4 nextB bcfg
  rw [show [true] ++ P (k+1) ++ [true] = [true,true,true,true,false] ++ P k ++ [true] by simp [List.append_assoc]]
  change run0 p 15 ⟨2,[true,true,true,true,false] ++ (P k ++ [true]),O 3⟩ = _
  have h (L : List Bool) : run0 p 15 ⟨2,[true,true,true,true,false] ++ L,O 3⟩ =
    some ⟨1,[true,true,true,false] ++ L,O 5⟩ := rfl
  rw [h]
  rw [← List.append_assoc,← P_succ,align]
  rfl

theorem bridge2 (k : Nat) : run0 p 7 (after4 (k+1) 2) = some (nextB (k+1) 1) := by
  unfold after4 nextB bcfg
  rw [show [true] ++ P (k+1) ++ [true] = [true,true,true,true,false] ++ P k ++ [true] by simp [List.append_assoc]]
  change run0 p 7 ⟨2,[true,true,true,true,false] ++ (P k ++ [true]),O 2⟩ = _
  have h (L : List Bool) : run0 p 7 ⟨2,[true,true,true,true,false] ++ L,O 2⟩ =
    some ⟨1,[true,true,true,false,true,true,true,false] ++ L,O 1⟩ := rfl
  rw [h]
  rw [show [true,true,true,false,true,true,true,false] ++ (P k ++ [true]) = P (k+2) ++ [true] by simp [List.append_assoc],align]
  rfl

def final (k : Nat) : Z0 := ⟨5,[false,true,false] ++ P (k+1) ++ [true],[]⟩
theorem stop (k : Nat) : run0 p 2 (after4 (k+1) 1) = some ⟨5,[false,true,false] ++ P (k+1) ++ [true],[]⟩ := by rfl

theorem phaseBase (j n k r : Nat) (h : n+6*(j+1)+3 = 4*k+r) :
  run0 p (innerCost j n + (4*(n+6*(j+1))+11) + 4*k) (nextB j n) = some (after4 k r) := by
  have h1 := join0 (inner j n) (rise (n+6*(j+1)))
  rw [h] at h1
  exact join0 h1 (c4sweep k r)

theorem seed : run0 p 76 (project start) = some (nextB 1 4) := rfl
theorem phase0 : run0 p 194 (nextB 1 4) = some (nextB 3 5) := by
  rw [show 194=innerCost 1 4+(4*(4+6*(1+1))+11)+4*(3+1)+15 by decide]
  exact join0 (phaseBase 1 4 (3+1) 3 (by decide)) (bridge3 3)
theorem prefix0 : run0 p 270 (project start) = some (nextB 3 5) := by
  rw [show 270=76+194 by decide]
  exact join0 seed phase0
theorem phase1 : run0 p 458 (nextB 3 5) = some (nextB 7 4) := by
  rw [show 458=innerCost 3 5+(4*(5+6*(3+1))+11)+4*(7+1)+11 by decide]
  exact join0 (phaseBase 3 5 (7+1) 0 (by decide)) (bridge0 7)
theorem prefix1 : run0 p 728 (project start) = some (nextB 7 4) := by
  rw [show 728=270+458 by decide]
  exact join0 prefix0 phase1
theorem phase2 : run0 p 1214 (nextB 7 4) = some (nextB 12 5) := by
  rw [show 1214=innerCost 7 4+(4*(4+6*(7+1))+11)+4*(12+1)+15 by decide]
  exact join0 (phaseBase 7 4 (12+1) 3 (by decide)) (bridge3 12)
theorem prefix2 : run0 p 1942 (project start) = some (nextB 12 5) := by
  rw [show 1942=728+1214 by decide]
  exact join0 prefix1 phase2
theorem phase3 : run0 p 2774 (nextB 12 5) = some (nextB 21 1) := by
  rw [show 2774=innerCost 12 5+(4*(5+6*(12+1))+11)+4*(20+1)+7 by decide]
  exact join0 (phaseBase 12 5 (20+1) 2 (by decide)) (bridge2 20)
theorem prefix3 : run0 p 4716 (project start) = some (nextB 21 1) := by
  rw [show 4716=1942+2774 by decide]
  exact join0 prefix2 phase3
theorem phase4 : run0 p 6674 (nextB 21 1) = some (nextB 33 4) := by
  rw [show 6674=innerCost 21 1+(4*(1+6*(21+1))+11)+4*(33+1)+11 by decide]
  exact join0 (phaseBase 21 1 (33+1) 0 (by decide)) (bridge0 33)
theorem prefix4 : run0 p 11390 (project start) = some (nextB 33 4) := by
  rw [show 11390=4716+6674 by decide]
  exact join0 prefix3 phase4
theorem phase5 : run0 p 15618 (nextB 33 4) = some (nextB 51 5) := by
  rw [show 15618=innerCost 33 4+(4*(4+6*(33+1))+11)+4*(51+1)+15 by decide]
  exact join0 (phaseBase 33 4 (51+1) 3 (by decide)) (bridge3 51)
theorem prefix5 : run0 p 27008 (project start) = some (nextB 51 5) := by
  rw [show 27008=11390+15618 by decide]
  exact join0 prefix4 phase5
theorem phase6 : run0 p 35306 (nextB 51 5) = some (nextB 79 4) := by
  rw [show 35306=innerCost 51 5+(4*(5+6*(51+1))+11)+4*(79+1)+11 by decide]
  exact join0 (phaseBase 51 5 (79+1) 0 (by decide)) (bridge0 79)
theorem prefix6 : run0 p 62314 (project start) = some (nextB 79 4) := by
  rw [show 62314=27008+35306 by decide]
  exact join0 prefix5 phase6
theorem phase7 : run0 p 80846 (nextB 79 4) = some (nextB 120 5) := by
  rw [show 80846=innerCost 79 4+(4*(4+6*(79+1))+11)+4*(120+1)+15 by decide]
  exact join0 (phaseBase 79 4 (120+1) 3 (by decide)) (bridge3 120)
theorem prefix7 : run0 p 143160 (project start) = some (nextB 120 5) := by
  rw [show 143160=62314+80846 by decide]
  exact join0 prefix6 phase7
theorem phase8 : run0 p 182270 (nextB 120 5) = some (nextB 183 1) := by
  rw [show 182270=innerCost 120 5+(4*(5+6*(120+1))+11)+4*(182+1)+7 by decide]
  exact join0 (phaseBase 120 5 (182+1) 2 (by decide)) (bridge2 182)
theorem prefix8 : run0 p 325430 (project start) = some (nextB 183 1) := by
  rw [show 325430=143160+182270 by decide]
  exact join0 prefix7 phase8
theorem phase9 : run0 p 413294 (nextB 183 1) = some (nextB 276 4) := by
  rw [show 413294=innerCost 183 1+(4*(1+6*(183+1))+11)+4*(276+1)+11 by decide]
  exact join0 (phaseBase 183 1 (276+1) 0 (by decide)) (bridge0 276)
theorem prefix9 : run0 p 738724 (project start) = some (nextB 276 4) := by
  rw [show 738724=325430+413294 by decide]
  exact join0 prefix8 phase9
theorem phase10 : run0 p 934633 (nextB 276 4) = some (final 416) := by
  rw [show 934633=innerCost 276 4+(4*(4+6*(276+1))+11)+4*(416+1)+2 by decide]
  exact join0 (phaseBase 276 4 (416+1) 1 (by decide)) (stop 416)
theorem prefix10 : run0 p 1673357 (project start) = some (final 416) := by
  rw [show 1673357=738724+934633 by decide]
  exact join0 prefix9 phase10

theorem first_query : zipRead p 1673357 = some (5,false) := by
  have h := (run_project p 1673357 start).trans prefix10
  unfold zipRead
  cases he : zrun p 1673357 start with
  | none => simp [he] at h
  | some z =>
    have h' : project z = final 416 := by
      simpa only [he,Option.map_some,Option.some.injEq] using h
    have hs : (z.q,z.l.headD false) = (5,false) := by
      change ((project z).q,(project z).l.headD false) = _
      rw [h']; rfl
    exact congrArg some hs

theorem noAssignedHalt : weightedTNFNoAssignedHalt p := by
  intro s; rcases s with ⟨q,b⟩; have hq : q.val < 6 := q.isLt
  have hcases : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    simp only [Fin.ext_iff]; omega
  rcases hcases with h|h|h|h|h|h <;> subst q <;> cases b <;> decide

theorem query : zipQueryOK 1673363 p 1673357 (5,false) = true := by
  simp only [zipQueryOK,first_query,decide_true,Bool.true_and]
  decide

theorem weighted : Cover (WeightedBound 1673363) p := by
  apply Cover.leaf
  intro m hm
  exact (certifiedZip 1673363 p (.last 1673357 (5,false)) (by decide) noAssignedHalt
    (by simp only [zipCheck,query,Bool.true_and]; decide)).sound m hm

#print axioms inner
#print axioms first_query
#print axioms weighted
end BB6.Agent6E0ZeroRCRecurrence
