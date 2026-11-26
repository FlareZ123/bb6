import Raw59PackedQuery
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent6E0ZeroRCRecurrence
open BB6Coverage BB6Coverage.Agent31Pump
open BB6.Agent32Raw59PackedQuery BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent10ZipAudit BB6.Agent47PartialAudit

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

#print axioms inner
end BB6.Agent6E0ZeroRCRecurrence
