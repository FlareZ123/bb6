import SweepPumping

namespace BB6.Agent44Raw11A1LA
open BB6Coverage BB6Coverage.Agent31Pump

/-- A genuine Raw11 descendant with only five ordinary rows assigned.
    C1 and all D/E/F rows are never queried, for every completion. -/
def table : PartialMachine := fun s => match s.1.val, s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,1⟩)
  | 2, false => some (some ⟨false,false,0⟩)
  | _, _ => none

def ones (n : Nat) : List Bool := List.replicate n true

theorem ones_succ (n : Nat) : ones (n+1) = true :: ones n := rfl

theorem ones_snoc (n : Nat) : ones n ++ [true] = ones (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ones_succ,ones_succ,List.cons_append,ih]

theorem sweepA (n : Nat) (L R : List Bool) :
    run0 table n ⟨0,ones n ++ L,R⟩ = some ⟨0,L,ones n ++ R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h := ih (true :: R)
    rw [ones_succ,List.cons_append]
    change run0 table n ⟨0,ones n ++ L,true :: R⟩ = some ⟨0,L,true :: (ones n ++ R)⟩
    rw [h]
    congr 2
    rw [← List.cons_append,← ones_succ,← ones_snoc,List.append_assoc]
    rfl

theorem sweepB (n : Nat) (L : List Bool) :
    run0 table n ⟨1,true :: L,ones n ++ [false]⟩ =
      some ⟨1,true :: ones n ++ L,[false]⟩ := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    rw [ones_succ,List.cons_append]
    change run0 table n ⟨1,true :: true :: L,ones n ++ [false]⟩ = _
    rw [ih (true :: L)]
    congr 2
    change true :: (ones n ++ (true :: L)) = true :: true :: (ones n ++ L)
    apply congrArg (List.cons true)
    calc
      ones n ++ true :: L = (ones n ++ [true]) ++ L := by rw [List.append_assoc]; rfl
      _ = true :: (ones n ++ L) := by rw [ones_snoc,ones_succ,List.cons_append]


def cfg (n : Nat) : Z0 := ⟨2,false :: ones (2*n+2),[]⟩

theorem growth (n : Nat) : run0 table (4*n+7) (cfg n) = some (cfg (n+1)) := by
  have h0 : run0 table 1 (cfg n) = some ⟨0,ones (2*n+2),[false]⟩ := rfl
  have h1 : run0 table (2*n+2) ⟨0,ones (2*n+2),[false]⟩ = some ⟨0,[],ones (2*n+2) ++ [false]⟩ := by
    simpa using sweepA (2*n+2) [] [false]
  have h2 : run0 table 1 ⟨0,[],ones (2*n+2) ++ [false]⟩ = some ⟨1,[true,true],ones (2*n+1) ++ [false]⟩ := by
    rw [show 2*n+2=2*n+1+1 by omega,ones_succ]
    rfl
  have h3 := sweepB (2*n+1) [true]
  have h4 : run0 table 2 ⟨1,true :: ones (2*n+1) ++ [true],[false]⟩ = some (cfg (n+1)) := by
    change run0 table 2 ⟨1,true :: (ones (2*n+1) ++ [true]),[false]⟩ = _
    rw [ones_snoc]
    change some (⟨2,false :: true :: true :: ones (2*n+1+1),[]⟩ : Z0) = some (cfg (n+1))
    rw [cfg,show 2*(n+1)+2=2*n+1+1+1+1 by omega,ones_succ,ones_succ]
    rfl
  have h := join0 (join0 (join0 (join0 h0 h1) h2) h3) h4
  rw [show 4*n+7=1+(2*n+2)+1+(2*n+1)+2 by omega]
  exact h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table cfg 2 (fun n => 4*n+7) rfl (by intro n; omega) growth m hm

#print axioms never
end BB6.Agent44Raw11A1LA
