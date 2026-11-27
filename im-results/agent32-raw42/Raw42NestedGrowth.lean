import SweepPumping

open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 4096
namespace BB6.Agent32Raw42Nested

theorem repAdd (P : List Bool) (a b : Nat) :
    rep P (a+b) = rep P a ++ rep P b := by
  induction a with
  | zero => simp [rep]
  | succ a ih =>
    rw [show a+1+b = (a+b)+1 by omega]
    simp only [rep,ih,List.append_assoc]

theorem repDouble (n : Nat) : rep [true,true] n = rep [true] (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1) = 2+2*n by omega,repAdd [true] 2 (2*n)]
    simp only [rep,ih,List.append_assoc,List.cons_append,List.nil_append,List.append_nil]

namespace OneLBZeroLD
def p : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨true,false,1⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => some (some ⟨false,false,3⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨false,false,1⟩)
  | _ => none

def family (n : Nat) : Z0 :=
  ⟨1,[],[false,true,true] ++ rep [true] n ++ [false,true,true] ++ rep [true,true] n⟩

theorem first : run0 p 15 ⟨0,[],[]⟩ = some (family 0) := by decide

theorem entry (n : Nat) : run0 p 3 (family n) =
    some ⟨1,[false,true],[false,true] ++ rep [true] n ++ [false,true,true] ++ rep [true,true] n⟩ := by rfl

theorem transferR (L R : List Bool) :
    run0 p 3 ⟨1,[false,true] ++ L,[false] ++ [true] ++ R⟩ =
    some ⟨1,[false,true] ++ [true] ++ L,[false] ++ R⟩ := by rfl

theorem turn (n : Nat) : run0 p 10
    ⟨1,[false,true] ++ rep [true] n,[false,true,false,true,true] ++ rep [true,true] n⟩ =
    some ⟨1,rep [true] n,[true,true,false,true,true,true,true] ++ rep [true,true] n⟩ := by rfl

theorem transferL (L R : List Bool) :
    run0 p 1 ⟨1,[] ++ [true] ++ L,[true,true] ++ R⟩ =
    some ⟨1,[] ++ L,[true,true] ++ [true] ++ R⟩ := by rfl

theorem finish (n : Nat) : run0 p 8
    ⟨1,[],[true,true] ++ rep [true] n ++ [false,true,true,true,true] ++ rep [true,true] n⟩ =
    some (family (n+1)) := by
  have h : run0 p 8
      ⟨1,[],[true,true] ++ rep [true] n ++ [false,true,true,true,true] ++ rep [true,true] n⟩ =
      some ⟨1,[],[false,true,true,true] ++ rep [true] n ++ [false,true,true,true,true] ++ rep [true,true] n⟩ := by rfl
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using h

theorem grow (n : Nat) : run0 p (4*n+21) (family n) = some (family (n+1)) := by
  have h0 := entry n
  have h1 : run0 p (3*n)
      ⟨1,[false,true],[false,true] ++ rep [true] n ++ [false,true,true] ++ rep [true,true] n⟩ =
      some ⟨1,[false,true] ++ rep [true] n,[false,true,false,true,true] ++ rep [true,true] n⟩ := by
    -- Transfer all but the final fixed one to the left zipper.
    have hs := sweepR p 1 [false,true] [false] [true] [true] 3 transferR n [] ([true,false,true,true] ++ rep [true,true] n)
    have he : ([false] ++ rep [true] n ++ [true,false,true,true] ++ rep [true,true] n) =
        [false,true] ++ rep [true] n ++ [false,true,true] ++ rep [true,true] n := by
      have hh := congrArg (fun w => [false] ++ w ++ [false,true,true] ++ rep [true,true] n) (rep_snoc [true] n)
      simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using hh
    have ht : run0 p (3*n)
        ⟨1,[false,true],[false] ++ rep [true] n ++ [true,false,true,true] ++ rep [true,true] n⟩ =
        some ⟨1,[false,true] ++ rep [true] n,[false,true,false,true,true] ++ rep [true,true] n⟩ := by
      simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using hs
    rw [he] at ht
    exact ht
  have h2 := turn n
  have h3 : run0 p n
      ⟨1,rep [true] n,[true,true,false,true,true,true,true] ++ rep [true,true] n⟩ =
      some ⟨1,[],[true,true] ++ rep [true] n ++ [false,true,true,true,true] ++ rep [true,true] n⟩ := by
    simpa only [Nat.one_mul,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using
      (sweepL p 1 [] [true,true] [true] [true] 1 transferL n [] ([false,true,true,true,true] ++ rep [true,true] n))
  have h := join0 (join0 (join0 (join0 h0 h1) h2) h3) (finish n)
  rw [show 3+3*n+10+n+8 = 4*n+21 by omega] at h
  exact h

theorem never : ∀ m, compatible p m → NeverHalts m :=
  never_of_growth p family 15 (fun n => 4*n+21) first (by omega) grow
#print axioms never
end OneLBZeroLD

namespace OneLBZeroRD
def p : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨true,false,1⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => some (some ⟨false,true,3⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨false,false,1⟩)
  | _ => none

theorem innerEntry (n : Nat) (R : List Bool) :
    run0 p 3 ⟨1,[],[true,true] ++ rep [true] n ++ [false] ++ R⟩ =
    some ⟨1,[false,true],[false] ++ rep [true] n ++ [false] ++ R⟩ := by rfl

theorem transferR (L R : List Bool) :
    run0 p 3 ⟨1,[false,true] ++ L,[false] ++ [true] ++ R⟩ =
    some ⟨1,[false,true] ++ [true] ++ L,[false] ++ R⟩ := by rfl

theorem innerTurn (n : Nat) (R : List Bool) :
    run0 p 6 ⟨1,[false,true] ++ rep [true] n,[false,false] ++ R⟩ =
    some ⟨1,rep [true] n,[true,false,true,true] ++ R⟩ := by rfl

theorem transferL (L R : List Bool) :
    run0 p 1 ⟨1,[] ++ [true] ++ L,[true] ++ R⟩ =
    some ⟨1,[] ++ L,[true] ++ [true] ++ R⟩ := by rfl

theorem inner (n : Nat) (R : List Bool) :
    run0 p (4*n+9) ⟨1,[],[true,true] ++ rep [true] n ++ [false] ++ R⟩ =
    some ⟨1,[],[true] ++ rep [true] n ++ [false,true,true] ++ R⟩ := by
  have h0 := innerEntry n R
  have h1 : run0 p (3*n)
      ⟨1,[false,true],[false] ++ rep [true] n ++ [false] ++ R⟩ =
      some ⟨1,[false,true] ++ rep [true] n,[false,false] ++ R⟩ := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using (sweepR p 1 [false,true] [false] [true] [true] 3 transferR n [] ([false] ++ R))
  have h2 := innerTurn n R
  have h3 : run0 p n
      ⟨1,rep [true] n,[true,false,true,true] ++ R⟩ =
      some ⟨1,[],[true] ++ rep [true] n ++ [false,true,true] ++ R⟩ := by
    simpa only [Nat.one_mul,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using (sweepL p 1 [] [true] [true] [true] 1 transferL n [] ([false,true,true] ++ R))
  have h := join0 (join0 (join0 h0 h1) h2) h3
  rw [show 3+3*n+6+n = 4*n+9 by omega] at h
  exact h

theorem last (R : List Bool) : run0 p 5 ⟨1,[],[true,false] ++ R⟩ =
    some ⟨1,[],[false,true,true] ++ R⟩ := by rfl

def drainCost : Nat → Nat
  | 0 => 5
  | n+1 => (4*n+9) + drainCost n

theorem drain (n : Nat) (R : List Bool) :
    run0 p (drainCost n) ⟨1,[],[true] ++ rep [true] n ++ [false] ++ R⟩ =
    some ⟨1,[],[false] ++ rep [true,true] (n+1) ++ R⟩ := by
  induction n generalizing R with
  | zero => simpa only [drainCost,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using last R
  | succ n ih =>
    have h0 := inner n R
    have h1 : run0 p (drainCost n)
        ⟨1,[],[true] ++ rep [true] n ++ [false,true,true] ++ R⟩ =
        some ⟨1,[],[false] ++ rep [true,true] (n+1) ++ [true,true] ++ R⟩ := by
      simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using ih ([true,true] ++ R)
    have h := join0 h0 h1
    have he : (⟨1,[],[false] ++ rep [true,true] (n+1) ++ [true,true] ++ R⟩ : Z0) =
        ⟨1,[],[false] ++ rep [true,true] (n+2) ++ R⟩ := by
      have hs := congrArg (fun w => (⟨1,[],[false] ++ w ++ R⟩ : Z0)) (rep_snoc [true,true] (n+1))
      simpa only [rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using hs
    rw [he] at h
    simpa only [drainCost,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using h

theorem outerEntry (n : Nat) :
    run0 p 3 ⟨1,[],[false,true] ++ rep [true] n⟩ =
    some ⟨1,[false,true],[false] ++ rep [true] n⟩ := by rfl

theorem outerTurn (n : Nat) :
    run0 p 6 ⟨1,[false,true] ++ rep [true] n,[false]⟩ =
    some ⟨1,rep [true] n,[true,false,true,true]⟩ := by rfl

theorem outer (n : Nat) :
    run0 p (4*n+9) ⟨1,[],[false,true] ++ rep [true] n⟩ =
    some ⟨1,[],[true] ++ rep [true] n ++ [false,true,true]⟩ := by
  have h0 := outerEntry n
  have h1 : run0 p (3*n) ⟨1,[false,true],[false] ++ rep [true] n⟩ =
      some ⟨1,[false,true] ++ rep [true] n,[false]⟩ := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using (sweepR p 1 [false,true] [false] [true] [true] 3 transferR n [] [])
  have h2 := outerTurn n
  have h3 : run0 p n ⟨1,rep [true] n,[true,false,true,true]⟩ =
      some ⟨1,[],[true] ++ rep [true] n ++ [false,true,true]⟩ := by
    simpa only [Nat.one_mul,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using (sweepL p 1 [] [true] [true] [true] 1 transferL n [] [false,true,true])
  have h := join0 (join0 (join0 h0 h1) h2) h3
  rw [show 3+3*n+6+n = 4*n+9 by omega] at h
  exact h

def size : Nat → Nat
  | 0 => 3
  | n+1 => 2*size n+3

def family (n : Nat) : Z0 := ⟨1,[],[false,true] ++ rep [true] (size n)⟩

theorem first : run0 p 12 ⟨0,[],[]⟩ = some (family 0) := by decide

theorem grow (n : Nat) : run0 p (4*size n+9+drainCost (size n)) (family n) =
    some (family (n+1)) := by
  have h0 := outer (size n)
  have h1 : run0 p (drainCost (size n))
      ⟨1,[],[true] ++ rep [true] (size n) ++ [false,true,true]⟩ =
      some ⟨1,[],[false] ++ rep [true,true] (size n+1) ++ [true,true]⟩ := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using drain (size n) [true,true]
  have h := join0 h0 h1
  have he : (⟨1,[],[false] ++ rep [true,true] (size n+1) ++ [true,true]⟩ : Z0) = family (n+1) := by
    rw [repDouble]
    unfold family
    rw [size, show 2*(size n+1) = 2*size n+2 by omega]
    -- Move the last two ones to the exponent and unfold one leading one.
    have ha : rep [true] (2*size n+2) ++ [true,true] = [true] ++ rep [true] (2*size n+3) := by
      calc
        _ = rep [true] (2*size n+2) ++ rep [true] 2 := by rfl
        _ = rep [true] (2*size n+2+2) := (repAdd [true] (2*size n+2) 2).symm
        _ = rep [true] ((2*size n+3)+1) := by congr 1 <;> omega
        _ = _ := by rfl
    have hb := congrArg (fun w => (⟨1,[],[false] ++ w⟩ : Z0)) ha
    simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using hb
  rw [he] at h
  exact h

theorem never : ∀ m, compatible p m → NeverHalts m :=
  never_of_growth p family 12 (fun n => 4*size n+9+drainCost (size n)) first (by omega) grow
#print axioms never
end OneLBZeroRD

namespace OneLCOneLC
def p : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨true,false,2⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => some (some ⟨true,false,2⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨false,false,1⟩)
  | _ => none

theorem innerEntry (n : Nat) (R : List Bool) :
    run0 p 5 ⟨2,[],[true,true] ++ rep [true] n ++ [false] ++ R⟩ =
    some ⟨1,[false,true],[false] ++ rep [true] n ++ [false] ++ R⟩ := by rfl

theorem transferR (L R : List Bool) :
    run0 p 3 ⟨1,[false,true] ++ L,[false] ++ [true] ++ R⟩ =
    some ⟨1,[false,true] ++ [true] ++ L,[false] ++ R⟩ := by rfl

theorem innerTurn (n : Nat) (R : List Bool) :
    run0 p 6 ⟨1,[false,true] ++ rep [true] n,[false,false] ++ R⟩ =
    some ⟨2,rep [true] n,[true,false,true,true] ++ R⟩ := by rfl

theorem transferL (L R : List Bool) :
    run0 p 1 ⟨2,[] ++ [true] ++ L,[true] ++ R⟩ =
    some ⟨2,[] ++ L,[true] ++ [true] ++ R⟩ := by rfl

theorem inner (n : Nat) (R : List Bool) :
    run0 p (4*n+11) ⟨2,[],[true,true] ++ rep [true] n ++ [false] ++ R⟩ =
    some ⟨2,[],[true] ++ rep [true] n ++ [false,true,true] ++ R⟩ := by
  have h0 := innerEntry n R
  have h1 : run0 p (3*n)
      ⟨1,[false,true],[false] ++ rep [true] n ++ [false] ++ R⟩ =
      some ⟨1,[false,true] ++ rep [true] n,[false,false] ++ R⟩ := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using (sweepR p 1 [false,true] [false] [true] [true] 3 transferR n [] ([false] ++ R))
  have h2 := innerTurn n R
  have h3 : run0 p n
      ⟨2,rep [true] n,[true,false,true,true] ++ R⟩ =
      some ⟨2,[],[true] ++ rep [true] n ++ [false,true,true] ++ R⟩ := by
    simpa only [Nat.one_mul,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using (sweepL p 2 [] [true] [true] [true] 1 transferL n [] ([false,true,true] ++ R))
  have h := join0 (join0 (join0 h0 h1) h2) h3
  rw [show 5+3*n+6+n = 4*n+11 by omega] at h
  exact h

theorem last (R : List Bool) : run0 p 7 ⟨2,[],[true,false] ++ R⟩ =
    some ⟨1,[],[false,true,true] ++ R⟩ := by rfl

def drainCost : Nat → Nat
  | 0 => 7
  | n+1 => (4*n+11) + drainCost n

theorem drain (n : Nat) (R : List Bool) :
    run0 p (drainCost n) ⟨2,[],[true] ++ rep [true] n ++ [false] ++ R⟩ =
    some ⟨1,[],[false] ++ rep [true,true] (n+1) ++ R⟩ := by
  induction n generalizing R with
  | zero => simpa only [drainCost,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using last R
  | succ n ih =>
    have h0 := inner n R
    have h1 : run0 p (drainCost n)
        ⟨2,[],[true] ++ rep [true] n ++ [false,true,true] ++ R⟩ =
        some ⟨1,[],[false] ++ rep [true,true] (n+1) ++ [true,true] ++ R⟩ := by
      simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using ih ([true,true] ++ R)
    have h := join0 h0 h1
    have he : (⟨1,[],[false] ++ rep [true,true] (n+1) ++ [true,true] ++ R⟩ : Z0) =
        ⟨1,[],[false] ++ rep [true,true] (n+2) ++ R⟩ := by
      have hs := congrArg (fun w => (⟨1,[],[false] ++ w ++ R⟩ : Z0)) (rep_snoc [true,true] (n+1))
      simpa only [rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using hs
    rw [he] at h
    simpa only [drainCost,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using h

theorem outerEntry (n : Nat) :
    run0 p 3 ⟨1,[],[false,true] ++ rep [true] n⟩ =
    some ⟨1,[false,true],[false] ++ rep [true] n⟩ := by rfl

theorem outerTurn (n : Nat) :
    run0 p 6 ⟨1,[false,true] ++ rep [true] n,[false]⟩ =
    some ⟨2,rep [true] n,[true,false,true,true]⟩ := by rfl

theorem outer (n : Nat) :
    run0 p (4*n+9) ⟨1,[],[false,true] ++ rep [true] n⟩ =
    some ⟨2,[],[true] ++ rep [true] n ++ [false,true,true]⟩ := by
  have h0 := outerEntry n
  have h1 : run0 p (3*n) ⟨1,[false,true],[false] ++ rep [true] n⟩ =
      some ⟨1,[false,true] ++ rep [true] n,[false]⟩ := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using (sweepR p 1 [false,true] [false] [true] [true] 3 transferR n [] [])
  have h2 := outerTurn n
  have h3 : run0 p n ⟨2,rep [true] n,[true,false,true,true]⟩ =
      some ⟨2,[],[true] ++ rep [true] n ++ [false,true,true]⟩ := by
    simpa only [Nat.one_mul,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using (sweepL p 2 [] [true] [true] [true] 1 transferL n [] [false,true,true])
  have h := join0 (join0 (join0 h0 h1) h2) h3
  rw [show 3+3*n+6+n = 4*n+9 by omega] at h
  exact h

def size : Nat → Nat
  | 0 => 3
  | n+1 => 2*size n+3

def family (n : Nat) : Z0 := ⟨1,[],[false,true] ++ rep [true] (size n)⟩

theorem first : run0 p 14 ⟨0,[],[]⟩ = some (family 0) := by decide

theorem grow (n : Nat) : run0 p (4*size n+9+drainCost (size n)) (family n) =
    some (family (n+1)) := by
  have h0 := outer (size n)
  have h1 : run0 p (drainCost (size n))
      ⟨2,[],[true] ++ rep [true] (size n) ++ [false,true,true]⟩ =
      some ⟨1,[],[false] ++ rep [true,true] (size n+1) ++ [true,true]⟩ := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using drain (size n) [true,true]
  have h := join0 h0 h1
  have he : (⟨1,[],[false] ++ rep [true,true] (size n+1) ++ [true,true]⟩ : Z0) = family (n+1) := by
    rw [repDouble]
    unfold family
    rw [size, show 2*(size n+1) = 2*size n+2 by omega]
    -- Move the last two ones to the exponent and unfold one leading one.
    have ha : rep [true] (2*size n+2) ++ [true,true] = [true] ++ rep [true] (2*size n+3) := by
      calc
        _ = rep [true] (2*size n+2) ++ rep [true] 2 := by rfl
        _ = rep [true] (2*size n+2+2) := (repAdd [true] (2*size n+2) 2).symm
        _ = rep [true] ((2*size n+3)+1) := by congr 1 <;> omega
        _ = _ := by rfl
    have hb := congrArg (fun w => (⟨1,[],[false] ++ w⟩ : Z0)) ha
    simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using hb
  rw [he] at h
  exact h

theorem never : ∀ m, compatible p m → NeverHalts m :=
  never_of_growth p family 14 (fun n => 4*size n+9+drainCost (size n)) first (by omega) grow
#print axioms never
end OneLCOneLC

end BB6.Agent32Raw42Nested
