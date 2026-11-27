import SweepPumping

open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 4096
namespace BB6.Agent32Raw42Wide

theorem slideBit (b : Bool) (n k : Nat) :
    rep [b] k ++ rep [b,b] n = rep [b,b] n ++ rep [b] k := by
  induction k with
  | zero => simp [rep]
  | succ k ih =>
    calc
      rep [b] (k+1) ++ rep [b,b] n = [b] ++ (rep [b] k ++ rep [b,b] n) := by simp only [rep,List.append_assoc]
      _ = [b] ++ (rep [b,b] n ++ rep [b] k) := by rw [ih]
      _ = ([b] ++ rep [b,b] n) ++ rep [b] k := by simp only [List.append_assoc]
      _ = (rep [b,b] n ++ [b]) ++ rep [b] k := by rw [show [b] ++ rep [b,b] n = rep [b,b] n ++ [b] from rotate b [b] n]
      _ = rep [b,b] n ++ rep [b] (k+1) := by simp only [rep,List.append_assoc]

namespace ZeroLAOneRC

def p : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨true,true,2⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨false,false,0⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨false,false,1⟩)
  | _ => none

def family (n : Nat) : Z0 := ⟨3,[false,false,true] ++ rep [true,true] n ++ [true,true,true],[]⟩

theorem first : run0 p 16 ⟨0,[],[]⟩ = some (family 0) := by decide

theorem transfer0 (L R : List Bool) : run0 p 6 ⟨3,[false,false,true] ++ [true,true] ++ L,[] ++ R⟩ = some ⟨3,[false,false,true] ++ L,[] ++ [true,true] ++ R⟩ := by rfl

theorem phase1 (n : Nat) : run0 p 11 ⟨3,[false,false,true,true,true,true],rep [true,true] n⟩ = some ⟨1,[false,true],[false,true,true,true,true] ++ rep [true,true] n⟩ := by rfl

theorem transfer2 (L R : List Bool) : run0 p 6 ⟨1,[false] ++ L,[false,true,true,true,true] ++ [true,true] ++ R⟩ = some ⟨1,[false] ++ [true,true] ++ L,[false,true,true,true,true] ++ R⟩ := by rfl

theorem phase3 (n : Nat) : run0 p 14 ⟨1,[false] ++ rep [true,true] n ++ [true],[false,true,true,true,true]⟩ = some ⟨3,[false,false,true,true,true,true,true] ++ rep [true,true] n ++ [true],[]⟩ := by rfl

theorem grow (n : Nat) : run0 p (12*n+25) (family n) = some (family (n+1)) := by
  have h0 : run0 p (6*n) (family n) = some ⟨3,[false,false,true,true,true,true],rep [true,true] n⟩ := by
    simpa only [family,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using
      (sweepL p 3 [false,false,true] [] [true,true] [true,true] 6 transfer0 n [true,true,true] [])
  have h1 := phase1 n
  have h2 : run0 p (6*n) ⟨1,[false,true],[false,true,true,true,true] ++ rep [true,true] n⟩ = some ⟨1,[false] ++ rep [true,true] n ++ [true],[false,true,true,true,true]⟩ := by
    simpa only [family,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using
      (sweepR p 1 [false] [false,true,true,true,true] [true,true] [true,true] 6 transfer2 n [true] [])
  have h3 := phase3 n
  have h := join0 (join0 (join0 (h0) h1) h2) h3
  rw [show 6*n+11+6*n+14 = 12*n+25 by omega] at h
  have he : (⟨3,[false,false,true,true,true,true,true] ++ rep [true,true] n ++ [true],[]⟩ : Z0) = family (n+1) := by
    have hs := congrArg (fun w => (⟨3,[false,false,true,true,true] ++ w ++ [true],[]⟩ : Z0)) (slideBit true n 2)
    simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using hs
  rw [he] at h
  exact h

theorem never : ∀ m, compatible p m → NeverHalts m :=
  never_of_growth p family 16 (fun n => 12*n+25) first (by omega) grow
#print axioms never

end ZeroLAOneRC

namespace OneLAZeroRD

def p : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨false,true,3⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨true,false,0⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨false,false,1⟩)
  | _ => none

def family (n : Nat) : Z0 := ⟨3,[false,false,true] ++ rep [true,true] n ++ [true,true,true,true],[]⟩

theorem first : run0 p 30 ⟨0,[],[]⟩ = some (family 0) := by decide

theorem transfer0 (L R : List Bool) : run0 p 8 ⟨3,[false,false,true] ++ [true,true] ++ L,[] ++ R⟩ = some ⟨3,[false,false,true] ++ L,[] ++ [true,true] ++ R⟩ := by rfl

theorem phase1 (n : Nat) : run0 p 20 ⟨3,[false,false,true,true,true,true,true],rep [true,true] n⟩ = some ⟨2,[false,true],[true,true,true,true,true,true] ++ rep [true,true] n⟩ := by rfl

theorem transfer2 (L R : List Bool) : run0 p 6 ⟨2,[false] ++ L,[true,true,true,true,true,true] ++ [true,true] ++ R⟩ = some ⟨2,[false] ++ [true,true] ++ L,[true,true,true,true,true,true] ++ R⟩ := by rfl

theorem phase3 (n : Nat) : run0 p 19 ⟨2,[false] ++ rep [true,true] n ++ [true],[true,true,true,true,true,true]⟩ = some ⟨3,[false,false,true,true,true,true,true,true] ++ rep [true,true] n ++ [true],[]⟩ := by rfl

theorem grow (n : Nat) : run0 p (14*n+39) (family n) = some (family (n+1)) := by
  have h0 : run0 p (8*n) (family n) = some ⟨3,[false,false,true,true,true,true,true],rep [true,true] n⟩ := by
    simpa only [family,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using
      (sweepL p 3 [false,false,true] [] [true,true] [true,true] 8 transfer0 n [true,true,true,true] [])
  have h1 := phase1 n
  have h2 : run0 p (6*n) ⟨2,[false,true],[true,true,true,true,true,true] ++ rep [true,true] n⟩ = some ⟨2,[false] ++ rep [true,true] n ++ [true],[true,true,true,true,true,true]⟩ := by
    simpa only [family,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using
      (sweepR p 2 [false] [true,true,true,true,true,true] [true,true] [true,true] 6 transfer2 n [true] [])
  have h3 := phase3 n
  have h := join0 (join0 (join0 (h0) h1) h2) h3
  rw [show 8*n+20+6*n+19 = 14*n+39 by omega] at h
  have he : (⟨3,[false,false,true,true,true,true,true,true] ++ rep [true,true] n ++ [true],[]⟩ : Z0) = family (n+1) := by
    have hs := congrArg (fun w => (⟨3,[false,false,true,true,true] ++ w ++ [true],[]⟩ : Z0)) (slideBit true n 3)
    simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using hs
  rw [he] at h
  exact h

theorem never : ∀ m, compatible p m → NeverHalts m :=
  never_of_growth p family 30 (fun n => 14*n+39) first (by omega) grow
#print axioms never

end OneLAZeroRD

namespace OneLCZeroRB

def p : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨true,false,2⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => some (some ⟨false,true,1⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨false,false,1⟩)
  | _ => none

def family (n : Nat) : Z0 := ⟨3,[false,false,true] ++ rep [true,true] n ++ [true,true,true,true],[]⟩

theorem first : run0 p 28 ⟨0,[],[]⟩ = some (family 0) := by decide

theorem transfer0 (L R : List Bool) : run0 p 10 ⟨3,[false,false,true] ++ [true,true] ++ L,[] ++ R⟩ = some ⟨3,[false,false,true] ++ L,[] ++ [true,true] ++ R⟩ := by rfl

theorem phase1 (n : Nat) : run0 p 24 ⟨3,[false,false,true,true,true,true,true],rep [true,true] n⟩ = some ⟨2,[false,true],[true,true,true,true,true,true] ++ rep [true,true] n⟩ := by rfl

theorem transfer2 (L R : List Bool) : run0 p 6 ⟨2,[false] ++ L,[true,true,true,true,true,true] ++ [true,true] ++ R⟩ = some ⟨2,[false] ++ [true,true] ++ L,[true,true,true,true,true,true] ++ R⟩ := by rfl

theorem phase3 (n : Nat) : run0 p 19 ⟨2,[false] ++ rep [true,true] n ++ [true],[true,true,true,true,true,true]⟩ = some ⟨3,[false,false,true,true,true,true,true,true] ++ rep [true,true] n ++ [true],[]⟩ := by rfl

theorem grow (n : Nat) : run0 p (16*n+43) (family n) = some (family (n+1)) := by
  have h0 : run0 p (10*n) (family n) = some ⟨3,[false,false,true,true,true,true,true],rep [true,true] n⟩ := by
    simpa only [family,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using
      (sweepL p 3 [false,false,true] [] [true,true] [true,true] 10 transfer0 n [true,true,true,true] [])
  have h1 := phase1 n
  have h2 : run0 p (6*n) ⟨2,[false,true],[true,true,true,true,true,true] ++ rep [true,true] n⟩ = some ⟨2,[false] ++ rep [true,true] n ++ [true],[true,true,true,true,true,true]⟩ := by
    simpa only [family,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using
      (sweepR p 2 [false] [true,true,true,true,true,true] [true,true] [true,true] 6 transfer2 n [true] [])
  have h3 := phase3 n
  have h := join0 (join0 (join0 (h0) h1) h2) h3
  rw [show 10*n+24+6*n+19 = 16*n+43 by omega] at h
  have he : (⟨3,[false,false,true,true,true,true,true,true] ++ rep [true,true] n ++ [true],[]⟩ : Z0) = family (n+1) := by
    have hs := congrArg (fun w => (⟨3,[false,false,true,true,true] ++ w ++ [true],[]⟩ : Z0)) (slideBit true n 3)
    simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using hs
  rw [he] at h
  exact h

theorem never : ∀ m, compatible p m → NeverHalts m :=
  never_of_growth p family 28 (fun n => 16*n+43) first (by omega) grow
#print axioms never

end OneLCZeroRB

namespace OneLCZeroRD

def p : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨true,false,2⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => some (some ⟨false,true,3⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨false,false,1⟩)
  | _ => none

def family (n : Nat) : Z0 := ⟨3,[false,false,true] ++ rep [true,true] n ++ [true,true,true,true],[]⟩

theorem first : run0 p 28 ⟨0,[],[]⟩ = some (family 0) := by decide

theorem transfer0 (L R : List Bool) : run0 p 8 ⟨3,[false,false,true] ++ [true,true] ++ L,[] ++ R⟩ = some ⟨3,[false,false,true] ++ L,[] ++ [true,true] ++ R⟩ := by rfl

theorem phase1 (n : Nat) : run0 p 20 ⟨3,[false,false,true,true,true,true,true],rep [true,true] n⟩ = some ⟨2,[false,true],[true,true,true,true,true,true] ++ rep [true,true] n⟩ := by rfl

theorem transfer2 (L R : List Bool) : run0 p 6 ⟨2,[false] ++ L,[true,true,true,true,true,true] ++ [true,true] ++ R⟩ = some ⟨2,[false] ++ [true,true] ++ L,[true,true,true,true,true,true] ++ R⟩ := by rfl

theorem phase3 (n : Nat) : run0 p 19 ⟨2,[false] ++ rep [true,true] n ++ [true],[true,true,true,true,true,true]⟩ = some ⟨3,[false,false,true,true,true,true,true,true] ++ rep [true,true] n ++ [true],[]⟩ := by rfl

theorem grow (n : Nat) : run0 p (14*n+39) (family n) = some (family (n+1)) := by
  have h0 : run0 p (8*n) (family n) = some ⟨3,[false,false,true,true,true,true,true],rep [true,true] n⟩ := by
    simpa only [family,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using
      (sweepL p 3 [false,false,true] [] [true,true] [true,true] 8 transfer0 n [true,true,true,true] [])
  have h1 := phase1 n
  have h2 : run0 p (6*n) ⟨2,[false,true],[true,true,true,true,true,true] ++ rep [true,true] n⟩ = some ⟨2,[false] ++ rep [true,true] n ++ [true],[true,true,true,true,true,true]⟩ := by
    simpa only [family,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using
      (sweepR p 2 [false] [true,true,true,true,true,true] [true,true] [true,true] 6 transfer2 n [true] [])
  have h3 := phase3 n
  have h := join0 (join0 (join0 (h0) h1) h2) h3
  rw [show 8*n+20+6*n+19 = 14*n+39 by omega] at h
  have he : (⟨3,[false,false,true,true,true,true,true,true] ++ rep [true,true] n ++ [true],[]⟩ : Z0) = family (n+1) := by
    have hs := congrArg (fun w => (⟨3,[false,false,true,true,true] ++ w ++ [true],[]⟩ : Z0)) (slideBit true n 3)
    simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using hs
  rw [he] at h
  exact h

theorem never : ∀ m, compatible p m → NeverHalts m :=
  never_of_growth p family 28 (fun n => 14*n+39) first (by omega) grow
#print axioms never

end OneLCZeroRD

namespace OneRBOneLC

def p : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨true,true,1⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => some (some ⟨true,false,2⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨false,false,1⟩)
  | _ => none

def family (n : Nat) : Z0 := ⟨3,[false,false,true,true] ++ rep [true,true] n ++ [true,true],[]⟩

theorem first : run0 p 24 ⟨0,[],[]⟩ = some (family 0) := by decide

theorem phase0 (n : Nat) : run0 p 5 ⟨3,[false,false,true,true] ++ rep [true,true] n ++ [true,true],[]⟩ = some ⟨2,[true,true,true] ++ rep [true,true] n ++ [true,true],[true]⟩ := by rfl

theorem transfer1 (L R : List Bool) : run0 p 2 ⟨2,[true,true,true] ++ [true,true] ++ L,[] ++ R⟩ = some ⟨2,[true,true,true] ++ L,[] ++ [true,true] ++ R⟩ := by rfl

theorem phase2 (n : Nat) : run0 p 6 ⟨2,[true,true,true,true,true],rep [true,true] n ++ [true]⟩ = some ⟨3,[true,false],[true,true,true,true] ++ rep [true,true] n ++ [true]⟩ := by rfl

theorem transfer3 (L R : List Bool) : run0 p 6 ⟨3,[true,false] ++ L,[true,true,true,true] ++ [true,true] ++ R⟩ = some ⟨3,[true,false] ++ [true,true] ++ L,[true,true,true,true] ++ R⟩ := by rfl

theorem phase4 (n : Nat) : run0 p 18 ⟨3,[true,false] ++ rep [true,true] n,[true,true,true,true,true]⟩ = some ⟨3,[false,false,true,true,true,true,true,true] ++ rep [true,true] n,[]⟩ := by rfl

theorem grow (n : Nat) : run0 p (8*n+29) (family n) = some (family (n+1)) := by
  have h0 := phase0 n
  have h1 : run0 p (2*n) ⟨2,[true,true,true] ++ rep [true,true] n ++ [true,true],[true]⟩ = some ⟨2,[true,true,true,true,true],rep [true,true] n ++ [true]⟩ := by
    simpa only [family,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using
      (sweepL p 2 [true,true,true] [] [true,true] [true,true] 2 transfer1 n [true,true] [true])
  have h2 := phase2 n
  have h3 : run0 p (6*n) ⟨3,[true,false],[true,true,true,true] ++ rep [true,true] n ++ [true]⟩ = some ⟨3,[true,false] ++ rep [true,true] n,[true,true,true,true,true]⟩ := by
    simpa only [family,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using
      (sweepR p 3 [true,false] [true,true,true,true] [true,true] [true,true] 6 transfer3 n [] [true])
  have h4 := phase4 n
  have h := join0 (join0 (join0 (join0 (h0) h1) h2) h3) h4
  rw [show 5+2*n+6+6*n+18 = 8*n+29 by omega] at h
  have he : (⟨3,[false,false,true,true,true,true,true,true] ++ rep [true,true] n,[]⟩ : Z0) = family (n+1) := by
    have hs := congrArg (fun w => (⟨3,[false,false,true,true,true,true] ++ w ++ [],[]⟩ : Z0)) (slideBit true n 2)
    simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using hs
  rw [he] at h
  exact h

theorem never : ∀ m, compatible p m → NeverHalts m :=
  never_of_growth p family 24 (fun n => 8*n+29) first (by omega) grow
#print axioms never

end OneRBOneLC

namespace OneLBOneRC

def p : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨true,false,1⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => some (some ⟨true,true,2⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨false,false,1⟩)
  | _ => none

def family (n : Nat) : Z0 := ⟨3,[false,false,true] ++ rep [true,true] n ++ [true,true,true],[]⟩

theorem first : run0 p 16 ⟨0,[],[]⟩ = some (family 0) := by decide

theorem phase0 (n : Nat) : run0 p 3 ⟨3,[false,false,true] ++ rep [true,true] n ++ [true,true,true],[]⟩ = some ⟨1,rep [true,true] n ++ [true,true,true],[false,true,true]⟩ := by rfl

theorem transfer1 (L R : List Bool) : run0 p 2 ⟨1,[] ++ [true,true] ++ L,[] ++ R⟩ = some ⟨1,[] ++ L,[] ++ [true,true] ++ R⟩ := by rfl

theorem phase2 (n : Nat) : run0 p 4 ⟨1,[true,true,true],rep [true,true] n ++ [false,true,true]⟩ = some ⟨2,[true,true],[true,true] ++ rep [true,true] n ++ [false,true,true]⟩ := by rfl

theorem transfer3 (L R : List Bool) : run0 p 2 ⟨2,[true] ++ L,[true,true] ++ [true,true] ++ R⟩ = some ⟨2,[true] ++ [true,true] ++ L,[true,true] ++ R⟩ := by rfl

theorem phase4 (n : Nat) : run0 p 10 ⟨2,[true] ++ rep [true,true] n ++ [true],[true,true,false,true,true]⟩ = some ⟨3,[false,false,true,true,true,true,true] ++ rep [true,true] n ++ [true],[]⟩ := by rfl

theorem grow (n : Nat) : run0 p (4*n+17) (family n) = some (family (n+1)) := by
  have h0 := phase0 n
  have h1 : run0 p (2*n) ⟨1,rep [true,true] n ++ [true,true,true],[false,true,true]⟩ = some ⟨1,[true,true,true],rep [true,true] n ++ [false,true,true]⟩ := by
    simpa only [family,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using
      (sweepL p 1 [] [] [true,true] [true,true] 2 transfer1 n [true,true,true] [false,true,true])
  have h2 := phase2 n
  have h3 : run0 p (2*n) ⟨2,[true,true],[true,true] ++ rep [true,true] n ++ [false,true,true]⟩ = some ⟨2,[true] ++ rep [true,true] n ++ [true],[true,true,false,true,true]⟩ := by
    simpa only [family,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using
      (sweepR p 2 [true] [true,true] [true,true] [true,true] 2 transfer3 n [true] [false,true,true])
  have h4 := phase4 n
  have h := join0 (join0 (join0 (join0 (h0) h1) h2) h3) h4
  rw [show 3+2*n+4+2*n+10 = 4*n+17 by omega] at h
  have he : (⟨3,[false,false,true,true,true,true,true] ++ rep [true,true] n ++ [true],[]⟩ : Z0) = family (n+1) := by
    have hs := congrArg (fun w => (⟨3,[false,false,true,true,true] ++ w ++ [true],[]⟩ : Z0)) (slideBit true n 2)
    simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using hs
  rw [he] at h
  exact h

theorem never : ∀ m, compatible p m → NeverHalts m :=
  never_of_growth p family 16 (fun n => 4*n+17) first (by omega) grow
#print axioms never

end OneLBOneRC

namespace OneREOneLD

def p : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨true,true,4⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨false,false,1⟩)
  | (4,false) => some (some ⟨true,false,3⟩)
  | _ => none

def family (n : Nat) : Z0 := ⟨3,[false,false,true] ++ rep [true,true] n ++ [true,true,true],[]⟩

theorem first : run0 p 20 ⟨0,[],[]⟩ = some (family 0) := by decide

theorem phase0 (n : Nat) : run0 p 2 ⟨3,[false,false,true] ++ rep [true,true] n ++ [true,true,true],[]⟩ = some ⟨3,[true] ++ rep [true,true] n ++ [true,true,true],[true,true]⟩ := by rfl

theorem transfer1 (L R : List Bool) : run0 p 6 ⟨3,[true] ++ [true,true] ++ L,[] ++ R⟩ = some ⟨3,[true] ++ L,[] ++ [true,true] ++ R⟩ := by rfl

theorem phase2 (n : Nat) : run0 p 11 ⟨3,[true,true,true,true],rep [true,true] n ++ [true,true]⟩ = some ⟨2,[false,true],[true,true,true] ++ rep [true,true] n ++ [true,true]⟩ := by rfl

theorem transfer3 (L R : List Bool) : run0 p 6 ⟨2,[false] ++ L,[true,true,true] ++ [true,true] ++ R⟩ = some ⟨2,[false] ++ [true,true] ++ L,[true,true,true] ++ R⟩ := by rfl

theorem phase4 (n : Nat) : run0 p 16 ⟨2,[false] ++ rep [true,true] n ++ [true],[true,true,true,true,true]⟩ = some ⟨3,[false,false,true,true,true,true,true] ++ rep [true,true] n ++ [true],[]⟩ := by rfl

theorem grow (n : Nat) : run0 p (12*n+29) (family n) = some (family (n+1)) := by
  have h0 := phase0 n
  have h1 : run0 p (6*n) ⟨3,[true] ++ rep [true,true] n ++ [true,true,true],[true,true]⟩ = some ⟨3,[true,true,true,true],rep [true,true] n ++ [true,true]⟩ := by
    simpa only [family,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using
      (sweepL p 3 [true] [] [true,true] [true,true] 6 transfer1 n [true,true,true] [true,true])
  have h2 := phase2 n
  have h3 : run0 p (6*n) ⟨2,[false,true],[true,true,true] ++ rep [true,true] n ++ [true,true]⟩ = some ⟨2,[false] ++ rep [true,true] n ++ [true],[true,true,true,true,true]⟩ := by
    simpa only [family,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using
      (sweepR p 2 [false] [true,true,true] [true,true] [true,true] 6 transfer3 n [true] [true,true])
  have h4 := phase4 n
  have h := join0 (join0 (join0 (join0 (h0) h1) h2) h3) h4
  rw [show 2+6*n+11+6*n+16 = 12*n+29 by omega] at h
  have he : (⟨3,[false,false,true,true,true,true,true] ++ rep [true,true] n ++ [true],[]⟩ : Z0) = family (n+1) := by
    have hs := congrArg (fun w => (⟨3,[false,false,true,true,true] ++ w ++ [true],[]⟩ : Z0)) (slideBit true n 2)
    simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using hs
  rw [he] at h
  exact h

theorem never : ∀ m, compatible p m → NeverHalts m :=
  never_of_growth p family 20 (fun n => 12*n+29) first (by omega) grow
#print axioms never

end OneREOneLD

namespace OneRBZeroRC

def p : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨true,true,1⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => some (some ⟨false,true,2⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨false,false,1⟩)
  | _ => none

def family (n : Nat) : Z0 := ⟨3,rep [false,false] n ++ [false,false,false,false,true,true],[]⟩

theorem first : run0 p 11 ⟨0,[],[]⟩ = some (family 0) := by decide

theorem transfer0 (L R : List Bool) : run0 p 2 ⟨3,[] ++ [false,false] ++ L,[] ++ R⟩ = some ⟨3,[] ++ L,[] ++ [true,true] ++ R⟩ := by rfl

theorem phase1 (n : Nat) : run0 p 7 ⟨3,[false,false,false,false,true,true],rep [true,true] n⟩ = some ⟨2,[true,true,true],[true,true,true] ++ rep [true,true] n⟩ := by rfl

theorem transfer2 (L R : List Bool) : run0 p 2 ⟨2,[true] ++ L,[true,true,true] ++ [true,true] ++ R⟩ = some ⟨2,[true] ++ [false,false] ++ L,[true,true,true] ++ R⟩ := by rfl

theorem phase3 (n : Nat) : run0 p 5 ⟨2,[true] ++ rep [false,false] n ++ [true,true],[true,true,true]⟩ = some ⟨3,[false,false,false,false,false,false] ++ rep [false,false] n ++ [true,true],[]⟩ := by rfl

theorem grow (n : Nat) : run0 p (4*n+12) (family n) = some (family (n+1)) := by
  have h0 : run0 p (2*n) (family n) = some ⟨3,[false,false,false,false,true,true],rep [true,true] n⟩ := by
    simpa only [family,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using
      (sweepL p 3 [] [] [false,false] [true,true] 2 transfer0 n [false,false,false,false,true,true] [])
  have h1 := phase1 n
  have h2 : run0 p (2*n) ⟨2,[true,true,true],[true,true,true] ++ rep [true,true] n⟩ = some ⟨2,[true] ++ rep [false,false] n ++ [true,true],[true,true,true]⟩ := by
    simpa only [family,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using
      (sweepR p 2 [true] [true,true,true] [true,true] [false,false] 2 transfer2 n [true,true] [])
  have h3 := phase3 n
  have h := join0 (join0 (join0 (h0) h1) h2) h3
  rw [show 2*n+7+2*n+5 = 4*n+12 by omega] at h
  have he : (⟨3,[false,false,false,false,false,false] ++ rep [false,false] n ++ [true,true],[]⟩ : Z0) = family (n+1) := by
    have hs := congrArg (fun w => (⟨3,[false,false] ++ w ++ [true,true],[]⟩ : Z0)) (slideBit false n 4)
    simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using hs
  rw [he] at h
  exact h

theorem never : ∀ m, compatible p m → NeverHalts m :=
  never_of_growth p family 11 (fun n => 4*n+12) first (by omega) grow
#print axioms never

end OneRBZeroRC

end BB6.Agent32Raw42Wide
