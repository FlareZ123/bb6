import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BB6.Agent16Raw44C1RA_A1LE_F1Variants
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/-!
Two C1=1RA, A1=1LE, E0=1LF, E1=0LA counters with F1=1LE/1LC.
F0 is unrestricted.  The F-head normal form has a block of n repeating
1110 words to its left (nearest-head-first), followed by 1111, and the
fixed right word 1101.  One full phase adds one 1110 word.
The 22n+58/24n+60 laws are original-machine exact path identities, and
never_of_growth promotes it to all 25 F0 assignments.
-/
def table (toC : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true  => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true  => some (some ⟨false,false,0⟩)
  | 5,true  => some (some ⟨true,false,if toC then 2 else 4⟩)
  | _,_ => none

def ones (n : Nat) : List Bool := rep [true] n
def U (n : Nat) : List Bool := rep [true,true,true,false] n
def V (n : Nat) : List Bool := rep [true,true,false,true] n
def W (n : Nat) : List Bool := rep [true,true,true,false] n
def X (n : Nat) : List Bool := rep [false,true] n
def Y (n : Nat) : List Bool := rep [true,false,true,false] n
def Z (n : Nat) : List Bool := rep [true,true,false,true] n

private theorem rep_add (P : List Bool) (n m : Nat) :
    rep P (n+m) = rep P n ++ rep P m := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rep,ih,List.append_assoc]

private theorem rep2 (n : Nat) :
    rep [true,true] n = ones (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      rep [true,true] (n+1) = [true,true] ++ rep [true,true] n := by rfl
      _ = [true,true] ++ ones (2*n) := by rw [ih]
      _ = ones (2*(n+1)) := by
        rw [show 2*(n+1)=2*n+2 by omega]
        rfl

private theorem rep4 (n : Nat) :
    rep [true,true,true,true] n = ones (4*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      rep [true,true,true,true] (n+1) =
          [true,true,true,true] ++ rep [true,true,true,true] n := by rfl
      _ = [true,true,true,true] ++ ones (4*n) := by rw [ih]
      _ = ones (4*(n+1)) := by
        rw [show 4*(n+1)=4*n+4 by omega]
        rfl

private theorem rotateV (n : Nat) :
    [true] ++ V (n+1) = W (n+1) ++ [true] := by
  simpa only [V,W] using (rotate true [true,true,false] (n+1))

private theorem rotateX (n : Nat) :
    X (2*n+5) ++ [true] =
      [false,true,false] ++ Y (n+1) ++ [true,false,true,true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      X (2*(n+1)+5) ++ [true] =
        [false,true,false,true] ++ (X (2*n+5) ++ [true]) := by
          rw [show 2*(n+1)+5=2+(2*n+5) by omega]
          simp only [X,rep,List.append_assoc]
      _ = [false,true,false,true] ++
          ([false,true,false] ++ Y (n+1) ++ [true,false,true,true]) := by rw [ih]
      _ = [false,true,false] ++ Y (n+2) ++ [true,false,true,true] := by rfl

private theorem rotateZ (n : Nat) :
    [true] ++ Z (n+1) ++ [true,true,true] =
      U (n+1) ++ [true,true,true,true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      [true] ++ Z (n+2) ++ [true,true,true] =
        [true,true,true,false] ++ ([true] ++ Z (n+1) ++ [true,true,true]) := by rfl
      _ = [true,true,true,false] ++ (U (n+1) ++ [true,true,true,true]) := by rw [ih]
      _ = U (n+2) ++ [true,true,true,true] := by rfl

private theorem fpacket (toC : Bool) (L R : List Bool) :
    run0 (table toC) (if toC then 6 else 4) ⟨5,[true,true,true,false] ++ L,R⟩ =
      some ⟨5,L,[true,true,false,true] ++ R⟩ := by
  cases toC <;> rfl

private theorem ffinish (toC : Bool) (R : List Bool) :
    run0 (table toC) (if toC then 6 else 4) ⟨5,[true,true,true,true],R⟩ =
      some ⟨0,[],[false,true,false,true] ++ R⟩ := by
  cases toC <;> rfl

private theorem afront3 (toC : Bool) (R : List Bool) :
    run0 (table toC) 3 ⟨0,[],[false,true,false] ++ R⟩ =
      some ⟨0,[false,true,true,true],R⟩ := by cases toC <;> rfl

private theorem apacket (toC : Bool) (L R : List Bool) :
    run0 (table toC) 8 ⟨0,[false] ++ L,[true,true,true,false] ++ R⟩ =
      some ⟨0,[false,true,true,true,true] ++ L,R⟩ := by
  cases toC <;> rfl

private theorem afinish3 (toC : Bool) (L : List Bool) :
    run0 (table toC) 3 ⟨0,[false] ++ L,[true]⟩ =
      some ⟨3,[false,false,false,true] ++ L,[]⟩ := by cases toC <;> rfl

private theorem dzero3 (toC : Bool) (L : List Bool) :
    run0 (table toC) 3 ⟨3,[false,false,false] ++ L,[]⟩ =
      some ⟨3,L,[true,true,true]⟩ := by cases toC <;> rfl

private theorem dturn5 (toC : Bool) (L : List Bool) :
    run0 (table toC) 5 ⟨3,[true,true] ++ L,[true,true,true]⟩ =
      some ⟨0,[false] ++ L,[false,true,true,true]⟩ := by cases toC <;> rfl

private theorem amiddle5 (toC : Bool) (L : List Bool) :
    run0 (table toC) 5 ⟨0,[false] ++ L,[false,true,true,true]⟩ =
      some ⟨0,[true,true] ++ L,[false,true,true]⟩ := by cases toC <;> rfl

private theorem astep2 (toC : Bool) (L R : List Bool) :
    run0 (table toC) 2 ⟨0,[true,true] ++ L,R⟩ =
      some ⟨0,L,[false,true] ++ R⟩ := by cases toC <;> rfl

private theorem apacket2 (toC : Bool) (L R : List Bool) :
    run0 (table toC) 6 ⟨0,[false] ++ L,[true,false,true,false] ++ R⟩ =
      some ⟨0,[false,true,true,false,true] ++ L,R⟩ := by cases toC <;> rfl

private theorem afinish10 (toC : Bool) (L : List Bool) :
    run0 (table toC) 10 ⟨0,[false] ++ L,[true,false,true,true]⟩ =
      some ⟨5,[true] ++ L,[true,true,false,true]⟩ := by cases toC <;> rfl

def phase (n : Nat) : Z0 :=
  ⟨5,U n ++ [true,true,true,true],[true,true,false,true]⟩
def leftA (n : Nat) : Z0 :=
  ⟨0,[],[false,true,false,true] ++ V (n+1)⟩
def rightD (n : Nat) : Z0 :=
  ⟨3,[false,false,false] ++ ones (4*n+8),[]⟩
def leftA2 (n : Nat) : Z0 :=
  ⟨0,[],X (2*n+5) ++ [true]⟩

/-- F sweeps left through n 1110 blocks, then crosses the final 1111. -/
theorem stageF (toC : Bool) (n : Nat) :
    run0 (table toC) ((if toC then 6 else 4)*(n+1)) (phase n) = some (leftA n) := by
  have h1 : run0 (table toC) ((if toC then 6 else 4)*n) (phase n) =
      some ⟨5,[true,true,true,true],V n ++ [true,true,false,true]⟩ := by
    have H := sweepL (table toC) 5 [] [] [true,true,true,false] [true,true,false,true]
      (if toC then 6 else 4) (fpacket toC) n [true,true,true,true] [true,true,false,true]
    simpa only [phase,U,V,List.nil_append,List.append_assoc,
      List.append_nil] using H
  have h2 : run0 (table toC) (if toC then 6 else 4)
      ⟨5,[true,true,true,true],V n ++ [true,true,false,true]⟩ =
      some (leftA n) := by
    have H := ffinish toC (V n ++ [true,true,false,true])
    have hs : V n ++ [true,true,false,true] = V (n+1) := by
      unfold V
      rw [rep_snoc]
      rfl
    simpa only [leftA,hs,List.append_assoc] using H
  have H := join0 h1 h2
  have ht : ((if toC then 6 else 4)*n) + (if toC then 6 else 4) =
      (if toC then 6 else 4)*(n+1) := by cases toC <;> omega
  simpa only [ht] using H

/-- A traverses the 0100 word train rightward, filling it with ones. -/
theorem stageA (toC : Bool) (n : Nat) :
    run0 (table toC) (8*n+14) (leftA n) = some (rightD n) := by
  have h1 : run0 (table toC) 3 (leftA n) =
      some ⟨0,[false,true,true,true],W (n+1) ++ [true]⟩ := by
    have H := afront3 toC ([true] ++ V (n+1))
    have hv := rotateV n
    simpa only [leftA,hv,List.append_assoc,List.nil_append] using H
  have h2 : run0 (table toC) (8*(n+1))
      ⟨0,[false,true,true,true],W (n+1) ++ [true]⟩ =
      some ⟨0,[false] ++ rep [true,true,true,true] (n+1) ++ [true,true,true],[true]⟩ := by
    have H := sweepR (table toC) 0 [false] [] [true,true,true,false] [true,true,true,true]
      8 (apacket toC) (n+1) [true,true,true] [true]
    simpa only [W,List.cons_append,List.append_assoc,List.nil_append] using H
  have h3 : run0 (table toC) 3
      ⟨0,[false] ++ rep [true,true,true,true] (n+1) ++ [true,true,true],[true]⟩ =
      some (rightD n) := by
    have H := afinish3 toC (rep [true,true,true,true] (n+1) ++ [true,true,true])
    have hones : [true] ++ rep [true,true,true,true] (n+1) ++ [true,true,true] =
        ones (4*n+8) := by
      rw [rep4]
      unfold ones
      rw [show 4*n+8 = (1+4*(n+1))+3 by omega]
      rw [rep_add,rep_add]
      rfl
    simpa only [rightD,List.append_assoc,hones] using H
  have H := join0 (join0 h1 h2) h3
  have ht : (3+8*(n+1))+3=8*n+14 := by omega
  simpa only [ht] using H

/-- Rewind through the right blank and the uniform ones run, leaving
the 01 word train at a new leftmost blank. -/
theorem stageD (toC : Bool) (n : Nat) :
    run0 (table toC) (4*n+21) (rightD n) = some (leftA2 n) := by
  have h1 : run0 (table toC) 3 (rightD n) =
      some ⟨3,ones (4*n+8),[true,true,true]⟩ := by
    simpa only [rightD] using dzero3 toC (ones (4*n+8))
  have h2 : run0 (table toC) 5 ⟨3,ones (4*n+8),[true,true,true]⟩ =
      some ⟨0,[false] ++ ones (4*n+6),[false,true,true,true]⟩ := by
    have hsplit : ones (4*n+8) = [true,true] ++ ones (4*n+6) := by
      unfold ones
      rw [show 4*n+8=2+(4*n+6) by omega]
      rfl
    simpa only [hsplit] using dturn5 toC (ones (4*n+6))
  have h3 : run0 (table toC) 5
      ⟨0,[false] ++ ones (4*n+6),[false,true,true,true]⟩ =
      some ⟨0,ones (4*n+8),[false,true,true]⟩ := by
    have hsplit : ones (4*n+8) = [true,true] ++ ones (4*n+6) := by
      unfold ones
      rw [show 4*n+8=2+(4*n+6) by omega]
      rfl
    simpa only [hsplit] using amiddle5 toC (ones (4*n+6))
  have h4 : run0 (table toC) (4*n+8)
      ⟨0,ones (4*n+8),[false,true,true]⟩ =
      some (leftA2 n) := by
    have H := sweepL (table toC) 0 [] [] [true,true] [false,true]
      2 (astep2 toC) toC (2*n+4) [] [false,true,true]
    have hl : rep [true,true] (2*n+4) = ones (4*n+8) := by
      rw [rep2,show 2*(2*n+4)=4*n+8 by omega]
    have hr : rep [false,true] (2*n+4) ++ [false,true,true] =
        X (2*n+5) ++ [true] := by
      unfold X
      rw [show 2*n+5=(2*n+4)+1 by omega]
      calc
        rep [false,true] (2*n+4) ++ [false,true,true] =
          (rep [false,true] (2*n+4) ++ [false,true]) ++ [true] := by
            simp only [List.append_assoc,List.cons_append]
        _ = rep [false,true] ((2*n+4)+1) ++ [true] := by rw [rep_snoc]; rfl
    simpa only [leftA2,hl,hr,List.append_nil,List.nil_append] using H
  have H := join0 (join0 (join0 h1 h2) h3) h4
  have ht : ((3+5)+5)+(4*n+8)=4*n+21 := by omega
  simpa only [ht] using H

/-- A traverses the alternating word train and deposits a new 1110 block,
returning to the right-end F entry without ever evaluating F0. -/
theorem stageA2 (toC : Bool) (n : Nat) :
    run0 (table toC) (6*n+19) (leftA2 n) = some (phase (n+1)) := by
  have h1 : run0 (table toC) 3 (leftA2 n) =
      some ⟨0,[false,true,true,true],Y (n+1) ++ [true,false,true,true]⟩ := by
    have H := afront3 toC (Y (n+1) ++ [true,false,true,true])
    simpa only [leftA2,rotateX,List.append_assoc,List.nil_append] using H
  have h2 : run0 (table toC) (6*(n+1))
      ⟨0,[false,true,true,true],Y (n+1) ++ [true,false,true,true]⟩ =
      some ⟨0,[false] ++ Z (n+1) ++ [true,true,true],[true,false,true,true]⟩ := by
    have H := sweepR (table toC) 0 [false] [] [true,false,true,false] [true,true,false,true]
      6 (apacket2 toC) toC (n+1) [true,true,true] [true,false,true,true]
    simpa only [Y,Z,List.cons_append,List.append_assoc,List.nil_append] using H
  have h3 : run0 (table toC) 10
      ⟨0,[false] ++ Z (n+1) ++ [true,true,true],[true,false,true,true]⟩ =
      some (phase (n+1)) := by
    have H := afinish10 toC (Z (n+1) ++ [true,true,true])
    have hz : [true] ++ (Z (n+1) ++ [true,true,true]) =
        U (n+1) ++ [true,true,true,true] := by
      rw [← List.append_assoc]
      exact rotateZ n
    simpa only [phase,hz] using H
  have H := join0 (join0 h1 h2) h3
  have ht : (3+6*(n+1))+10=6*n+19 := by omega
  simpa only [ht] using H

/-- Exact original-machine infinite phase recurrence. -/
theorem growth (toC : Bool) (n : Nat) :
    run0 (table toC) (if toC then 24*n+60 else 22*n+58) (phase n) =
      some (phase (n+1)) := by
  have H := join0 (join0 (join0 (stageF toC n) (stageA toC n))
    (stageD toC n)) (stageA2 toC n)
  have ht : (((((if toC then 6 else 4)*(n+1))+(8*n+14))+(4*n+21))+
      (6*n+19))=(if toC then 24*n+60 else 22*n+58) := by
    cases toC <;> omega
  simpa only [ht] using H

theorem entry (toC : Bool) :
    run0 (table toC) 53 ⟨0,[],[]⟩ = some (phase 0) := by
  cases toC <;> rfl

theorem never (toC : Bool) (m : Machine) (hm : compatible (table toC) m) :
    NeverHalts m :=
  never_of_growth (table toC) phase 53
    (fun n => if toC then 24*n+60 else 22*n+58) (entry toC)
    (fun n => by cases toC <;> omega) (growth toC) m hm

theorem literal_cover (toC : Bool) (bound : Nat) :
    Cover (DecidedBelow bound) (table toC) :=
  Cover.leaf (table toC) (fun m hm => Or.inl (never toC m hm))

#print axioms entry
#print axioms stageF
#print axioms stageA
#print axioms stageD
#print axioms stageA2
#print axioms growth
#print axioms never
#print axioms literal_cover

end BB6.Agent16Raw44C1RA_A1LE_F1Variants
