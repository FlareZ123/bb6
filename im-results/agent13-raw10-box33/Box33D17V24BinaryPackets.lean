import Box33PrefixMacro
namespace BB6.Agent13.Box33D17V24BinaryPackets
open C9Pair
open BB6.Agent13.Box33D14Growth (z word rep rep_add cfg)
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
inductive Variant where | m35 | m49 deriving DecidableEq
def step (v : Variant) (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (left .A true c)
  | .B,false => some (left .C true c)
  | .B,true => some (right .F false c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (match v with | .m35 => left .C true c | .m49 => left .B false c)
  | .E,false => some (right .F true c)
  | .E,true => none
  | .F,false => some (right .A true c)
  | .F,true => some (right .F false c)
abbrev run (v : Variant) := BB6.Agent13.Box33PrefixMacro.run (step v)
theorem run_add (v : Variant) (m n : Nat) (c : Config) :
    run v (m+n) c = (run v m c).bind (run v n) :=
  BB6.Agent13.Box33PrefixMacro.run_add (step v) m n c
abbrev A := cfg .A
abbrev C := cfg .C
abbrev F := cfg .F
abbrev ones := rep [true]
abbrev zeros := rep [false]
abbrev p100 := rep [true,false,false]
abbrev p101 := rep [true,false,true]
abbrev p001 := rep [false,false,true]

theorem aOne (v : Variant) (b : Bool) (l r : Stream) :
    run v 1 (A (push b l) (push true r)) = some (A l (push b (push true r))) := by
  simp [A,cfg,BB6.Agent13.Box33PrefixMacro.run,step,left,right]

theorem aOnes (v : Variant) (k : Nat) (l r : Stream) :
    run v (k+1) (A (ones k (push false l)) (push true r)) =
      some (A l (push false (ones (k+1) r))) := by
  induction k generalizing r with
  | zero => exact aOne v false l r
  | succ k ih =>
    rw [show k+1+1=1+(k+1) by omega,run_add]
    change (run v 1 (A (push true (ones k (push false l))) (push true r))).bind _ = _
    rw [aOne,Option.bind_some,ih]
    rw [show ones (k+1) (push true r) = ones (k+1+1) r from (rep_add [true] (k+1) 1 r).symm]
    rw [show k+1+1=1+(k+1) by omega]

theorem fOne (v : Variant) (l r : Stream) :
    run v 1 (F l (push true r)) = some (F (push false l) r) := by
  simp [F,cfg,BB6.Agent13.Box33PrefixMacro.run,step,right]

theorem fOnes (v : Variant) (k : Nat) (l r : Stream) :
    run v k (F l (ones k r)) = some (F (zeros k l) r) := by
  induction k generalizing l r with
  | zero => rfl
  | succ k ih =>
    rw [run_add,show ones (k+1) r = ones k (push true r) from rep_add [true] k 1 r,ih,Option.bind_some]
    exact fOne v (zeros k l) r

theorem carryEnter (v : Variant) (l r : Stream) :
    run v 2 (A l (word [false,true] r)) = some (F (word [false,true] l) r) := by
  simp [A,F,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]

theorem carryExit (v : Variant) (l r : Stream) :
    run v 3 (F (push false l) (word [false,true] r)) = some (A l (word [false,true,true] r)) := by
  simp [A,F,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]

theorem carry (v : Variant) (k : Nat) (l r : Stream) :
    run v (k+5) (A l (push false (ones (k+1) (word [false,true] r)))) =
      some (A (zeros k (push true l)) (word [false,true,true] r)) := by
  rw [show k+5=2+k+3 by omega,run_add,run_add]
  change ((run v 2 (A l (word [false,true] (ones k (word [false,true] r))))).bind (run v k)).bind (run v 3) = _
  rw [carryEnter,Option.bind_some,fOnes,Option.bind_some]
  rw [show zeros k (word [false,true] l) = push false (zeros k (push true l)) from (rep_add [false] k 1 (push true l)).symm.trans (by rw [show k+1=1+k by omega,rep_add]; rfl)]
  exact carryExit v _ _

-- m49: first sweep removes 101 packets and prepends 001 packets on the right.
theorem enter49 (l : Stream) : run .m49 2 (A l z) = some (C l (word [true,true] z)) := by
  simp [A,C,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem left49 (l r : Stream) :
    run .m49 3 (C (word [true,false,true] l) (word [true,true] r)) =
      some (C l (word [true,true] (word [false,false,true] r))) := by
  simp [C,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem leftSweep49 (n : Nat) (l r : Stream) :
    run .m49 (3*n) (C (p101 n l) (word [true,true] r)) =
      some (C l (word [true,true] (p001 n r))) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [show 3*(n+1)=3+3*n by omega,run_add]
    change (run .m49 3 (C (word [true,false,true] (p101 n l)) (word [true,true] r))).bind _ = _
    rw [left49,Option.bind_some,ih,show p001 (n+1) r = p001 n (word [false,false,true] r) from rep_add [false,false,true] n 1 r]

theorem middle49 (l r : Stream) :
    run .m49 4 (C (word [true,false,false,true] l) (word [true,true] r)) =
      some (A l (push true (word [false,true] (word [false,false,true] r)))) := by
  simp [A,C,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]

theorem turn49 (l r : Stream) :
    run .m49 4 (A l (word [false,true,true,false,false,true] r)) =
      some (A (word [true,false,false,true] l) (word [false,true] r)) := by
  simp [A,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem right49 (l r : Stream) :
    run .m49 3 (A l (word [false,true,false,false,true] r)) =
      some (A (word [true,false,true] l) (word [false,true] r)) := by
  simp [A,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem finish49 (l : Stream) :
    run .m49 3 (A l (word [false,true] z)) = some (A (word [true,false,true] l) z) := by
  simp [A,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem rightSweep49 (n : Nat) (l : Stream) :
    run .m49 (3*n+3) (A l (word [false,true] (p001 n z))) =
      some (A (p101 (n+1) l) z) := by
  induction n generalizing l with
  | zero => exact finish49 l
  | succ n ih =>
    rw [show 3*(n+1)+3=3+(3*n+3) by omega,run_add]
    change (run .m49 3 (A l (word [false,true,false,false,true] (p001 n z)))).bind _ = _
    rw [right49,Option.bind_some,ih,show p101 (n+1+1) l = p101 (n+1) (word [true,false,true] l) from rep_add [true,false,true] (n+1) 1 l]

theorem return49 (n k : Nat) (l : Stream) :
    run .m49 (6*n+2*k+19) (A (p101 n (word [true,false,false,true] (ones k (push false l)))) z) =
      some (A (p101 (n+1) (word [true,false,false,true] (zeros k (push true l)))) z) := by
  rw [show 6*n+2*k+19=2+3*n+4+(k+1)+(k+5)+4+(3*n+3) by omega]
  rw [run_add .m49 (2+3*n+4+(k+1)+(k+5)+4) (3*n+3),run_add .m49 (2+3*n+4+(k+1)+(k+5)) 4,run_add .m49 (2+3*n+4+(k+1)) (k+5),run_add .m49 (2+3*n+4) (k+1),run_add .m49 (2+3*n) 4,run_add .m49 2 (3*n)]
  rw [enter49,Option.bind_some,leftSweep49,Option.bind_some,middle49,Option.bind_some,aOnes,Option.bind_some,carry,Option.bind_some]
  change (run .m49 4 (A (zeros k (push true l)) (word [false,true,true,false,false,true] (p001 n z)))).bind _ = _
  rw [turn49,Option.bind_some,rightSweep49]

-- m35 uses 100 on the left and 101 on the right, with a different return sweep.
theorem left35 (l r : Stream) :
    run .m35 5 (A (word [true,false,false] l) (word [false,false] r)) =
      some (A l (word [false,false] (word [true,false,true] r))) := by
  simp [A,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem leftSweep35 (n : Nat) (l r : Stream) :
    run .m35 (5*n) (A (p100 n l) (word [false,false] r)) =
      some (A l (word [false,false] (p101 n r))) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [show 5*(n+1)=5+5*n by omega,run_add]
    change (run .m35 5 (A (word [true,false,false] (p100 n l)) (word [false,false] r))).bind _ = _
    rw [left35,Option.bind_some,ih,show p101 (n+1) r = p101 n (word [true,false,true] r) from rep_add [true,false,true] n 1 r]
theorem middle35 (l r : Stream) :
    run .m35 5 (A (word [true,false,true] l) (word [false,false] r)) =
      some (A l (word [true,false,true,false,true] r)) := by
  simp [A,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem turn35 (l r : Stream) :
    run .m35 6 (A l (word [false,true,true,false,true] r)) =
      some (A (word [false,true] l) (word [false,true,true] r)) := by
  simp [A,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem right35 (l r : Stream) :
    run .m35 7 (A l (word [false,true,true,true,false,true] r)) =
      some (A (word [false,false,true] l) (word [false,true,true] r)) := by
  simp [A,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem finish35 (l : Stream) :
    run .m35 4 (A l (word [false,true,true] z)) = some (A (word [true,false,false,true] l) z) := by
  simp [A,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem rightSweep35 (n : Nat) (l r : Stream) :
    run .m35 (7*n) (A l (word [false,true,true] (p101 n r))) =
      some (A (p001 n l) (word [false,true,true] r)) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [show 7*(n+1)=7+7*n by omega,run_add]
    change (run .m35 7 (A l (word [false,true,true,true,false,true] (p101 n r)))).bind _ = _
    rw [right35,Option.bind_some,ih,show p001 (n+1) l = p001 n (word [false,false,true] l) from rep_add [false,false,true] n 1 l]
theorem packetShift (n : Nat) (l : Stream) :
    push true (p001 n l) = p100 n (push true l) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change push true (word [false,false,true] (p001 n l)) = word [true,false,false] (p100 n (push true l))
    change word [true,false,false] (push true (p001 n l)) = _
    rw [ih]
theorem return35 (n k : Nat) (l : Stream) :
    run .m35 (12*n+2*k+21) (A (p100 n (word [true,false,true] (ones k (push false l)))) z) =
      some (A (p100 (n+1) (word [true,false,true] (zeros k (push true l)))) z) := by
  rw [show 12*n+2*k+21=5*n+5+(k+1)+(k+5)+6+7*n+4 by omega]
  rw [run_add .m35 (5*n+5+(k+1)+(k+5)+6+7*n) 4,run_add .m35 (5*n+5+(k+1)+(k+5)+6) (7*n),run_add .m35 (5*n+5+(k+1)+(k+5)) 6,run_add .m35 (5*n+5+(k+1)) (k+5),run_add .m35 (5*n+5) (k+1),run_add .m35 (5*n) 5]
  have hfirst := leftSweep35 n (word [true,false,true] (ones k (push false l))) z
  rw [show word [false,false] z = z by simp [word]] at hfirst
  rw [hfirst,Option.bind_some]
  change (((((run .m35 5 (A (word [true,false,true] (ones k (push false l))) (word [false,false] (p101 n z)))).bind (run .m35 (k+1))).bind (run .m35 (k+5))).bind (run .m35 6)).bind (run .m35 (7*n))).bind (run .m35 4) = _
  rw [middle35,Option.bind_some]
  change ((((run .m35 (k+1) (A (ones k (push false l)) (push true (word [false,true,false,true] (p101 n z))))).bind (run .m35 (k+5))).bind (run .m35 6)).bind (run .m35 (7*n))).bind (run .m35 4) = _
  rw [aOnes,Option.bind_some]
  change (((run .m35 (k+5) (A l (push false (ones (k+1) (word [false,true] (word [false,true] (p101 n z))))))).bind (run .m35 6)).bind (run .m35 (7*n))).bind (run .m35 4) = _
  rw [carry,Option.bind_some]
  change (((run .m35 6 (A (zeros k (push true l)) (word [false,true,true,false,true] (p101 n z)))).bind (run .m35 (7*n))).bind (run .m35 4)) = _
  rw [turn35,Option.bind_some,rightSweep35,Option.bind_some,finish35]
  change some (A (word [true,false,false] (push true (p001 n (word [false,true] (zeros k (push true l)))))) z) = _
  rw [packetShift]
  rfl

-- Finite binary suffixes always admit a first zero; the carry can expand the word.
theorem splitBits (bs : List Bool) : ∃ k ds, word bs z = ones k (push false (word ds z)) := by
  induction bs with
  | nil => exact ⟨0,[],by simp [word,rep]⟩
  | cons b bs ih =>
    cases b with
    | false => exact ⟨0,bs,rfl⟩
    | true =>
      obtain ⟨k,ds,h⟩ := ih
      exact ⟨k+1,ds,by simp [word,rep,h]⟩
theorem zeroWord (k : Nat) (bs : List Bool) :
    zeros k (push true (word bs z)) = word (List.replicate k false ++ true::bs) z := by
  induction k with
  | zero => rfl
  | succ k ih => simp [rep,List.replicate_succ,word,ih]
def phase (v : Variant) (n : Nat) (bs : List Bool) : Config :=
  match v with
  | .m35 => A (p100 n (word [true,false,true] (word bs z))) z
  | .m49 => A (p101 n (word [true,false,false,true] (word bs z))) z
theorem progress (v : Variant) (n : Nat) (bs : List Bool) :
    ∃ t bs', 0<t ∧ run v t (phase v n bs) = some (phase v (n+1) bs') := by
  obtain ⟨k,ds,h⟩ := splitBits bs
  cases v with
  | m35 =>
    refine ⟨12*n+2*k+21,List.replicate k false ++ true::ds,by omega,?_⟩
    unfold phase
    rw [h,←zeroWord]
    exact return35 n k (word ds z)
  | m49 =>
    refine ⟨6*n+2*k+19,List.replicate k false ++ true::ds,by omega,?_⟩
    unfold phase
    rw [h,←zeroWord]
    exact return49 n k (word ds z)
theorem neverPhase (v : Variant) (t n : Nat) (bs : List Bool) :
    run v t (phase v n bs) ≠ none := by
  induction t using Nat.strongRecOn generalizing n bs with
  | ind t ih =>
    intro h
    obtain ⟨s,bs',hs,he⟩ := progress v n bs
    by_cases ht : t≤s
    · rw [←show t+(s-t)=s by omega,run_add,h] at he
      contradiction
    · rw [←show s+(t-s)=t by omega,run_add,he,Option.bind_some] at h
      exact ih _ (by omega) _ _ h
theorem init35 : run .m35 9 (A z z) = some (phase .m35 0 [true,true]) := by
  simp [phase,p100,A,cfg,word,rep,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem init49 : run .m49 55 (A z z) = some (phase .m49 3 [true,true]) := by
  have h9 : run .m49 9 (A z z) = some (A (word [true,false,true,true,true] z) z) := by
    simp [A,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h15 : run .m49 15 (A (word [true,false,true,true,true] z) z) = some (A (word [true,false,true,true,false,true,true] z) z) := by
    simp [A,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h31 : run .m49 31 (A (word [true,false,true,true,false,true,true] z) z) = some (phase .m49 3 [true,true]) := by
    simp [phase,p101,A,cfg,word,rep,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  rw [show 55=9+15+31 by decide,run_add .m49 (9+15) 31,run_add .m49 9 15,h9,Option.bind_some,h15,Option.bind_some,h31]
theorem neverBlank (v : Variant) (t : Nat) : run v t (A z z) ≠ none := by
  cases v with
  | m35 =>
    intro h
    by_cases ht : t≤9
    · have he := init35
      rw [←show t+(9-t)=9 by omega,run_add,h] at he
      contradiction
    · rw [←show 9+(t-9)=t by omega,run_add,init35,Option.bind_some] at h
      exact neverPhase .m35 _ 0 _ h
  | m49 =>
    intro h
    by_cases ht : t≤55
    · have he := init49
      rw [←show t+(55-t)=55 by omega,run_add,h] at he
      contradiction
    · rw [←show 55+(t-55)=t by omega,run_add,init49,Option.bind_some] at h
      exact neverPhase .m49 _ 3 _ h
open BB6Coverage
open Box17 (index decode)
def codes : Variant → List (Fin 25)
  | .m35 => [8,3,11,22,1,13,17,11,24,0,4,22]
  | .m49 => [8,3,11,22,1,13,17,5,24,0,4,22]
def table (v : Variant) : Machine := fun s => decode ((codes v).getD (index s).val 0)
theorem project_step (v : Variant) (c : BB6Coverage.Config) :
    (rawStep (table v) c).map BB6.Agent13.Box33PrefixMacro.project = step v (BB6.Agent13.Box33PrefixMacro.project c) := by
  rw [BB6.Agent13.Box33PrefixMacro.map_step]
  rcases c with ⟨s,p,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t p <;> cases v <;>
    simp only [readSlot,Box33Source.project,hb] <;> rfl
theorem never (v : Variant) : NeverHalts (table v) := by
  apply BB6.Agent13.Box33PrefixMacro.sourceNever (table v) (step v) (project_step v)
  intro n
  have hb : BB6.Agent13.Box33PrefixMacro.project BB6Coverage.blank = A z z := by
    change Box33Source.project false BB6Coverage.blank = A z z
    rw [Box33Source.project_blank false]
    simp [A,cfg,Box33UnarySweeper.blank] <;> rfl
  rw [hb]
  exact neverBlank v n
def partialTable (v : Variant) : PartialMachine := fun s => some (table v s)
theorem compatible_never (v : Variant) (m : Machine) (hm : compatible (partialTable v) m) : NeverHalts m := by
  have he : m = table v := funext fun s => hm s _ rfl
  rw [he]
  exact never v
#print axioms neverBlank
#print axioms compatible_never
end BB6.Agent13.Box33D17V24BinaryPackets
