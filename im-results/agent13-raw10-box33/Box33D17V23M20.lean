import Box33PrefixMacro

namespace BB6.Agent13.Box33D17V23M20
open C9Pair
open BB6.Agent13.Box33D14Growth (z word rep rep_succ rep_add cfg ones)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

def step (c : C9Pair.Config) : Option C9Pair.Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (left .A true c)
  | .B,false => some (left .C true c)
  | .B,true => some (right .F false c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (left .C true c)
  | .E,false => some (left .F true c)
  | .E,true => none
  | .F,false => some (right .A true c)
  | .F,true => some (right .F false c)

abbrev run := BB6.Agent13.Box33PrefixMacro.run step
theorem run_add (m n : Nat) (c : C9Pair.Config) :
    run (m+n) c = (run m c).bind (run n) :=
  BB6.Agent13.Box33PrefixMacro.run_add step m n c
abbrev A := cfg .A
abbrev F := cfg .F
abbrev zeros := rep [false]
abbrev lp := rep [true,false,false]
abbrev rp := rep [false,true,true]
abbrev tp := rep [false,false,true]

def dRight : Nat → Stream
  | 0 => z
  | k+1 => word [false,false,true] (rp k (word [false,true] z))

theorem dPopRaw (l r : Stream) :
    run 5 (A (word [true,false,false] l) (word [false,false] r)) =
    some (A l (word [false,false,true,false,true] r)) := by
  simp [A,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]

theorem dPop (k : Nat) (l : Stream) :
    run 5 (A (word [true,false,false] l) (dRight k)) = some (A l (dRight (k+1))) := by
  cases k with
  | zero => simpa [dRight,rep,word] using dPopRaw l z
  | succ k => simpa [dRight,rep,word] using dPopRaw l (push true (rp k (word [false,true] z)))

theorem dSweep (n k : Nat) (l : Stream) :
    run (5*n) (A (lp n l) (dRight k)) = some (A l (dRight (k+n))) := by
  induction n generalizing k with
  | zero => simp [BB6.Agent13.Box33PrefixMacro.run,rep]
  | succ n ih =>
    rw [show 5*(n+1)=5+5*n by omega]
    change run (5+5*n) (A (word [true,false,false] (lp n l)) (dRight k)) = _
    rw [run_add,dPop,Option.bind_some,ih]
    rw [show k+1+n=k+(n+1) by omega]

def LA (l r : Stream) : Config := ⟨.A,pop l,l 0,r⟩
theorem dEnter (l r : Stream) :
    run 5 (A (word [true,false] l) (word [false,false] r)) =
      some (LA l (word [false,true,false,true] r)) := by
  simp [A,LA,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]

theorem aLeftOne (l r : Stream) : run 1 (LA (push true l) r) = some (LA l (push true r)) := by
  simp [LA,BB6.Agent13.Box33PrefixMacro.run,step,left]

theorem aLeft (n : Nat) (l r : Stream) :
    run n (LA (ones n l) r) = some (LA l (ones n r)) := by
  induction n generalizing l r with
  | zero => simp [BB6.Agent13.Box33PrefixMacro.run,rep]
  | succ n ih =>
    rw [run_add,show ones (n+1) l = ones n (push true l) from rep_add [true] n 1 l,
      ih,Option.bind_some]
    exact aLeftOne l (ones n r)

theorem dAnchorRaw (n : Nat) (l r : Stream) :
    run (5+n) (A (word [true,false] (ones n (push false l))) (word [false,false] r)) =
      some (A l (push false (ones n (word [false,true,false,true] r)))) := by
  rw [run_add,dEnter,Option.bind_some,aLeft]
  rfl

def sRight (j k : Nat) : Stream :=
  push false (ones (j+1) (word [false,true] (rp k (word [false,true] z))))

theorem dAnchor (j k : Nat) (l : Stream) :
    run (5+(j+1)) (A (word [true,false] (ones (j+1) (push false l))) (dRight k)) =
      some (A l (sRight j k)) := by
  cases k with
  | zero => simpa [dRight,sRight,rep,word] using dAnchorRaw (j+1) l z
  | succ k => simpa [dRight,sRight,rep,word] using
      dAnchorRaw (j+1) l (push true (rp k (word [false,true] z)))

theorem sEnter (l r : Stream) :
    run 2 (A l (word [false,true] r)) = some (F (word [false,true] l) r) := by
  simp [A,F,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]

theorem fOne (l r : Stream) : run 1 (F l (push true r)) = some (F (push false l) r) := by
  simp [F,cfg,BB6.Agent13.Box33PrefixMacro.run,step,right]

theorem fSweep (n : Nat) (l r : Stream) :
    run n (F l (ones n r)) = some (F (zeros n l) r) := by
  induction n generalizing l r with
  | zero => simp [BB6.Agent13.Box33PrefixMacro.run,rep]
  | succ n ih =>
    rw [run_add,show ones (n+1) r = ones n (push true r) from rep_add [true] n 1 r,
      ih,Option.bind_some]
    exact fOne (zeros n l) r

theorem sFinishRaw (l r : Stream) :
    run 3 (F (push false l) (word [false,true] r)) = some (A l (word [false,true,true] r)) := by
  simp [A,F,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]

theorem sTransfer (n : Nat) (l r : Stream) :
    run (n+5) (A l (word [false,true] (ones n (word [false,true] r)))) =
      some (A (zeros n (push true l)) (word [false,true,true] r)) := by
  rw [show n+5=2+n+3 by omega,run_add,run_add,sEnter,Option.bind_some,fSweep,Option.bind_some]
  have h : zeros n (word [false,true] l) = push false (zeros n (push true l)) := by
    change zeros n (zeros 1 (push true l)) = zeros 1 (zeros n (push true l))
    exact (rep_add [false] n 1 (push true l)).symm.trans (by rw [Nat.add_comm n 1]; exact rep_add [false] 1 n (push true l))
  rw [h,sFinishRaw]

theorem sFirst (j k : Nat) (l : Stream) :
    run (j+5) (A l (sRight j k)) =
      some (A (zeros j (push true l)) (word [false,true,true] (rp k (word [false,true] z)))) := by
  simpa [sRight,rep,word] using sTransfer j l (rp k (word [false,true] z))

theorem middle3 (k : Nat) (l : Stream) :
    run (7*(k+1)) (A l (word [false,true,true,true] (rp k (word [false,true] z)))) =
      some (A (tp (k+1) l) (word [false,true,true] z)) := by
  induction k generalizing l with
  | zero => simpa [rep,word] using sTransfer 2 l z
  | succ k ih =>
    rw [show 7*(k+1+1)=7+7*(k+1) by omega,run_add]
    have he := sTransfer 2 l (push true (rp k (word [false,true] z)))
    change run 7 (A l (word [false,true,true,true] (rp (k+1) (word [false,true] z)))) = _ at he
    rw [he,Option.bind_some]
    change run (7*(k+1)) (A (tp 1 l) (word [false,true,true,true] (rp k (word [false,true] z)))) = _
    rw [ih]
    exact congrArg (fun s => some (A s (word [false,true,true] z))) (rep_add [false,false,true] (k+1) 1 l).symm

theorem middle (k : Nat) (l : Stream) :
    run (6+7*k) (A l (word [false,true,true] (rp k (word [false,true] z)))) =
      some (A (tp k (word [false,true] l)) (word [false,true,true] z)) := by
  cases k with
  | zero => simpa [rep,word] using sTransfer 1 l z
  | succ k =>
    rw [run_add]
    have he := sTransfer 1 l (push true (rp k (word [false,true] z)))
    change run 6 (A l (word [false,true,true] (rp (k+1) (word [false,true] z)))) = _ at he
    rw [he,Option.bind_some]
    exact middle3 k (word [false,true] l)

theorem sEnd (l : Stream) :
    run 4 (A l (word [false,true,true] z)) = some (A (word [true,false,false,true] l) z) := by
  simp [A,F,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]

theorem transpose (k : Nat) (l : Stream) :
    push true (tp k l) = lp k (push true l) := by
  induction k with
  | zero => simp [rep]
  | succ k ih => simp [rep,word,ih]

theorem epoch (j k : Nat) (u : Stream) :
    run (12*k+2*j+21) (A (lp k (word [true,false] (ones (j+1) (push false u)))) z) =
      some (A (lp (k+1) (word [true,false,true] (zeros j (push true u)))) z) := by
  rw [show 12*k+2*j+21=5*k+(5+(j+1))+(j+5)+(6+7*k)+4 by omega,
    run_add,run_add,run_add,run_add]
  rw [show z=dRight 0 from rfl,dSweep,Option.bind_some]
  simp only [Nat.zero_add]
  rw [dAnchor,Option.bind_some,sFirst,Option.bind_some,middle,Option.bind_some,sEnd]
  change some (A (word [true,false,false] (push true (tp k (word [false,true] (zeros j (push true u)))))) z) = _
  rw [transpose]
  rfl

theorem splitTail (xs : List Bool) : ∃ j ys, word xs z = ones j (push false (word ys z)) := by
  induction xs with
  | nil => exact ⟨0,[],by simp [word,rep]⟩
  | cons x xs ih =>
    cases x with
    | false => exact ⟨0,xs,rfl⟩
    | true =>
      obtain ⟨j,ys,h⟩ := ih
      exact ⟨j+1,ys,by simp [word,rep,h]⟩

theorem zeroTail (j : Nat) (ys : List Bool) :
    zeros j (push true (word ys z)) = word (List.replicate j false ++ true::ys) z := by
  induction j with
  | zero => rfl
  | succ j ih => simp [rep,word,List.replicate_succ,ih]

def root (k : Nat) (xs : List Bool) : Config := A (lp k (word [true,false,true] (word xs z))) z

theorem rootProgress (k : Nat) (xs : List Bool) :
    ∃ t ys, 0<t ∧ run t (root k xs) = some (root (k+1) ys) := by
  obtain ⟨j,ys,h⟩ := splitTail xs
  refine ⟨12*k+2*j+21,List.replicate j false ++ true::ys,by omega,?_⟩
  unfold root
  rw [h,←zeroTail]
  exact epoch j k (word ys z)

theorem neverRoot (n k : Nat) (xs : List Bool) : run n (root k xs) ≠ none := by
  induction n using Nat.strongRecOn generalizing k xs with
  | ind n ih =>
    intro h
    obtain ⟨t,ys,ht,he⟩ := rootProgress k xs
    by_cases hn : n≤t
    · rw [←show n+(t-n)=t by omega,run_add,h] at he
      contradiction
    · rw [←show t+(n-t)=n by omega,run_add,he,Option.bind_some] at h
      exact ih (n-t) (by omega) (k+1) ys h

theorem init : run 15 (A z z) = some (root 0 [true,false,false,true]) := by
  simp [root,A,F,cfg,word,rep,BB6.Agent13.Box33PrefixMacro.run,step,left,right]

theorem neverBlank (n : Nat) : run n (A z z) ≠ none := by
  intro h
  by_cases hn : n≤15
  · have he := init
    rw [←show n+(15-n)=15 by omega,run_add,h] at he
    contradiction
  · rw [←show 15+(n-15)=n by omega,run_add,init,Option.bind_some] at h
    exact neverRoot (n-15) 0 _ h

open BB6Coverage
open Box17 (index decode)
def codes : List (Fin 25) := [8,3,11,22,1,13,17,11,23,0,4,22]
def table : Machine := fun s => decode (codes.getD (index s).val 0)
theorem project_step (c : BB6Coverage.Config) :
    (rawStep table c).map BB6.Agent13.Box33PrefixMacro.project = step (BB6.Agent13.Box33PrefixMacro.project c) := by
  rw [BB6.Agent13.Box33PrefixMacro.map_step]
  rcases c with ⟨s,p,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t p <;>
    simp only [readSlot,Box33Source.project,hb] <;> rfl
theorem never : NeverHalts table := by
  apply BB6.Agent13.Box33PrefixMacro.sourceNever table step project_step
  intro n
  exact neverBlank n
def partialTable : PartialMachine := fun s => some (table s)
theorem compatible_never (m : Machine) (hm : compatible partialTable m) : NeverHalts m := by
  have he : m = table := funext fun s => hm s _ rfl
  rw [he]
  exact never

#print axioms epoch
#print axioms neverBlank
#print axioms compatible_never
end BB6.Agent13.Box33D17V23M20
