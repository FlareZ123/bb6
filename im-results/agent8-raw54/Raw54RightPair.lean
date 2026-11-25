import Raw54Pair
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.RightPair
open BB6Coverage BB6Coverage.Agent31Pump

def table (v : Bool) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some (if v then ⟨false,true,2⟩ else ⟨false,true,1⟩))
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some (if v then ⟨true,true,2⟩ else ⟨false,false,1⟩))
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none

def ones : List Bool := [true,true,true,true]
def zeros : List Bool := [false,false,false,false]
def anchor (v : Bool) : List Bool := if v then [true,true,true,true,true,true,false,true,false] else [true,true,true,false,false,false,false,false,true]
abbrev word := BB6.Agent8Raw54.Pair.word
def cfg (v : Bool) (k : Nat) (bs : List Bool) : Z0 :=
  ⟨0,false :: (rep ones k ++ anchor v),(word bs).tail⟩
def entry (v : Bool) : Nat := if v then 49 else 33
def advanceCost (_v : Bool) : Nat := 4

theorem first (v : Bool) : run0 (table v) (entry v) ⟨0,[],[]⟩ = some (cfg v 0 []) := by
  cases v <;> rfl

theorem advance (v : Bool) (k : Nat) (bs : List Bool) :
    run0 (table v) (advanceCost v) (cfg v k (true::bs)) = some (cfg v (k+1) bs) := by
  cases v <;> cases bs <;> rfl

theorem word_insert_tail (k : Nat) (bs : List Bool) :
    (word (List.replicate k false ++ true::bs)).tail = rep zeros k ++ ([false,true,true] ++ word bs) :=
  BB6.Agent8Raw54.Pair.word_insert_tail k bs

theorem resetPrefix (v : Bool) (k : Nat) (bs : List Bool) :
    run0 (table v) 6 (cfg v k (false::bs)) =
      some ⟨4,rep ones k ++ (true :: anchor v), [false,true,true] ++ word bs⟩ := by
  have h : true :: (rep ones k ++ anchor v) = rep ones k ++ (true :: anchor v) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      calc
        _ = ones ++ (true :: (rep ones k ++ anchor v)) := rfl
        _ = ones ++ (rep ones k ++ (true :: anchor v)) := congrArg (fun xs => ones ++ xs) ih
        _ = _ := by simp only [rep,List.append_assoc]
  change _ = some (⟨4,rep ones k ++ (true :: anchor v),_⟩ : Z0)
  rw [← h]
  cases v <;> rfl

theorem resetPrefixEmpty (v : Bool) (k : Nat) :
    run0 (table v) 6 (cfg v k []) =
      some ⟨4,rep ones k ++ (true :: anchor v), [false,true,true]⟩ := by
  have h : true :: (rep ones k ++ anchor v) = rep ones k ++ (true :: anchor v) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      calc
        _ = ones ++ (true :: (rep ones k ++ anchor v)) := rfl
        _ = ones ++ (rep ones k ++ (true :: anchor v)) := congrArg (fun xs => ones ++ xs) ih
        _ = _ := by simp only [rep,List.append_assoc]
  change _ = some (⟨4,rep ones k ++ (true :: anchor v),_⟩ : Z0)
  rw [← h]
  cases v <;> rfl

def suffixCost (v : Bool) : Nat := if v then 58 else 20

theorem resetSuffix (v : Bool) (k : Nat) (r : List Bool) :
    run0 (table v) (suffixCost v) ⟨4,true :: anchor v,rep zeros k ++ ([false,true,true] ++ r)⟩ =
      some ⟨0,false::anchor v,rep zeros k ++ ([false,true,true] ++ r)⟩ := by
  cases k <;> cases v <;> rfl

theorem reset (v : Bool) (k : Nat) (bs : List Bool) :
    run0 (table v) (6+4*k+suffixCost v) (cfg v k (false::bs)) =
      some (cfg v 0 (List.replicate k false ++ true::bs)) := by
  have a := resetPrefix v k bs
  have b := sweepL (table v) 4 [] [] ones zeros 4
    (by intro L R; cases v <;> rfl) k (true :: anchor v) ([false,true,true] ++ word bs)
  have c := resetSuffix v k (word bs)
  have H := join0 (join0 a b) c
  simpa only [cfg,rep,List.nil_append,word_insert_tail] using H

theorem resetEmpty (v : Bool) (k : Nat) :
    run0 (table v) (6+4*k+suffixCost v) (cfg v k []) =
      some (cfg v 0 (List.replicate k false ++ [true])) := by
  have a := resetPrefixEmpty v k
  have b := sweepL (table v) 4 [] [] ones zeros 4
    (by intro L R; cases v <;> rfl) k (true :: anchor v) [false,true,true]
  have c := resetSuffix v k []
  have H := join0 (join0 a b) c
  simpa only [cfg,rep,List.nil_append,word_insert_tail,word,List.append_nil,BB6.Agent8Raw54.Pair.word] using H

def next : Nat × List Bool → Nat × List Bool
  | (k,[]) => (0,List.replicate k false ++ [true])
  | (k,false::bs) => (0,List.replicate k false ++ true::bs)
  | (k,true::bs) => (k+1,bs)

def orbit : Nat → Nat × List Bool
  | 0 => (0,[])
  | n+1 => next (orbit n)
def family (v : Bool) (n : Nat) : Z0 := cfg v (orbit n).1 (orbit n).2

theorem next_run (v : Bool) (k : Nat) (bs : List Bool) :
    ∃ t, 0 < t ∧ run0 (table v) t (cfg v k bs) = some (cfg v (next (k,bs)).1 (next (k,bs)).2) := by
  cases bs with
  | nil => exact ⟨6+4*k+suffixCost v,by omega,resetEmpty v k⟩
  | cons b bs =>
    cases b
    · exact ⟨6+4*k+suffixCost v,by omega,reset v k bs⟩
    · exact ⟨advanceCost v,by cases v <;> decide,advance v k bs⟩

theorem family_next (v : Bool) (n : Nat) :
    ∃ t, 0 < t ∧ run0 (table v) t (family v n) = some (family v (n+1)) := by
  unfold family
  simp only [orbit]
  cases h : orbit n with
  | mk k bs => exact next_run v k bs

theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  exact BB6.Agent8Raw54.never_of_returns (table v) (family v) (entry v) (first v) (family_next v) m hm

#print axioms family_next
#print axioms never
end BB6.Agent8Raw54.RightPair
