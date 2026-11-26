import Raw54RACounterCore
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.RADigit
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent8Raw54.RACounter

def encWord (z o e : List Bool) : List Bool → List Bool
  | [] => e
  | false::w => z ++ encWord z o e w
  | true::w => o ++ encWord z o e w
def bumpGrow : List Bool → List Bool
  | [] => [false]
  | false::w => true::w
  | true::w => false::bumpGrow w
def costGrow (a b d i j : Nat) : Nat → List Bool → Nat
  | 0, [] => j
  | k+1, [] => a*k+d
  | 0, false::_ => i
  | k+1, false::_ => a*k+b
  | k, true::w => costGrow a b d i j (k+1) w

theorem costGrow_pos (a b d i j : Nat) (hb : 0 < b) (hd : 0 < d) (hi : 0 < i) (hj : 0 < j)
    (w : List Bool) (k : Nat) : 0 < costGrow a b d i j k w := by
  induction w generalizing k with
  | nil => cases k <;> simp only [costGrow] <;> omega
  | cons x w ih =>
    cases x
    · cases k <;> simp only [costGrow] <;> omega
    · simpa only [costGrow] using ih (k+1)

theorem growWord (p : PartialMachine) (z o e : List Bool) (a b d i j : Nat)
    (inc : ∀ T, run0 p i (A (z ++ T)) = some (A (o ++ T)))
    (empty : run0 p j (A e) = some (A (z ++ e)))
    (stop : ∀ k T, run0 p (a*k+b) (A (o ++ (rep o k ++ (z ++ T)))) = some (A (z ++ (rep z k ++ (o ++ T)))))
    (overflow : ∀ k, run0 p (a*k+d) (A (o ++ (rep o k ++ e))) = some (A (z ++ (z ++ (rep z k ++ e)))))
    (w : List Bool) (k : Nat) :
    run0 p (costGrow a b d i j k w) (A (rep o k ++ encWord z o e w)) =
      some (A (rep z k ++ encWord z o e (bumpGrow w))) := by
  induction w generalizing k with
  | nil =>
    cases k with
    | zero => simpa only [encWord,bumpGrow,costGrow,rep,List.nil_append] using empty
    | succ k =>
      simpa only [encWord,bumpGrow,costGrow,rep,← List.append_assoc (rep z k) z e,rep_snoc,List.append_assoc] using overflow k
  | cons h w ih =>
    cases h
    · cases k with
      | zero => simpa only [encWord,bumpGrow,costGrow,rep,List.nil_append] using inc (encWord z o e w)
      | succ k => simpa only [encWord,bumpGrow,costGrow,rep,List.append_assoc] using stop k (encWord z o e w)
    · have H := ih (k+1)
      simpa only [encWord,bumpGrow,costGrow,rep,← rep_snoc o k,← rep_snoc z k,List.append_assoc] using H

def wordsGrow : Nat → List Bool | 0 => [] | n+1 => bumpGrow (wordsGrow n)
def familyGrow (z o e : List Bool) (n : Nat) : Z0 := A (encWord z o e (wordsGrow n))
def epochCost (a b d i j : Nat) (n : Nat) : Nat := costGrow a b d i j 0 (wordsGrow n)
theorem neverGrow (p : PartialMachine) (z o e : List Bool) (a b d i j : Nat)
    (hb : 0 < b) (hd : 0 < d) (hi : 0 < i) (hj : 0 < j)
    (entry : run0 p 8 ⟨0,[],[]⟩ = some (A e))
    (inc : ∀ T, run0 p i (A (z ++ T)) = some (A (o ++ T)))
    (empty : run0 p j (A e) = some (A (z ++ e)))
    (stop : ∀ k T, run0 p (a*k+b) (A (o ++ (rep o k ++ (z ++ T)))) = some (A (z ++ (rep z k ++ (o ++ T)))))
    (overflow : ∀ k, run0 p (a*k+d) (A (o ++ (rep o k ++ e))) = some (A (z ++ (z ++ (rep z k ++ e)))))
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply never_of_growth p (familyGrow z o e) 8 (epochCost a b d i j) entry
    (fun n => costGrow_pos a b d i j hb hd hi hj (wordsGrow n) 0) _ m hm
  intro n
  have H := growWord p z o e a b d i j inc empty stop overflow (wordsGrow n) 0
  simpa only [familyGrow,epochCost,rep,List.nil_append,wordsGrow] using H

theorem carryPrefix (p : PartialMachine) (z o zp mark : List Bool) (a b c d : Nat)
    (stop : ∀ k T, run0 p (a*k+b) (A (mark ++ (rep o k ++ (z ++ T)))) = some (A (zp ++ (rep z k ++ (o ++ T)))))
    (overflow : ∀ k, run0 p (c*k+d) (A (mark ++ rep o k)) = some (A (zp ++ (rep z k ++ o))))
    (w : List Bool) (k : Nat) :
    run0 p (carryCost a b c d k w) (A (mark ++ (rep o k ++ encWord z o [] w))) =
      some (A (zp ++ (rep z k ++ encWord z o [] (bump w)))) := by
  induction w generalizing k with
  | nil => simpa only [encWord,bump,carryCost,List.append_nil] using overflow k
  | cons h w ih =>
    cases h
    · simpa only [encWord,bump,carryCost] using stop k (encWord z o [] w)
    · have H := ih (k+1)
      simpa only [encWord,bump,carryCost,rep,← rep_snoc o k,← rep_snoc z k,List.append_assoc] using H

def familyPrefix (z o mark : List Bool) (n : Nat) : Z0 := A (mark ++ encWord z o [] (words n))
theorem neverPrefix (p : PartialMachine) (z o zp mark : List Bool) (a b c d : Nat)
    (entry : run0 p 8 ⟨0,[],[]⟩ = some (A mark))
    (inc : ∀ T, run0 p 8 (A (zp ++ T)) = some (A (mark ++ T)))
    (stop : ∀ k T, run0 p (a*k+b) (A (mark ++ (rep o k ++ (z ++ T)))) = some (A (zp ++ (rep z k ++ (o ++ T)))))
    (overflow : ∀ k, run0 p (c*k+d) (A (mark ++ rep o k)) = some (A (zp ++ (rep z k ++ o))))
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply never_of_growth p (familyPrefix z o mark) 8 (cost a b c d) (by simpa only [familyPrefix,words,encWord,List.append_nil] using entry) (by intro n; unfold cost; omega) _ m hm
  intro n
  have H := join0 (carryPrefix p z o zp mark a b c d stop overflow (words n) 0) (inc (encWord z o [] (bump (words n))))
  simpa only [familyPrefix,cost,rep,List.nil_append,words] using H
#print axioms neverGrow
#print axioms neverPrefix
end BB6.Agent8Raw54.RADigit
