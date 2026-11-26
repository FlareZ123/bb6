import Raw54RADigitCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.RA.M11
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent8Raw54.RACounter BB6.Agent8Raw54.RADigit
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨false,true,4⟩)
  | _,_ => none
def Z : List Bool := [false,false,false,false,false]
def O : List Bool := [false,true,true,false,false]
def T2 : List Bool := [true,true,true,true,true]
def E : List Bool := [false,true,true]
theorem inc0 (T : List Bool) : run0 table 8 (A (Z ++ T)) = some (A (O ++ T)) := by rfl
theorem inc1 (T : List Bool) : run0 table 14 (A (O ++ T)) = some (A (T2 ++ T)) := by rfl
theorem last1 : run0 table 14 (A E) = some (A T2) := by rfl
theorem carry0 (n : Nat) (T : List Bool) : run0 table (10*n+18) ⟨0,[false,false],([true,true,true,true,true] ++ (rep [true,true,true,true,true] n ++ ([false,false,false,false,false] ++ T)))⟩ = some ⟨0,[false,false],([false,false,false,false,false] ++ (rep [false,false,false,false,false] n ++ ([false,true,true,false,false] ++ T)))⟩ := by
  have h0 : run0 table 1 ⟨0,[false,false],([true,true,true,true,true] ++ (rep [true,true,true,true,true] n ++ ([false,false,false,false,false] ++ T)))⟩ = some ⟨1,[true,true,false],([true,true,true,true] ++ (rep [true,true,true,true,true] n ++ ([false,false,false,false,false] ++ T)))⟩ := by rfl
  have h1 : run0 table (5*n) ⟨1,[true,true,false],([true,true,true,true] ++ (rep [true,true,true,true,true] n ++ ([false,false,false,false,false] ++ T)))⟩ = some ⟨1,([true] ++ (rep [true,true,true,true,true] n ++ [true,false])),([true,true,true,true,false,false,false,false,false] ++ T)⟩ := by
    exact sweepR table 1 [true] [true,true,true,true] [true,true,true,true,true] [true,true,true,true,true] 5 (fun _ _ => rfl) n [true,false] ([false,false,false,false,false] ++ T)
  have g1 := join0 h0 h1
  have h2 : run0 table 10 ⟨1,([true] ++ (rep [true,true,true,true,true] n ++ [true,false])),([true,true,true,true,false,false,false,false,false] ++ T)⟩ = some ⟨4,([true,true,true,true,true] ++ (rep [true,true,true,true,true] n ++ [true,false])),([false,true,true,false,false] ++ T)⟩ := by rfl
  have g2 := join0 g1 h2
  have h3 : run0 table (5*n) ⟨4,([true,true,true,true,true] ++ (rep [true,true,true,true,true] n ++ [true,false])),([false,true,true,false,false] ++ T)⟩ = some ⟨4,[true,true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false] n ++ ([false,true,true,false,false] ++ T)))⟩ := by
    exact sweepL table 4 [true,true,true,true,true] [] [true,true,true,true,true] [false,false,false,false,false] 5 (fun _ _ => rfl) n [true,false] ([false,true,true,false,false] ++ T)
  have g3 := join0 g2 h3
  have h4 : run0 table 7 ⟨4,[true,true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false] n ++ ([false,true,true,false,false] ++ T)))⟩ = some ⟨0,[false,false],([false,false,false,false,false] ++ (rep [false,false,false,false,false] n ++ ([false,true,true,false,false] ++ T)))⟩ := by rfl
  have g4 := join0 g3 h4
  rw [show 1+(5*n)+10+(5*n)+7=10*n+18 by omega] at g4
  exact g4
theorem carry1 (n : Nat) (T : List Bool) : run0 table (10*n+24) ⟨0,[false,false],([true,true,true,true,true] ++ (rep [true,true,true,true,true] n ++ ([false,true,true,false,false] ++ T)))⟩ = some ⟨0,[false,false],([false,false,false,false,false] ++ (rep [false,false,false,false,false] n ++ ([true,true,true,true,true] ++ T)))⟩ := by
  have h0 : run0 table 1 ⟨0,[false,false],([true,true,true,true,true] ++ (rep [true,true,true,true,true] n ++ ([false,true,true,false,false] ++ T)))⟩ = some ⟨1,[true,true,false],([true,true,true,true] ++ (rep [true,true,true,true,true] n ++ ([false,true,true,false,false] ++ T)))⟩ := by rfl
  have h1 : run0 table (5*n) ⟨1,[true,true,false],([true,true,true,true] ++ (rep [true,true,true,true,true] n ++ ([false,true,true,false,false] ++ T)))⟩ = some ⟨1,([true] ++ (rep [true,true,true,true,true] n ++ [true,false])),([true,true,true,true,false,true,true,false,false] ++ T)⟩ := by
    exact sweepR table 1 [true] [true,true,true,true] [true,true,true,true,true] [true,true,true,true,true] 5 (fun _ _ => rfl) n [true,false] ([false,true,true,false,false] ++ T)
  have g1 := join0 h0 h1
  have h2 : run0 table 17 ⟨1,([true] ++ (rep [true,true,true,true,true] n ++ [true,false])),([true,true,true,true,false,true,true,false,false] ++ T)⟩ = some ⟨4,([true,true,true,true] ++ (rep [true,true,true,true,true] n ++ [true,false])),([false,true,true,true,true,true] ++ T)⟩ := by rfl
  have g2 := join0 g1 h2
  have h3 : run0 table (5*n) ⟨4,([true,true,true,true] ++ (rep [true,true,true,true,true] n ++ [true,false])),([false,true,true,true,true,true] ++ T)⟩ = some ⟨4,[true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false] n ++ ([false,true,true,true,true,true] ++ T)))⟩ := by
    exact sweepL table 4 [true,true,true,true] [] [true,true,true,true,true] [false,false,false,false,false] 5 (fun _ _ => rfl) n [true,false] ([false,true,true,true,true,true] ++ T)
  have g3 := join0 g2 h3
  have h4 : run0 table 6 ⟨4,[true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false] n ++ ([false,true,true,true,true,true] ++ T)))⟩ = some ⟨0,[false,false],([false,false,false,false] ++ (rep [false,false,false,false,false] n ++ ([false,true,true,true,true,true] ++ T)))⟩ := by rfl
  have g4 := join0 g3 h4
  have e5 : (⟨0,[false,false],([false,false,false,false] ++ (rep [false,false,false,false,false] n ++ ([false,true,true,true,true,true] ++ T)))⟩ : Z0) = ⟨0,[false,false],([false,false,false,false,false] ++ (rep [false,false,false,false,false] n ++ ([true,true,true,true,true] ++ T)))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) ((moveCut [false,false,false,false] ([true,true,true,true,true] ++ T) [false,false,false,false] false n).symm)
  rw [e5] at g4
  rw [show 1+(5*n)+17+(5*n)+6=10*n+24 by omega] at g4
  exact g4
theorem carryLast1 (n : Nat) : run0 table (10*n+24) ⟨0,[false,false],([true,true,true,true,true] ++ (rep [true,true,true,true,true] n ++ [false,true,true]))⟩ = some ⟨0,[false,false],([false,false,false,false,false] ++ (rep [false,false,false,false,false] n ++ [true,true,true,true,true]))⟩ := by
  have h0 : run0 table 1 ⟨0,[false,false],([true,true,true,true,true] ++ (rep [true,true,true,true,true] n ++ [false,true,true]))⟩ = some ⟨1,[true,true,false],([true,true,true,true] ++ (rep [true,true,true,true,true] n ++ [false,true,true]))⟩ := by rfl
  have h1 : run0 table (5*n) ⟨1,[true,true,false],([true,true,true,true] ++ (rep [true,true,true,true,true] n ++ [false,true,true]))⟩ = some ⟨1,([true] ++ (rep [true,true,true,true,true] n ++ [true,false])),[true,true,true,true,false,true,true]⟩ := by
    exact sweepR table 1 [true] [true,true,true,true] [true,true,true,true,true] [true,true,true,true,true] 5 (fun _ _ => rfl) n [true,false] [false,true,true]
  have g1 := join0 h0 h1
  have h2 : run0 table 17 ⟨1,([true] ++ (rep [true,true,true,true,true] n ++ [true,false])),[true,true,true,true,false,true,true]⟩ = some ⟨4,([true,true,true,true] ++ (rep [true,true,true,true,true] n ++ [true,false])),[false,true,true,true,true,true]⟩ := by rfl
  have g2 := join0 g1 h2
  have h3 : run0 table (5*n) ⟨4,([true,true,true,true] ++ (rep [true,true,true,true,true] n ++ [true,false])),[false,true,true,true,true,true]⟩ = some ⟨4,[true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false] n ++ [false,true,true,true,true,true]))⟩ := by
    exact sweepL table 4 [true,true,true,true] [] [true,true,true,true,true] [false,false,false,false,false] 5 (fun _ _ => rfl) n [true,false] [false,true,true,true,true,true]
  have g3 := join0 g2 h3
  have h4 : run0 table 6 ⟨4,[true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false] n ++ [false,true,true,true,true,true]))⟩ = some ⟨0,[false,false],([false,false,false,false] ++ (rep [false,false,false,false,false] n ++ [false,true,true,true,true,true]))⟩ := by rfl
  have g4 := join0 g3 h4
  have e5 : (⟨0,[false,false],([false,false,false,false] ++ (rep [false,false,false,false,false] n ++ [false,true,true,true,true,true]))⟩ : Z0) = ⟨0,[false,false],([false,false,false,false,false] ++ (rep [false,false,false,false,false] n ++ [true,true,true,true,true]))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) ((moveCut [false,false,false,false] [true,true,true,true,true] [false,false,false,false] false n).symm)
  rw [e5] at g4
  rw [show 1+(5*n)+17+(5*n)+6=10*n+24 by omega] at g4
  exact g4
theorem carryLast2 (n : Nat) : run0 table (10*n+18) ⟨0,[false,false],([true,true,true,true,true] ++ (rep [true,true,true,true,true] n ++ []))⟩ = some ⟨0,[false,false],([false,false,false,false,false] ++ (rep [false,false,false,false,false] n ++ [false,true,true]))⟩ := by
  have h0 : run0 table 1 ⟨0,[false,false],([true,true,true,true,true] ++ (rep [true,true,true,true,true] n ++ []))⟩ = some ⟨1,[true,true,false],([true,true,true,true] ++ (rep [true,true,true,true,true] n ++ []))⟩ := by rfl
  have h1 : run0 table (5*n) ⟨1,[true,true,false],([true,true,true,true] ++ (rep [true,true,true,true,true] n ++ []))⟩ = some ⟨1,([true] ++ (rep [true,true,true,true,true] n ++ [true,false])),[true,true,true,true]⟩ := by
    exact sweepR table 1 [true] [true,true,true,true] [true,true,true,true,true] [true,true,true,true,true] 5 (fun _ _ => rfl) n [true,false] []
  have g1 := join0 h0 h1
  have h2 : run0 table 10 ⟨1,([true] ++ (rep [true,true,true,true,true] n ++ [true,false])),[true,true,true,true]⟩ = some ⟨4,([true,true,true,true,true] ++ (rep [true,true,true,true,true] n ++ [true,false])),[false,true,true]⟩ := by rfl
  have g2 := join0 g1 h2
  have h3 : run0 table (5*n) ⟨4,([true,true,true,true,true] ++ (rep [true,true,true,true,true] n ++ [true,false])),[false,true,true]⟩ = some ⟨4,[true,true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false] n ++ [false,true,true]))⟩ := by
    exact sweepL table 4 [true,true,true,true,true] [] [true,true,true,true,true] [false,false,false,false,false] 5 (fun _ _ => rfl) n [true,false] [false,true,true]
  have g3 := join0 g2 h3
  have h4 : run0 table 7 ⟨4,[true,true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false] n ++ [false,true,true]))⟩ = some ⟨0,[false,false],([false,false,false,false,false] ++ (rep [false,false,false,false,false] n ++ [false,true,true]))⟩ := by rfl
  have g4 := join0 g3 h4
  rw [show 1+(5*n)+10+(5*n)+7=10*n+18 by omega] at g4
  exact g4
inductive Digit where | zero | one | two
inductive W where | lastOne | lastTwo | cons (d : Digit) (w : W)
def encD : Digit → List Bool | .zero => Z | .one => O | .two => T2
def encode : W → List Bool
  | .lastOne => E
  | .lastTwo => T2
  | .cons d w => encD d ++ encode w
def next : W → W
  | .lastOne => .lastTwo
  | .lastTwo => .cons .zero .lastOne
  | .cons .zero w => .cons .one w
  | .cons .one w => .cons .two w
  | .cons .two w => .cons .zero (next w)
def count : Nat → W → Nat
  | 0, .lastOne => 14
  | k+1, .lastOne => 10*k+24
  | k, .lastTwo => 10*k+18
  | 0, .cons .zero _ => 8
  | k+1, .cons .zero _ => 10*k+18
  | 0, .cons .one _ => 14
  | k+1, .cons .one _ => 10*k+24
  | k, .cons .two w => count (k+1) w

theorem positive (w : W) (k : Nat) : 0 < count k w := by
  induction w generalizing k with
  | lastOne => cases k <;> simp only [count] <;> omega
  | lastTwo => cases k <;> simp only [count] <;> omega
  | cons d w ih =>
    cases d
    · cases k <;> simp only [count] <;> omega
    · cases k <;> simp only [count] <;> omega
    · simpa only [count] using ih (k+1)

theorem epoch (w : W) (k : Nat) :
    run0 table (count k w) (A (rep T2 k ++ encode w)) =
      some (A (rep Z k ++ encode (next w))) := by
  induction w generalizing k with
  | lastOne =>
    cases k with
    | zero => exact last1
    | succ k => simpa only [count,encode,next,rep,List.append_assoc,A,T2,Z,E] using carryLast1 k
  | lastTwo =>
    have H := carryLast2 k
    have hz : rep Z k ++ (Z ++ E) = Z ++ (rep Z k ++ E) := by
      rw [← List.append_assoc, rep_snoc, List.append_assoc]
    simp only [count,encode,next,encD]
    rw [rep_snoc T2 k, hz]
    simpa only [A,T2,Z,E,List.append_nil] using H
  | cons d w ih =>
    cases d
    · cases k with
      | zero => exact inc0 (encode w)
      | succ k => simpa only [count,encode,next,encD,rep,List.append_assoc,A,T2,Z,O] using carry0 k (encode w)
    · cases k with
      | zero => exact inc1 (encode w)
      | succ k => simpa only [count,encode,next,encD,rep,List.append_assoc,A,T2,Z,O] using carry1 k (encode w)
    · have H := ih (k+1)
      simpa only [count,encode,next,encD,rep,← rep_snoc T2 k,← rep_snoc Z k,List.append_assoc] using H

def orbit : Nat → W | 0 => .lastOne | n+1 => next (orbit n)
def family (n : Nat) : Z0 := A (encode (orbit n))
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  apply never_of_growth table family 8 (fun n => count 0 (orbit n)) (by rfl)
    (fun n => positive (orbit n) 0) _ m hm
  intro n
  simpa only [family,orbit,rep,List.nil_append] using epoch (orbit n) 0
#print axioms never
end BB6.Agent8Raw54.RA.M11
