import Raw54RAClosedCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.RA.M35
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent8Raw54.RACounter BB6.Agent8Raw54.RAClosed
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none
inductive Digit where | d0 | d1 | d2 | d3
inductive W where | e0 | e1 | e2 | cons (d : Digit) (w : W)
def D : Digit → List Bool | .d0 => [false,false,false,false,false,false,false] | .d1 => [false,true,true,false,false,false,false] | .d2 => [false,false,false,true,true,true,false] | .d3 => [false,true,true,true,true,true,false]
def enc : W → List Bool
  | .e0 => [false,true,true]
  | .e1 => [false,false,false,true,true,true]
  | .e2 => [false,true,true,true,true,true]
  | .cons d w => D d ++ enc w
def pre (d : Digit) : Nat → W → W | 0, w => w | k+1, w => .cons d (pre d k w)
theorem enc_pre (d : Digit) (k : Nat) (w : W) : enc (pre d k w) = rep (D d) k ++ enc w := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [pre,enc,ih,rep,List.append_assoc]
theorem d0zero (T : List Bool) : run0 table 8 (A (D .d0 ++ T)) = some (A (D .d1 ++ T)) := by rfl
theorem d0carry (n : Nat) (T : List Bool) : run0 table (16*n+24) ⟨0,[false,false],([false,true,true,true,true,true,false] ++ (rep [false,true,true,true,true,true,false] n ++ ([false,false,false,false,false,false,false] ++ T)))⟩ = some ⟨0,[false,false],([false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ ([false,true,true,false,false,false,false] ++ T)))⟩ := by
  have h0 : run0 table (9*n) ⟨0,[false,false],([false,true,true,true,true,true,false] ++ (rep [false,true,true,true,true,true,false] n ++ ([false,false,false,false,false,false,false] ++ T)))⟩ = some ⟨0,([false] ++ (rep [true,true,true,true,true,true,true] n ++ [false])),([false,true,true,true,true,true,false,false,false,false,false,false,false,false] ++ T)⟩ := by
    exact sweepR table 0 [false] [false,true,true,true,true,true,false] [false,true,true,true,true,true,false] [true,true,true,true,true,true,true] 9 (fun _ _ => rfl) n [false] ([false,false,false,false,false,false,false] ++ T)
  have h1 : run0 table 15 ⟨0,([false] ++ (rep [true,true,true,true,true,true,true] n ++ [false])),([false,true,true,true,true,true,false,false,false,false,false,false,false,false] ++ T)⟩ = some ⟨4,([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true] n ++ [false])),([false,true,true,false,false,false,false] ++ T)⟩ := by rfl
  have g1 := join0 h0 h1
  have h2 : run0 table (7*n) ⟨4,([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true] n ++ [false])),([false,true,true,false,false,false,false] ++ T)⟩ = some ⟨4,[true,true,true,true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false,false,false] n ++ ([false,true,true,false,false,false,false] ++ T)))⟩ := by
    exact sweepL table 4 [true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true] [false,false,false,false,false,false,false] 7 (fun _ _ => rfl) n [false] ([false,true,true,false,false,false,false] ++ T)
  have g2 := join0 g1 h2
  have h3 : run0 table 9 ⟨4,[true,true,true,true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false,false,false] n ++ ([false,true,true,false,false,false,false] ++ T)))⟩ = some ⟨0,[false,false],([false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ ([false,true,true,false,false,false,false] ++ T)))⟩ := by rfl
  have g3 := join0 g2 h3
  rw [show (9*n)+15+(7*n)+9=16*n+24 by omega] at g3
  exact g3
theorem d1zero (T : List Bool) : run0 table 16 (A (D .d1 ++ T)) = some (A (D .d2 ++ T)) := by rfl
theorem d1carry (n : Nat) (T : List Bool) : run0 table (16*n+32) ⟨0,[false,false],([false,true,true,true,true,true,false] ++ (rep [false,true,true,true,true,true,false] n ++ ([false,true,true,false,false,false,false] ++ T)))⟩ = some ⟨0,[false,false],([false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ ([false,false,false,true,true,true,false] ++ T)))⟩ := by
  have h0 : run0 table (9*n) ⟨0,[false,false],([false,true,true,true,true,true,false] ++ (rep [false,true,true,true,true,true,false] n ++ ([false,true,true,false,false,false,false] ++ T)))⟩ = some ⟨0,([false] ++ (rep [true,true,true,true,true,true,true] n ++ [false])),([false,true,true,true,true,true,false,false,true,true,false,false,false,false] ++ T)⟩ := by
    exact sweepR table 0 [false] [false,true,true,true,true,true,false] [false,true,true,true,true,true,false] [true,true,true,true,true,true,true] 9 (fun _ _ => rfl) n [false] ([false,true,true,false,false,false,false] ++ T)
  have h1 : run0 table 21 ⟨0,([false] ++ (rep [true,true,true,true,true,true,true] n ++ [false])),([false,true,true,true,true,true,false,false,true,true,false,false,false,false] ++ T)⟩ = some ⟨4,([true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true] n ++ [false])),([false,true,true,true,false] ++ T)⟩ := by rfl
  have g1 := join0 h0 h1
  have h2 : run0 table (7*n) ⟨4,([true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true] n ++ [false])),([false,true,true,true,false] ++ T)⟩ = some ⟨4,[true,true,true,true,true,true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false,false,false] n ++ ([false,true,true,true,false] ++ T)))⟩ := by
    exact sweepL table 4 [true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true] [false,false,false,false,false,false,false] 7 (fun _ _ => rfl) n [false] ([false,true,true,true,false] ++ T)
  have g2 := join0 g1 h2
  have h3 : run0 table 11 ⟨4,[true,true,true,true,true,true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false,false,false] n ++ ([false,true,true,true,false] ++ T)))⟩ = some ⟨0,[false,false],([false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ ([false,true,true,true,false] ++ T)))⟩ := by rfl
  have g3 := join0 g2 h3
  have e4 : (⟨0,[false,false],([false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ ([false,true,true,true,false] ++ T)))⟩ : Z0) = ⟨0,[false,false],([false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ ([false,false,true,true,true,false] ++ T)))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [false,false,false,false,false,false,false,false] ([false,true,true,true,false] ++ T) [false,false,false,false,false,false] false n)
  rw [e4] at g3
  have e5 : (⟨0,[false,false],([false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ ([false,false,true,true,true,false] ++ T)))⟩ : Z0) = ⟨0,[false,false],([false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ ([false,false,false,true,true,true,false] ++ T)))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [false,false,false,false,false,false,false] ([false,false,true,true,true,false] ++ T) [false,false,false,false,false,false] false n)
  rw [e5] at g3
  rw [show (9*n)+21+(7*n)+11=16*n+32 by omega] at g3
  exact g3
theorem d2zero (T : List Bool) : run0 table 8 (A (D .d2 ++ T)) = some (A (D .d3 ++ T)) := by rfl
theorem d2carry (n : Nat) (T : List Bool) : run0 table (16*n+24) ⟨0,[false,false],([false,true,true,true,true,true,false] ++ (rep [false,true,true,true,true,true,false] n ++ ([false,false,false,true,true,true,false] ++ T)))⟩ = some ⟨0,[false,false],([false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ ([false,true,true,true,true,true,false] ++ T)))⟩ := by
  have h0 : run0 table (9*n) ⟨0,[false,false],([false,true,true,true,true,true,false] ++ (rep [false,true,true,true,true,true,false] n ++ ([false,false,false,true,true,true,false] ++ T)))⟩ = some ⟨0,([false] ++ (rep [true,true,true,true,true,true,true] n ++ [false])),([false,true,true,true,true,true,false,false,false,false,true,true,true,false] ++ T)⟩ := by
    exact sweepR table 0 [false] [false,true,true,true,true,true,false] [false,true,true,true,true,true,false] [true,true,true,true,true,true,true] 9 (fun _ _ => rfl) n [false] ([false,false,false,true,true,true,false] ++ T)
  have h1 : run0 table 15 ⟨0,([false] ++ (rep [true,true,true,true,true,true,true] n ++ [false])),([false,true,true,true,true,true,false,false,false,false,true,true,true,false] ++ T)⟩ = some ⟨4,([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true] n ++ [false])),([false,true,true,true,true,true,false] ++ T)⟩ := by rfl
  have g1 := join0 h0 h1
  have h2 : run0 table (7*n) ⟨4,([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true] n ++ [false])),([false,true,true,true,true,true,false] ++ T)⟩ = some ⟨4,[true,true,true,true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false,false,false] n ++ ([false,true,true,true,true,true,false] ++ T)))⟩ := by
    exact sweepL table 4 [true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true] [false,false,false,false,false,false,false] 7 (fun _ _ => rfl) n [false] ([false,true,true,true,true,true,false] ++ T)
  have g2 := join0 g1 h2
  have h3 : run0 table 9 ⟨4,[true,true,true,true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false,false,false] n ++ ([false,true,true,true,true,true,false] ++ T)))⟩ = some ⟨0,[false,false],([false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ ([false,true,true,true,true,true,false] ++ T)))⟩ := by rfl
  have g3 := join0 g2 h3
  rw [show (9*n)+15+(7*n)+9=16*n+24 by omega] at g3
  exact g3
theorem e0zero : run0 table 16 (A (enc .e0)) = some (A (enc (W.e1))) := by rfl
theorem e0carry (n : Nat) : run0 table (16*n+32) ⟨0,[false,false],([false,true,true,true,true,true,false] ++ (rep [false,true,true,true,true,true,false] n ++ [false,true,true]))⟩ = some ⟨0,[false,false],([false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ [false,false,false,true,true,true]))⟩ := by
  have h0 : run0 table (9*n) ⟨0,[false,false],([false,true,true,true,true,true,false] ++ (rep [false,true,true,true,true,true,false] n ++ [false,true,true]))⟩ = some ⟨0,([false] ++ (rep [true,true,true,true,true,true,true] n ++ [false])),[false,true,true,true,true,true,false,false,true,true]⟩ := by
    exact sweepR table 0 [false] [false,true,true,true,true,true,false] [false,true,true,true,true,true,false] [true,true,true,true,true,true,true] 9 (fun _ _ => rfl) n [false] [false,true,true]
  have h1 : run0 table 21 ⟨0,([false] ++ (rep [true,true,true,true,true,true,true] n ++ [false])),[false,true,true,true,true,true,false,false,true,true]⟩ = some ⟨4,([true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true] n ++ [false])),[false,true,true,true]⟩ := by rfl
  have g1 := join0 h0 h1
  have h2 : run0 table (7*n) ⟨4,([true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true] n ++ [false])),[false,true,true,true]⟩ = some ⟨4,[true,true,true,true,true,true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false,false,false] n ++ [false,true,true,true]))⟩ := by
    exact sweepL table 4 [true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true] [false,false,false,false,false,false,false] 7 (fun _ _ => rfl) n [false] [false,true,true,true]
  have g2 := join0 g1 h2
  have h3 : run0 table 11 ⟨4,[true,true,true,true,true,true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false,false,false] n ++ [false,true,true,true]))⟩ = some ⟨0,[false,false],([false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ [false,true,true,true]))⟩ := by rfl
  have g3 := join0 g2 h3
  have e4 : (⟨0,[false,false],([false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ [false,true,true,true]))⟩ : Z0) = ⟨0,[false,false],([false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ [false,false,true,true,true]))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [false,false,false,false,false,false,false,false] [false,true,true,true] [false,false,false,false,false,false] false n)
  rw [e4] at g3
  have e5 : (⟨0,[false,false],([false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ [false,false,true,true,true]))⟩ : Z0) = ⟨0,[false,false],([false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ [false,false,false,true,true,true]))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [false,false,false,false,false,false,false] [false,false,true,true,true] [false,false,false,false,false,false] false n)
  rw [e5] at g3
  rw [show (9*n)+21+(7*n)+11=16*n+32 by omega] at g3
  exact g3
theorem e1zero : run0 table 8 (A (enc .e1)) = some (A (enc (W.e2))) := by rfl
theorem e1carry (n : Nat) : run0 table (16*n+24) ⟨0,[false,false],([false,true,true,true,true,true,false] ++ (rep [false,true,true,true,true,true,false] n ++ [false,false,false,true,true,true]))⟩ = some ⟨0,[false,false],([false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ [false,true,true,true,true,true]))⟩ := by
  have h0 : run0 table (9*n) ⟨0,[false,false],([false,true,true,true,true,true,false] ++ (rep [false,true,true,true,true,true,false] n ++ [false,false,false,true,true,true]))⟩ = some ⟨0,([false] ++ (rep [true,true,true,true,true,true,true] n ++ [false])),[false,true,true,true,true,true,false,false,false,false,true,true,true]⟩ := by
    exact sweepR table 0 [false] [false,true,true,true,true,true,false] [false,true,true,true,true,true,false] [true,true,true,true,true,true,true] 9 (fun _ _ => rfl) n [false] [false,false,false,true,true,true]
  have h1 : run0 table 15 ⟨0,([false] ++ (rep [true,true,true,true,true,true,true] n ++ [false])),[false,true,true,true,true,true,false,false,false,false,true,true,true]⟩ = some ⟨4,([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true] n ++ [false])),[false,true,true,true,true,true]⟩ := by rfl
  have g1 := join0 h0 h1
  have h2 : run0 table (7*n) ⟨4,([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true] n ++ [false])),[false,true,true,true,true,true]⟩ = some ⟨4,[true,true,true,true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false,false,false] n ++ [false,true,true,true,true,true]))⟩ := by
    exact sweepL table 4 [true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true] [false,false,false,false,false,false,false] 7 (fun _ _ => rfl) n [false] [false,true,true,true,true,true]
  have g2 := join0 g1 h2
  have h3 : run0 table 9 ⟨4,[true,true,true,true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false,false,false] n ++ [false,true,true,true,true,true]))⟩ = some ⟨0,[false,false],([false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ [false,true,true,true,true,true]))⟩ := by rfl
  have g3 := join0 g2 h3
  rw [show (9*n)+15+(7*n)+9=16*n+24 by omega] at g3
  exact g3
theorem e2zero : run0 table 24 (A (enc .e2)) = some (A (enc (W.cons .d0 .e0))) := by rfl
theorem e2carry (n : Nat) : run0 table (16*n+40) ⟨0,[false,false],([false,true,true,true,true,true,false] ++ (rep [false,true,true,true,true,true,false] n ++ [false,true,true,true,true,true]))⟩ = some ⟨0,[false,false],([false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ [false,false,false,false,false,false,false,false,true,true]))⟩ := by
  have h0 : run0 table (9*n) ⟨0,[false,false],([false,true,true,true,true,true,false] ++ (rep [false,true,true,true,true,true,false] n ++ [false,true,true,true,true,true]))⟩ = some ⟨0,([false] ++ (rep [true,true,true,true,true,true,true] n ++ [false])),[false,true,true,true,true,true,false,false,true,true,true,true,true]⟩ := by
    exact sweepR table 0 [false] [false,true,true,true,true,true,false] [false,true,true,true,true,true,false] [true,true,true,true,true,true,true] 9 (fun _ _ => rfl) n [false] [false,true,true,true,true,true]
  have h1 : run0 table 24 ⟨0,([false] ++ (rep [true,true,true,true,true,true,true] n ++ [false])),[false,true,true,true,true,true,false,false,true,true,true,true,true]⟩ = some ⟨4,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true] n ++ [false])),[false,true,true]⟩ := by rfl
  have g1 := join0 h0 h1
  have h2 : run0 table (7*n) ⟨4,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true] n ++ [false])),[false,true,true]⟩ = some ⟨4,[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false,false,false] n ++ [false,true,true]))⟩ := by
    exact sweepL table 4 [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true] [false,false,false,false,false,false,false] 7 (fun _ _ => rfl) n [false] [false,true,true]
  have g2 := join0 g1 h2
  have h3 : run0 table 16 ⟨4,[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false,false,false] n ++ [false,true,true]))⟩ = some ⟨0,[false,false],([false,false,false,false,false,false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ [false,true,true]))⟩ := by rfl
  have g3 := join0 g2 h3
  have e4 : (⟨0,[false,false],([false,false,false,false,false,false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ [false,true,true]))⟩ : Z0) = ⟨0,[false,false],([false,false,false,false,false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ [false,false,true,true]))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [false,false,false,false,false,false,false,false,false,false,false,false,false] [false,true,true] [false,false,false,false,false,false] false n)
  rw [e4] at g3
  have e5 : (⟨0,[false,false],([false,false,false,false,false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ [false,false,true,true]))⟩ : Z0) = ⟨0,[false,false],([false,false,false,false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ [false,false,false,true,true]))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [false,false,false,false,false,false,false,false,false,false,false,false] [false,false,true,true] [false,false,false,false,false,false] false n)
  rw [e5] at g3
  have e6 : (⟨0,[false,false],([false,false,false,false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ [false,false,false,true,true]))⟩ : Z0) = ⟨0,[false,false],([false,false,false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ [false,false,false,false,true,true]))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [false,false,false,false,false,false,false,false,false,false,false] [false,false,false,true,true] [false,false,false,false,false,false] false n)
  rw [e6] at g3
  have e7 : (⟨0,[false,false],([false,false,false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ [false,false,false,false,true,true]))⟩ : Z0) = ⟨0,[false,false],([false,false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ [false,false,false,false,false,true,true]))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [false,false,false,false,false,false,false,false,false,false] [false,false,false,false,true,true] [false,false,false,false,false,false] false n)
  rw [e7] at g3
  have e8 : (⟨0,[false,false],([false,false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ [false,false,false,false,false,true,true]))⟩ : Z0) = ⟨0,[false,false],([false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ [false,false,false,false,false,false,true,true]))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [false,false,false,false,false,false,false,false,false] [false,false,false,false,false,true,true] [false,false,false,false,false,false] false n)
  rw [e8] at g3
  have e9 : (⟨0,[false,false],([false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ [false,false,false,false,false,false,true,true]))⟩ : Z0) = ⟨0,[false,false],([false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ [false,false,false,false,false,false,false,true,true]))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [false,false,false,false,false,false,false,false] [false,false,false,false,false,false,true,true] [false,false,false,false,false,false] false n)
  rw [e9] at g3
  have e10 : (⟨0,[false,false],([false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ [false,false,false,false,false,false,false,true,true]))⟩ : Z0) = ⟨0,[false,false],([false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false] n ++ [false,false,false,false,false,false,false,false,true,true]))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [false,false,false,false,false,false,false] [false,false,false,false,false,false,false,true,true] [false,false,false,false,false,false] false n)
  rw [e10] at g3
  rw [show (9*n)+24+(7*n)+16=16*n+40 by omega] at g3
  exact g3
theorem closedCarry (w : W) (k : Nat) : ∃ t w', 0<t ∧ run0 table t (A (rep (D .d3) k ++ enc w)) = some (A (enc w')) := by
  induction w generalizing k with
  | e0 =>
    cases k with
    | zero => exact ⟨16,W.e1,by omega,e0zero⟩
    | succ k =>
      refine ⟨16*k+32,pre .d0 (k+1) (W.e1),by omega,?_⟩
      simpa only [enc_pre,enc,rep,D,List.append_assoc,List.nil_append,List.append_nil,A] using e0carry k
  | e1 =>
    cases k with
    | zero => exact ⟨8,W.e2,by omega,e1zero⟩
    | succ k =>
      refine ⟨16*k+24,pre .d0 (k+1) (W.e2),by omega,?_⟩
      simpa only [enc_pre,enc,rep,D,List.append_assoc,List.nil_append,List.append_nil,A] using e1carry k
  | e2 =>
    cases k with
    | zero => exact ⟨24,W.cons .d0 .e0,by omega,e2zero⟩
    | succ k =>
      refine ⟨16*k+40,pre .d0 (k+1) (W.cons .d0 .e0),by omega,?_⟩
      simpa only [enc_pre,enc,rep,D,List.append_assoc,List.nil_append,List.append_nil,List.cons_append,A] using e2carry k
  | cons d w ih =>
    cases d
    · cases k with
      | zero => exact ⟨8,.cons .d1 w,by omega,d0zero (enc w)⟩
      | succ k =>
        refine ⟨16*k+24,pre .d0 (k+1) (.cons .d1 w),by omega,?_⟩
        simpa only [enc_pre,enc,rep,D,List.append_assoc,List.nil_append,List.append_nil,A] using d0carry k (enc w)
    · cases k with
      | zero => exact ⟨16,.cons .d2 w,by omega,d1zero (enc w)⟩
      | succ k =>
        refine ⟨16*k+32,pre .d0 (k+1) (.cons .d2 w),by omega,?_⟩
        simpa only [enc_pre,enc,rep,D,List.append_assoc,List.nil_append,List.append_nil,A] using d1carry k (enc w)
    · cases k with
      | zero => exact ⟨8,.cons .d3 w,by omega,d2zero (enc w)⟩
      | succ k =>
        refine ⟨16*k+24,pre .d0 (k+1) (.cons .d3 w),by omega,?_⟩
        simpa only [enc_pre,enc,rep,D,List.append_assoc,List.nil_append,List.append_nil,A] using d2carry k (enc w)
    · obtain ⟨t,w',ht,H⟩ := ih (k+1)
      refine ⟨t,w',ht,?_⟩
      simpa only [enc,rep,← rep_snoc (D .d3) k,List.append_assoc] using H
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  apply neverOfSection table W (fun w => A (enc w)) .e0 8 (by rfl) _ m hm
  intro w
  simpa only [rep,List.nil_append] using closedCarry w 0
#print axioms never
end BB6.Agent8Raw54.RA.M35
