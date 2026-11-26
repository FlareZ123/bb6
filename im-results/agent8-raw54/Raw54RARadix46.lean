import Raw54RAClosedCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.RA.M46
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent8Raw54.RACounter BB6.Agent8Raw54.RAClosed
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨true,true,1⟩)
  | _,_ => none
inductive Digit where | d0 | d1 | d2 | d3 | d4 | d5 | d6
inductive W where | e0 | e1 | e2 | cons (d : Digit) (w : W)
def D : Digit → List Bool | .d0 => [false,false,false,false,false,false,false,false] | .d1 => [false,true,true,false,false,false,false,false] | .d2 => [true,true,true,false,false,false,false,false] | .d3 => [false,false,false,false,false,false,true,true] | .d4 => [false,true,true,false,false,false,true,true] | .d5 => [true,true,true,false,false,false,true,true] | .d6 => [true,true,true,true,true,true,true,true]
def enc : W → List Bool
  | .e0 => []
  | .e1 => [false,true,true]
  | .e2 => [true,true,true]
  | .cons d w => D d ++ enc w
def pre (d : Digit) : Nat → W → W | 0, w => w | k+1, w => .cons d (pre d k w)
theorem enc_pre (d : Digit) (k : Nat) (w : W) : enc (pre d k w) = rep (D d) k ++ enc w := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [pre,enc,ih,rep,List.append_assoc]
theorem d0zero (T : List Bool) : run0 table 8 (A (D .d0 ++ T)) = some (A (D .d1 ++ T)) := by rfl
theorem d0carry (n : Nat) (T : List Bool) : run0 table (16*n+24) ⟨0,[false,false],([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([false,false,false,false,false,false,false,false] ++ T)))⟩ = some ⟨0,[false,false],([false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ ([false,true,true,false,false,false,false,false] ++ T)))⟩ := by
  have h0 : run0 table 1 ⟨0,[false,false],([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([false,false,false,false,false,false,false,false] ++ T)))⟩ = some ⟨1,[true,true,false],([true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([false,false,false,false,false,false,false,false] ++ T)))⟩ := by rfl
  have h1 : run0 table (8*n) ⟨1,[true,true,false],([true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([false,false,false,false,false,false,false,false] ++ T)))⟩ = some ⟨1,([true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),([true,true,true,true,true,true,true,false,false,false,false,false,false,false,false] ++ T)⟩ := by
    exact sweepR table 1 [true] [true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] 8 (fun _ _ => rfl) n [true,false] ([false,false,false,false,false,false,false,false] ++ T)
  have g1 := join0 h0 h1
  have h2 : run0 table 13 ⟨1,([true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),([true,true,true,true,true,true,true,false,false,false,false,false,false,false,false] ++ T)⟩ = some ⟨4,([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),([false,true,true,false,false,false,false,false] ++ T)⟩ := by rfl
  have g2 := join0 g1 h2
  have h3 : run0 table (8*n) ⟨4,([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),([false,true,true,false,false,false,false,false] ++ T)⟩ = some ⟨4,[true,true,true,true,true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false,false,false,false] n ++ ([false,true,true,false,false,false,false,false] ++ T)))⟩ := by
    exact sweepL table 4 [true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true] [false,false,false,false,false,false,false,false] 8 (fun _ _ => rfl) n [true,false] ([false,true,true,false,false,false,false,false] ++ T)
  have g3 := join0 g2 h3
  have h4 : run0 table 10 ⟨4,[true,true,true,true,true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false,false,false,false] n ++ ([false,true,true,false,false,false,false,false] ++ T)))⟩ = some ⟨0,[false,false],([false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ ([false,true,true,false,false,false,false,false] ++ T)))⟩ := by rfl
  have g4 := join0 g3 h4
  rw [show 1+(8*n)+13+(8*n)+10=16*n+24 by omega] at g4
  exact g4
theorem d1zero (T : List Bool) : run0 table 8 (A (D .d1 ++ T)) = some (A (D .d2 ++ T)) := by rfl
theorem d1carry (n : Nat) (T : List Bool) : run0 table (16*n+24) ⟨0,[false,false],([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([false,true,true,false,false,false,false,false] ++ T)))⟩ = some ⟨0,[false,false],([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,true,true,false,false,false,false,false] ++ T)))⟩ := by
  have h0 : run0 table 1 ⟨0,[false,false],([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([false,true,true,false,false,false,false,false] ++ T)))⟩ = some ⟨1,[true,true,false],([true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([false,true,true,false,false,false,false,false] ++ T)))⟩ := by rfl
  have h1 : run0 table (8*n) ⟨1,[true,true,false],([true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([false,true,true,false,false,false,false,false] ++ T)))⟩ = some ⟨1,([true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),([true,true,true,true,true,true,true,false,true,true,false,false,false,false,false] ++ T)⟩ := by
    exact sweepR table 1 [true] [true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] 8 (fun _ _ => rfl) n [true,false] ([false,true,true,false,false,false,false,false] ++ T)
  have g1 := join0 h0 h1
  have h2 : run0 table 9 ⟨1,([true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),([true,true,true,true,true,true,true,false,true,true,false,false,false,false,false] ++ T)⟩ = some ⟨2,([true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),([true,false,false,false,false,false] ++ T)⟩ := by rfl
  have g2 := join0 g1 h2
  have h3 : run0 table (8*n) ⟨2,([true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),([true,false,false,false,false,false] ++ T)⟩ = some ⟨2,[true,true,true,true,true,true,true,true,true,true,true,false],([] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,false,false,false,false,false] ++ T)))⟩ := by
    exact sweepL table 2 [true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] 8 (fun _ _ => rfl) n [true,false] ([true,false,false,false,false,false] ++ T)
  have g3 := join0 g2 h3
  have h4 : run0 table 14 ⟨2,[true,true,true,true,true,true,true,true,true,true,true,false],([] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,false,false,false,false,false] ++ T)))⟩ = some ⟨0,[false,false],([true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,false,false,false,false,false] ++ T)))⟩ := by rfl
  have g4 := join0 g3 h4
  have e5 : (⟨0,[false,false],([true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,false,false,false,false,false] ++ T)))⟩ : Z0) = ⟨0,[false,false],([true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,true,false,false,false,false,false] ++ T)))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [true,true,true,true,true,true,true,true,true] ([true,false,false,false,false,false] ++ T) [true,true,true,true,true,true,true] true n)
  rw [e5] at g4
  have e6 : (⟨0,[false,false],([true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,true,false,false,false,false,false] ++ T)))⟩ : Z0) = ⟨0,[false,false],([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,true,true,false,false,false,false,false] ++ T)))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [true,true,true,true,true,true,true,true] ([true,true,false,false,false,false,false] ++ T) [true,true,true,true,true,true,true] true n)
  rw [e6] at g4
  rw [show 1+(8*n)+9+(8*n)+14=16*n+24 by omega] at g4
  exact g4
theorem d2zero (T : List Bool) : run0 table 18 (A (D .d2 ++ T)) = some (A (D .d3 ++ T)) := by rfl
theorem d2carry (n : Nat) (T : List Bool) : run0 table (16*n+34) ⟨0,[false,false],([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,true,true,false,false,false,false,false] ++ T)))⟩ = some ⟨0,[false,false],([false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ ([false,false,false,false,false,false,true,true] ++ T)))⟩ := by
  have h0 : run0 table 1 ⟨0,[false,false],([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,true,true,false,false,false,false,false] ++ T)))⟩ = some ⟨1,[true,true,false],([true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,true,true,false,false,false,false,false] ++ T)))⟩ := by rfl
  have h1 : run0 table (8*n) ⟨1,[true,true,false],([true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,true,true,false,false,false,false,false] ++ T)))⟩ = some ⟨1,([true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),([true,true,true,true,true,true,true,true,true,true,false,false,false,false,false] ++ T)⟩ := by
    exact sweepR table 1 [true] [true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] 8 (fun _ _ => rfl) n [true,false] ([true,true,true,false,false,false,false,false] ++ T)
  have g1 := join0 h0 h1
  have h2 : run0 table 18 ⟨1,([true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),([true,true,true,true,true,true,true,true,true,true,false,false,false,false,false] ++ T)⟩ = some ⟨4,([true,true,true,true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),([false,true,true] ++ T)⟩ := by rfl
  have g2 := join0 g1 h2
  have h3 : run0 table (8*n) ⟨4,([true,true,true,true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),([false,true,true] ++ T)⟩ = some ⟨4,[true,true,true,true,true,true,true,true,true,true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false,false,false,false] n ++ ([false,true,true] ++ T)))⟩ := by
    exact sweepL table 4 [true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true] [false,false,false,false,false,false,false,false] 8 (fun _ _ => rfl) n [true,false] ([false,true,true] ++ T)
  have g3 := join0 g2 h3
  have h4 : run0 table 15 ⟨4,[true,true,true,true,true,true,true,true,true,true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false,false,false,false] n ++ ([false,true,true] ++ T)))⟩ = some ⟨0,[false,false],([false,false,false,false,false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ ([false,true,true] ++ T)))⟩ := by rfl
  have g4 := join0 g3 h4
  have e5 : (⟨0,[false,false],([false,false,false,false,false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ ([false,true,true] ++ T)))⟩ : Z0) = ⟨0,[false,false],([false,false,false,false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ ([false,false,true,true] ++ T)))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [false,false,false,false,false,false,false,false,false,false,false,false] ([false,true,true] ++ T) [false,false,false,false,false,false,false] false n)
  rw [e5] at g4
  have e6 : (⟨0,[false,false],([false,false,false,false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ ([false,false,true,true] ++ T)))⟩ : Z0) = ⟨0,[false,false],([false,false,false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ ([false,false,false,true,true] ++ T)))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [false,false,false,false,false,false,false,false,false,false,false] ([false,false,true,true] ++ T) [false,false,false,false,false,false,false] false n)
  rw [e6] at g4
  have e7 : (⟨0,[false,false],([false,false,false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ ([false,false,false,true,true] ++ T)))⟩ : Z0) = ⟨0,[false,false],([false,false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ ([false,false,false,false,true,true] ++ T)))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [false,false,false,false,false,false,false,false,false,false] ([false,false,false,true,true] ++ T) [false,false,false,false,false,false,false] false n)
  rw [e7] at g4
  have e8 : (⟨0,[false,false],([false,false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ ([false,false,false,false,true,true] ++ T)))⟩ : Z0) = ⟨0,[false,false],([false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ ([false,false,false,false,false,true,true] ++ T)))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [false,false,false,false,false,false,false,false,false] ([false,false,false,false,true,true] ++ T) [false,false,false,false,false,false,false] false n)
  rw [e8] at g4
  have e9 : (⟨0,[false,false],([false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ ([false,false,false,false,false,true,true] ++ T)))⟩ : Z0) = ⟨0,[false,false],([false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ ([false,false,false,false,false,false,true,true] ++ T)))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [false,false,false,false,false,false,false,false] ([false,false,false,false,false,true,true] ++ T) [false,false,false,false,false,false,false] false n)
  rw [e9] at g4
  rw [show 1+(8*n)+18+(8*n)+15=16*n+34 by omega] at g4
  exact g4
theorem d3zero (T : List Bool) : run0 table 8 (A (D .d3 ++ T)) = some (A (D .d4 ++ T)) := by rfl
theorem d3carry (n : Nat) (T : List Bool) : run0 table (16*n+24) ⟨0,[false,false],([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([false,false,false,false,false,false,true,true] ++ T)))⟩ = some ⟨0,[false,false],([false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ ([false,true,true,false,false,false,true,true] ++ T)))⟩ := by
  have h0 : run0 table 1 ⟨0,[false,false],([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([false,false,false,false,false,false,true,true] ++ T)))⟩ = some ⟨1,[true,true,false],([true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([false,false,false,false,false,false,true,true] ++ T)))⟩ := by rfl
  have h1 : run0 table (8*n) ⟨1,[true,true,false],([true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([false,false,false,false,false,false,true,true] ++ T)))⟩ = some ⟨1,([true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),([true,true,true,true,true,true,true,false,false,false,false,false,false,true,true] ++ T)⟩ := by
    exact sweepR table 1 [true] [true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] 8 (fun _ _ => rfl) n [true,false] ([false,false,false,false,false,false,true,true] ++ T)
  have g1 := join0 h0 h1
  have h2 : run0 table 13 ⟨1,([true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),([true,true,true,true,true,true,true,false,false,false,false,false,false,true,true] ++ T)⟩ = some ⟨4,([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),([false,true,true,false,false,false,true,true] ++ T)⟩ := by rfl
  have g2 := join0 g1 h2
  have h3 : run0 table (8*n) ⟨4,([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),([false,true,true,false,false,false,true,true] ++ T)⟩ = some ⟨4,[true,true,true,true,true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false,false,false,false] n ++ ([false,true,true,false,false,false,true,true] ++ T)))⟩ := by
    exact sweepL table 4 [true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true] [false,false,false,false,false,false,false,false] 8 (fun _ _ => rfl) n [true,false] ([false,true,true,false,false,false,true,true] ++ T)
  have g3 := join0 g2 h3
  have h4 : run0 table 10 ⟨4,[true,true,true,true,true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false,false,false,false] n ++ ([false,true,true,false,false,false,true,true] ++ T)))⟩ = some ⟨0,[false,false],([false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ ([false,true,true,false,false,false,true,true] ++ T)))⟩ := by rfl
  have g4 := join0 g3 h4
  rw [show 1+(8*n)+13+(8*n)+10=16*n+24 by omega] at g4
  exact g4
theorem d4zero (T : List Bool) : run0 table 8 (A (D .d4 ++ T)) = some (A (D .d5 ++ T)) := by rfl
theorem d4carry (n : Nat) (T : List Bool) : run0 table (16*n+24) ⟨0,[false,false],([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([false,true,true,false,false,false,true,true] ++ T)))⟩ = some ⟨0,[false,false],([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,true,true,false,false,false,true,true] ++ T)))⟩ := by
  have h0 : run0 table 1 ⟨0,[false,false],([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([false,true,true,false,false,false,true,true] ++ T)))⟩ = some ⟨1,[true,true,false],([true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([false,true,true,false,false,false,true,true] ++ T)))⟩ := by rfl
  have h1 : run0 table (8*n) ⟨1,[true,true,false],([true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([false,true,true,false,false,false,true,true] ++ T)))⟩ = some ⟨1,([true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),([true,true,true,true,true,true,true,false,true,true,false,false,false,true,true] ++ T)⟩ := by
    exact sweepR table 1 [true] [true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] 8 (fun _ _ => rfl) n [true,false] ([false,true,true,false,false,false,true,true] ++ T)
  have g1 := join0 h0 h1
  have h2 : run0 table 9 ⟨1,([true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),([true,true,true,true,true,true,true,false,true,true,false,false,false,true,true] ++ T)⟩ = some ⟨2,([true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),([true,false,false,false,true,true] ++ T)⟩ := by rfl
  have g2 := join0 g1 h2
  have h3 : run0 table (8*n) ⟨2,([true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),([true,false,false,false,true,true] ++ T)⟩ = some ⟨2,[true,true,true,true,true,true,true,true,true,true,true,false],([] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,false,false,false,true,true] ++ T)))⟩ := by
    exact sweepL table 2 [true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] 8 (fun _ _ => rfl) n [true,false] ([true,false,false,false,true,true] ++ T)
  have g3 := join0 g2 h3
  have h4 : run0 table 14 ⟨2,[true,true,true,true,true,true,true,true,true,true,true,false],([] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,false,false,false,true,true] ++ T)))⟩ = some ⟨0,[false,false],([true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,false,false,false,true,true] ++ T)))⟩ := by rfl
  have g4 := join0 g3 h4
  have e5 : (⟨0,[false,false],([true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,false,false,false,true,true] ++ T)))⟩ : Z0) = ⟨0,[false,false],([true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,true,false,false,false,true,true] ++ T)))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [true,true,true,true,true,true,true,true,true] ([true,false,false,false,true,true] ++ T) [true,true,true,true,true,true,true] true n)
  rw [e5] at g4
  have e6 : (⟨0,[false,false],([true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,true,false,false,false,true,true] ++ T)))⟩ : Z0) = ⟨0,[false,false],([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,true,true,false,false,false,true,true] ++ T)))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [true,true,true,true,true,true,true,true] ([true,true,false,false,false,true,true] ++ T) [true,true,true,true,true,true,true] true n)
  rw [e6] at g4
  rw [show 1+(8*n)+9+(8*n)+14=16*n+24 by omega] at g4
  exact g4
theorem d5zero (T : List Bool) : run0 table 18 (A (D .d5 ++ T)) = some (A (D .d6 ++ T)) := by rfl
theorem d5carry (n : Nat) (T : List Bool) : run0 table (16*n+34) ⟨0,[false,false],([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,true,true,false,false,false,true,true] ++ T)))⟩ = some ⟨0,[false,false],([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,true,true,true,true,true,true,true] ++ T)))⟩ := by
  have h0 : run0 table 1 ⟨0,[false,false],([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,true,true,false,false,false,true,true] ++ T)))⟩ = some ⟨1,[true,true,false],([true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,true,true,false,false,false,true,true] ++ T)))⟩ := by rfl
  have h1 : run0 table (8*n) ⟨1,[true,true,false],([true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,true,true,false,false,false,true,true] ++ T)))⟩ = some ⟨1,([true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),([true,true,true,true,true,true,true,true,true,true,false,false,false,true,true] ++ T)⟩ := by
    exact sweepR table 1 [true] [true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] 8 (fun _ _ => rfl) n [true,false] ([true,true,true,false,false,false,true,true] ++ T)
  have g1 := join0 h0 h1
  have h2 : run0 table 14 ⟨1,([true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),([true,true,true,true,true,true,true,true,true,true,false,false,false,true,true] ++ T)⟩ = some ⟨2,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),([true] ++ T)⟩ := by rfl
  have g2 := join0 g1 h2
  have h3 : run0 table (8*n) ⟨2,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),([true] ++ T)⟩ = some ⟨2,[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false],([] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true] ++ T)))⟩ := by
    exact sweepL table 2 [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] 8 (fun _ _ => rfl) n [true,false] ([true] ++ T)
  have g3 := join0 g2 h3
  have h4 : run0 table 19 ⟨2,[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false],([] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true] ++ T)))⟩ = some ⟨0,[false,false],([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true] ++ T)))⟩ := by rfl
  have g4 := join0 g3 h4
  have e5 : (⟨0,[false,false],([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true] ++ T)))⟩ : Z0) = ⟨0,[false,false],([true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,true] ++ T)))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [true,true,true,true,true,true,true,true,true,true,true,true,true,true] ([true] ++ T) [true,true,true,true,true,true,true] true n)
  rw [e5] at g4
  have e6 : (⟨0,[false,false],([true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,true] ++ T)))⟩ : Z0) = ⟨0,[false,false],([true,true,true,true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,true,true] ++ T)))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [true,true,true,true,true,true,true,true,true,true,true,true,true] ([true,true] ++ T) [true,true,true,true,true,true,true] true n)
  rw [e6] at g4
  have e7 : (⟨0,[false,false],([true,true,true,true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,true,true] ++ T)))⟩ : Z0) = ⟨0,[false,false],([true,true,true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,true,true,true] ++ T)))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [true,true,true,true,true,true,true,true,true,true,true,true] ([true,true,true] ++ T) [true,true,true,true,true,true,true] true n)
  rw [e7] at g4
  have e8 : (⟨0,[false,false],([true,true,true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,true,true,true] ++ T)))⟩ : Z0) = ⟨0,[false,false],([true,true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,true,true,true,true] ++ T)))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [true,true,true,true,true,true,true,true,true,true,true] ([true,true,true,true] ++ T) [true,true,true,true,true,true,true] true n)
  rw [e8] at g4
  have e9 : (⟨0,[false,false],([true,true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,true,true,true,true] ++ T)))⟩ : Z0) = ⟨0,[false,false],([true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,true,true,true,true,true] ++ T)))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [true,true,true,true,true,true,true,true,true,true] ([true,true,true,true,true] ++ T) [true,true,true,true,true,true,true] true n)
  rw [e9] at g4
  have e10 : (⟨0,[false,false],([true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,true,true,true,true,true] ++ T)))⟩ : Z0) = ⟨0,[false,false],([true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,true,true,true,true,true,true] ++ T)))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [true,true,true,true,true,true,true,true,true] ([true,true,true,true,true,true] ++ T) [true,true,true,true,true,true,true] true n)
  rw [e10] at g4
  have e11 : (⟨0,[false,false],([true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,true,true,true,true,true,true] ++ T)))⟩ : Z0) = ⟨0,[false,false],([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ ([true,true,true,true,true,true,true,true] ++ T)))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [true,true,true,true,true,true,true,true] ([true,true,true,true,true,true,true] ++ T) [true,true,true,true,true,true,true] true n)
  rw [e11] at g4
  rw [show 1+(8*n)+14+(8*n)+19=16*n+34 by omega] at g4
  exact g4
theorem e0zero : run0 table 8 (A (enc .e0)) = some (A (enc (W.e1))) := by rfl
theorem e0carry (n : Nat) : run0 table (16*n+24) ⟨0,[false,false],([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ []))⟩ = some ⟨0,[false,false],([false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ [false,true,true]))⟩ := by
  have h0 : run0 table 1 ⟨0,[false,false],([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ []))⟩ = some ⟨1,[true,true,false],([true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ []))⟩ := by rfl
  have h1 : run0 table (8*n) ⟨1,[true,true,false],([true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ []))⟩ = some ⟨1,([true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),[true,true,true,true,true,true,true]⟩ := by
    exact sweepR table 1 [true] [true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] 8 (fun _ _ => rfl) n [true,false] []
  have g1 := join0 h0 h1
  have h2 : run0 table 13 ⟨1,([true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),[true,true,true,true,true,true,true]⟩ = some ⟨4,([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),[false,true,true]⟩ := by rfl
  have g2 := join0 g1 h2
  have h3 : run0 table (8*n) ⟨4,([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),[false,true,true]⟩ = some ⟨4,[true,true,true,true,true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false,false,false,false] n ++ [false,true,true]))⟩ := by
    exact sweepL table 4 [true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true] [false,false,false,false,false,false,false,false] 8 (fun _ _ => rfl) n [true,false] [false,true,true]
  have g3 := join0 g2 h3
  have h4 : run0 table 10 ⟨4,[true,true,true,true,true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false,false,false,false] n ++ [false,true,true]))⟩ = some ⟨0,[false,false],([false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ [false,true,true]))⟩ := by rfl
  have g4 := join0 g3 h4
  rw [show 1+(8*n)+13+(8*n)+10=16*n+24 by omega] at g4
  exact g4
theorem e1zero : run0 table 8 (A (enc .e1)) = some (A (enc (W.e2))) := by rfl
theorem e1carry (n : Nat) : run0 table (16*n+24) ⟨0,[false,false],([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [false,true,true]))⟩ = some ⟨0,[false,false],([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,true,true]))⟩ := by
  have h0 : run0 table 1 ⟨0,[false,false],([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [false,true,true]))⟩ = some ⟨1,[true,true,false],([true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [false,true,true]))⟩ := by rfl
  have h1 : run0 table (8*n) ⟨1,[true,true,false],([true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [false,true,true]))⟩ = some ⟨1,([true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),[true,true,true,true,true,true,true,false,true,true]⟩ := by
    exact sweepR table 1 [true] [true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] 8 (fun _ _ => rfl) n [true,false] [false,true,true]
  have g1 := join0 h0 h1
  have h2 : run0 table 9 ⟨1,([true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),[true,true,true,true,true,true,true,false,true,true]⟩ = some ⟨2,([true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),[true]⟩ := by rfl
  have g2 := join0 g1 h2
  have h3 : run0 table (8*n) ⟨2,([true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),[true]⟩ = some ⟨2,[true,true,true,true,true,true,true,true,true,true,true,false],([] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true]))⟩ := by
    exact sweepL table 2 [true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] 8 (fun _ _ => rfl) n [true,false] [true]
  have g3 := join0 g2 h3
  have h4 : run0 table 14 ⟨2,[true,true,true,true,true,true,true,true,true,true,true,false],([] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true]))⟩ = some ⟨0,[false,false],([true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true]))⟩ := by rfl
  have g4 := join0 g3 h4
  have e5 : (⟨0,[false,false],([true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true]))⟩ : Z0) = ⟨0,[false,false],([true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,true]))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [true,true,true,true,true,true,true,true,true] [true] [true,true,true,true,true,true,true] true n)
  rw [e5] at g4
  have e6 : (⟨0,[false,false],([true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,true]))⟩ : Z0) = ⟨0,[false,false],([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,true,true]))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [true,true,true,true,true,true,true,true] [true,true] [true,true,true,true,true,true,true] true n)
  rw [e6] at g4
  rw [show 1+(8*n)+9+(8*n)+14=16*n+24 by omega] at g4
  exact g4
theorem e2zero : run0 table 18 (A (enc .e2)) = some (A (enc (W.cons .d3 .e0))) := by rfl
theorem e2carry (n : Nat) : run0 table (16*n+34) ⟨0,[false,false],([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,true,true]))⟩ = some ⟨0,[false,false],([false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ [false,false,false,false,false,false,true,true]))⟩ := by
  have h0 : run0 table 1 ⟨0,[false,false],([true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,true,true]))⟩ = some ⟨1,[true,true,false],([true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,true,true]))⟩ := by rfl
  have h1 : run0 table (8*n) ⟨1,[true,true,false],([true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,true,true]))⟩ = some ⟨1,([true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),[true,true,true,true,true,true,true,true,true,true]⟩ := by
    exact sweepR table 1 [true] [true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] 8 (fun _ _ => rfl) n [true,false] [true,true,true]
  have g1 := join0 h0 h1
  have h2 : run0 table 18 ⟨1,([true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),[true,true,true,true,true,true,true,true,true,true]⟩ = some ⟨4,([true,true,true,true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),[false,true,true]⟩ := by rfl
  have g2 := join0 g1 h2
  have h3 : run0 table (8*n) ⟨4,([true,true,true,true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [true,false])),[false,true,true]⟩ = some ⟨4,[true,true,true,true,true,true,true,true,true,true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false,false,false,false] n ++ [false,true,true]))⟩ := by
    exact sweepL table 4 [true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true] [false,false,false,false,false,false,false,false] 8 (fun _ _ => rfl) n [true,false] [false,true,true]
  have g3 := join0 g2 h3
  have h4 : run0 table 15 ⟨4,[true,true,true,true,true,true,true,true,true,true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false,false,false,false] n ++ [false,true,true]))⟩ = some ⟨0,[false,false],([false,false,false,false,false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ [false,true,true]))⟩ := by rfl
  have g4 := join0 g3 h4
  have e5 : (⟨0,[false,false],([false,false,false,false,false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ [false,true,true]))⟩ : Z0) = ⟨0,[false,false],([false,false,false,false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ [false,false,true,true]))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [false,false,false,false,false,false,false,false,false,false,false,false] [false,true,true] [false,false,false,false,false,false,false] false n)
  rw [e5] at g4
  have e6 : (⟨0,[false,false],([false,false,false,false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ [false,false,true,true]))⟩ : Z0) = ⟨0,[false,false],([false,false,false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ [false,false,false,true,true]))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [false,false,false,false,false,false,false,false,false,false,false] [false,false,true,true] [false,false,false,false,false,false,false] false n)
  rw [e6] at g4
  have e7 : (⟨0,[false,false],([false,false,false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ [false,false,false,true,true]))⟩ : Z0) = ⟨0,[false,false],([false,false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ [false,false,false,false,true,true]))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [false,false,false,false,false,false,false,false,false,false] [false,false,false,true,true] [false,false,false,false,false,false,false] false n)
  rw [e7] at g4
  have e8 : (⟨0,[false,false],([false,false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ [false,false,false,false,true,true]))⟩ : Z0) = ⟨0,[false,false],([false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ [false,false,false,false,false,true,true]))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [false,false,false,false,false,false,false,false,false] [false,false,false,false,true,true] [false,false,false,false,false,false,false] false n)
  rw [e8] at g4
  have e9 : (⟨0,[false,false],([false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ [false,false,false,false,false,true,true]))⟩ : Z0) = ⟨0,[false,false],([false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ [false,false,false,false,false,false,true,true]))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [false,false,false,false,false,false,false,false] [false,false,false,false,false,true,true] [false,false,false,false,false,false,false] false n)
  rw [e9] at g4
  rw [show 1+(8*n)+18+(8*n)+15=16*n+34 by omega] at g4
  exact g4
theorem closedCarry (w : W) (k : Nat) : ∃ t w', 0<t ∧ run0 table t (A (rep (D .d6) k ++ enc w)) = some (A (enc w')) := by
  induction w generalizing k with
  | e0 =>
    cases k with
    | zero => exact ⟨8,W.e1,by omega,e0zero⟩
    | succ k =>
      refine ⟨16*k+24,pre .d0 (k+1) (W.e1),by omega,?_⟩
      simpa only [enc_pre,enc,rep,D,List.append_assoc,List.nil_append,List.append_nil,A] using e0carry k
  | e1 =>
    cases k with
    | zero => exact ⟨8,W.e2,by omega,e1zero⟩
    | succ k =>
      refine ⟨16*k+24,pre .d6 (k+1) (W.e2),by omega,?_⟩
      simpa only [enc_pre,enc,rep,D,List.append_assoc,List.nil_append,List.append_nil,A] using e1carry k
  | e2 =>
    cases k with
    | zero => exact ⟨18,W.cons .d3 .e0,by omega,e2zero⟩
    | succ k =>
      refine ⟨16*k+34,pre .d0 (k+1) (W.cons .d3 .e0),by omega,?_⟩
      simpa only [enc_pre,enc,rep,D,List.append_assoc,List.nil_append,List.append_nil,A] using e2carry k
  | cons d w ih =>
    cases d
    · cases k with
      | zero => exact ⟨8,.cons .d1 w,by omega,d0zero (enc w)⟩
      | succ k =>
        refine ⟨16*k+24,pre .d0 (k+1) (.cons .d1 w),by omega,?_⟩
        simpa only [enc_pre,enc,rep,D,List.append_assoc,List.nil_append,List.append_nil,A] using d0carry k (enc w)
    · cases k with
      | zero => exact ⟨8,.cons .d2 w,by omega,d1zero (enc w)⟩
      | succ k =>
        refine ⟨16*k+24,pre .d6 (k+1) (.cons .d2 w),by omega,?_⟩
        simpa only [enc_pre,enc,rep,D,List.append_assoc,List.nil_append,List.append_nil,A] using d1carry k (enc w)
    · cases k with
      | zero => exact ⟨18,.cons .d3 w,by omega,d2zero (enc w)⟩
      | succ k =>
        refine ⟨16*k+34,pre .d0 (k+1) (.cons .d3 w),by omega,?_⟩
        simpa only [enc_pre,enc,rep,D,List.append_assoc,List.nil_append,List.append_nil,A] using d2carry k (enc w)
    · cases k with
      | zero => exact ⟨8,.cons .d4 w,by omega,d3zero (enc w)⟩
      | succ k =>
        refine ⟨16*k+24,pre .d0 (k+1) (.cons .d4 w),by omega,?_⟩
        simpa only [enc_pre,enc,rep,D,List.append_assoc,List.nil_append,List.append_nil,A] using d3carry k (enc w)
    · cases k with
      | zero => exact ⟨8,.cons .d5 w,by omega,d4zero (enc w)⟩
      | succ k =>
        refine ⟨16*k+24,pre .d6 (k+1) (.cons .d5 w),by omega,?_⟩
        simpa only [enc_pre,enc,rep,D,List.append_assoc,List.nil_append,List.append_nil,A] using d4carry k (enc w)
    · cases k with
      | zero => exact ⟨18,.cons .d6 w,by omega,d5zero (enc w)⟩
      | succ k =>
        refine ⟨16*k+34,pre .d6 (k+1) (.cons .d6 w),by omega,?_⟩
        simpa only [enc_pre,enc,rep,D,List.append_assoc,List.nil_append,List.append_nil,A] using d5carry k (enc w)
    · obtain ⟨t,w',ht,H⟩ := ih (k+1)
      refine ⟨t,w',ht,?_⟩
      simpa only [enc,rep,← rep_snoc (D .d6) k,List.append_assoc] using H
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  apply neverOfSection table W (fun w => A (enc w)) .e1 8 (by rfl) _ m hm
  intro w
  simpa only [rep,List.nil_append] using closedCarry w 0
#print axioms never
end BB6.Agent8Raw54.RA.M46
