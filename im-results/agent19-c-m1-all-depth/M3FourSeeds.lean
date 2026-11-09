import TowerAllOdd
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace BB6.Agent19M3Four
open BB6.Agent19OddTower
open BB6.Agent4Four
open BB6.Agent46

def r : Nat → Nat
  | 0 => 7
  | 1 => 9
  | _ => 11

def s (c q : Nat) : Nat :=
  match c with
  | 0 => 57+512*q
  | 1 => 1976+2048*q
  | _ => 1463+8192*q

def t (c q : Nat) : Nat :=
  match c with
  | 0 => 28+255*q
  | 1 => 244+255*q
  | _ => 43+255*q

private theorem base (c q : Nat) :
    K 3 (r c) (t c q) 0+J 3 (r c) (s c q) (t c q) 0+3*3+5 =
      (2:Nat)^(2*3+2)*(J 3 (r c) (s c q) (t c q) 0+3) := by
  cases c with
  | zero =>
      simp [K,J,R,S,r,s,t,bandY]
      omega
  | succ c =>
      cases c with
      | zero =>
          simp [K,J,R,S,r,s,t,bandY]
          omega
      | succ c =>
          simp [K,J,R,S,r,s,t,bandY]
          omega

theorem extra_three_stopping (c q h : Nat) :
    K 3 (r c) (t c q) h+J 3 (r c) (s c q) (t c q) h+3*3+5 =
      (2:Nat)^(2*3+2)*(J 3 (r c) (s c q) (t c q) h+3) := by
  apply tower_stopping 3 (r c) (s c q) (t c q) h
  · cases c with
    | zero => decide
    | succ c => cases c with
      | zero => decide
      | succ c => simp [r]
  · cases c with
    | zero => decide
    | succ c => cases c with
      | zero => decide
      | succ c => simp [r]
  · exact base c q

theorem extra_three_blank_unreachable (c q h time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (2*J 3 (r c) (s c q) (t c q) h+3,
        K 3 (r c) (t c q) h) := by
  exact tower_blank_excluded _ _ _ _ _ _

#print axioms extra_three_stopping
#print axioms extra_three_blank_unreachable
end BB6.Agent19M3Four
