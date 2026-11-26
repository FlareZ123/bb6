import SweepPumping
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.RACounter
open BB6Coverage BB6Coverage.Agent31Pump

def zero : List Bool := [false,false,false]
def one : List Bool := [true,true,true]
def mark : List Bool := [false,true,true]
def A (r : List Bool) : Z0 := ⟨0,[false,false],r⟩
def enc : List Bool → List Bool
  | [] => []
  | false::w => zero ++ enc w
  | true::w => one ++ enc w
def bump : List Bool → List Bool
  | [] => [true]
  | false::w => true::w
  | true::w => false::bump w
def carryCost (a b c d : Nat) : Nat → List Bool → Nat
  | k, [] => c*k+d
  | k, false::_ => a*k+b
  | k, true::w => carryCost a b c d (k+1) w

theorem carry (p : PartialMachine) (a b c d : Nat)
    (stop : ∀ k T, run0 p (a*k+b) (A (mark ++ (rep one k ++ (zero ++ T)))) =
      some (A (zero ++ (rep zero k ++ (one ++ T)))))
    (overflow : ∀ k, run0 p (c*k+d) (A (mark ++ rep one k)) =
      some (A (zero ++ (rep zero k ++ one))))
    (w : List Bool) (k : Nat) :
    run0 p (carryCost a b c d k w) (A (mark ++ (rep one k ++ enc w))) =
      some (A (zero ++ (rep zero k ++ enc (bump w)))) := by
  induction w generalizing k with
  | nil => simpa only [enc,bump,carryCost,List.append_nil] using overflow k
  | cons h w ih =>
    cases h
    · simpa only [enc,bump,carryCost] using stop k (enc w)
    · have H := ih (k+1)
      simpa only [enc,bump,carryCost,rep,← rep_snoc one k,← rep_snoc zero k,List.append_assoc] using H

def words : Nat → List Bool | 0 => [] | n+1 => bump (words n)
def family (n : Nat) : Z0 := A (mark ++ enc (words n))
def cost (a b c d : Nat) (n : Nat) : Nat := carryCost a b c d 0 (words n)+8

theorem never (p : PartialMachine) (a b c d : Nat)
    (entry : run0 p 8 ⟨0,[],[]⟩ = some (A mark))
    (inc : ∀ T, run0 p 8 (A (zero ++ T)) = some (A (mark ++ T)))
    (stop : ∀ k T, run0 p (a*k+b) (A (mark ++ (rep one k ++ (zero ++ T)))) =
      some (A (zero ++ (rep zero k ++ (one ++ T)))))
    (overflow : ∀ k, run0 p (c*k+d) (A (mark ++ rep one k)) =
      some (A (zero ++ (rep zero k ++ one))))
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply never_of_growth p family 8 (cost a b c d) entry (by intro n; unfold cost; omega) _ m hm
  intro n
  have H := join0 (carry p a b c d stop overflow (words n) 0) (inc (enc (bump (words n))))
  simpa only [family,cost,rep,List.nil_append,words] using H
#print axioms never
end BB6.Agent8Raw54.RACounter
