import BusyBeaver.BB6.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

/-!
Source-authentic cryptid #623 ternary drain arithmetic. All theorem statements
and definitions below refer to unmodified Google DeepMind Cryptids declarations,
not the standalone duplicated arithmetic. Source revision pinned by the manual
agent49-623-parity-source workflow, c86f15861709b76042998c5211c7b2f83991621b.
-/

namespace BB6.Agent8InverseSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

theorem evalA_nine (x m : Nat) :
    evalA 3 (9*x+7) m = some (3,x,m+6*x+7) := by
  have h1 : (9*x+7)%3 = 1 := by omega
  have h2 : (9*x+7)/3 = 3*x+2 := by omega
  have h3 : (3*x+2)%3 = 2 := by omega
  have h4 : (3*x+2)/3 = x := by omega
  rw [evalA]
  simp [h1,h2,evalA,h3,h4]
  omega

theorem drainB_nine (x d : Nat) :
    drainB 3 (9*x+8) d = drainB 3 x (d+24*x+26) := by
  rw [drainB]
  have hn : 9*x+8 ≠ 0 := by omega
  have hp : 9*x+8-1 = 9*x+7 := by omega
  have hlt : x < 9*x+8 := by omega
  simp only [if_neg hn, hp, evalA_nine, Option.bind_some, if_pos hlt]
  congr 1
  omega

theorem evalA_four (m : Nat) :
    evalA 3 4 m = some (0,0,m+10) := by
  simp [evalA, Nat.add_assoc]

theorem evalA_sixteen (m : Nat) :
    evalA 3 16 m = some (3,1,m+13) := by
  simp [evalA, Nat.add_assoc]

theorem evalA_zero (m : Nat) :
    evalA 3 0 m = some (2,0,m+2) := by
  simp [evalA]

def oddPulse : Nat → Nat
  | 0 => 5
  | n+1 => 9 * oddPulse n + 8

def oddGain : Nat → Nat
  | 0 => 23
  | n+1 => 24 * oddPulse n + 26 + oddGain n

def evenPulse : Nat → Nat
  | 0 => 17
  | n+1 => 9 * evenPulse n + 8

def evenGain : Nat → Nat
  | 0 => 57
  | n+1 => 24 * evenPulse n + 26 + evenGain n

theorem oddPulse_run (n d : Nat) :
    drainB 3 (oddPulse n) d = some (.D 0 (d + oddGain n)) := by
  induction n generalizing d with
  | zero =>
    change drainB 3 5 d = some (.D 0 (d + 23))
    rw [drainB]
    simp only [if_neg (by decide : (5:Nat) ≠ 0), Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    rw [evalA_four]
    simp only [Option.bind_some, if_pos (by decide : (0:Nat) < 5)]
    rw [drainB]
    simp only [if_pos (by decide : (0:Nat) = 0)]
    congr 1
  | succ n ih =>
    change drainB 3 (9 * oddPulse n + 8) d =
      some (.D 0 (d + (24 * oddPulse n + 26 + oddGain n)))
    rw [drainB_nine, ih]
    simp only [Nat.add_assoc]

theorem evenPulse_run (n d : Nat) :
    drainB 3 (evenPulse n) d = some (.D 2 (d + evenGain n)) := by
  induction n generalizing d with
  | zero =>
    change drainB 3 17 d = some (.D 2 (d + 57))
    rw [drainB]
    simp only [if_neg (by decide : (17:Nat) ≠ 0), Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    rw [evalA_sixteen]
    simp only [Option.bind_some, if_pos (by decide : 1 < 17)]
    rw [drainB]
    simp only [if_neg (by decide : (1:Nat) ≠ 0), Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    rw [evalA_zero]
    simp only [Option.bind_some, if_pos (by decide : (0:Nat) < 1)]
    rw [drainB]
    simp only [if_pos (by decide : (0:Nat) = 0)]
    congr 1
  | succ n ih =>
    change drainB 3 (9 * evenPulse n + 8) d =
      some (.D 2 (d + (24 * evenPulse n + 26 + evenGain n)))
    rw [drainB_nine, ih]
    simp only [Nat.add_assoc]

theorem oddPulse_closed (n : Nat) :
    oddPulse n + 1 = 6 * 9 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [oddPulse, Nat.pow_succ]
    omega

theorem evenPulse_closed (n : Nat) :
    evenPulse n + 1 = 18 * 9 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [evenPulse, Nat.pow_succ]
    omega

theorem oddGain_closed (n : Nat) :
    oddGain n = 18 * 9 ^ n + 2*n + 5 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h := oddPulse_closed n
    simp only [oddGain, Nat.pow_succ]
    omega

theorem evenGain_closed (n : Nat) :
    evenGain n = 54 * 9 ^ n + 2*n + 3 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h := evenPulse_closed n
    simp only [evenGain, Nat.pow_succ]
    omega

theorem odd_pulse_exact (n d : Nat) :
    drainB 3 (oddPulse n) d =
      some (.D 0 (d + 18*9^n + 2*n + 5)) := by
  rw [oddPulse_run, oddGain_closed]
  simp only [Nat.add_assoc]

theorem even_pulse_exact (n d : Nat) :
    drainB 3 (evenPulse n) d =
      some (.D 2 (d + 54*9^n + 2*n + 3)) := by
  rw [evenPulse_run, evenGain_closed]
  simp only [Nat.add_assoc]

#print axioms odd_pulse_exact
#print axioms even_pulse_exact
#print axioms oddPulse_run
#print axioms evenPulse_run
#print axioms evalA_nine
#print axioms drainB_nine

end BB6.Agent8InverseSource
