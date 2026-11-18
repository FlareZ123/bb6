import Lean.Elab.Tactic.Omega
set_option maxRecDepth 8192

namespace BB6.Agent9RestartWallTelescoping

/--
A restart segment is represented by its successive edge costs. The scalar
source recurrence is
  x + 14*P = 2^e*x' + 2*(c+3+s),
where x=d-1 and s is cost relative to the restart state. This file proves
the arbitrary-start telescoping identity for that recurrence. It does not
by itself prove that every CountCone suffix instantiates RestartWalk; that
source-history extraction is a separate obligation.
-/
def weightS (s : Nat) : List Nat → Nat
  | [] => 0
  | e :: es => 2^s + weightS (s+e) es

def weightT (s : Nat) : List Nat → Nat
  | [] => 0
  | e :: es => s * 2^s + weightT (s+e) es

def totalCost : List Nat → Nat
  | [] => 0
  | e :: es => e + totalCost es

inductive RestartWalk (P c : Nat) : Nat → Nat → List Nat → Nat → Prop
  | nil (x s : Nat) : RestartWalk P c x s [] x
  | cons {x s e : Nat} {es : List Nat} {x' xend : Nat}
      (hstep : x + 14*P = 2^e*x' + 2*(c+3+s))
      (hrest : RestartWalk P c x' (s+e) es xend) :
      RestartWalk P c x s (e::es) xend

theorem restart_walk_telescopes
    (P c x s xend : Nat) (es : List Nat)
    (h : RestartWalk P c x s es xend) :
    2^s*x + 14*P*weightS s es =
      2^(s+totalCost es)*xend + 2*((c+3)*weightS s es + weightT s es) := by
  induction h with
  | nil x s => simp [weightS, weightT, totalCost]
  | @cons x s e es x' xend hstep hrest ih =>
      simp only [weightS, weightT, totalCost]
      have hpow : 2^s * 2^e = 2^(s+e) := by rw [← Nat.pow_add]
      have hstepScaled :
          2^s*x + 14*P*2^s = 2^(s+e)*x' + 2*((c+3)*2^s+s*2^s) := by
        calc
          2^s*x + 14*P*2^s = 2^s*(x+14*P) := by
            rw [Nat.mul_add]
            simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          _ = 2^s*(2^e*x'+2*(c+3+s)) := by rw [hstep]
          _ = 2^s*(2^e*x') + 2^s*(2*(c+3+s)) := by rw [Nat.mul_add]
          _ = (2^s*2^e)*x' + 2*(2^s*(c+3+s)) := by
            simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          _ = 2^(s+e)*x' + 2*(2^s*(c+3+s)) := by rw [hpow]
          _ = 2^(s+e)*x' + 2*((c+3)*2^s+s*2^s) := by
            congr 1
            rw [Nat.mul_add]
            simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      calc
        2^s*x + 14*P*(2^s + weightS (s+e) es)
            = (2^s*x + 14*P*2^s) + 14*P*weightS (s+e) es := by
                rw [Nat.mul_add]
                omega
        _ = (2^(s+e)*x' + 2*((c+3)*2^s+s*2^s)) + 14*P*weightS (s+e) es := by
              rw [hstepScaled]
        _ = (2^(s+e)*x' + 14*P*weightS (s+e) es) +
              2*((c+3)*2^s+s*2^s) := by omega
        _ = (2^(s+e+totalCost es)*xend +
              2*((c+3)*weightS (s+e) es + weightT (s+e) es)) +
              2*((c+3)*2^s+s*2^s) := by rw [ih]
        _ = 2^(s+(e+totalCost es))*xend +
              2*((c+3)*(2^s+weightS (s+e) es) +
                (s*2^s+weightT (s+e) es)) := by
              simp [Nat.pow_add, Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
                Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem restart_wall_identity_additive
    (P c xhalf xend : Nat) (es : List Nat)
    (hwalk : RestartWalk P c (2*xhalf) 0 es xend)
    (hwall : xend = 2*P + 2*totalCost es + 2*c + 6) :
    xhalf + P*(7*weightS 0 es) =
      P*2^(totalCost es) +
        2^(totalCost es)*(totalCost es+c+3) +
        (c+3)*weightS 0 es + weightT 0 es := by
  have htel := restart_walk_telescopes P c (2*xhalf) 0 xend es hwalk
  simp only [Nat.pow_zero, Nat.zero_add] at htel
  rw [hwall] at htel
  have hterm :
      2^(totalCost es)*(2*P+2*totalCost es+2*c+6) =
        2*(P*2^(totalCost es) +
          2^(totalCost es)*(totalCost es+c+3)) := by
    have hlin : 2*P+2*totalCost es+2*c+6 =
        2*(P+totalCost es+c+3) := by omega
    calc
      2^(totalCost es)*(2*P+2*totalCost es+2*c+6)
          = 2^(totalCost es)*(2*(P+totalCost es+c+3)) := by rw [hlin]
      _ = 2*(2^(totalCost es)*(P+totalCost es+c+3)) := by ac_rfl
      _ = 2*(2^(totalCost es)*P +
            2^(totalCost es)*(totalCost es+c+3)) := by
          have hlin2 : P+totalCost es+c+3 = P+(totalCost es+c+3) := by omega
          rw [hlin2, Nat.mul_add]
      _ = 2*(P*2^(totalCost es) +
            2^(totalCost es)*(totalCost es+c+3)) := by ac_rfl
  have hdouble :
      2*(xhalf + P*(7*weightS 0 es)) =
      2*(P*2^(totalCost es) +
        2^(totalCost es)*(totalCost es+c+3) +
        (c+3)*weightS 0 es + weightT 0 es) := by
    calc
      2*(xhalf + P*(7*weightS 0 es)) =
          2*xhalf + 14*P*weightS 0 es := by
            rw [Nat.mul_add]
            ac_rfl
      _ = 2^(totalCost es)*(2*P+2*totalCost es+2*c+6) +
            2*((c+3)*weightS 0 es+weightT 0 es) := by
          simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using htel
      _ = 2*(P*2^(totalCost es) +
            2^(totalCost es)*(totalCost es+c+3)) +
            2*((c+3)*weightS 0 es+weightT 0 es) := by rw [hterm]
      _ = 2*(P*2^(totalCost es) +
            2^(totalCost es)*(totalCost es+c+3) +
            (c+3)*weightS 0 es + weightT 0 es) := by
          simp [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
            Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hdouble

theorem restart_wall_nonnegative_N
    (P L S T c xhalf : Nat)
    (hid : xhalf + P*(7*S) =
      P*2^L + 2^L*(L+c+3) + (c+3)*S + T)
    (hxhalf : xhalf < P) : 2^L ≤ 7*S := by
  by_cases hlt : 7*S < 2^L
  · have hlt' : 7*S+1 ≤ 2^L := by omega
    have hmul : P*(7*S+1) ≤ P*2^L := Nat.mul_le_mul_left P hlt'
    have hsplit : P*(7*S+1) = P*(7*S)+P := by simp [Nat.mul_add]
    have hleft : xhalf + P*(7*S) < P*(7*S+1) := by rw [hsplit]; omega
    have hpow : 0 < 2^L := Nat.pow_pos (by decide)
    have hR : 0 < 2^L*(L+c+3)+(c+3)*S+T := by omega
    have hright : P*2^L < P*2^L + (2^L*(L+c+3)+(c+3)*S+T) :=
      Nat.lt_add_of_pos_right hR
    omega
  · omega

#print axioms restart_walk_telescopes
#print axioms restart_wall_identity_additive
#print axioms restart_wall_nonnegative_N

end BB6.Agent9RestartWallTelescoping
