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

theorem restart_aggregate_step
    (P c x0 x x' L S T e : Nat)
    (hInv : x0 + 14*P*S = 2^L*x + 2*((c+3)*S+T))
    (hStep : x + 14*P = 2^e*x' + 2*(c+3+L)) :
    x0 + 14*P*(S+2^L) =
      2^(L+e)*x' + 2*((c+3)*(S+2^L) + (T+L*2^L)) := by
  have hpow : 2^L*2^e=2^(L+e) := by rw [← Nat.pow_add]
  calc
    x0 + 14*P*(S+2^L) = x0+14*P*S+14*P*2^L := by
      rw [Nat.mul_add]
      omega
    _ = 2^L*x + 2*((c+3)*S+T) + 14*P*2^L := by rw [hInv]
    _ = 2^L*x + 2^L*(14*P) + 2*((c+3)*S+T) := by ac_rfl
    _ = 2^L*(x+14*P) + 2*((c+3)*S+T) := by rw [← Nat.mul_add]
    _ = 2^L*(2^e*x'+2*(c+3+L)) + 2*((c+3)*S+T) := by rw [hStep]
    _ = 2^L*(2^e*x') + 2^L*(2*(c+3+L)) + 2*((c+3)*S+T) := by rw [Nat.mul_add]
    _ = (2^L*2^e)*x' + 2^L*(2*(c+3+L)) + 2*((c+3)*S+T) := by
      rw [← Nat.mul_assoc]
    _ = 2^(L+e)*x' + 2^L*(2*(c+3+L)) + 2*((c+3)*S+T) := by rw [hpow]
    _ = 2^(L+e)*x' + 2*((c+3+L)*2^L) + 2*((c+3)*S+T) := by ac_rfl
    _ = 2^(L+e)*x' + 2*((c+3)*(S+2^L) + (T+L*2^L)) := by
      simp [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem restart_wall_identity_from_invariant
    (P c xhalf L S T : Nat)
    (hInv : 2*xhalf + 14*P*S =
      2^L*(2*P+2*L+2*c+6) + 2*((c+3)*S+T)) :
    xhalf + P*(7*S) =
      P*2^L + 2^L*(L+c+3) + (c+3)*S + T := by
  have hterm :
      2^L*(2*P+2*L+2*c+6) = 2*(P*2^L+2^L*(L+c+3)) := by
    have hlin : 2*P+2*L+2*c+6=2*(P+L+c+3) := by omega
    calc
      _ = 2^L*(2*(P+L+c+3)) := by rw [hlin]
      _ = 2*(2^L*(P+L+c+3)) := by ac_rfl
      _ = 2*(2^L*P+2^L*(L+c+3)) := by
        have hlin2 : P+L+c+3=P+(L+c+3) := by omega
        rw [hlin2, Nat.mul_add]
      _ = 2*(P*2^L+2^L*(L+c+3)) := by ac_rfl
  have hdouble :
      2*(xhalf+P*(7*S)) =
      2*(P*2^L+2^L*(L+c+3)+(c+3)*S+T) := by
    calc
      _ = 2*xhalf+14*P*S := by rw [Nat.mul_add]; ac_rfl
      _ = 2^L*(2*P+2*L+2*c+6)+2*((c+3)*S+T) := hInv
      _ = 2*(P*2^L+2^L*(L+c+3))+2*((c+3)*S+T) := by rw [hterm]
      _ = 2*(P*2^L+2^L*(L+c+3)+(c+3)*S+T) := by
        simp [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
          Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0<2) hdouble

theorem source_edge_recurrence
    (P n b d m t c : Nat)
    (hMass : b+d+2*m+2*n+13=14*P)
    (hInv2 : 2*d+b+6=2^(t+1)*(c+3))
    (hd : 1≤d) :
    d-1+14*P = 2^(t+1)*(c+3)+2*(m+n+3) := by
  omega

theorem source_wall_endpoint
    (P n b d m : Nat)
    (hMass : b+d+2*m+2*n+13=14*P)
    (hWall : b+4*m+4*n+20=12*P) :
    d=2*P+2*m+2*n+7 := by
  omega

theorem restart_half_defect_lt
    (P n b d m F : Nat)
    (hMass : b+d+2*m+2*n+13=14*P)
    (hF : b+2*m+2*n+8=12*P+F)
    (hFpos : 0<F)
    (hdOdd : d%2=1) :
    ∃ xhalf, d-1=2*xhalf ∧ xhalf<P := by
  have hcore : d-1+F+6=2*P := by omega
  refine ⟨(d-1)/2, ?_, ?_⟩
  · omega
  · omega

theorem restart_half_defect_lt_of_int
    (P n b d m : Nat)
    (hP : P=2^n)
    (hMass : b+d+2*m+2*n+13=14*P)
    (hFpos : 0 < (b:Int)+2*(m:Int)+2*(n:Int)+8-12*(2:Int)^n)
    (hdOdd : d%2=1) :
    ∃ xhalf, d-1=2*xhalf ∧ xhalf<P := by
  have hMassI : (b:Int)+(d:Int)+2*(m:Int)+2*(n:Int)+13=14*(P:Int) := by
    exact_mod_cast hMass
  have hPI : (P:Int)=(2:Int)^n := by exact_mod_cast hP
  have hFposI : 0 < (b:Int)+2*(m:Int)+2*(n:Int)+8-12*(P:Int) := by
    simpa [hPI] using hFpos
  have hcoreI : (d:Int)-1 < 2*(P:Int) := by omega
  have hd1 : 1≤d := by omega
  have hcore : d-1 < 2*P := by omega
  refine ⟨(d-1)/2, ?_, ?_⟩
  · omega
  · omega

#print axioms restart_half_defect_lt_of_int
#print axioms restart_half_defect_lt
#print axioms source_edge_recurrence
#print axioms source_wall_endpoint
#print axioms restart_aggregate_step
#print axioms restart_wall_identity_from_invariant
#print axioms restart_walk_telescopes
#print axioms restart_wall_identity_additive
#print axioms restart_wall_nonnegative_N

end BB6.Agent9RestartWallTelescoping
