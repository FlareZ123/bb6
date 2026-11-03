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


/-- Source-matched evaluator residual bound (same argument as Agent49). -/
theorem evalA_b_le_k (a : Nat) :
    ∀ k m aa bb dd : Nat, evalA a k m = some (aa,bb,dd) → bb ≤ k := by
  induction a with
  | zero =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases h2 : k%3 = 2
    · simp [h2] at h
      cases h
      omega
    · by_cases h0 : k%3 = 0
      · simp [h2,h0] at h
      · simp [h2,h0] at h
        cases h
        omega
  | succ a ih =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases h2 : k%3 = 2
    · simp [h2] at h
      cases h
      omega
    · by_cases h0 : k%3 = 0
      · simp [h2,h0] at h
        cases h
        omega
      · simp [h2,h0] at h
        have ht := ih (k/3) (m+2*(k/3)+3) aa bb dd h
        omega

theorem evalA_nine_minus_one (a b m : Nat) (hb : 0 < b) :
    evalA a (9*b-1) m = some (a+1,3*b-1,m) := by
  have hm : (9*b-1)%3 = 2 := by omega
  have hd : (9*b-1)/3 = 3*b-1 := by omega
  rw [evalA]
  simp [hm,hd]

theorem evalA_three_minus_two (a b m : Nat) (hb : 0 < b) :
    evalA (a+1) (3*b-2) m = evalA a (b-1) (m+2*(b-1)+3) := by
  have hm : (3*b-2)%3 = 1 := by omega
  have hz : (3*b-2)%3 ≠ 0 := by omega
  have hd : (3*b-2)/3 = b-1 := by omega
  rw [evalA]
  simp [hm,hz,hd]

/-- Exact two-digit pumping for ALL positive block counts, including halting. -/
theorem drainB_scale_nine (a b d : Nat) (hb : 0 < b) :
    drainB a (9*b) d = drainB a b (d+24*b+2) := by
  have h9 : 9*b ≠ 0 := by omega
  have h3 : 3*b-1 ≠ 0 := by omega
  have hfirst : 3*b-1 < 9*b := by omega
  have h3sub : (3*b-1)-1=3*b-2 := by omega
  have hm9 : d+2*(9*b)+3=d+18*b+3 := by omega
  have hm3 : (d+18*b+3)+2*(3*b-1)+3=d+24*b+4 := by omega
  have hm : (d+24*b+4)+2*(b-1)+3=(d+24*b+2)+2*b+3 := by omega
  rw [drainB]
  simp only [if_neg h9, hm9, evalA_nine_minus_one a b (d+18*b+3) hb,
    Option.bind_some, if_pos hfirst]
  rw [drainB]
  simp only [if_neg h3, h3sub, hm3, evalA_three_minus_two a b (d+24*b+4) hb, hm]
  have hright : drainB a b (d+24*b+2) =
      (evalA a (b-1) ((d+24*b+2)+2*b+3)).bind (fun p =>
         if p.2.1 < b then drainB p.1 p.2.1 p.2.2 else none) := by
    rw [drainB]
    simp only [if_neg (by omega : b ≠ 0)]
  rw [hright]
  cases he : evalA a (b-1) ((d+24*b+2)+2*b+3) with
  | none => simp [he]
  | some p =>
    rcases p with ⟨aa,bb,dd⟩
    have small := evalA_b_le_k a (b-1) ((d+24*b+2)+2*b+3) aa bb dd he
    have hbb : bb < b := by omega
    have hbb3 : bb < 3*b-1 := by omega
    simp only [he, Option.bind_some, if_pos hbb, if_pos hbb3]

#print axioms drainB_scale_nine

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


/-! Source-authentic infinite four-way #623 high-level collisions. -/

theorem c_e1 (q : Nat) :
    evalA 2 (486*q+41) (972*q+89) = some (3, 162*q+13, 972*q+89) := by
  rw [evalA]
  simp only [if_pos (by omega : (486*q+41)%3 = 2)]
  simp only [Option.some.injEq, Prod.mk.injEq, true_and, and_true]
  omega

theorem c_e2 (q : Nat) :
    evalA 3 (162*q+12) (1296*q+118) = some (2,54*q+4,1296*q+120) := by
  rw [evalA]
  simp only [if_neg (by omega : (162*q+12)%3 ≠ 2),
    if_neg (by omega : (3:Nat) ≠ 0), if_pos (by omega : (162*q+12)%3=0)]
  simp only [Option.some.injEq, Prod.mk.injEq, true_and, and_true]
  omega

theorem c_e3 (q : Nat) :
    evalA 2 (54*q+3) (1404*q+131) = some (1,18*q+1,1404*q+133) := by
  rw [evalA]
  simp only [if_neg (by omega : (54*q+3)%3 ≠ 2),
    if_neg (by omega : (2:Nat) ≠ 0), if_pos (by omega : (54*q+3)%3=0)]
  simp only [Option.some.injEq, Prod.mk.injEq, true_and, and_true]
  omega

theorem c_e4 (q : Nat) :
    evalA 1 (18*q) (1440*q+138) = some (0,6*q,1440*q+140) := by
  rw [evalA]
  simp only [if_neg (by omega : (18*q)%3 ≠ 2),
    if_neg (by omega : (1:Nat) ≠ 0), if_pos (by omega : (18*q)%3=0)]
  simp only [Option.some.injEq, Prod.mk.injEq, true_and, and_true]
  omega

theorem c_step (q : Nat) :
  highLevelNext (.D (486*q+44) (486*q+40)) = drainB 0 (6*q) (1440*q+140) := by
  simp only [highLevelNext]
  have h0 : 486*q+44 ≠ 0 := by omega
  have hodd : (486*q+40)%2 ≠ 1 := by omega
  have hfar : (486*q+44) ≥ (486*q+40)+3 := by omega
  simp only [if_neg h0, if_neg (by omega : ¬ ((486*q+40)%2=1 ∧ 486*q+44 ≥ (486*q+40)+5)), if_pos (And.intro (by omega : (486*q+40)%2=0) hfar)]
  have harg : 486*q+44-(486*q+40)-2=2 := by omega
  have harg2 : 486*q+40+2=486*q+42 := by omega
  rw [harg,harg2]
  rw [drainB]
  simp only [if_neg (by omega : 486*q+42 ≠ 0)]
  have hm1 : 486*q+42-1 = 486*q+41 := by omega
  have hm2 : 2+2*(486*q+42)+3 = 972*q+89 := by omega
  rw [hm1,hm2,c_e1]
  simp only [Option.bind_some, if_pos (by omega : 162*q+13 < 486*q+42)]
  rw [drainB]
  simp only [if_neg (by omega : 162*q+13 ≠ 0)]
  have hm3 : 162*q+13-1=162*q+12 := by omega
  have hm4 : (972*q+89)+2*(162*q+13)+3=1296*q+118 := by omega
  rw [hm3,hm4,c_e2]
  simp only [Option.bind_some, if_pos (by omega : 54*q+4 < 162*q+13)]
  rw [drainB]
  simp only [if_neg (by omega : 54*q+4 ≠ 0)]
  have hm5 : 54*q+4-1=54*q+3 := by omega
  have hm6 : (1296*q+120)+2*(54*q+4)+3=1404*q+131 := by omega
  rw [hm5,hm6,c_e3]
  simp only [Option.bind_some, if_pos (by omega : 18*q+1 < 54*q+4)]
  rw [drainB]
  simp only [if_neg (by omega : 18*q+1 ≠ 0)]
  have hm7 : 18*q+1-1=18*q := by omega
  have hm8 : (1404*q+133)+2*(18*q+1)+3=1440*q+138 := by omega
  rw [hm7,hm8,c_e4]
  simp only [Option.bind_some, if_pos (by omega : 6*q < 18*q+1)]

theorem d_eval (q : Nat) :
    evalA 2 (162*q+13) (1296*q+124) = some (0, 6*q, 1440*q+140) := by
  rw [evalA]
  simp only [if_neg (by omega : (162*q+13)%3 ≠ 2),
    if_neg (by omega : (2:Nat) ≠ 0),
    if_neg (by omega : (162*q+13)%3 ≠ 0)]
  have hm1 : (162*q+13)/3=54*q+4 := by omega
  have hm2 : 2-1 = 1 := by omega
  have hm3 : 1296*q+124+2*(54*q+4)+3 = 1404*q+135 := by omega
  rw [hm1, hm2, hm3]
  rw [evalA]
  simp only [if_neg (by omega : (54*q+4)%3 ≠ 2),
    if_neg (by omega : (1:Nat) ≠ 0),
    if_neg (by omega : (54*q+4)%3 ≠ 0)]
  have hn1 : (54*q+4)/3=18*q+1 := by omega
  have hn2 : 1-1=0 := by omega
  have hn3 : 1404*q+135+2*(18*q+1)+3 = 1440*q+140 := by omega
  rw [hn1, hn2, hn3]
  rw [evalA]
  simp only [if_neg (by omega : (18*q+1)%3 ≠ 2), if_pos (by decide : (0:Nat)=0),
    if_neg (by omega : (18*q+1)%3 ≠ 0)]
  simp only [if_true, Option.some.injEq, Prod.mk.injEq, true_and, and_true]
  omega

theorem d_step (q : Nat) :
  highLevelNext (.D (486*q+44) (486*q+44)) = drainB 0 (6*q) (1440*q+140) := by
  simp only [highLevelNext]
  have h0 : 486*q+44 ≠ 0 := by omega
  have h1 : ¬ ((486*q+44)%2=1 ∧ 486*q+44 ≥ (486*q+44)+5) := by omega
  have h2 : ¬ ((486*q+44)%2=0 ∧ 486*q+44 ≥ (486*q+44)+3) := by omega
  have h3 : (486*q+44)%2 ≠ 1 := by omega
  have h4 : 486*q+44 ≠ (486*q+44)+2 := by omega
  have h5 : (486*q+44)%2 ≠ 1 := by omega
  simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]
  have he : evalA 1 (486*q+44) (972*q+93) = some (2, 162*q+14, 972*q+93) := by
    rw [evalA]
    simp only [if_pos (by omega : (486*q+44)%3=2)]
    simp only [Option.some.injEq, Prod.mk.injEq, true_and, and_true]
    omega
  have harg1 : (486*q+44)+1-(486*q+44)=1 := by omega
  have harg2 : 2*(486*q+44)+5=972*q+93 := by omega
  rw [harg1,harg2,he]
  simp only [Option.bind_some]
  rw [drainB]
  simp only [if_neg (by omega : 162*q+14 ≠ 0)]
  have hm1 : 162*q+14-1=162*q+13 := by omega
  have hm2 : 972*q+93+2*(162*q+14)+3=1296*q+124 := by omega
  rw [hm1,hm2,d_eval]
  simp only [Option.bind_some, if_pos (by omega : 6*q < 162*q+14)]

theorem a_eval (q : Nat) :
    evalA 7 (486*q+40) (972*q+88) = some (2, 2*q, 1452*q+138) := by
  calc
    evalA 7 (486*q+40) (972*q+88) = evalA 6 (162*q+13) (1296*q+117) := by
      rw [evalA]
      simp only [if_neg (by omega : (486*q+40)%3 ≠ 2),
        if_neg (by omega : (7:Nat) ≠ 0),
        if_neg (by omega : (486*q+40)%3 ≠ 0)]
      congr 1 <;> omega
    _ = evalA 5 (54*q+4) (1404*q+128) := by
      rw [evalA]
      simp only [if_neg (by omega : (162*q+13)%3 ≠ 2),
        if_neg (by omega : (6:Nat) ≠ 0),
        if_neg (by omega : (162*q+13)%3 ≠ 0)]
      congr 1 <;> omega
    _ = evalA 4 (18*q+1) (1440*q+133) := by
      rw [evalA]
      simp only [if_neg (by omega : (54*q+4)%3 ≠ 2),
        if_neg (by omega : (5:Nat) ≠ 0),
        if_neg (by omega : (54*q+4)%3 ≠ 0)]
      congr 1 <;> omega
    _ = evalA 3 (6*q) (1452*q+136) := by
      rw [evalA]
      simp only [if_neg (by omega : (18*q+1)%3 ≠ 2),
        if_neg (by omega : (4:Nat) ≠ 0),
        if_neg (by omega : (18*q+1)%3 ≠ 0)]
      congr 1 <;> omega
    _ = some (2, 2*q, 1452*q+138) := by
      rw [evalA]
      simp only [if_neg (by omega : (6*q)%3 ≠ 2),
        if_neg (by omega : (3:Nat) ≠ 0),
        if_pos (by omega : (6*q)%3=0)]
      simp only [Option.some.injEq, Prod.mk.injEq, true_and, and_true]
      omega

theorem a_step (q : Nat) :
  highLevelNext (.D (486*q+42) (486*q+45)) = drainB 2 (2*q) (1452*q+138) := by
  simp only [highLevelNext]
  have h0 : 486*q+42 ≠ 0 := by omega
  have h1 : ¬ ((486*q+45)%2=1 ∧ 486*q+42 ≥ (486*q+45)+5) := by omega
  have h2 : ¬ ((486*q+45)%2=0 ∧ 486*q+42 ≥ (486*q+45)+3) := by omega
  have h3 : (486*q+42)%2 ≠ 1 := by omega
  have h4 : 486*q+42 ≠ (486*q+45)+2 := by omega
  have h5 : (486*q+45)%2=1 := by omega
  simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]
  have harg1 : 486*q+45+4-(486*q+42)=7 := by omega
  have harg2 : 486*q+42-1=486*q+41 := by omega
  rw [harg1,harg2]
  rw [drainB]
  simp only [if_neg (by omega : 486*q+41 ≠ 0)]
  have hm1 : 486*q+41-1 = 486*q+40 := by omega
  have hm2 : 3+2*(486*q+41)+3=972*q+88 := by omega
  rw [hm1,hm2,a_eval]
  simp only [Option.bind_some, if_pos (by omega : 2*q < 486*q+41)]

theorem b_eval (q : Nat) :
    evalA 4 (162*q+13) (1296*q+122) = some (0, 2*q, 1452*q+143) := by
  calc
    evalA 4 (162*q+13) (1296*q+122) = evalA 3 (54*q+4) (1404*q+133) := by
      rw [evalA]
      simp only [if_neg (by omega : (162*q+13)%3 ≠ 2),
        if_neg (by omega : (4:Nat) ≠ 0),
        if_neg (by omega : (162*q+13)%3 ≠ 0)]
      congr 1 <;> omega
    _ = evalA 2 (18*q+1) (1440*q+138) := by
      rw [evalA]
      simp only [if_neg (by omega : (54*q+4)%3 ≠ 2),
        if_neg (by omega : (3:Nat) ≠ 0),
        if_neg (by omega : (54*q+4)%3 ≠ 0)]
      congr 1 <;> omega
    _ = evalA 1 (6*q) (1452*q+141) := by
      rw [evalA]
      simp only [if_neg (by omega : (18*q+1)%3 ≠ 2),
        if_neg (by omega : (2:Nat) ≠ 0),
        if_neg (by omega : (18*q+1)%3 ≠ 0)]
      congr 1 <;> omega
    _ = some (0, 2*q, 1452*q+143) := by
      rw [evalA]
      simp only [if_neg (by omega : (6*q)%3 ≠ 2),
        if_neg (by omega : (1:Nat) ≠ 0),
        if_pos (by omega : (6*q)%3=0)]
      simp only [Option.some.injEq, Prod.mk.injEq, true_and, and_true]
      omega

theorem b_step (q : Nat) :
  highLevelNext (.D (486*q+42) (486*q+46)) = drainB 0 (2*q) (1452*q+143) := by
  simp only [highLevelNext]
  have h0 : 486*q+42 ≠ 0 := by omega
  have h1 : ¬ ((486*q+46)%2=1 ∧ 486*q+42 ≥ (486*q+46)+5) := by omega
  have h2 : ¬ ((486*q+46)%2=0 ∧ 486*q+42 ≥ (486*q+46)+3) := by omega
  have h3 : (486*q+42)%2 ≠ 1 := by omega
  have h4 : 486*q+42 ≠ (486*q+46)+2 := by omega
  have h5 : (486*q+46)%2 ≠ 1 := by omega
  simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]
  have he : evalA 5 (486*q+42) (972*q+89) = some (4, 162*q+14, 972*q+91) := by
    rw [evalA]
    simp only [if_neg (by omega : (486*q+42)%3 ≠ 2),
      if_neg (by omega : (5:Nat) ≠ 0),
      if_pos (by omega : (486*q+42)%3=0)]
    simp only [Option.some.injEq, Prod.mk.injEq, true_and, and_true]
    omega
  have harg1 : 486*q+46+1-(486*q+42)=5 := by omega
  have harg2 : 2*(486*q+42)+5=972*q+89 := by omega
  rw [harg1,harg2,he]
  simp only [Option.bind_some]
  rw [drainB]
  simp only [if_neg (by omega : 162*q+14 ≠ 0)]
  have hm1 : 162*q+14-1=162*q+13 := by omega
  have hm2 : 972*q+91+2*(162*q+14)+3=1296*q+122 := by omega
  rw [hm1,hm2,b_eval]
  simp only [Option.bind_some, if_pos (by omega : 2*q < 162*q+14)]


def gain2 : Nat → Nat
  | 0 => 0
  | n+1 => gain2 n + 48*9^n + 2

def gain6 : Nat → Nat
  | 0 => 0
  | n+1 => gain6 n + 144*9^n + 2

theorem gain2_closed (n : Nat) : gain2 n + 6 = 6*9^n + 2*n := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [gain2, Nat.pow_succ]
    omega

theorem gain6_closed (n : Nat) : gain6 n + 18 = 18*9^n + 2*n := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [gain6, Nat.pow_succ]
    omega

theorem drainB_pow2 (a n d : Nat) :
    drainB a (2*9^n) d = drainB a 2 (d+gain2 n) := by
  induction n generalizing d with
  | zero => simp [gain2]
  | succ n ih =>
    have hb : 0 < 2*9^n := by
      have hp : 0 < 9^n := Nat.pow_pos (by decide)
      omega
    calc
      drainB a (2*9^(n+1)) d = drainB a (9*(2*9^n)) d := by simp only [Nat.pow_succ]; congr 1; ac_rfl
      _ = drainB a (2*9^n) (d+24*(2*9^n)+2) := drainB_scale_nine a (2*9^n) d hb
      _ = drainB a 2 ((d+24*(2*9^n)+2)+gain2 n) := ih _
      _ = drainB a 2 (d+gain2 (n+1)) := by
        congr 1
        simp only [gain2]
        omega

theorem drainB_pow6 (a n d : Nat) :
    drainB a (6*9^n) d = drainB a 6 (d+gain6 n) := by
  induction n generalizing d with
  | zero => simp [gain6]
  | succ n ih =>
    have hb : 0 < 6*9^n := by
      have hp : 0 < 9^n := Nat.pow_pos (by decide)
      omega
    calc
      drainB a (6*9^(n+1)) d = drainB a (9*(6*9^n)) d := by simp only [Nat.pow_succ]; congr 1; ac_rfl
      _ = drainB a (6*9^n) (d+24*(6*9^n)+2) := drainB_scale_nine a (6*9^n) d hb
      _ = drainB a 6 ((d+24*(6*9^n)+2)+gain6 n) := ih _
      _ = drainB a 6 (d+gain6 (n+1)) := by
        congr 1
        simp only [gain6]
        omega

theorem eA_two (d : Nat) :
    evalA 2 1 (d+7) = some (0,0,d+12) := by
  simp [evalA, Nat.add_assoc]

theorem eB_two (d : Nat) :
    evalA 0 1 (d+7) = some (0,0,d+7) := by
  simp [evalA]

theorem eB_six (d : Nat) :
    evalA 0 5 (d+15) = some (1,1,d+15) := by
  simp [evalA]

theorem eB_one (d : Nat) :
    evalA 1 0 (d+20) = some (0,0,d+22) := by
  simp [evalA]

theorem drainB_twoA (d : Nat) :
    drainB 2 2 d = some (.D 0 (d+12)) := by
  rw [drainB]
  simp only [if_neg (by decide : (2:Nat) ≠ 0), Nat.reduceSub, Nat.reduceMul,
    Nat.reduceAdd, eA_two, Option.bind_some, if_pos (by decide : (0:Nat)<2)]
  rw [drainB]
  simp only [if_true]

theorem drainB_twoB (d : Nat) :
    drainB 0 2 d = some (.D 0 (d+7)) := by
  rw [drainB]
  simp only [if_neg (by decide : (2:Nat) ≠ 0), Nat.reduceSub, Nat.reduceMul,
    Nat.reduceAdd, eB_two, Option.bind_some, if_pos (by decide : (0:Nat)<2)]
  rw [drainB]
  simp only [if_true]

theorem drainB_six (d : Nat) :
    drainB 0 6 d = some (.D 0 (d+22)) := by
  rw [drainB]
  simp only [if_neg (by decide : (6:Nat) ≠ 0), Nat.reduceSub, Nat.reduceMul,
    Nat.reduceAdd, eB_six, Option.bind_some, if_pos (by decide : (1:Nat)<6)]
  rw [drainB]
  simp only [if_neg (by decide : (1:Nat) ≠ 0), Nat.reduceSub, Nat.reduceMul,
    Nat.reduceAdd, eB_one, Option.bind_some, if_pos (by decide : (0:Nat)<1)]
  rw [drainB]
  simp only [if_true]

theorem a_pulse (n : Nat) :
    highLevelNext (.D (486*9^n+42) (486*9^n+45)) =
      some (.D 0 (1458*9^n+2*n+144)) := by
  rw [a_step,drainB_pow2,drainB_twoA]
  have hg := gain2_closed n
  congr 2
  omega

theorem b_pulse (n : Nat) :
    highLevelNext (.D (486*9^n+42) (486*9^n+46)) =
      some (.D 0 (1458*9^n+2*n+144)) := by
  rw [b_step,drainB_pow2,drainB_twoB]
  have hg := gain2_closed n
  congr 2
  omega

theorem c_pulse (n : Nat) :
    highLevelNext (.D (486*9^n+44) (486*9^n+40)) =
      some (.D 0 (1458*9^n+2*n+144)) := by
  rw [c_step,drainB_pow6,drainB_six]
  have hg := gain6_closed n
  congr 2
  omega

theorem d_pulse (n : Nat) :
    highLevelNext (.D (486*9^n+44) (486*9^n+44)) =
      some (.D 0 (1458*9^n+2*n+144)) := by
  rw [d_step,drainB_pow6,drainB_six]
  have hg := gain6_closed n
  congr 2
  omega

theorem four_pulses (n : Nat) :
    highLevelNext (.D (486*9^n+42) (486*9^n+45)) = some (.D 0 (1458*9^n+2*n+144)) ∧
    highLevelNext (.D (486*9^n+42) (486*9^n+46)) = some (.D 0 (1458*9^n+2*n+144)) ∧
    highLevelNext (.D (486*9^n+44) (486*9^n+40)) = some (.D 0 (1458*9^n+2*n+144)) ∧
    highLevelNext (.D (486*9^n+44) (486*9^n+44)) = some (.D 0 (1458*9^n+2*n+144)) := by
  exact ⟨a_pulse n,b_pulse n,c_pulse n,d_pulse n⟩

#print axioms four_pulses
#print axioms c_step
#print axioms d_step

end BB6.Agent8InverseSource
