import Lean
namespace BB623
inductive S where
  | D (a d : Nat)
  deriving DecidableEq, Repr

def evalA (a k m : Nat) : Option (Nat × Nat × Nat) :=
  if k % 3 = 2 then some (a + 1, k / 3, m)
  else if a = 0 then (if k % 3 = 0 then none else some (0, k / 3, m))
  else if k % 3 = 0 then some (a - 1, k / 3, m + 2)
  else evalA (a - 1) (k / 3) (m + 2 * (k / 3) + 3)
termination_by a
decreasing_by omega

def drainB (a b d : Nat) : Option S :=
  if b = 0 then some (.D a d)
  else (evalA a (b - 1) (d + 2 * b + 3)).bind fun p =>
      if p.2.1 < b then drainB p.1 p.2.1 p.2.2 else none
termination_by b
decreasing_by omega

def next : S → Option S
  | .D a d =>
    if a = 0 then
      if d % 2 = 1 then drainB (d + 1) 2 2 else some (.D d 7)
    else if d % 2 = 1 ∧ a ≥ d + 5 then drainB (a - d - 5) (d + 3) 5
    else if d % 2 = 0 ∧ a ≥ d + 3 then drainB (a - d - 2) (d + 2) 2
    else if a % 2 = 1 then none
    else if a = d + 2 then drainB 0 a 2
    else if d % 2 = 1 then drainB (d + 4 - a) (a - 1) 3
    else (evalA (d + 1 - a) a (2 * a + 5)).bind fun p => drainB p.1 p.2.1 p.2.2

-- helpers for specific large linear terms
private theorem congr_m3 (q : Nat) : (486*q+42)%3=0 := by omega
private theorem congr_m2 (q : Nat) : (486*q+44)%3=2 := by omega

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
  next (.D (486*q+44) (486*q+40)) = drainB 0 (6*q) (1440*q+140) := by
  simp only [next]
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
  next (.D (486*q+44) (486*q+44)) = drainB 0 (6*q) (1440*q+140) := by
  simp only [next]
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
  next (.D (486*q+42) (486*q+45)) = drainB 2 (2*q) (1452*q+138) := by
  simp only [next]
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
  next (.D (486*q+42) (486*q+46)) = drainB 0 (2*q) (1452*q+143) := by
  simp only [next]
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
    next (.D (486*9^n+42) (486*9^n+45)) =
      some (.D 0 (1458*9^n+2*n+144)) := by
  rw [a_step,drainB_pow2,drainB_twoA]
  have hg := gain2_closed n
  congr 2
  omega

theorem b_pulse (n : Nat) :
    next (.D (486*9^n+42) (486*9^n+46)) =
      some (.D 0 (1458*9^n+2*n+144)) := by
  rw [b_step,drainB_pow2,drainB_twoB]
  have hg := gain2_closed n
  congr 2
  omega

theorem c_pulse (n : Nat) :
    next (.D (486*9^n+44) (486*9^n+40)) =
      some (.D 0 (1458*9^n+2*n+144)) := by
  rw [c_step,drainB_pow6,drainB_six]
  have hg := gain6_closed n
  congr 2
  omega

theorem d_pulse (n : Nat) :
    next (.D (486*9^n+44) (486*9^n+44)) =
      some (.D 0 (1458*9^n+2*n+144)) := by
  rw [d_step,drainB_pow6,drainB_six]
  have hg := gain6_closed n
  congr 2
  omega

theorem four_pulses (n : Nat) :
    next (.D (486*9^n+42) (486*9^n+45)) = some (.D 0 (1458*9^n+2*n+144)) ∧
    next (.D (486*9^n+42) (486*9^n+46)) = some (.D 0 (1458*9^n+2*n+144)) ∧
    next (.D (486*9^n+44) (486*9^n+40)) = some (.D 0 (1458*9^n+2*n+144)) ∧
    next (.D (486*9^n+44) (486*9^n+44)) = some (.D 0 (1458*9^n+2*n+144)) := by
  exact ⟨a_pulse n,b_pulse n,c_pulse n,d_pulse n⟩

#print axioms four_pulses
#print axioms c_step
#print axioms d_step

/-! Uniform 9-adic translation and inverse-collision transfer. -/

def liftTriple (z : Nat) (p : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (p.1, p.2.1, p.2.2+z)

def liftState (z : Nat) : S → S
  | .D a d => .D a (d+z)

theorem evalA_shift (a : Nat) : ∀ k m z,
    evalA a k (m+z) = (evalA a k m).map (liftTriple z) := by
  induction a with
  | zero =>
    intro k m z
    conv =>
      lhs
      rw [evalA]
    conv =>
      rhs
      arg 2
      rw [evalA]
    by_cases h2 : k%3=2
    · simp [h2, liftTriple]
    · by_cases h0 : k%3=0
      · simp [h2,h0,liftTriple]
      · simp [h2,h0,liftTriple]
  | succ a ih =>
    intro k m z
    conv =>
      lhs
      rw [evalA]
    conv =>
      rhs
      arg 2
      rw [evalA]
    by_cases h2 : k%3=2
    · simp [h2,liftTriple]
    · by_cases h0 : k%3=0
      · simp [h2,h0,liftTriple,Nat.add_assoc]
        omega
      · simp only [h2,h0,if_false, Nat.succ_ne_zero, Nat.succ_sub_one]
        have hm : m+z+2*(k/3)+3 = (m+2*(k/3)+3)+z := by omega
        rw [hm, ih (k/3) (m+2*(k/3)+3) z]

theorem drainB_shift (b : Nat) : ∀ a d z,
    drainB a b (d+z) = (drainB a b d).map (liftState z) := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a d z
    conv =>
      lhs
      rw [drainB]
    conv =>
      rhs
      arg 2
      rw [drainB]
    by_cases hb : b=0
    · simp [hb, liftState]
    · simp only [if_neg hb]
      have hm : d+z+2*b+3=(d+2*b+3)+z := by omega
      rw [hm, evalA_shift]
      cases he : evalA a (b-1) (d+2*b+3) with
      | none => simp [he]
      | some p =>
        rcases p with ⟨aa,bb,dd⟩
        simp only [he,Option.map_some,liftTriple,Option.bind_some]
        by_cases hlt : bb<b
        · simp only [if_pos hlt]
          rw [ih bb hlt aa dd z]
        · simp only [if_neg hlt,Option.map_none]

def pathA (q : Nat) : Option S := next (.D (486*q+42) (486*q+45))
def pathB (q : Nat) : Option S := next (.D (486*q+42) (486*q+46))
def pathC (q : Nat) : Option S := next (.D (486*q+44) (486*q+40))
def pathD (q : Nat) : Option S := next (.D (486*q+44) (486*q+44))

theorem pair_CD (q : Nat) : pathC q = pathD q := by
  rw [pathC,pathD,c_step,d_step]

theorem scale_A (q : Nat) (hq : 0 < q) :
    pathA (9*q) = (pathA q).map (liftState (11664*q+2)) := by
  simp only [pathA]
  rw [a_step (9*q), a_step q]
  have hk : 2*(9*q) = 9*(2*q) := by omega
  rw [hk, drainB_scale_nine 2 (2*q) (1452*(9*q)+138) (by omega)]
  have hm : 1452*(9*q)+138+24*(2*q)+2=(1452*q+138)+(11664*q+2) := by omega
  rw [hm, drainB_shift]

theorem scale_B (q : Nat) (hq : 0 < q) :
    pathB (9*q) = (pathB q).map (liftState (11664*q+2)) := by
  simp only [pathB]
  rw [b_step (9*q), b_step q]
  have hk : 2*(9*q) = 9*(2*q) := by omega
  rw [hk, drainB_scale_nine 0 (2*q) (1452*(9*q)+143) (by omega)]
  have hm : 1452*(9*q)+143+24*(2*q)+2=(1452*q+143)+(11664*q+2) := by omega
  rw [hm, drainB_shift]

theorem scale_C (q : Nat) (hq : 0 < q) :
    pathC (9*q) = (pathC q).map (liftState (11664*q+2)) := by
  simp only [pathC]
  rw [c_step (9*q), c_step q]
  have hk : 6*(9*q) = 9*(6*q) := by omega
  rw [hk, drainB_scale_nine 0 (6*q) (1440*(9*q)+140) (by omega)]
  have hm : 1440*(9*q)+140+24*(6*q)+2=(1440*q+140)+(11664*q+2) := by omega
  rw [hm, drainB_shift]

theorem scale_D (q : Nat) (hq : 0 < q) :
    pathD (9*q) = (pathD q).map (liftState (11664*q+2)) := by
  rw [← pair_CD (9*q), ← pair_CD q]
  exact scale_C q hq

theorem pair_preserved_A_B (q : Nat) (hq : 0 < q)
    (hab : pathA q = pathB q) : pathA (9*q) = pathB (9*q) := by
  rw [scale_A q hq, scale_B q hq, hab]

theorem pair_preserved_B_C (q : Nat) (hq : 0 < q)
    (hbc : pathB q = pathC q) : pathB (9*q) = pathC (9*q) := by
  rw [scale_B q hq, scale_C q hq, hbc]

#print axioms pair_CD
#print axioms scale_A
#print axioms scale_C
#print axioms pair_preserved_A_B


theorem allNone16 :
    pathA 16 = none ∧ pathB 16 = none ∧ pathC 16 = none ∧ pathD 16 = none := by
  decide +kernel

theorem allNone16_pulse (n : Nat) :
    pathA (16*9^n) = none ∧ pathB (16*9^n) = none ∧
    pathC (16*9^n) = none ∧ pathD (16*9^n) = none := by
  induction n with
  | zero =>
    simpa using allNone16
  | succ n ih =>
    have hpos : 0 < 16*9^n := by
      have hp : 0 < 9^n := Nat.pow_pos (by decide)
      omega
    have hq : 16*9^(n+1)=9*(16*9^n) := by
      simp only [Nat.pow_succ]
      ac_rfl
    rw [hq, scale_A _ hpos, scale_B _ hpos, scale_C _ hpos, scale_D _ hpos]
    simp [ih.1, ih.2.1, ih.2.2.1, ih.2.2.2]

#print axioms allNone16_pulse


/-! Exact positive-density synthetic halting cylinder. -/

theorem eva0_fail (r m : Nat) : evalA 0 (6*r+3) m = none := by
  rw [evalA]
  simp only [if_neg (by omega : (6*r+3)%3 ≠ 2),
    if_pos (by decide : (0:Nat)=0),
    if_pos (by omega : (6*r+3)%3=0), if_true]

theorem eva2_fail (r m : Nat) : evalA 2 (54*r+31) m = none := by
  calc
    evalA 2 (54*r+31) m = evalA 1 (18*r+10) (m+2*(18*r+10)+3) := by
      rw [evalA]
      simp only [if_neg (by omega : (54*r+31)%3 ≠ 2),
        if_neg (by decide : (2:Nat)≠0),
        if_neg (by omega : (54*r+31)%3 ≠ 0)]
      congr 1 <;> omega
    _ = evalA 0 (6*r+3) ((m+2*(18*r+10)+3)+2*(6*r+3)+3) := by
      rw [evalA]
      simp only [if_neg (by omega : (18*r+10)%3 ≠ 2),
        if_neg (by decide : (1:Nat)≠0),
        if_neg (by omega : (18*r+10)%3 ≠ 0)]
      congr 1 <;> omega
    _ = none := eva0_fail r _

theorem eva0_firstB (r m : Nat) :
    evalA 0 (18*r+13) m = some (0, 6*r+4, m) := by
  rw [evalA]
  simp only [if_neg (by omega : (18*r+13)%3 ≠ 2),
    if_pos (by decide : (0:Nat)=0),
    if_neg (by omega : (18*r+13)%3≠0), if_true]
  simp only [Option.some.injEq,Prod.mk.injEq,true_and,and_true]
  omega

theorem eva0_firstC (r m : Nat) :
    evalA 0 (54*r+41) m = some (1, 18*r+13, m) := by
  rw [evalA]
  simp only [if_pos (by omega : (54*r+41)%3=2)]
  simp only [Option.some.injEq,Prod.mk.injEq,true_and,and_true]
  omega

theorem eva1_middleC (r m : Nat) :
    evalA 1 (18*r+12) m = some (0, 6*r+4, m+2) := by
  rw [evalA]
  simp only [if_neg (by omega : (18*r+12)%3≠2),
    if_neg (by decide : (1:Nat)≠0),
    if_pos (by omega : (18*r+12)%3=0)]
  simp only [Option.some.injEq,Prod.mk.injEq,true_and,and_true]
  omega

theorem a_halt_residue (r : Nat) : pathA (27*r+16) = none := by
  simp only [pathA]
  rw [a_step]
  rw [drainB]
  simp only [if_neg (by omega : 2*(27*r+16) ≠ 0)]
  have hk : 2*(27*r+16)-1 = 54*r+31 := by omega
  rw [hk, eva2_fail]
  simp only [Option.bind_none]

theorem b_halt_residue (r : Nat) : pathB (9*r+7) = none := by
  simp only [pathB]
  rw [b_step]
  rw [drainB]
  simp only [if_neg (by omega : 2*(9*r+7)≠0)]
  have hk : 2*(9*r+7)-1=18*r+13 := by omega
  rw [hk, eva0_firstB]
  simp only [Option.bind_some, if_pos (by omega : 6*r+4 < 2*(9*r+7))]
  rw [drainB]
  simp only [if_neg (by omega : 6*r+4≠0)]
  have hk2 : 6*r+4-1=6*r+3 := by omega
  rw [hk2, eva0_fail]
  simp only [Option.bind_none]

theorem c_halt_residue (r : Nat) : pathC (9*r+7) = none := by
  simp only [pathC]
  rw [c_step]
  rw [drainB]
  simp only [if_neg (by omega : 6*(9*r+7)≠0)]
  have hk : 6*(9*r+7)-1=54*r+41 := by omega
  rw [hk,eva0_firstC]
  simp only [Option.bind_some, if_pos (by omega : 18*r+13 < 6*(9*r+7))]
  rw [drainB]
  simp only [if_neg (by omega : 18*r+13≠0)]
  have hk2 : 18*r+13-1=18*r+12 := by omega
  rw [hk2,eva1_middleC]
  simp only [Option.bind_some, if_pos (by omega : 6*r+4 < 18*r+13)]
  rw [drainB]
  simp only [if_neg (by omega : 6*r+4≠0)]
  have hk3 : 6*r+4-1=6*r+3 := by omega
  rw [hk3,eva0_fail]
  simp only [Option.bind_none]

theorem four_halt_residue (r : Nat) :
    pathA (27*r+16) = none ∧ pathB (27*r+16) = none ∧
    pathC (27*r+16) = none ∧ pathD (27*r+16) = none := by
  have hq : 27*r+16=9*(3*r+1)+7 := by omega
  exact ⟨a_halt_residue r,
    hq ▸ b_halt_residue (3*r+1),
    hq ▸ c_halt_residue (3*r+1),
    (pair_CD (27*r+16)).symm ▸ (hq ▸ c_halt_residue (3*r+1))⟩

#print axioms four_halt_residue

end BB623
