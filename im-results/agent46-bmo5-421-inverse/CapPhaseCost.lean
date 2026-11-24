import CapPhase
namespace CapSieve

/-- Positive-coordinate history after one same-band inverse from W=-w.
    The history counts that first step. No guard on intermediate band size. -/
inductive PositiveHistory (j : Nat) (w : Int) : Nat → Nat → Nat → Prop where
  | first {x : Nat} : Band j x → 3*W j x=8*(P j:Int)-6-w → PositiveHistory j w 1 j x
  | same {s k x y : Nat} : PositiveHistory j w s k y → RegFrom k x y → PositiveHistory j w (s+1) k x
  | down {s k x y : Nat} : PositiveHistory j w s (k+1) y → RegFrom k x y → PositiveHistory j w (s+1) k x

/-- The exact affine packet remains strictly below the top coefficient.
    This is independent of how long the positive sector survives. -/
theorem positive_history_packet {j s k x : Nat} {w : Int} (hw : 0<w)
    (h : PositiveHistory j w s k x) :
    ∃ A C : Int, 0<A ∧ A<4*(3^s:Int) ∧ A%3≠0 ∧ C<0 ∧
      (3^s:Int)*W k x=A*(P k:Int)+C := by
  induction h with
  | first hb he => exact ⟨8,-6-w,by decide,by decide,by decide,by omega,by simp; omega⟩
  | @same s k x y h hr ih =>
    obtain ⟨A,C,hA,hA',hu,hC,he⟩:=ih
    let D : Int := 3^s
    have hD : 0<D := Int.pow_pos (by decide)
    have hW:=w_regular_same hr
    refine ⟨A+8*D,C-6*D,by omega,?_,?_,by omega,?_⟩
    · rw [Int.pow_succ]; change A+8*D<4*(D*3); omega
    · have hs : 0<s := by
        cases h <;> omega
      have hd : D%3=0 := by
        cases s with
        | zero => omega
        | succ s => simp [D,Int.pow_succ]
      rw [Int.add_emod,Int.mul_emod,hd]; simpa using hu
    · rw [Int.pow_succ]; change D*3*W k x=(A+8*D)*(P k:Int)+(C-6*D)
      change D*W k y=A*(P k:Int)+C at he
      grind
  | @down s k x y h hr ih =>
    obtain ⟨A,C,hA,hA',hu,hC,he⟩:=ih
    let D : Int := 3^s
    have hD : 0<D := Int.pow_pos (by decide)
    have hW:=w_regular_down hr
    refine ⟨2*A,C,by omega,?_,?_,hC,?_⟩
    · rw [Int.pow_succ]; change 2*A<4*(D*3); omega
    · rw [Int.mul_emod]; omega
    · rw [Int.pow_succ]; change D*3*W k x=2*A*(P k:Int)+C
      rw [p_succ] at he
      simp only [Int.natCast_mul] at he
      change D*W (k+1) y=A*(2*(P k:Int))+C at he
      grind

/-- Number of descents is bounded by the number of positive history steps. -/
theorem positive_history_index {j s k x : Nat} {w : Int} (h : PositiveHistory j w s k x) :
    k≤j ∧ j+1≤k+s := by
  induction h <;> omega

/-- A low-boundary exit after s positive steps needs exponential scale
    5*2^k to fit inside the available power-of-three denominator. -/
theorem positive_boundary_cost {j s k x : Nat} {w : Int} (hw : 0<w)
    (h : PositiveHistory j w s k x) (hx : x≤P k+2) :
    (P k:Int)≤(3^s:Int)*(6*(k:Int)+35) := by
  obtain ⟨A,C,hA,hA',_,hC,he⟩:=positive_history_packet hw h
  let D : Int := 3^s
  have hD : 0<D := Int.pow_pos (by decide)
  have hP : 0≤(P k:Int) := by omega
  have hmul:=Int.mul_le_mul_of_nonneg_right (show A≤4*D-1 by omega) hP
  have hW : 4*(P k:Int)-(6*(k:Int)+35)≤W k x := by unfold W; omega
  have hlow:=Int.mul_le_mul_of_nonneg_left hW (Int.le_of_lt hD)
  change D*W k x=A*(P k:Int)+C at he
  change (P k:Int)≤D*(6*(k:Int)+35)
  grind

/-- Eliminating the current band index gives an initial-band-only bound.
    The length required for a low-boundary return grows linearly in j
    up to logarithmic terms, since P_j=5*2^j. -/
theorem positive_boundary_initial_cost {j s k x : Nat} {w : Int} (hw : 0<w)
    (h : PositiveHistory j w s k x) (hx : x≤P k+2) :
    2*(P j:Int)≤(6^s:Int)*(6*(j:Int)+35) := by
  have ⟨hkj,hks⟩:=positive_history_index h
  have hc:=positive_boundary_cost hw h hx
  have hp : P j=P k*2^(j-k) := by
    unfold P
    have hpow : 2^j=2^k*2^(j-k) := by rw [←Nat.pow_add,show k+(j-k)=j by omega]
    rw [hpow]
    grind
  have hh : 2*2^(j-k)≤2^s := by
    rw [Nat.mul_comm,←Nat.pow_succ]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hp' : (P j:Int)=(P k:Int)*(2^(j-k):Int) := by exact_mod_cast hp
  have hh' : 2*(2^(j-k):Int)≤(2^s:Int) := by exact_mod_cast hh
  have hP : 0≤(P k:Int) := by omega
  have ha:=Int.mul_le_mul_of_nonneg_left hh' hP
  have hb:=Int.mul_le_mul_of_nonneg_left hc (show 0≤(2^s:Int) from Int.pow_nonneg (by decide))
  have hm:=Int.mul_le_mul_of_nonneg_left (show 6*(k:Int)+35≤6*(j:Int)+35 by omega)
    (show 0≤(6^s:Int) from Int.pow_nonneg (by decide))
  have he : (2^s:Int)*(3^s:Int)=(6^s:Int) := by rw [←Int.mul_pow]; rfl
  calc
    2*(P j:Int) = (P k:Int)*(2*2^(j-k)) := by rw [hp']; grind
    _ ≤ (P k:Int)*2^s := ha
    _ = 2^s*(P k:Int) := Int.mul_comm _ _
    _ ≤ 2^s*(3^s*(6*(k:Int)+35)) := hb
    _ = 6^s*(6*(k:Int)+35) := by rw [←Int.mul_assoc,he]
    _ ≤ _ := hm

#print axioms positive_boundary_initial_cost
#print axioms positive_history_packet
#print axioms positive_history_index
#print axioms positive_boundary_cost

/-- The affine packet carries a second, monotone weight.  Writing
    B=4*3^s-A, each same-band inverse keeps B fixed, while a
    one-band descent changes B to 2*B+4*3^s.  Consequently B*P_k
    never falls below its initial value 4*P_j. -/
theorem positive_history_packet_weight {j s k x : Nat} {w : Int} (hw : 0<w)
    (h : PositiveHistory j w s k x) :
    ∃ A C : Int, 0<A ∧ A<4*(3^s:Int) ∧ A%3≠0 ∧ C≤ -6-w ∧
      (3^s:Int)*W k x=A*(P k:Int)+C ∧
      (4*(3^s:Int)-A)*(P k:Int) ≥4*(P j:Int) := by
  induction h with
  | first hb he =>
    refine ⟨8,-6-w,by decide,by decide,by decide,by omega,?_,?_⟩
    · change (3:Int)*W j x=8*(P j:Int)-6-w
      omega
    · change (4:Int)*(P j:Int)≥4*(P j:Int)
      omega
  | @same s k x y h hr ih =>
    obtain ⟨A,C,hA,hA',hu,hC,he,hB⟩:=ih
    let D : Int := 3^s
    have hD : 0<D := Int.pow_pos (by decide)
    have hW:=w_regular_same hr
    refine ⟨A+8*D,C-6*D,by omega,?_,?_,by omega,?_,?_⟩
    · rw [Int.pow_succ]
      change A+8*D<4*(D*3)
      omega
    · have hs : 0<s := by cases h <;> omega
      have hd : D%3=0 := by
        cases s with
        | zero => omega
        | succ s => simp [D,Int.pow_succ]
      rw [Int.add_emod,Int.mul_emod,hd]
      simpa using hu
    · rw [Int.pow_succ]
      change D*3*W k x=(A+8*D)*(P k:Int)+(C-6*D)
      change D*W k y=A*(P k:Int)+C at he
      grind
    · rw [Int.pow_succ]
      change (4*(D*3)-(A+8*D))*(P k:Int)≥4*(P j:Int)
      have heq : 4*(D*3)-(A+8*D)=4*D-A := by ring
      rw [heq]
      exact hB
  | @down s k x y h hr ih =>
    obtain ⟨A,C,hA,hA',hu,hC,he,hB⟩:=ih
    let D : Int := 3^s
    have hD : 0<D := Int.pow_pos (by decide)
    have hW:=w_regular_down hr
    refine ⟨2*A,C,by omega,?_,?_,hC,?_,?_⟩
    · rw [Int.pow_succ]
      change 2*A<4*(D*3)
      omega
    · rw [Int.mul_emod]
      omega
    · rw [Int.pow_succ]
      change D*3*W k x=2*A*(P k:Int)+C
      rw [p_succ] at he
      simp only [Int.natCast_mul] at he
      change D*W (k+1) y=A*(2*(P k:Int))+C at he
      grind
    · rw [Int.pow_succ]
      change (4*(D*3)-2*A)*(P k:Int)≥4*(P j:Int)
      have hp : (P (k+1):Int)=2*(P k:Int) := by exact_mod_cast p_succ k
      calc
        (4*(D*3)-2*A)*(P k:Int)
            = (4*D-A)*(P (k+1):Int)+4*D*(P k:Int) := by rw [hp]; ring
        _ ≥ 4*(P j:Int) := by
          have hD0 : 0≤D := le_of_lt hD
          have hP0 : 0≤(P k:Int) := by exact_mod_cast Nat.zero_le (P k)
          have hterm : 0≤4*D*(P k:Int) := by positivity
          nlinarith [hB,hterm]

/-- Every state in a positive history is in its recorded band. -/
theorem positive_history_band {j s k x : Nat} {w : Int}
    (h : PositiveHistory j w s k x) : Band k x := by
  induction h with
  | first hb he => exact hb
  | @same s k x y h hr ih =>
    obtain ⟨r,hr,rfl,rfl⟩:=hr
    exact regular_band k r hr
  | @down s k x y h hr ih =>
    obtain ⟨r,hr,rfl,rfl⟩:=hr
    exact regular_band k r hr

/-- A sharp all-depth cost barrier for a positive excursion that reaches
    the low boundary x<=P_k+2.  The extra factor comes from the monotone
    packet weight (4*3^s-A)*P_k, not from a finite-depth estimate. -/
theorem positive_boundary_cost_sharp {j s k x : Nat} {w : Int} (hw : 0<w)
    (h : PositiveHistory j w s k x) (hx : x≤P k+2) :
    (4*(P j:Int)+6+w) ≤ (3^s:Int)*(6*(k:Int)+35) := by
  obtain ⟨A,C,hA,hA',hu,hC,he,hB⟩:=positive_history_packet_weight hw h
  let D : Int := 3^s
  have hD : 0<D := Int.pow_pos (by decide)
  have hb:=positive_history_band h
  have hQNat : Q k x≤3*k+16 := by
    have hl:=l_add k
    unfold Q
    omega
  have hQ : (Q k x:Int)≤3*(k:Int)+16 := by exact_mod_cast hQNat
  have hWQ : W k x+2*(Q k x:Int)=4*(P k:Int)-3 := by
    have hl:=l_add k
    unfold W Q
    omega
  have hrel : 2*D*(Q k x:Int)=(4*D-A)*(P k:Int)-3*D-C := by
    change D*(W k x:Int)=A*(P k:Int)+C at he
    nlinarith [he,hWQ]
  have hmul:=Int.mul_le_mul_of_nonneg_left hQ (le_of_lt hD)
  have hupper : 2*D*(Q k x:Int)≤D*(6*(k:Int)+32) := by nlinarith
  have hC' : 6+w≤-C := by omega
  have hlower : 4*(P j:Int)+6+w-3*D≤2*D*(Q k x:Int) := by
    nlinarith [hB,hC',hrel]
  have hfinal:=le_trans hlower hupper
  nlinarith

#print axioms positive_history_packet_weight
#print axioms positive_history_band
#print axioms positive_boundary_cost_sharp

end CapSieve
