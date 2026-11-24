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
theorem positive_history_packet {j s k x : Nat} {w : Int} (_hw : 0<w)
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
theorem positive_history_packet_weight {j s k x : Nat} {w : Int} (_hw : 0<w)
    (h : PositiveHistory j w s k x) :
    ∃ A C : Int, 0<A ∧ A<4*(3^s:Int) ∧ A%3≠0 ∧ C≤ -6-w ∧
      (3^s:Int)*W k x=A*(P k:Int)+C ∧
      (4*(3^s:Int)-A)*(P k:Int) ≥4*(P j:Int) := by
  induction h with
  | first hb he =>
    refine ⟨8,-6-w,by decide,by decide,by decide,by omega,?_,?_⟩
    · simp
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
      have heq : 4*(D*3)-(A+8*D)=4*D-A := by omega
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
            = (4*D-A)*(P (k+1):Int)+4*D*(P k:Int) := by rw [hp]; grind
        _ ≥ 4*(P j:Int) := by
          have hP0 : 0≤(P k:Int) := by exact_mod_cast Nat.zero_le (P k)
          have hterm : 0≤4*D*(P k:Int) := by
            apply Int.mul_nonneg
            · exact Int.mul_nonneg (by decide) (Int.le_of_lt hD)
            · exact hP0
          grind

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
    have hq:=q_eq hb
    omega
  have hQ : (Q k x:Int)≤3*(k:Int)+16 := by exact_mod_cast hQNat
  have hWQ : W k x+2*(Q k x:Int)=4*(P k:Int)-3 := by
    have hq:=q_eq hb
    have hqI : (Q k x:Int)+2*(P k:Int)=2*(x:Int)+3*(k:Int)+12 := by exact_mod_cast hq
    unfold W
    omega
  have hrel : 2*D*(Q k x:Int)=(4*D-A)*(P k:Int)-3*D-C := by
    change D*(W k x:Int)=A*(P k:Int)+C at he
    grind
  have hmul:=Int.mul_le_mul_of_nonneg_left hQ (Int.le_of_lt hD)
  have hupper : 2*D*(Q k x:Int)≤D*(6*(k:Int)+32) := by grind
  have hC' : 6+w≤-C := by omega
  have hlower : 4*(P j:Int)+6+w-3*D≤2*D*(Q k x:Int) := by
    grind
  have hsum : 4*(P j:Int)+6+w≤D*(6*(k:Int)+32)+3*D := by omega
  change 4*(P j:Int)+6+w≤D*(6*(k:Int)+35)
  rw [Int.mul_add] at hsum ⊢
  omega


/-- A stronger packet weight records the exact band drop: after d=j-k
    one-band descents, B=4*3^s-A is at least 4*3^d. -/
theorem positive_history_packet_bandweight {j s k x : Nat} {w : Int} (_hw : 0<w)
    (h : PositiveHistory j w s k x) :
    ∃ A C : Int, 0<A ∧ A<4*(3^s:Int) ∧ A%3≠0 ∧ C≤ -6-w ∧
      (3^s:Int)*W k x=A*(P k:Int)+C ∧
      4*(3^(j-k):Int)≤4*(3^s:Int)-A := by
  induction h with
  | first hb he =>
    refine ⟨8,-6-w,by decide,by decide,by decide,by omega,?_,?_⟩
    · simp
      omega
    · simp
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
      change 4*(3^(j-k):Int)≤4*(D*3)-(A+8*D)
      have heq : 4*(D*3)-(A+8*D)=4*D-A := by omega
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
      change 4*(3^(j-k):Int)≤4*(D*3)-2*A
      have hidx:=positive_history_index h
      have hd : j-k≤s := by omega
      have hpowNat : 3^(j-k)≤3^s :=
        Nat.pow_le_pow_right (by decide) hd
      have hpow : (3^(j-k):Int)≤D := by
        change (3^(j-k):Int)≤(3^s:Int)
        exact_mod_cast hpowNat
      have hdec : j-k=j-(k+1)+1 := by omega
      have hprevNat : 3^(j-k)=3^(j-(k+1))*3 := by
        rw [hdec,Nat.pow_succ]
      have hprev : (3^(j-k):Int)=(3^(j-(k+1)):Int)*3 := by
        exact_mod_cast hprevNat
      have hBscaled : 8*(3^(j-(k+1)):Int)≤2*(4*D-A) := by omega
      have hDscaled : 12*(3^(j-(k+1)):Int)≤4*D := by
        rw [hprev] at hpow
        omega
      have htarget : 4*(3^(j-k):Int)≤2*(4*D-A)+4*D := by
        rw [hprev]
        omega
      calc
        4*(3^(j-k):Int)≤2*(4*D-A)+4*D := htarget
        _=4*(D*3)-2*A := by omega

/-- Low-boundary returns require many same-band inversions, even when
    arbitrary one-band descents occur in between. -/
theorem positive_boundary_cost_bandsharp {j s k x : Nat} {w : Int} (hw : 0<w)
    (h : PositiveHistory j w s k x) (hx : x≤P k+2) :
    (4*(3^(j-k):Int)*(P k:Int)+6+w) ≤ (3^s:Int)*(6*(k:Int)+35) := by
  obtain ⟨A,C,hA,hA',hu,hC,he,hB⟩:=positive_history_packet_bandweight hw h
  let D : Int := 3^s
  have hD : 0<D := Int.pow_pos (by decide)
  have hb:=positive_history_band h
  have hQNat : Q k x≤3*k+16 := by
    have hq:=q_eq hb
    omega
  have hQ : (Q k x:Int)≤3*(k:Int)+16 := by exact_mod_cast hQNat
  have hWQ : W k x+2*(Q k x:Int)=4*(P k:Int)-3 := by
    have hq:=q_eq hb
    have hqI : (Q k x:Int)+2*(P k:Int)=2*(x:Int)+3*(k:Int)+12 := by exact_mod_cast hq
    unfold W
    omega
  have hrel : 2*D*(Q k x:Int)=(4*D-A)*(P k:Int)-3*D-C := by
    change D*(W k x:Int)=A*(P k:Int)+C at he
    grind
  have hmul:=Int.mul_le_mul_of_nonneg_left hQ (Int.le_of_lt hD)
  have hupper : 2*D*(Q k x:Int)≤D*(6*(k:Int)+32) := by grind
  have hC' : 6+w≤-C := by omega
  have hP0 : 0≤(P k:Int) := by exact_mod_cast Nat.zero_le (P k)
  have hBprod : 4*(3^(j-k):Int)*(P k:Int)≤(4*D-A)*(P k:Int) :=
    Int.mul_le_mul_of_nonneg_right hB hP0
  have hlower :
      4*(3^(j-k):Int)*(P k:Int)+6+w-3*D≤2*D*(Q k x:Int) := by
    grind
  have hsum :
      4*(3^(j-k):Int)*(P k:Int)+6+w≤D*(6*(k:Int)+32)+3*D := by omega
  change 4*(3^(j-k):Int)*(P k:Int)+6+w≤D*(6*(k:Int)+35)
  rw [Int.mul_add] at hsum ⊢
  omega

#print axioms positive_history_packet_bandweight
#print axioms positive_boundary_cost_bandsharp


/-- Exact cost of a complete positive-to-negative skip return.  If a
    positive history starts at -w0, reaches a two-band skip parent, and
    that negative parent strips to unit w1 in n steps, the two units and
    the whole intervening history satisfy this inequality. -/
theorem positive_skip_return_cost {j s k x z n : Nat} {w0 w1 : Int}
    (hw0 : 0<w0) (hk : 2≤k)
    (h : PositiveHistory j w0 s k x)
    (hskip : RegFrom (k-2) z x)
    (hstrip : W (k-2) z=-(3^n:Int)*w1) :
    (4*(3^(j-k):Int)*(P k:Int)+6+w0) ≤
      (3^s:Int)*((3^(n+1):Int)*w1+6) := by
  obtain ⟨A,C,hA,hA',hu,hC,he,hB⟩:=positive_history_packet_bandweight hw0 h
  let D : Int := 3^s
  have hb:=positive_history_band h
  have hk' : (k-2)+2=k := by omega
  have hband' : Band ((k-2)+2) x := by simpa [hk'] using hb
  have hqskip0:=skip_reset_q hskip hband' hstrip
  have hqskip : 2*(Q k x:Int)=(3^(n+1):Int)*w1+3 := by
    simpa [hk'] using hqskip0
  have hWQ : W k x+2*(Q k x:Int)=4*(P k:Int)-3 := by
    have hq:=q_eq hb
    have hqI : (Q k x:Int)+2*(P k:Int)=2*(x:Int)+3*(k:Int)+12 := by exact_mod_cast hq
    unfold W
    omega
  have hrel : 2*D*(Q k x:Int)=(4*D-A)*(P k:Int)-3*D-C := by
    change D*(W k x:Int)=A*(P k:Int)+C at he
    grind
  have hreturn0 :
      D*((3^(n+1):Int)*w1+3)=(4*D-A)*(P k:Int)-3*D-C := by
    rw [←hqskip]
    simpa [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm] using hrel
  have hreturn :
      D*((3^(n+1):Int)*w1+6)=(4*D-A)*(P k:Int)-C := by
    calc
      D*((3^(n+1):Int)*w1+6)
          =D*((3^(n+1):Int)*w1+3)+3*D := by
            simp only [Int.mul_add]
            omega
      _=(4*D-A)*(P k:Int)-3*D-C+3*D := by rw [hreturn0]
      _=(4*D-A)*(P k:Int)-C := by omega
  have hP0 : 0≤(P k:Int) := by exact_mod_cast Nat.zero_le (P k)
  have hBprod : 4*(3^(j-k):Int)*(P k:Int)≤(4*D-A)*(P k:Int) :=
    Int.mul_le_mul_of_nonneg_right hB hP0
  have hC' : 6+w0≤-C := by omega
  rw [hreturn]
  omega


/-- A two-band skip parent is an exceptional return with a sharper
    denominator: its exact Q-coordinate gives 6*k-9. -/
theorem positive_skip_parent_cost {j s k x z : Nat} {w0 : Int}
    (hw0 : 0<w0) (hk : 2≤k)
    (h : PositiveHistory j w0 s k x)
    (hskip : RegFrom (k-2) z x) :
    (4*(3^(j-k):Int)*(P k:Int)+6+w0) ≤
      (3^s:Int)*(6*(k:Int)-9) := by
  let w1 : Int := -W (k-2) z
  have hb:=positive_history_band h
  have hk' : (k-2)+2=k := by omega
  have hband' : Band ((k-2)+2) x := by simpa [hk'] using hb
  have hstrip : W (k-2) z=-(3^0:Int)*w1 := by
    simp [w1]
  have hret:=positive_skip_return_cost hw0 hk h hskip hstrip
  have hwindow:=skip_reset_band_window hskip hband' hstrip
  have hfactor0 : (3:Int)*w1≤6*(((k-2):Nat):Int)-3 := by
    simpa using hwindow.2
  have hfactor : (3:Int)*w1+6≤6*(k:Int)-9 := by omega
  have hD0 : 0≤(3^s:Int) := Int.le_of_lt (Int.pow_pos (by decide))
  have hmul:=Int.mul_le_mul_of_nonneg_left hfactor hD0
  have hret' :
      4*(3^(j-k):Int)*(P k:Int)+6+w0≤
        (3^s:Int)*((3:Int)*w1+6) := by
    simpa [w1] using hret
  calc
    _≤(3^s:Int)*((3:Int)*w1+6) := hret'
    _≤(3^s:Int)*(6*(k:Int)-9) := hmul

/-- A special parent at P_k has the exact Q-coordinate 3k+12, giving
    the complementary exceptional-return denominator 6*k+27. -/
theorem positive_special_return_cost {j s k : Nat} {w0 : Int}
    (hw0 : 0<w0)
    (h : PositiveHistory j w0 s k (P k)) :
    (4*(3^(j-k):Int)*(P k:Int)+6+w0) ≤
      (3^s:Int)*(6*(k:Int)+27) := by
  obtain ⟨A,C,hA,hA',hu,hC,he,hB⟩:=positive_history_packet_bandweight hw0 h
  let D : Int := 3^s
  have hb:=positive_history_band h
  have hq:=q_eq hb
  have hqI : (Q k (P k):Int)+2*(P k:Int)
      =2*(P k:Int)+3*(k:Int)+12 := by exact_mod_cast hq
  have hQ : 2*(Q k (P k):Int)=6*(k:Int)+24 := by omega
  have hWQ : W k (P k)+2*(Q k (P k):Int)=4*(P k:Int)-3 := by
    unfold W
    omega
  have hrel :
      2*D*(Q k (P k):Int)=(4*D-A)*(P k:Int)-3*D-C := by
    change D*(W k (P k):Int)=A*(P k:Int)+C at he
    grind
  have hreturn0 :
      D*(2*(Q k (P k):Int))=(4*D-A)*(P k:Int)-3*D-C := by
    simpa [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm] using hrel
  have hreturn :
      D*(6*(k:Int)+27)=(4*D-A)*(P k:Int)-C := by
    calc
      D*(6*(k:Int)+27)=D*(2*(Q k (P k):Int)+3) := by
        rw [hQ]
        have hnum : 6*(k:Int)+27=6*(k:Int)+24+3 := by omega
        rw [hnum]
      _=D*(2*(Q k (P k):Int))+3*D := by
        simp only [Int.mul_add]
        omega
      _=(4*D-A)*(P k:Int)-3*D-C+3*D := by rw [hreturn0]
      _=(4*D-A)*(P k:Int)-C := by omega
  have hP0 : 0≤(P k:Int) := by exact_mod_cast Nat.zero_le (P k)
  have hBprod : 4*(3^(j-k):Int)*(P k:Int)≤(4*D-A)*(P k:Int) :=
    Int.mul_le_mul_of_nonneg_right hB hP0
  have hC' : 6+w0≤-C := by omega
  rw [hreturn]
  omega

#print axioms positive_skip_parent_cost
#print axioms positive_special_return_cost

#print axioms positive_skip_return_cost


/-- Decompose a positive history at its last one-band descent.  Its suffix
    is a same-band run, beginning either at the initial positive state or
    immediately after that last descent. -/
theorem positive_history_final_run {j s k x : Nat} {w : Int}
    (h : PositiveHistory j w s k x) :
    ∃ r z, SameRun k r x z ∧
      ((k=j ∧ 3*W j z=8*(P j:Int)-6-w) ∨
       ∃ s' y, PositiveHistory j w s' (k+1) y ∧ RegFrom k z y) := by
  refine PositiveHistory.rec
    (motive := fun s k x =>
      ∃ r z, SameRun k r x z ∧
        ((k=j ∧ 3*W j z=8*(P j:Int)-6-w) ∨
         ∃ s' y, PositiveHistory j w s' (k+1) y ∧ RegFrom k z y))
    ?_ ?_ ?_ h
  · intro x hb he
    exact ⟨0,x,SameRun.zero hb,Or.inl ⟨rfl,he⟩⟩
  · intro s k x y h hr ih
    obtain ⟨r,z,hs,hbase⟩:=ih
    exact ⟨r+1,z,SameRun.head hr hs,hbase⟩
  · intro s k x y h hr ih
    obtain ⟨r,hr0,hx,hy⟩:=hr
    have hb : Band k x := by rw [hx]; exact regular_band k r hr0
    exact ⟨0,x,SameRun.zero hb,Or.inr ⟨s,y,h,⟨r,hr0,hx,hy⟩⟩⟩

/-- The start of the final same-band suffix always has Q at least
    (2*P_k-1)/3, whether it is the initial positive state or follows
    a one-band descent. -/
theorem positive_history_final_run_q_lower {j s k x : Nat} {w : Int}
    (hw : 0<w) (h : PositiveHistory j w s k x) :
    ∃ r z, SameRun k r x z ∧
      2*(P k:Int)-1≤3*(Q k z:Int) := by
  obtain ⟨r,z,hs,hbase⟩:=positive_history_final_run h
  refine ⟨r,z,hs,?_⟩
  rcases hbase with ⟨hkj,he⟩ | ⟨s',y,hy,hr⟩
  · subst k
    have hbz:Band j z := (same_run_bands hs).2
    have hq:=q_eq hbz
    have hqI : (Q j z:Int)+2*(P j:Int)=2*(z:Int)+3*(j:Int)+12 := by
      exact_mod_cast hq
    have hWQ : W j z+2*(Q j z:Int)=4*(P j:Int)-3 := by
      unfold W
      omega
    omega
  · have hreg : RegFrom k z y := hr
    have hwreg:=w_regular_down hreg
    obtain ⟨r0,hr0,hz,hyEq⟩:=hreg
    have hbz:Band k z := by rw [hz]; exact regular_band k r0 hr0
    have hby:=positive_history_band hy
    have hqx:=q_eq hbz
    have hqy:=q_eq hby
    have hqxI : (Q k z:Int)+2*(P k:Int)=2*(z:Int)+3*(k:Int)+12 := by
      exact_mod_cast hqx
    have hqyI : (Q (k+1) y:Int)+2*(P (k+1):Int)
        =2*(y:Int)+3*((k+1):Int)+12 := by exact_mod_cast hqy
    have hWQx : W k z+2*(Q k z:Int)=4*(P k:Int)-3 := by
      unfold W
      omega
    have hWQy : W (k+1) y+2*(Q (k+1) y:Int)
        =4*(P (k+1):Int)-3 := by
      unfold W
      omega
    have hpI : (P (k+1):Int)=2*(P k:Int) := by
      exact_mod_cast p_succ k
    have hdownQ :
        3*(Q k z:Int)=(Q (k+1) y:Int)+(P (k+1):Int)-3 := by
      omega
    have hqlo : k+7≤Q (k+1) y := by
      have hqb:=q_bounds hby
      omega
    have hqloI : (k:Int)+7≤(Q (k+1) y:Int) := by exact_mod_cast hqlo
    omega

/-- If a positive history reaches the low boundary, its final same-band
    suffix has length in a narrow logarithmic window. -/
theorem positive_history_boundary_final_run {j s k x : Nat} {w : Int}
    (hw : 0<w) (h : PositiveHistory j w s k x) (hx : x≤P k+2) :
    ∃ r z, SameRun k r x z ∧
      2*P k≤3^(r+1)*(3*k+16)+1 ∧
      3^r*(k+6)≤2*P k+k+2 := by
  obtain ⟨r,z,hs,hstart⟩:=positive_history_final_run_q_lower hw h
  obtain ⟨q,hq,hqlo,hqhi⟩:=boundary_run_divisor hs hx
  have hbz:Band k z:=(same_run_bands hs).2
  have hQzHi : Q k z≤2*P k+k+2 := (q_bounds hbz).2
  have hfirst : 2*P k≤3^(r+1)*(3*k+16)+1 := by
    have hstartI : 2*(P k:Int)≤3*(Q k z:Int)+1 := by omega
    have hqCast : (Q k z:Int)=(3^r:Int)*(q:Int) := by exact_mod_cast hq
    have hpow : 3*(Q k z:Int)=(3^(r+1):Int)*(q:Int) := by
      rw [hqCast,Int.pow_succ]
      simp [Int.mul_assoc,Int.mul_left_comm,Int.mul_comm]
    have hqhiI : (q:Int)≤3*(k:Int)+16 := by exact_mod_cast hqhi
    have hmul : (3^(r+1):Int)*(q:Int)≤
        (3^(r+1):Int)*(3*(k:Int)+16) :=
      Int.mul_le_mul_of_nonneg_left hqhiI
        (Int.le_of_lt (Int.pow_pos (by decide)))
    have hfinalI :
        2*(P k:Int)≤(3^(r+1):Int)*(3*(k:Int)+16)+1 := by
      rw [hpow] at hstartI
      omega
    exact_mod_cast hfinalI
  have hsecond : 3^r*(k+6)≤2*P k+k+2 := by
    have hmulNat:=Nat.mul_le_mul_left (3^r) hqlo
    rw [←hq] at hmulNat
    exact Nat.le_trans hmulNat hQzHi
  exact ⟨r,z,hs,hfirst,hsecond⟩

#print axioms positive_history_final_run
#print axioms positive_history_final_run_q_lower
#print axioms positive_history_boundary_final_run

#print axioms positive_history_packet_weight
#print axioms positive_history_band
#print axioms positive_boundary_cost_sharp

end CapSieve
