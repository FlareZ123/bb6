import CapPhaseCost
import CapPositiveGate

namespace CapSieve

/-- A positive seed weight remains positive throughout every regular
    positive history.  The affine seed equation starts the induction, while
    each regular same-band or down-band edge multiplies W by three. -/
theorem positive_history_W_pos_seed
    {j s k x : Nat} {w : Int}
    (hseedpos : 0<8*(P j:Int)-6-w)
    (h : PositiveHistory j w s k x) :
    0<W k x := by
  induction h with
  | first hb he => omega
  | @same s k x y h hr ih =>
    have hW:=w_regular_same hr
    omega
  | @down s k x y h hr ih =>
    have hW:=w_regular_down hr
    omega

/-- Every down-band edge in a positive history with positive seed weight
    uses exactly the maximal same-band triple run encoded by positiveCount.
    Consequently its next Q-coordinate is the positiveNext recurrence. -/
theorem positive_history_down_is_positiveNext
    {j s k x : Nat} {w : Int}
    (hseedpos : 0<8*(P j:Int)-6-w)
    (h : PositiveHistory j w s k x)
    (hk : k<j) :
    ∃ r z s' y,
      SameRun k r x z ∧
      PositiveHistory j w s' (k+1) y ∧
      RegFrom k z y ∧
      positiveCount k (Q k x)=r ∧
      positiveNext k (Q k x)=Q (k+1) y := by
  obtain ⟨r,z,hs,hcase⟩:=positive_history_final_run_exact h
  rcases hcase with ⟨hkEq,hseed⟩ | ⟨s',y,hy,hr,hlow,hhigh⟩
  · omega
  · have hWposY:=positive_history_W_pos_seed hseedpos hy
    have hWdown:=w_regular_down hr
    have hWposZ : 0<W k z := by omega
    have hbz : Band k z := (same_run_bands hs).2
    have hbX : Band k x := (same_run_bands hs).1
    have hqz:=q_eq hbz
    have hqzI : (Q k z:Int)+2*(P k:Int)
        =2*(z:Int)+3*(k:Int)+12 := by
      exact_mod_cast hqz
    have hWQz : W k z+2*(Q k z:Int)=4*(P k:Int)-3 := by
      unfold W
      omega
    have hqzupperI : (Q k z:Int)≤2*(P k:Int)-2 := by omega
    have hqzupper : Q k z≤2*P k-2 := by
      exact_mod_cast hqzupperI
    have hq : Q k z=3^r*Q k x := same_run_q hs
    have hqPos : 0<Q k x := by
      have hqlo: k+6≤Q k x := (q_bounds hbX).1
      omega
    have hpowPos : 0<3^r := Nat.pow_pos (by decide)
    have hmul := Nat.le_mul_of_pos_left (Q k x) hpowPos
    change Q k x≤3^r*Q k x at hmul
    have hupper : Q k x≤2*P k-2 := by
      calc
        Q k x≤3^r*Q k x := hmul
        _=Q k z := by rw [← hq]
        _≤2*P k-2 := hqzupper
    have hcross : 2*P k-2<3^(r+1)*Q k x := by omega
    have hcount : positiveCount k (Q k x)=r := by
      unfold positiveCount
      apply CapMacro.triple_window_unique hqPos
      · exact CapMacro.tripleCount_spec hqPos (by omega)
      · exact ⟨hupper,hcross⟩
    have hprod : positiveProduct k (Q k x)=3^(r+1)*Q k x := by
      unfold positiveProduct
      rw [hcount]
    have hby : Band (k+1) y := positive_history_band hy
    have hqy:=q_eq hby
    have hqyI : (Q (k+1) y:Int)+2*(P (k+1):Int)
        =2*(y:Int)+3*((k+1):Int)+12 := by
      exact_mod_cast hqy
    have hWQy : W (k+1) y+2*(Q (k+1) y:Int)
        =4*(P (k+1):Int)-3 := by
      unfold W
      omega
    have hpI : (P (k+1):Int)=2*(P k:Int) := by
      exact_mod_cast p_succ k
    have hdownQ :
        3*(Q k z:Int)=(Q (k+1) y:Int)+(P (k+1):Int)-3 := by
      omega
    have hstepBaseI :
        (Q (k+1) y:Int)+2*(P k:Int)=3*(Q k z:Int)+3 := by
      omega
    have hstepBase :
        Q (k+1) y+2*P k=3*Q k z+3 := by
      exact_mod_cast hstepBaseI
    have hstep :
        Q (k+1) y+2*P k=3^(r+1)*Q k x+3 := by
      calc
        _=3*Q k z+3 := hstepBase
        _=3*(3^r*Q k x)+3 := by rw [hq]
        _=(3*3^r)*Q k x+3 := by rw [Nat.mul_assoc]
        _=(3^r*3)*Q k x+3 := by rw [Nat.mul_comm 3 (3^r)]
        _=3^(r+1)*Q k x+3 := by rw [Nat.pow_succ]
    have hnextEq:=positive_next_equation hqPos hupper
    rw [hprod] at hnextEq
    have hnext : positiveNext k (Q k x)=Q (k+1) y := by omega
    exact ⟨r,z,s',y,hs,hy,hr,hcount,hnext⟩

#print axioms positive_history_W_pos_seed
#print axioms positive_history_down_is_positiveNext

end CapSieve
