import Std
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

namespace NeedleTerminalDichotomy

theorem dvd_pow_sub_pow (a b m : Int) (h : m ∣ a - b) (n : Nat) :
    m ∣ a^n - b^n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : m ∣ a^n * (a-b) := Int.dvd_mul_of_dvd_right h
      have h2 : m ∣ (a^n-b^n) * b := Int.dvd_mul_of_dvd_left ih
      have heq : a^(n+1)-b^(n+1) = a^n*(a-b)+(a^n-b^n)*b := by
        rw [Int.pow_succ, Int.pow_succ]
        simp [Int.mul_sub, Int.mul_comm]
        omega
      rw [heq]
      exact Int.dvd_add h1 h2


theorem nat_sq_le_pow_two (v : Nat) (hv : 4 ≤ v) : v*v ≤ 2^v := by
  have haux : ∀ n : Nat, (n+4)*(n+4) ≤ 2^(n+4) := by
    intro n
    induction n with
    | zero => decide
    | succ n ih =>
      let m := n+4
      have hm3 : 3 ≤ m := by dsimp [m]; omega
      have h3m : 3*m ≤ m*m := Nat.mul_le_mul_right m hm3
      have hlin : 2*m+1 ≤ 3*m := by omega
      have hsum : 2*m+1 ≤ m*m := Nat.le_trans hlin h3m
      have hexp : (m+1)*(m+1) = m*m+(2*m+1) := by
        simp [Nat.mul_add, Nat.add_mul, Nat.two_mul, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm]
      have hsq : (m+1)*(m+1) ≤ 2*(m*m) := by
        calc
          (m+1)*(m+1) = m*m+(2*m+1) := hexp
          _ ≤ m*m+m*m := Nat.add_le_add_left hsum _
          _ = 2*(m*m) := by omega
      have hmul : 2*(m*m) ≤ 2*2^m := Nat.mul_le_mul_left 2 ih
      have hresult : (m+1)*(m+1) ≤ 2^(m+1) := by
        calc
          (m+1)*(m+1) ≤ 2*(m*m) := hsq
          _ ≤ 2*2^m := hmul
          _ = 2^(m+1) := by rw [Nat.pow_succ]; exact Nat.mul_comm _ _
      simpa [m, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hresult
  have hrepr : ∃ n : Nat, v=n+4 := ⟨v-4, by omega⟩
  rcases hrepr with ⟨n,rfl⟩
  exact haux n

theorem neg_three_pow_mod_two (n : Nat) : ((-3:Int)^n) % 2 = 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Int.pow_succ, Int.mul_emod]
      simp [ih]

/-- The quotient/remainder obstruction for every legal terminal feeder. -/
theorem terminal_remainder_dichotomy
    (q v K : Nat) (hv : 2 ≤ v)
    (hfeed : 2^(K+1)+3 = (2^(v+1)+3)*(2*q+3)+2*v) :
    2^v ≤ 3^(((K+1)/(v+1))+1) ∨
      2^((K+1)%(v+1)) < 4*v-6 := by
  let n := (K+1)/(v+1)
  let s := (K+1)%(v+1)
  let t := v-s
  let Dnat := 2^(v+1)+3
  let D : Int := Dnat
  let X : Nat := 3^(n+1)
  let Y : Nat := (2*v-3)*2^(t+1)
  let YI : Int := (2*(v:Int)-3)*(2:Int)^(t+1)
  have hslt : s < v+1 := Nat.mod_lt _ (by omega)
  have hsle : s≤v := Nat.le_of_lt_succ hslt
  have hst : s+t=v := by
    dsimp [t]
    omega
  have hdecomp : K+1=s+(v+1)*n := by
    simpa [n,s] using (Nat.mod_add_div (K+1) (v+1)).symm
  have hbase : D ∣ (2:Int)^(v+1)-(-3:Int) := by
    refine ⟨1, ?_⟩
    simp [D, Dnat, Int.natCast_pow]
  have hpow := dvd_pow_sub_pow ((2:Int)^(v+1)) (-3:Int) D hbase n
  have hpowScaled : D ∣ (2:Int)^s * (((2:Int)^(v+1))^n-(-3:Int)^n) :=
    Int.dvd_mul_of_dvd_right hpow
  have hpower : (2:Int)^(K+1) = (2:Int)^s * ((2:Int)^(v+1))^n := by
    rw [hdecomp, Int.pow_add, Int.pow_mul]
  have hscaled : D ∣ (2:Int)^(K+1) - (2:Int)^s*(-3:Int)^n := by
    have heq : (2:Int)^s*(((2:Int)^(v+1))^n-(-3:Int)^n) =
        (2:Int)^(K+1)-(2:Int)^s*(-3:Int)^n := by
      rw [Int.mul_sub, hpower]
    rw [heq] at hpowScaled
    exact hpowScaled
  have hfeedInt : (2:Int)^(K+1)+3 = D*(2*q+3)+2*v := by
    have hc := congrArg (fun z : Nat => (z:Int)) hfeed
    simpa [D, Dnat, Int.natCast_pow, Int.natCast_add, Int.natCast_mul] using hc
  have hsource : D ∣ (2:Int)^(K+1)+3-2*v := by
    have heq : (2:Int)^(K+1)+3-2*v = D*(2*q+3) := by
      rw [hfeedInt]
      omega
    exact ⟨2*q+3, heq⟩
  have hD : D ∣ (2:Int)^(v+1)+3 := by
    refine ⟨1, ?_⟩
    simp [D, Dnat, Int.natCast_pow]
  have hdiff : D ∣ ((2:Int)^(K+1)+3-2*v)-((2:Int)^(K+1)-(2:Int)^s*(-3:Int)^n) :=
    Int.dvd_sub hsource hscaled
  have hdiffEq :
      ((2:Int)^(K+1)+3-2*v)-((2:Int)^(K+1)-(2:Int)^s*(-3:Int)^n) =
        (2:Int)^s*(-3:Int)^n+3-2*v := by
    omega
  have hsourceSmall : D ∣ (2:Int)^s*(-3:Int)^n+3-2*v := by
    rw [←hdiffEq]
    exact hdiff
  have hsourceScaled : D ∣ ((2:Int)^s*(-3:Int)^n+3-2*v)*(2:Int)^(t+1) := by
    exact Int.dvd_mul_of_dvd_left hsourceSmall
  have hfirst : D ∣ (-3:Int)^n*((2:Int)^(v+1)+3) :=
    Int.dvd_mul_of_dvd_right hD
  have hres : D ∣ (-3:Int)^(n+1)-YI := by
    have hsum : D ∣
        (((2:Int)^s*(-3:Int)^n+3-2*v)*(2:Int)^(t+1)) -
        ((-3:Int)^n*((2:Int)^(v+1)+3)) :=
      Int.dvd_sub hsourceScaled hfirst
    have hpow2 : (2:Int)^s*(2:Int)^(t+1)=(2:Int)^(v+1) := by
      calc
        (2:Int)^s*(2:Int)^(t+1)=(2:Int)^(s+(t+1)) := by rw [←Int.pow_add]
        _=(2:Int)^(v+1) := by congr 1; omega
    have hY : YI=(2*(v:Int)-3)*(2:Int)^(t+1) := rfl
    have heq :
        (((2:Int)^s*(-3:Int)^n+3-2*v)*(2:Int)^(t+1)) -
        ((-3:Int)^n*((2:Int)^(v+1)+3)) =
        (-3:Int)^(n+1)-YI := by
      calc
        (((2:Int)^s*(-3:Int)^n+3-2*v)*(2:Int)^(t+1)) -
            ((-3:Int)^n*((2:Int)^(v+1)+3))
          = (-3:Int)^n*((2:Int)^s*(2:Int)^(t+1)) +
              (3-2*(v:Int))*(2:Int)^(t+1) -
              (-3:Int)^n*(2:Int)^(v+1) - 3*(-3:Int)^n := by
                simp [Int.add_mul, Int.sub_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
                omega
        _ = (3-2*(v:Int))*(2:Int)^(t+1) - 3*(-3:Int)^n := by rw [hpow2]; omega
        _ = (-3:Int)^(n+1)-YI := by
              have hcoef : (3:Int)-2*(v:Int)=-(2*(v:Int)-3) := by omega
              rw [Int.pow_succ, hcoef, hY]
              simp [Int.pow_succ, Int.neg_mul, Int.mul_neg, Int.mul_comm, Int.mul_left_comm]
              omega
    rw [heq] at hsum
    exact hsum
  by_cases hX : X < 2^v
  · by_cases hS : 2^s < 4*v-6
    · exact Or.inr hS
    · have hS' : 2*(2*v-3) ≤ 2^s := by omega
      have hmul : (2*(2*v-3))*2^t ≤2^s*2^t := Nat.mul_le_mul_right (2^t) hS'
      have hYle : Y ≤2^v := by
        dsimp [Y]
        calc
          (2*v-3)*2^(t+1) = (2*(2*v-3))*2^t := by
            rw [Nat.pow_succ]
            simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          _ ≤ 2^s*2^t := hmul
          _ = 2^v := by
            rw [←Nat.pow_add]
            congr 1
      have hsum : X+Y < Dnat := by
        have hpow : 2^v+2^v=2^(v+1) := by rw [Nat.pow_succ]; omega
        have hsmall : X+Y < 2^v+2^v := by omega
        calc
          X+Y < 2^v+2^v := hsmall
          _ = 2^(v+1) := hpow
          _ < Dnat := by dsimp [Dnat]; omega
      have hXabs : ((-3:Int)^(n+1)).natAbs=X := by
        simp [X, Int.natAbs_pow]
      have hYabs : YI.natAbs=Y := by
        have hnonneg : (0:Int) ≤ 2*(v:Int)-3 := by omega
        have hcast : (2*v-3 : Nat) = (2*(v:Int)-3) := by
          rw [Int.natCast_sub (by omega)]
          simp
        have hfactor : ((2*(v:Int)-3).natAbs : Int) = (2*v-3 : Nat) := by
          simpa [hcast] using Int.natAbs_of_nonneg hnonneg
        have hfactorNat : (2*(v:Int)-3).natAbs = 2*v-3 := Int.natCast_inj.mp hfactor
        simp [YI, Y, Int.natAbs_mul, Int.natAbs_pow, hfactorNat]
      have hzabs : ((-3:Int)^(n+1)-YI).natAbs < Dnat := by
        calc
          ((-3:Int)^(n+1)-YI).natAbs ≤ ((-3:Int)^(n+1)).natAbs+YI.natAbs :=
            Int.natAbs_sub_le _ _
          _=X+Y := by rw [hXabs,hYabs]
          _<Dnat := hsum
      have hDabs : D.natAbs=Dnat := by simp [D]
      rcases hres with ⟨c,hc⟩
      have hmulabs : ((-3:Int)^(n+1)-YI).natAbs=Dnat*c.natAbs := by
        rw [hc, Int.natAbs_mul, hDabs]
      have hDpos : 0<Dnat := by dsimp [Dnat]; omega
      have hc0 : c.natAbs=0 := by
        by_cases hcne : c.natAbs=0
        · exact hcne
        · have hcpos : 1≤c.natAbs := Nat.one_le_iff_ne_zero.mpr hcne
          have hle : Dnat ≤ Dnat*c.natAbs := by
            calc
              Dnat = Dnat*1 := by omega
              _ ≤ Dnat*c.natAbs := Nat.mul_le_mul_left Dnat hcpos
          omega
      have hz0 : (-3:Int)^(n+1)-YI=0 := by
        apply Int.natAbs_eq_zero.mp
        rw [hmulabs,hc0]
        simp
      have hpowmod := neg_three_pow_mod_two (n+1)
      have hYmod : YI%2=0 := by
        have hfactor : YI=((2*(v:Int)-3)*(2:Int)^t)*2 := by
          simp [YI, Int.pow_succ, Int.mul_comm, Int.mul_left_comm]
        rw [hfactor, Int.mul_emod]
        simp
      have hEq : (-3:Int)^(n+1)=YI := Int.sub_eq_zero.mp hz0
      have hmod := congrArg (fun z : Int => z%2) hEq
      rw [hpowmod,hYmod] at hmod
      simp at hmod
  · exact Or.inl (Nat.le_of_not_gt (by simpa [X,n] using hX))


theorem pow3_lt_pow2_of (n v : Nat) (h : 8*(n+1) ≤ 5*v) : 3^(n+1) < 2^v := by
  have hbase : 3^5 < 2^8 := by decide
  have hpow : (3^5)^(n+1) < (2^8)^(n+1) :=
    Nat.pow_lt_pow_left hbase (by omega)
  have hpow' : 3^(5*(n+1)) < 2^(8*(n+1)) := by
    calc
      3^(5*(n+1)) = (3^5)^(n+1) := by rw [Nat.pow_mul]
      _ < (2^8)^(n+1) := hpow
      _ = 2^(8*(n+1)) := by rw [Nat.pow_mul]
  have hpow2 : 2^(8*(n+1)) ≤ 2^(5*v) :=
    Nat.pow_le_pow_right (by decide : 2>0) h
  have hleft : (3^(n+1))^5 = 3^(5*(n+1)) := by
    rw [←Nat.pow_mul]
    congr 1
    omega
  have hright : (2^v)^5 = 2^(5*v) := by
    rw [←Nat.pow_mul]
    congr 1
    omega
  have hfinal : (3^(n+1))^5 < (2^v)^5 := by
    calc
      (3^(n+1))^5 = 3^(5*(n+1)) := hleft
      _ < 2^(8*(n+1)) := hpow'
      _ ≤ 2^(5*v) := hpow2
      _ = (2^v)^5 := hright.symm
  exact (Nat.pow_lt_pow_iff_left (by decide : 5 ≠ 0)).mp hfinal

/-- A terminal feeder either has quadratic-scale valuation or a logarithmically
    small remainder in the quotient by v+1. -/
theorem terminal_quadratic_or_small_remainder
    (q v K : Nat) (hv : 2 ≤ v)
    (hfeed : 2^(K+1)+3 = (2^(v+1)+3)*(2*q+3)+2*v) :
    8*(K+1) > (5*v-8)*(v+1) ∨
      2^((K+1)%(v+1)) < 4*v-6 := by
  let n := (K+1)/(v+1)
  let s := (K+1)%(v+1)
  have hdecomp : K+1=s+(v+1)*n := by
    simpa [n,s] using (Nat.mod_add_div (K+1) (v+1)).symm
  rcases terminal_remainder_dichotomy q v K hv hfeed with hhigh | hsmall
  · have hhigh' : 2^v ≤ 3^(n+1) := by simpa [n] using hhigh
    have hratio : 5*v < 8*(n+1) := by
      by_cases hnot : 8*(n+1) ≤ 5*v
      · have hbad := pow3_lt_pow2_of n v hnot
        omega
      · omega
    have hratio' : 5*v-8 < 8*n := by omega
    have hmul : (5*v-8)*(v+1) < (8*n)*(v+1) :=
      Nat.mul_lt_mul_of_pos_right hratio' (by omega)
    have hK : n*(v+1) ≤ K+1 := by
      rw [hdecomp]
      calc
        n*(v+1) = (v+1)*n := Nat.mul_comm _ _
        _ ≤ s+(v+1)*n := Nat.le_add_left _ _
    have hmulK : (8*n)*(v+1) ≤ 8*(K+1) := by
      calc
        (8*n)*(v+1) = 8*(n*(v+1)) := by simp [Nat.mul_assoc]
        _ ≤ 8*(K+1) := Nat.mul_le_mul_left 8 hK
    exact Or.inl (Nat.lt_of_lt_of_le hmul hmulK)
  · exact Or.inr hsmall


/-- Exact divisibility of the quotient-remainder residue. -/
theorem terminal_residue_dvd
    (q v K : Nat)
    (hfeed : 2^(K+1)+3 = (2^(v+1)+3)*(2*q+3)+2*v) :
    (2^(v+1)+3 : Int) ∣
      (2:Int)^((K+1)%(v+1)) * (-3:Int)^((K+1)/(v+1)) + 3 - 2*v := by
  let n := (K+1)/(v+1)
  let s := (K+1)%(v+1)
  let Dnat := 2^(v+1)+3
  let D : Int := Dnat
  have hdecomp : K+1=s+(v+1)*n := by
    simpa [n,s] using (Nat.mod_add_div (K+1) (v+1)).symm
  have hbase : D ∣ (2:Int)^(v+1)-(-3:Int) := by
    refine ⟨1, ?_⟩
    simp [D, Dnat, Int.natCast_pow]
  have hpow := dvd_pow_sub_pow ((2:Int)^(v+1)) (-3:Int) D hbase n
  have hpowScaled : D ∣ (2:Int)^s * (((2:Int)^(v+1))^n-(-3:Int)^n) :=
    Int.dvd_mul_of_dvd_right hpow
  have hpower : (2:Int)^(K+1) = (2:Int)^s * ((2:Int)^(v+1))^n := by
    rw [hdecomp, Int.pow_add, Int.pow_mul]
  have hscaled : D ∣ (2:Int)^(K+1) - (2:Int)^s*(-3:Int)^n := by
    have heq : (2:Int)^s*(((2:Int)^(v+1))^n-(-3:Int)^n) =
        (2:Int)^(K+1)-(2:Int)^s*(-3:Int)^n := by
      rw [Int.mul_sub, hpower]
    rw [heq] at hpowScaled
    exact hpowScaled
  have hfeedInt : (2:Int)^(K+1)+3 = D*(2*q+3)+2*v := by
    have hc := congrArg (fun z : Nat => (z:Int)) hfeed
    simpa [D, Dnat, Int.natCast_pow, Int.natCast_add, Int.natCast_mul] using hc
  have hsource : D ∣ (2:Int)^(K+1)+3-2*v := by
    have heq : (2:Int)^(K+1)+3-2*v = D*(2*q+3) := by
      rw [hfeedInt]
      omega
    exact ⟨2*q+3, heq⟩
  have hdiff : D ∣ ((2:Int)^(K+1)+3-2*v)-((2:Int)^(K+1)-(2:Int)^s*(-3:Int)^n) :=
    Int.dvd_sub hsource hscaled
  have hdiffEq :
      ((2:Int)^(K+1)+3-2*v)-((2:Int)^(K+1)-(2:Int)^s*(-3:Int)^n) =
        (2:Int)^s*(-3:Int)^n+3-2*v := by
    omega
  have hsourceSmall : D ∣ (2:Int)^s*(-3:Int)^n+3-2*v := by
    rw [←hdiffEq]
    exact hdiff
  simpa [D,Dnat,n,s] using hsourceSmall

/-- A terminal feeder either has exact cancellation in the residue, or its
    absolute residue is at least the terminal modulus. -/
theorem terminal_cancellation_or_magnitude
    (q v K : Nat) (hv : 2 ≤ v)
    (hfeed : 2^(K+1)+3 = (2^(v+1)+3)*(2*q+3)+2*v) :
    ((2:Int)^((K+1)%(v+1)) * (-3:Int)^((K+1)/(v+1)) + 3 - 2*v = 0) ∨
      3^((K+1)/(v+1))*2^((K+1)%(v+1))+2*v ≥ 2^(v+1) := by
  let n := (K+1)/(v+1)
  let s := (K+1)%(v+1)
  let Dnat := 2^(v+1)+3
  let D : Int := Dnat
  let AI : Int := (2:Int)^s*(-3:Int)^n
  let BI : Int := 2*(v:Int)-3
  let ZI : Int := AI+3-2*v
  have hres : D ∣ ZI := by
    simpa [D,Dnat,AI,ZI,n,s,Int.sub_eq_add_neg] using
      terminal_residue_dvd q v K hfeed
  by_cases hzero : ZI=0
  · exact Or.inl (by simpa [ZI,AI,n,s,Int.sub_eq_add_neg] using hzero)
  · have hDabs : D.natAbs=Dnat := by simp [D]
    have hAabs : AI.natAbs=3^n*2^s := by
      simp [AI,Int.natAbs_mul,Int.natAbs_pow,Nat.mul_comm]
    have hBabs : BI.natAbs=2*v-3 := by
      have hnonneg : (0:Int)≤2*(v:Int)-3 := by omega
      have hcast : (2*v-3 : Nat) = (2*(v:Int)-3) := by
        rw [Int.natCast_sub (by omega)]
        simp
      have hfactor : ((2*(v:Int)-3).natAbs : Int)=(2*v-3 : Nat) := by
        simpa [hcast] using Int.natAbs_of_nonneg hnonneg
      exact Int.natCast_inj.mp hfactor
    rcases hres with ⟨c,hc⟩
    have hcpos : 1≤c.natAbs := by
      by_cases hc0 : c.natAbs=0
      · have hcInt : c=0 := Int.natAbs_eq_zero.mp hc0
        subst c
        simp at hc
        exact False.elim (hzero hc)
      · exact Nat.one_le_iff_ne_zero.mpr hc0
    have hmulabs : ZI.natAbs=Dnat*c.natAbs := by
      rw [hc,Int.natAbs_mul,hDabs]
    have hDle : Dnat≤ZI.natAbs := by
      calc
        Dnat=Dnat*1 := by simp
        _≤Dnat*c.natAbs := Nat.mul_le_mul_left Dnat hcpos
        _=ZI.natAbs := hmulabs.symm
    have hZIeq : ZI=AI-BI := by dsimp [ZI,BI]; omega
    have hZupper : ZI.natAbs≤3^n*2^s+2*v := by
      rw [hZIeq]
      calc
        (AI-BI).natAbs≤AI.natAbs+BI.natAbs := Int.natAbs_sub_le _ _
        _=3^n*2^s+(2*v-3) := by rw [hAabs,hBabs]
        _≤3^n*2^s+2*v := Nat.add_le_add_left (by omega) _
    have hcombined : Dnat≤3^n*2^s+2*v := Nat.le_trans hDle hZupper
    have hDle' : 2^(v+1)≤Dnat := by
      dsimp [Dnat]
      exact Nat.le_add_right _ _
    exact Or.inr (Nat.le_trans hDle' hcombined)


/-- Every non-cancelling terminal feeder with valuation at least eleven has
    quadratic-scale exponent: v^2 ≤ 8(K+1). -/
theorem terminal_valuation_square_bound
    (q v K : Nat) (hv : 11 ≤ v)
    (hfeed : 2^(K+1)+3 = (2^(v+1)+3)*(2*q+3)+2*v)
    (hnoCancel :
      ¬ ((2:Int)^((K+1)%(v+1)) * (-3:Int)^((K+1)/(v+1)) + 3 - 2*v = 0)) :
    v*v ≤ 8*(K+1) := by
  let n := (K+1)/(v+1)
  let s := (K+1)%(v+1)
  have hdecomp : K+1=s+(v+1)*n := by
    simpa [n,s] using (Nat.mod_add_div (K+1) (v+1)).symm
  have hK : n*(v+1)≤K+1 := by
    rw [hdecomp]
    calc
      n*(v+1)=(v+1)*n := Nat.mul_comm _ _
      _≤s+(v+1)*n := Nat.le_add_left _ _
  have hmagOrZero := terminal_cancellation_or_magnitude q v K (by omega) hfeed
  have hmag : 3^n*2^s+2*v≥2^(v+1) := by
    rcases hmagOrZero with hzero | hmag
    · exact False.elim (hnoCancel (by simpa [n,s] using hzero))
    · simpa [n,s] using hmag
  rcases terminal_remainder_dichotomy q v K (by omega) hfeed with hhigh | hsmall
  · have h3lt4 : 3^(n+1)<4^(n+1) :=
      Nat.pow_lt_pow_left (by decide : 3<4) (Nat.succ_ne_zero n)
    have h4pow : 4^(n+1)=2^(2*(n+1)) := by
      have hfour : 4=2^2 := by decide
      calc
        4^(n+1)=(2^2)^(n+1) := by rw [hfour]
        _=2^(2*(n+1)) := by rw [Nat.pow_mul]
    have hpow : 2^v<2^(2*(n+1)) := by
      calc
        2^v≤3^(n+1) := by simpa [n] using hhigh
        _<4^(n+1) := h3lt4
        _=2^(2*(n+1)) := h4pow
    have hexp : v<2*(n+1) := by
      by_cases hlt : v<2*(n+1)
      · exact hlt
      · have hle : 2*(n+1)≤v := Nat.le_of_not_gt hlt
        have hpowle : 2^(2*(n+1))≤2^v := Nat.pow_le_pow_right (by decide : 2>0) hle
        exact False.elim ((Nat.not_lt_of_ge hpowle) hpow)
    have hn : 1≤n := by omega
    have hv4n : v≤4*n := by omega
    have hquad : v*v≤4*(K+1) := by
      have h1 : v*v≤v*(v+1) := Nat.mul_le_mul_left v (by omega)
      have h2 : v*(v+1)≤(4*n)*(v+1) := Nat.mul_le_mul_right (v+1) hv4n
      have h3 : (4*n)*(v+1)≤4*(K+1) := by
        calc
          (4*n)*(v+1)=4*(n*(v+1)) := by simp [Nat.mul_assoc]
          _≤4*(K+1) := Nat.mul_le_mul_left 4 hK
      exact Nat.le_trans h1 (Nat.le_trans h2 h3)
    exact Nat.le_trans hquad (Nat.mul_le_mul_right (K+1) (by decide : 4≤8))
  · have hsmall' : 2^s<4*v :=
      Nat.lt_of_lt_of_le hsmall (by omega)
    have hsq : v*v≤2^v := nat_sq_le_pow_two v (by omega)
    have h2v : 2*v≤2^v := by
      calc
        2*v≤v*v := Nat.mul_le_mul_right v (by omega)
        _≤2^v := hsq
    have hA_lt : 3^n*2^s <3^n*(4*v) :=
      Nat.mul_lt_mul_of_pos_left hsmall' (Nat.pow_pos (by decide))
    have hplus : 2^(v+1)<3^n*(4*v)+2*v :=
      Nat.lt_of_le_of_lt hmag (Nat.add_lt_add_right hA_lt (2*v))
    have hpowSucc : 2^(v+1)=2^v*2 := by rw [Nat.pow_succ]
    have hproduct : 2^v<3^n*(4*v) := by
      rw [hpowSucc] at hplus
      omega
    have h4v : 4*v≤2^v := by
      calc
        4*v≤v*v := Nat.mul_le_mul_right v (by omega)
        _≤2^v := hsq
    have hn : 1≤n := by
      by_cases hn0 : n=0
      · have hdivzero : (K+1)/(v+1)=0 := by simpa [n] using hn0
        have hprod0 : 2^v<4*v := by simpa [n,hdivzero] using hproduct
        omega
      · exact Nat.one_le_iff_ne_zero.mpr hn0
    have h3lt4 : 3^n<4^n := Nat.pow_lt_pow_left (by decide : 3<4) (Nat.ne_of_gt hn)
    have h4pow : 4^n=2^(2*n) := by
      have hfour : 4=2^2 := by decide
      calc
        4^n=(2^2)^n := by rw [hfour]
        _=2^(2*n) := by rw [Nat.pow_mul]
    have h3pow : 3^n<2^(2*n) := by rw [←h4pow]; exact h3lt4
    have hproductSq : 2^(2*v)<(3^n*(4*v))^2 := by
      have h := Nat.pow_lt_pow_left hproduct (by decide : 2≠0)
      have hleft : 2^(2*v)=(2^v)^2 := by
        rw [←Nat.pow_mul]
        congr 1
        omega
      rw [hleft]
      exact h
    have h3sq : (3^n)^2<2^(4*n) := by
      calc
        (3^n)^2<(4^n)^2 := Nat.pow_lt_pow_left h3lt4 (by decide : 2≠0)
        _=(2^(2*n))^2 := by rw [h4pow]
        _=2^(4*n) := by
          rw [←Nat.pow_mul]
          congr 1
          omega
    have h4vsq : (4*v)^2≤2^(v+4) := by
      calc
        (4*v)^2=4^2*v^2 := Nat.mul_pow _ _ _
        _=16*(v*v) := by simp [Nat.pow_two]
        _≤16*2^v := Nat.mul_le_mul_left 16 hsq
        _=2^(v+4) := by
          rw [Nat.pow_add]
          simp [Nat.mul_comm]
    have hprodUpper : (3^n*(4*v))^2≤2^(4*n+v+4) := by
      calc
        (3^n*(4*v))^2=(3^n)^2*(4*v)^2 := Nat.mul_pow _ _ _
        _≤2^(4*n)*2^(v+4) := Nat.mul_le_mul (Nat.le_of_lt h3sq) h4vsq
        _=2^(4*n+v+4) := by
          rw [←Nat.pow_add]
          congr 1
    have hboundExp : 2*v<4*n+v+4 := by
      have hpowCompare := Nat.lt_of_lt_of_le hproductSq hprodUpper
      by_cases hlt : 2*v<4*n+v+4
      · exact hlt
      · have hle : 4*n+v+4≤2*v := Nat.le_of_not_gt hlt
        have hpowle : 2^(4*n+v+4)≤2^(2*v) := Nat.pow_le_pow_right (by decide : 2>0) hle
        exact False.elim ((Nat.not_lt_of_ge hpowle) hpowCompare)
    have hnBound : v≤4*n+3 := by omega
    have hhalf : v≤2*(v-3) := by omega
    have hprod : v*(v+1)≤2*(v-3)*(v+1) := by
      calc
        v*(v+1)≤(2*(v-3))*(v+1) := Nat.mul_le_mul_right (v+1) hhalf
        _=2*(v-3)*(v+1) := by simp [Nat.mul_assoc]
    have hprodK : 2*(v-3)*(v+1)≤8*(K+1) := by
      calc
        2*(v-3)*(v+1)≤8*n*(v+1) := by
          have hcoef : 2*(v-3)≤8*n := by omega
          have hmul := Nat.mul_le_mul_right (v+1) hcoef
          simpa [Nat.mul_assoc] using hmul
        _=8*(n*(v+1)) := by simp [Nat.mul_assoc]
        _≤8*(K+1) := Nat.mul_le_mul_left 8 hK
    have hsqK : v*v≤8*(K+1) := by
      calc
        v*v≤v*(v+1) := Nat.mul_le_mul_left v (by omega)
        _≤2*(v-3)*(v+1) := hprod
        _≤8*(K+1) := hprodK
    exact hsqK


/-- Exact cancellation is precisely the synthetic feeder family. -/
theorem terminal_cancellation_classification
    (v n s : Nat) (hv : 2 ≤ v)
    (hzero : (2:Int)^s * (-3:Int)^n + 3 - 2*v = 0) :
    s=0 ∧ n%2=0 ∧ 2*v=3^n+3 := by
  have hAI : (2:Int)^s*(-3:Int)^n=2*(v:Int)-3 := by
    have h : (2:Int)^s*(-3:Int)^n+3-2*v=0 := hzero
    omega
  rcases Nat.mod_two_eq_zero_or_one n with heven | hodd
  · have hnegpow : (-3:Int)^n=(3:Int)^n := by
      rw [Int.neg_pow,heven]
      simp
    have hEqInt : (2:Int)^s*(3:Int)^n=2*(v:Int)-3 := by
      rw [hnegpow] at hAI
      exact hAI
    have hcast : (2*v-3 : Nat) = (2*(v:Int)-3) := by
      rw [Int.natCast_sub (by omega)]
      simp
    have hEqIntNat : ((2^s*3^n : Nat):Int)=(2*v-3 : Nat) := by
      rw [Int.natCast_mul,Int.natCast_pow,Int.natCast_pow,hcast]
      exact hEqInt
    have hEqNat : 2^s*3^n=2*v-3 := Int.natCast_inj.mp hEqIntNat
    have hRmod : (2*v-3)%2=1 := by
      have heq : 2*v-3=2*(v-2)+1 := by omega
      rw [heq,Nat.add_mod,Nat.mul_mod]
      simp
    have hs0 : s=0 := by
      by_cases hs : s=0
      · exact hs
      · rcases Nat.exists_eq_succ_of_ne_zero hs with ⟨r,hsucc⟩
        have hleft : (2^(r+1)*3^n)%2=0 := by
          rw [Nat.pow_succ,Nat.mul_mod]
          simp
        have hmod := congrArg (fun z : Nat => z%2) hEqNat
        rw [hsucc] at hmod
        rw [hleft,hRmod] at hmod
        omega
    have hfinal : 3^n=2*v-3 := by simpa [hs0] using hEqNat
    have hfinal' : 2*v=3^n+3 := by
      calc
        2*v=(2*v-3)+3 := by omega
        _=3^n+3 := by rw [hfinal]
    exact ⟨hs0,heven,hfinal'⟩
  · have hnegpow : (-3:Int)^n=-(3:Int)^n := by
      rw [Int.neg_pow,hodd]
      simp
    have hAI' : (2:Int)^s * -(3:Int)^n=2*(v:Int)-3 := by
      rw [hnegpow] at hAI
      exact hAI
    have hpos2 : (0:Int)<(2:Int)^s := Int.pow_pos (by decide)
    have hpos3 : (0:Int)<(3:Int)^n := Int.pow_pos (by decide)
    have hprodpos : (0:Int)<(2:Int)^s*(3:Int)^n := Int.mul_pos hpos2 hpos3
    have hleft : (2:Int)^s * -(3:Int)^n<0 := by
      rw [Int.mul_neg]
      exact Int.neg_neg_of_pos hprodpos
    have hnat : 0<2*v-3 := by omega
    have hcast : (2*v-3 : Nat) = (2*(v:Int)-3) := by
      rw [Int.natCast_sub (by omega)]
      simp
    have hright : (0:Int)<(2*v-3 : Nat) := Int.natCast_pos.mpr hnat
    have hAI'' : (2:Int)^s * -(3:Int)^n=(2*v-3 : Nat) := by
      rw [hcast]
      exact hAI'
    omega

/-- Main search consequence: apart from the exact synthetic cancellation
    family, every terminal feeder with v≥11 has v≤sqrt(8(K+1)). -/
theorem terminal_exception_or_square_bound
    (q v K : Nat) (hv : 11 ≤ v)
    (hfeed : 2^(K+1)+3 = (2^(v+1)+3)*(2*q+3)+2*v) :
    ((K+1)%(v+1)=0 ∧ ((K+1)/(v+1))%2=0 ∧
      2*v=3^((K+1)/(v+1))+3) ∨ v*v≤8*(K+1) := by
  let n := (K+1)/(v+1)
  let s := (K+1)%(v+1)
  by_cases hzero : (2:Int)^s*(-3:Int)^n+3-2*v=0
  · have hclass := terminal_cancellation_classification v n s (by omega) (by simpa [n,s] using hzero)
    exact Or.inl (by simpa [n,s] using hclass)
  · exact Or.inr (terminal_valuation_square_bound q v K hv hfeed (by simpa [n,s] using hzero))

end NeedleTerminalDichotomy
