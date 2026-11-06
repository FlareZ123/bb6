import Lean
namespace BB6.Agent13FixedDepth

/-- Ring identity for a fixed-depth affine inverse potential. -/
private theorem scaled_potential (A h s u z zp : Int)
    (hedge : A*zp=z+h*u) :
    A*((A-1)^2*zp -h*(A-1)*(u+s)+A*h*s) =
    (A-1)^2*z -h*(A-1)*u +A*h*s := by
  have hh := congrArg (fun x:Int => (A-1)^2*x) hedge
  simp only [Int.pow_succ', Int.pow_zero, Int.mul_one, Int.mul_add,
    Int.mul_sub, Int.sub_mul] at *
  simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] at *
  simp only [Int.mul_one] at *
  omega

/-- Nonvanishing follows from a divisibility obstruction modulo A-1. -/
private theorem potential_nonzero (A d h s u z : Int)
    (hA : A=d+1) (h2 : A=2*h)
    (hs : 0 < s) (hlt : s<d) :
    d^2*z -h*d*u+A*h*s ≠ 0 := by
  intro hz
  have heq : A*h*s = d*(h*u-d*z) := by
    simp only [Int.pow_succ', Int.pow_zero, Int.mul_one,
      Int.mul_sub, Int.sub_mul] at *
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] at *
    omega
  have hdA : d ∣ A*h*s := ⟨h*u-d*z, heq⟩
  have hdhs : d ∣ h*s := by
    have hdpart : d ∣ d*(h*s) := Int.dvd_mul_right d (h*s)
    have hh : A*h*s - d*(h*s) = h*s := by
      rw [hA]
      simp only [Int.add_mul, Int.mul_assoc, Int.one_mul]
      omega
    rw [←hh]
    exact Int.dvd_sub hdA hdpart
  have hd2 : d ∣ 2*h*s := by
    have hh : (2:Int)*h*s=2*(h*s) := by simp [Int.mul_assoc]
    rw [hh]
    exact Int.dvd_mul_of_dvd_right hdhs
  have hdpart : d ∣ d*s := Int.dvd_mul_right d s
  have hdiff : 2*h*s-d*s=s := by
    have hdd : d=2*h-1 := by omega
    rw [hdd]
    simp only [Int.sub_mul, Int.mul_assoc, Int.one_mul]
    omega
  have hds : d∣s := by
    rw [←hdiff]
    exact Int.dvd_sub hd2 hdpart
  have hle : d≤s := Int.le_of_dvd hs hds
  omega

private theorem exponent_domination (t : Nat) (ht:1≤t) :
    t+2 < (2:Nat)^(t+1) := by
  cases t with
  | zero => omega
  | succ x =>
    induction x with
    | zero => decide
    | succ x ih =>
      have hp : (2:Nat)^(x+2) > 0 := Nat.pow_pos (by decide)
      have he : (2:Nat)^((x+1)+2) = 2*((2:Nat)^(x+2)) := by
        have h1 : (x+1)+2=(x+2)+1 := by omega
        rw [h1,Nat.pow_succ]
        omega
      omega

/-- Integer obstruction to a run of one fixed positive dyadic depth. -/
def potential (L t m z : Nat) : Int :=
  let h : Int := (↑((2:Nat)^t))
  let A : Int := 2*h
  let d : Int := A-1
  let s : Int := ↑(t+1)
  let u : Int := ↑L+↑m+↑t-1
  d^2*(↑z) -h*d*u+A*h*s

private theorem edge_arithmetic (L t m z v zp : Nat)
    (ht:1≤t) (hdiv:z=2^t*v)
    (hnext:2*zp+1=L+m+t+v) :
    (2*(↑((2:Nat)^t):Int))*(↑zp:Int) =
      (↑z:Int) + (↑((2:Nat)^t):Int)*(↑L+↑m+↑t-1) := by
  let h : Int := ↑((2:Nat)^t)
  have hdiv' : (↑z:Int)=h*(↑v:Int) := by
    dsimp [h]
    exact_mod_cast hdiv
  have hnext' : 2*(↑zp:Int)+1=(↑L:Int)+↑m+↑t+↑v := by
    exact_mod_cast hnext
  have hscale := congrArg (fun x:Int => h*x) hnext'
  dsimp [h] at *
  have hcalc : (↑((2:Nat)^t):Int)*
      (2*(↑zp:Int)+1) = (↑((2:Nat)^t):Int)*
      ((↑L:Int)+↑m+↑t+↑v) := hscale
  simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] at *
  simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul] at *
  simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] at *
  omega

/-- One exact inverse edge at depth t≥1 scales potential by 2^(t+1). -/
theorem potential_step (L t m z v zp : Nat)
    (ht:1≤t) (hdiv:z=2^t*v)
    (hnext:2*zp+1=L+m+t+v) :
    (↑((2:Nat)^(t+1)):Int)*potential L t (m+t+1) zp =
      potential L t m z := by
  let h : Int := ↑((2:Nat)^t)
  let A : Int := 2*h
  let s : Int := ↑(t+1)
  let u : Int := ↑L+↑m+↑t-1
  have ha : (↑((2:Nat)^(t+1)):Int)=A := by
    dsimp [A,h]
    rw [Int.pow_succ']
  have hu : (↑L:Int)+(↑(m+t+1):Int)+↑t-1=u+s := by
    dsimp [u,s]
    omega
  have hed : A*(↑zp:Int)=(↑z:Int)+h*u := by
    exact edge_arithmetic L t m z v zp ht hdiv hnext
  have heq := scaled_potential A h s u (↑z) (↑zp) hed
  have hp0 : potential L t m z =
      (A-1)^2*(↑z:Int) -h*(A-1)*u+A*h*s := rfl
  have hp1 : potential L t (m+t+1) zp =
      (A-1)^2*(↑zp:Int) -h*(A-1)*(u+s)+A*h*s := by
    change (A-1)^2*(↑zp:Int) -h*(A-1)*
      ((↑L:Int)+(↑(m+t+1):Int)+↑t-1)+A*h*s = _
    rw [hu]
  rw [ha, hp0, hp1]
  exact heq

/-- The potential is nonzero at every integer scalar node for depth t≥1. -/
theorem potential_ne_zero (L t m z : Nat) (ht:1≤t) :
    potential L t m z ≠ 0 := by
  let h : Int := ↑((2:Nat)^t)
  let A : Int := 2*h
  let d : Int := A-1
  let s : Int := ↑(t+1)
  let u : Int := ↑L+↑m+↑t-1
  have hp := exponent_domination t ht
  have hpow : (2:Nat)^(t+1)=2*((2:Nat)^t) := by
    rw [show t+1=Nat.succ t by omega, Nat.pow_succ]
    omega
  have hs : 0 < s := by dsimp [s]; omega
  have hlt : s<d := by
    have hboundInt : (↑(t+2):Int) < (↑((2:Nat)^(t+1)):Int) := by
      exact_mod_cast hp
    have hstrong : (↑t:Int)+2 < 2*(2:Int)^t := by
      simpa [Int.natCast_pow, Int.pow_succ'] using hboundInt
    dsimp [s,d,A,h]
    omega
  exact potential_nonzero A d h s u (↑z) (by dsimp [d]; omega)
      rfl hs hlt

/-- Consecutive exact shadow edges, all at the same fixed dyadic depth. -/
inductive RunFixed (L t : Nat) : Nat → Nat → Nat → Prop where
| zero (m z : Nat) : RunFixed L t 0 m z
| more {N m z v zp : Nat} : RunFixed L t N (m+t+1) zp →
    z=2^t*v → 2*zp+1=L+m+t+v → RunFixed L t (N+1) m z

/-- N homogeneous positive-depth edges force 2^((t+1)N) divisibility. -/
theorem pow_dvd_potential (L t N m z : Nat) (ht:1≤t)
    (hr : RunFixed L t N m z) :
    (↑((2:Nat)^(t+1)):Int)^N ∣ potential L t m z := by
  induction hr with
  | zero m z => simp
  | @more N m z v zp hi hdiv hnext ih =>
      rcases ih with ⟨u,hu⟩
      refine ⟨u, ?_⟩
      calc
        potential L t m z =
            (↑((2:Nat)^(t+1)):Int)*potential L t (m+t+1) zp :=
              (potential_step L t m z v zp ht hdiv hnext).symm
        _ = (↑((2:Nat)^(t+1)):Int)*
            ((↑((2:Nat)^(t+1)):Int)^N*u) := by rw [hu]
        _ = (↑((2:Nat)^(t+1)):Int)^(N+1)*u := by
            rw [Int.pow_succ']
            ac_rfl

/-- Finite all-depth homogeneous-run bound from any starting scalar node. -/
theorem run_length_bound (L t N m z : Nat) (ht:1≤t)
    (hr:RunFixed L t N m z) :
    ((2:Nat)^(t+1))^N ≤ (potential L t m z).natAbs := by
  have hd := pow_dvd_potential L t N m z ht hr
  have hn : (((2:Nat)^(t+1))^N) ∣ (potential L t m z).natAbs := by
    have hh := (Int.natAbs_dvd_natAbs).mpr hd
    simpa [Int.natAbs_pow, Int.natAbs_natCast] using hh
  have hp : 0 < (potential L t m z).natAbs :=
    Int.natAbs_pos.mpr (potential_ne_zero L t m z ht)
  exact Nat.le_of_dvd hp hn

private theorem power_growth (A N : Nat) (hA:2≤A) : N < A^N := by
  induction N with
  | zero => simp
  | succ n ih =>
      have hp : 0 < A^n := Nat.pow_pos (by omega)
      have he : 2*(A^n) ≤ (A^n)*A := by
        have h := Nat.mul_le_mul_left (A^n) hA
        omega
      rw [Nat.pow_succ]
      omega

/-- No inverse path starting at one concrete scalar node can repeat any
    fixed positive dyadic depth forever. Mixed depths are not bounded here. -/
theorem no_infinite_fixed_depth (L t m z : Nat) (ht:1≤t)
    (hr : ∀ N : Nat, RunFixed L t N m z) : False := by
  let N := (potential L t m z).natAbs
  have hp := run_length_bound L t (N+1) m z ht (hr (N+1))
  have hh : (2:Nat)≤(2:Nat)^(t+1) := by
    have hpow : (2:Nat)^(t+1) ≥ 2^(1:Nat) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    simpa using hpow
  have hg := power_growth ((2:Nat)^(t+1)) (N+1) hh
  omega

#print axioms potential_step
#print axioms potential_ne_zero
#print axioms run_length_bound
#print axioms no_infinite_fixed_depth
end BB6.Agent13FixedDepth
