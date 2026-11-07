import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
namespace BB6.Agent48.FifthHigh

def den (v : Nat) : Nat := (2:Nat)^(v+1)+3
def bias (v : Nat) : Nat := 3*(2:Nat)^v+v+3
def equation (q v K : Nat) : Prop := den v*q + bias v=(2:Nat)^K

private theorem fourth_poly (x y : Nat) :
    y*(x*x*x*x) + (x+3)*(y*(3*x*x+27)) =
    (x+3)*(y*(x*x*x+9*x)) + 81*y := by
  simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  ac_rfl

private theorem power_formula (v s : Nat) :
    2*(2:Nat)^(4*v+3+s) = (2:Nat)^s*((2:Nat)^(v+1))^4 := by
  have h : 4*v+4+s = s+4*(v+1) := by omega
  have hp : 2*(2:Nat)^(4*v+3+s)=(2:Nat)^(4*v+4+s) := by
    have ht : 4*v+4+s = (4*v+3+s)+1 := by omega
    rw [ht,Nat.pow_succ']
  rw [hp,h,Nat.pow_add]
  have ht : (2:Nat)^(4*(v+1)) = ((2:Nat)^(v+1))^4 := by
    rw [Nat.mul_comm 4 (v+1), Nat.pow_mul]
  rw [ht]

private theorem high_mod (q v s : Nat)
    (h : equation q v (4*v+3+s)) :
    (2*v) % den v = (81*(2:Nat)^s+3) % den v := by
  let x : Nat := (2:Nat)^(v+1)
  let z : Nat := (2:Nat)^v
  let y : Nat := (2:Nat)^s
  let D : Nat := x+3
  have hx : x=2*z := by
    dsimp [x,z]
    rw [Nat.pow_succ']
  have hp : 2*(2:Nat)^(4*v+3+s)=y*x^4 := by
    simpa only [x,y] using power_formula v s
  have he0 : D*q+3*z+v+3=(2:Nat)^(4*v+3+s) := by
    simpa only [equation,den,bias,D,x,z,Nat.add_assoc] using h
  have he : y*x^4 = D*(2*q)+3*x+2*v+6 := by
    rw [←hp]
    rw [←he0]
    rw [hx]
    simp only [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hpoly : y*x^4 + D*(y*(3*x*x+27)) =
      D*(y*(x*x*x+9*x))+81*y := by
    simpa only [D, Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.one_mul, Nat.mul_assoc] using fourth_poly x y
  have hcore : D*(2*q+y*(3*x*x+27)+3)+2*v =
      D*(y*(x*x*x+9*x)) +81*y+3 := by
    calc
      D*(2*q+y*(3*x*x+27)+3)+2*v =
          y*x^4 + D*(y*(3*x*x+27))+3 := by
        rw [he]
        simp only [Nat.mul_add]
        omega
      _ = D*(y*(x*x*x+9*x)) +81*y+3 := by rw [hpoly]
  have hm := congrArg (fun a : Nat => a % D) hcore
  have hmod : (2*v)%D = (81*y+3)%D := by
    simpa [Nat.add_mod,Nat.mul_mod] using hm
  simpa only [den,D,x,y] using hmod

private theorem double_le_pow (v : Nat) (hv : 2 ≤ v) :
    2*v ≤ (2:Nat)^v := by
  have h : ∀ n : Nat, 2*(2+n) ≤ (2:Nat)^(2+n) := by
    intro n
    induction n with
    | zero => decide
    | succ n ih =>
      have hp : 2 ≤ (2:Nat)^(2+n) := by
        have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (by omega : 1≤2+n)
        simpa using hh
      have he : (2:Nat)^(2+(n+1))=2*((2:Nat)^(2+n)) := by
        have hh : 2+(n+1)=(2+n)+1 := by omega
        rw [hh,Nat.pow_succ']
      rw [he]
      omega
  have ha : 2+(v-2)=v := by omega
  simpa only [ha] using h (v-2)

/-- Exact one-step fifth-linear wall on the high-exponent side, with an isolated large witness. -/
theorem high_fifth_bound (q v s : Nat)
    (heq : equation q v (4*v+3+s)) :
    v ≤ s+6 ∨ (s=0 ∧ v=42) := by
  by_cases hv : v ≤ s+6
  · exact Or.inl hv
  · have hvlarge : s+7 ≤ v := by omega
    have h2v : 2*v ≤ (2:Nat)^v := double_le_pow v (by omega)
    have hpow : (2:Nat)^(v+1)=2*((2:Nat)^v) := by rw [Nat.pow_succ']
    have hD : 2*v < den v := by
      unfold den
      rw [hpow]
      omega
    have hge : (2:Nat)^(s+8) ≤ (2:Nat)^(v+1) :=
      Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (by omega)
    have hp2 : (2:Nat)^(s+8)=256*((2:Nat)^s) := by
      have hswap : s+8=8+s := by omega
      rw [hswap,Nat.pow_add]
    have hy : 0 < (2:Nat)^s := Nat.pow_pos (by decide)
    have hC : 81*(2:Nat)^s+3 < den v := by
      unfold den
      rw [hp2] at hge
      omega
    have hm := high_mod q v s heq
    rw [Nat.mod_eq_of_lt hD, Nat.mod_eq_of_lt hC] at hm
    right
    cases s with
    | zero =>
      simp at hm
      omega
    | succ s =>
      rw [Nat.pow_succ'] at hm
      omega

/-- A finite-width lower-side congruence: t powers close a fourth-power block. -/
private theorem near_mod (q v K t : Nat)
    (h : equation q v K) (ht : 1 ≤ t) (hKt : K+t=4*v+4) :
    ((2:Nat)^t*v) % den v = (81+3*(2:Nat)^(t-1)) % den v := by
  let x : Nat := (2:Nat)^(v+1)
  let z : Nat := (2:Nat)^v
  let y : Nat := (2:Nat)^t
  let w : Nat := (2:Nat)^(t-1)
  let D : Nat := x+3
  have hx : x=2*z := by
    dsimp [x,z]
    rw [Nat.pow_succ']
  have hy : y=2*w := by
    dsimp [y,w]
    have htw : t-1+1=t := by omega
    calc
      (2:Nat)^t = (2:Nat)^((t-1)+1) := by congr 1; omega
      _ = 2*(2:Nat)^(t-1) := by rw [Nat.pow_succ']
  have hp : y*(2:Nat)^K=x^4 := by
    dsimp [y,x]
    rw [←Nat.pow_add]
    have hh : t+K=4*(v+1) := by omega
    rw [hh,Nat.mul_comm 4 (v+1), Nat.pow_mul]
  have he0 : D*q+3*z+v+3=(2:Nat)^K := by
    simpa only [equation,den,bias,D,x,z,Nat.add_assoc] using h
  have hthree : y*(3*z)=3*w*x := by
    rw [hy,hx]
    simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  have he : x^4 = D*(y*q)+3*w*x+y*v+3*y := by
    calc
      x^4 = y*(D*q+3*z+v+3) := by rw [←hp,he0]
      _ = D*(y*q)+3*w*x+y*v+3*y := by
        simp only [Nat.mul_add]
        rw [hthree]
        simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  have hpoly : x^4+D*(3*x*x+27)=D*(x*x*x+9*x)+81 := by
    have h0 := fourth_poly x 1
    simpa [Nat.one_mul,Nat.mul_one,D,Nat.pow_succ,Nat.pow_zero,Nat.mul_assoc] using h0
  have hD3 : D*(3*w)=3*w*x+9*w := by
    dsimp [D]
    simp [Nat.add_mul, Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  have hy3 : 3*y=6*w := by rw [hy]; omega
  have hcore : D*(y*q+3*w+(3*x*x+27))+y*v =
      D*(x*x*x+9*x)+81+3*w := by
    calc
      D*(y*q+3*w+(3*x*x+27))+y*v =
          x^4 + D*(3*x*x+27) +3*w := by
        rw [he]
        simp only [Nat.mul_add]
        rw [hD3,hy3]
        omega
      _ = D*(x*x*x+9*x)+81+3*w := by rw [hpoly]
  have hm := congrArg (fun a : Nat => a % D) hcore
  have hmod : (y*v)%D = (81+3*w)%D := by
    simpa [Nat.add_mod,Nat.mul_mod] using hm
  simpa only [den,D,x,y,w] using hmod

private theorem linear64_le_pow (v : Nat) (hv : 10 ≤ v) :
    64*v ≤ (2:Nat)^(v+1) := by
  have h : ∀ n : Nat, 64*(10+n) ≤ (2:Nat)^(11+n) := by
    intro n
    induction n with
    | zero => decide
    | succ n ih =>
      have hbase : 64 ≤ (2:Nat)^(11+n) := by
        have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (by omega : 6≤11+n)
        have h6 : (2:Nat)^6=64 := by decide
        omega
      have hh : (2:Nat)^(11+(n+1)) = 2*((2:Nat)^(11+n)) := by
        have he : 11+(n+1)=(11+n)+1 := by omega
        rw [he,Nat.pow_succ']
      rw [hh]
      omega
  have he : 10+(v-10)=v := by omega
  simpa only [he,show 11+(v-10)=v+1 by omega] using h (v-10)

/-- In the five exponents immediately below the fourth-power threshold, all
    solutions have valuation at most nine. -/
theorem near_valuation_small (q v K t : Nat)
    (heq : equation q v K) (ht : 2 ≤ t) (ht6 : t ≤ 6)
    (hKt : K+t=4*v+4) : v ≤ 9 := by
  by_cases hvsmall : v ≤ 9
  · exact hvsmall
  · have hv : 10≤v := by omega
    have hl : 64*v ≤ (2:Nat)^(v+1) := linear64_le_pow v hv
    have hpow6 : (2:Nat)^t ≤ 64 := by
      have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) ht6
      have he : (2:Nat)^6=64 := by decide
      omega
    have hY : (2:Nat)^t*v ≤ 64*v := Nat.mul_le_mul_right v hpow6
    have hD : (2:Nat)^t*v < den v := by unfold den; omega
    have hpow5 : (2:Nat)^(t-1) ≤ 32 := by
      have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (by omega : t-1≤5)
      have he : (2:Nat)^5=32 := by decide
      omega
    have hpow11 : 2048 ≤ (2:Nat)^(v+1) := by
      have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (by omega : 11≤v+1)
      have he : (2:Nat)^11=2048 := by decide
      omega
    have hC : 81+3*(2:Nat)^(t-1) < den v := by unfold den; omega
    have hm:= near_mod q v K t heq (by omega) hKt
    rw [Nat.mod_eq_of_lt hD,Nat.mod_eq_of_lt hC] at hm
    have hp : (2:Nat)^t = 2*(2:Nat)^(t-1) := by
      calc
        (2:Nat)^t = (2:Nat)^((t-1)+1) := by congr 1; omega
        _ = 2*(2:Nat)^(t-1) := by rw [Nat.pow_succ']
    have hs : (2:Nat)^(t-1)=2*(2:Nat)^(t-2) := by
      calc
        (2:Nat)^(t-1) = (2:Nat)^((t-2)+1) := by congr 1; omega
        _ = 2*(2:Nat)^(t-2) := by rw [Nat.pow_succ']
    have hEven : ((2:Nat)^t*v)%2=0 := by rw [hp]; simp [Nat.mul_assoc]
    have hOdd : (81+3*(2:Nat)^(t-1))%2=1 := by rw [hs]; omega
    have hmod2 := congrArg (fun n : Nat => n%2) hm
    rw [hEven,hOdd] at hmod2
    omega
/-- Exhaustive seven-by-ten modular table, computed in the kernel. -/
private theorem near_residue_classification (v t : Nat)
    (hv : v < 10) (ht2 : 2≤t) (ht6 : t≤6)
    (hm : ((2:Nat)^t*v)%den v=(81+3*(2:Nat)^(t-1))%den v) :
    (v=0 ∧ t=4) ∨ (v=2 ∧ t=3) ∨ (v=3 ∧ t=4) ∨ (v=5 ∧ t=2) := by
  have finite : ∀ v ∈ List.range 10, ∀ t ∈ List.range 7,
      2≤t →
      ((2:Nat)^t*v)%den v=(81+3*(2:Nat)^(t-1))%den v →
      (v=0 ∧ t=4) ∨ (v=2 ∧ t=3) ∨ (v=3 ∧ t=4) ∨ (v=5 ∧ t=2) := by
    decide
  exact finite v (List.mem_range.mpr hv) t (List.mem_range.mpr (by omega)) ht2 hm

/-- Complete near-fourth-wall shape (all source-valid near predecessors). -/
theorem near_terminal_shapes (q v K t : Nat)
    (heq : equation q v K) (ht2 : 2≤t) (ht6 : t≤6)
    (hKt : K+t=4*v+4) :
    (q=45 ∧ v=2 ∧ K=9) ∨
    (q=214 ∧ v=3 ∧ K=12) ∨
    (q=62600 ∧ v=5 ∧ K=22) := by
  have hv := near_valuation_small q v K t heq ht2 ht6 hKt
  have hm := near_mod q v K t heq (by omega) hKt
  have hc := near_residue_classification v t (by omega) ht2 ht6 hm
  rcases hc with h0 | h2 | h3 | h5
  · rcases h0 with ⟨hv0,ht4⟩
    subst v
    subst t
    have hk : K=0 := by omega
    subst K
    simp [equation,den,bias] at heq
  · rcases h2 with ⟨hv2,ht3⟩
    subst v
    subst t
    have hk : K=9 := by omega
    subst K
    have hq : q=45 := by
      simp [equation,den,bias] at heq
      omega
    exact Or.inl ⟨hq,rfl,rfl⟩
  · rcases h3 with ⟨hv3,ht4⟩
    subst v
    subst t
    have hk : K=12 := by omega
    subst K
    have hq : q=214 := by
      simp [equation,den,bias] at heq
      omega
    exact Or.inr (Or.inl ⟨hq,rfl,rfl⟩)
  · rcases h5 with ⟨hv5,ht2⟩
    subst v
    subst t
    have hk : K=22 := by omega
    subst K
    have hq : q=62600 := by
      simp [equation,den,bias] at heq
      omega
    exact Or.inr (Or.inr ⟨hq,rfl,rfl⟩)

/-- Uniform fifth-linear valuation ceiling, conditional only on the previously
    source-certified fourth-linear ceiling. The isolated v=42,K=171 state is
    a genuine one-step predecessor, whereas all remaining states satisfy 5v≤K+3. -/
theorem fifth_from_fourth (q v K : Nat)
    (heq : equation q v K) (h4 : 4*v ≤ K+2) :
    (v=42 ∧ K=171) ∨ 5*v≤K+3 := by
  by_cases hhigh : 4*v+3≤K
  · let s := K-(4*v+3)
    have hK : 4*v+3+s=K := by dsimp [s]; omega
    have hh : equation q v (4*v+3+s) := by simpa only [hK] using heq
    rcases high_fifth_bound q v s hh with hs | ⟨hs0,hv42⟩
    · right
      dsimp [s] at hs
      omega
    · left
      dsimp [s] at hs0
      omega
  · let t := 4*v+4-K
    have ht2 : 2≤t := by dsimp [t]; omega
    have ht6 : t≤6 := by dsimp [t]; omega
    have hKt : K+t=4*v+4 := by dsimp [t]; omega
    have hh := near_terminal_shapes q v K t heq ht2 ht6 hKt
    rcases hh with ⟨_,hv,hk⟩ | ⟨_,hv,hk⟩ | ⟨_,hv,hk⟩
    · right; omega
    · right; omega
    · right; omega

private theorem exact_42_witness :
    equation 340282366920822406584691642613415018481 42 171 := by
  unfold equation den bias
  decide

/-- The sole exceptional fourth-power feeder is uniquely explicit. -/
theorem fifth_exact (q v K : Nat)
    (heq : equation q v K) (h4 : 4*v ≤ K+2) :
    (q=340282366920822406584691642613415018481 ∧ v=42 ∧ K=171) ∨
    5*v≤K+3 := by
  rcases fifth_from_fourth q v K heq h4 with ⟨hv,hK⟩ | hb
  · left
    subst v
    subst K
    have hq : q=340282366920822406584691642613415018481 := by
      simp [equation,den,bias] at heq
      omega
    exact ⟨hq,rfl,rfl⟩
  · exact Or.inr hb

#print axioms fifth_exact
#print axioms fifth_from_fourth
#print axioms high_fifth_bound
#print axioms high_mod
end BB6.Agent48.FifthHigh
