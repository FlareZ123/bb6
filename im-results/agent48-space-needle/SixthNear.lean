import SixthHigh
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
namespace BB6.Agent48.SixthHigh
open BB6.Agent48.FifthHigh

private theorem near_power (v K t : Nat) (hKt : K+t=5*v+5) :
    (2:Nat)^t*(2:Nat)^K = ((2:Nat)^(v+1))^5 := by
  rw [←Nat.pow_add]
  have h : t+K=5*(v+1) := by omega
  rw [h,Nat.mul_comm 5 (v+1),Nat.pow_mul]

private theorem near_mod (q v K t : Nat)
    (heq : equation q v K) (ht : 1≤t) (hKt : K+t=5*v+5) :
    ((2:Nat)^t*v+243)%den v=(3*(2:Nat)^(t-1))%den v := by
  let x : Nat := (2:Nat)^(v+1)
  let z : Nat := (2:Nat)^v
  let y : Nat := (2:Nat)^t
  let w : Nat := (2:Nat)^(t-1)
  let D : Nat := x+3
  have hx : x=2*z := by dsimp [x,z]; rw [Nat.pow_succ']
  have hy : y=2*w := by
    dsimp [y,w]
    have htw : t-1+1=t := by omega
    calc
      (2:Nat)^t = (2:Nat)^((t-1)+1) := by congr 1; omega
      _ = 2*(2:Nat)^(t-1) := by rw [Nat.pow_succ']
  have hp : y*(2:Nat)^K=x^5 := by
    simpa only [y,x] using near_power v K t hKt
  have he0 : D*q+3*z+v+3=(2:Nat)^K := by
    simpa only [equation,den,bias,D,x,z,Nat.add_assoc] using heq
  have hthree : y*(3*z)=3*w*x := by
    rw [hy,hx]
    simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  have he : x^5 = D*(y*q)+3*w*x+y*v+3*y := by
    calc
      x^5 = y*(D*q+3*z+v+3) := by rw [←hp,he0]
      _ = D*(y*q)+3*w*x+y*v+3*y := by
        simp only [Nat.mul_add]
        rw [hthree]
        simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  have hpoly : x^5+243+D*(3*x^3+27*x) =
      D*(x^4+9*x^2+81) := by
    have h0 := five_poly x 1
    simpa [Nat.one_mul,Nat.mul_one,D,Nat.mul_assoc] using h0
  have hD3 : D*(3*w)=3*w*x+9*w := by
    dsimp [D]
    simp [Nat.add_mul,Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  have hy3 : 3*y=6*w := by rw [hy]; omega
  have hcore : D*(y*q+3*w+(3*x^3+27*x))+(y*v+243) =
      D*(x^4+9*x^2+81)+3*w := by
    calc
      _ = x^5+243+D*(3*x^3+27*x)+3*w := by
        rw [he]
        simp only [Nat.mul_add]
        rw [hD3,hy3]
        omega
      _ = D*(x^4+9*x^2+81)+3*w := by rw [hpoly]
  have hm := congrArg (fun a : Nat => a%D) hcore
  have hmod : (y*v+243)%D=(3*w)%D := by
    simpa [Nat.add_mod,Nat.mul_mod] using hm
  simpa only [den,x,y,w,D] using hmod

private theorem lin256_lt_pow (v : Nat) (hv : 11≤v) :
    256*v+243 < (2:Nat)^(v+1)+3 := by
  have h : ∀ n : Nat,
      256*(11+n)+243 < (2:Nat)^(11+n+1)+3 := by
    intro n
    induction n with
    | zero => decide
    | succ n ih =>
      have hbase : 256 ≤ (2:Nat)^(11+n+1) := by
        have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat))
          (by omega : 8≤11+n+1)
        have h8 : (2:Nat)^8=256 := by decide
        omega
      have hh : (2:Nat)^(11+(n+1)+1)=2*((2:Nat)^(11+n+1)) := by
        have he : 11+(n+1)+1=(11+n+1)+1 := by omega
        rw [he,Nat.pow_succ']
      rw [hh]
      omega
  have h11 : 11+(v-11)=v := by omega
  simpa only [h11,show 11+(v-11)+1=v+1 by omega] using h (v-11)

/-- The near-fifth-power band contains no solution of valuation >=11. -/
theorem near_sixth_small (q v K t : Nat)
    (heq : equation q v K) (ht : 1≤t) (ht8 : t≤8)
    (hKt : K+t=5*v+5) : v≤10 := by
  by_cases hv : v≤10
  · exact hv
  · have hv11 : 11≤v := by omega
    have hlin := lin256_lt_pow v hv11
    have hpow8 : (2:Nat)^t≤256 := by
      have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) ht8
      have he : (2:Nat)^8=256 := by decide
      omega
    have hY : (2:Nat)^t*v≤256*v := Nat.mul_le_mul_right v hpow8
    have hD : (2:Nat)^t*v+243<den v := by unfold den; omega
    have hw : (2:Nat)^(t-1)≤128 := by
      have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat))
        (by omega : t-1≤7)
      have he : (2:Nat)^7=128 := by decide
      omega
    have hpow12 : 4096 ≤ (2:Nat)^(v+1) := by
      have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat))
        (by omega : 12≤v+1)
      have he : (2:Nat)^12=4096 := by decide
      omega
    have hC : 3*(2:Nat)^(t-1)<den v := by unfold den; omega
    have hm := near_mod q v K t heq ht hKt
    rw [Nat.mod_eq_of_lt hD,Nat.mod_eq_of_lt hC] at hm
    let w : Nat := (2:Nat)^(t-1)
    have hy : (2:Nat)^t=2*w := by
      dsimp [w]
      calc
        (2:Nat)^t=(2:Nat)^((t-1)+1) := by congr 1; omega
        _ = 2*(2:Nat)^(t-1) := by rw [Nat.pow_succ']
    rw [hy] at hm
    have h3 : 3*w≤2*w*v := by
      calc
        3*w=w*3 := by ac_rfl
        _ ≤ w*(2*v) := Nat.mul_le_mul_left w (by omega)
        _ = 2*w*v := by ac_rfl
    omega

private theorem near_residue_table (v t : Nat)
    (hv : v<11) (ht : 2≤t) (ht8 : t≤8)
    (hm : ((2:Nat)^t*v+243)%den v=(3*(2:Nat)^(t-1))%den v) :
    (v=0 ∧ t=5) ∨ (v=2 ∧ t=6) ∨
    (v=3 ∧ t=8) ∨ (v=5 ∧ t=8) := by
  have h : ∀ v ∈ List.range 11, ∀ t ∈ List.range 9,
      2≤t →
      ((2:Nat)^t*v+243)%den v=(3*(2:Nat)^(t-1))%den v →
      (v=0 ∧ t=5) ∨ (v=2 ∧ t=6) ∨
      (v=3 ∧ t=8) ∨ (v=5 ∧ t=8) := by
    decide
  exact h v (List.mem_range.mpr hv) t
    (List.mem_range.mpr (by omega)) ht hm

/-- Every low-side source in the fifth-linear band is one of three genuine
    affine triples; only the latter two fail the sixth-linear regular bound. -/
theorem near_sixth_shapes (q v K t : Nat)
    (heq : equation q v K) (ht : 2≤t) (ht8 : t≤8)
    (hKt : K+t=5*v+5) :
    (q=45 ∧ v=2 ∧ K=9) ∨
    (q=214 ∧ v=3 ∧ K=12) ∨
    (q=62600 ∧ v=5 ∧ K=22) := by
  have hv := near_sixth_small q v K t heq (by omega) ht8 hKt
  have hm := near_mod q v K t heq (by omega) hKt
  rcases near_residue_table v t (by omega) ht ht8 hm with h0 | h2 | h3 | h5
  · rcases h0 with ⟨hv0,ht5⟩
    subst v
    subst t
    have hk : K=0 := by omega
    subst K
    simp [equation,den,bias] at heq
  · rcases h2 with ⟨hv2,ht6⟩
    subst v
    subst t
    have hk : K=9 := by omega
    subst K
    have hq : q=45 := by
      simp [equation,den,bias] at heq
      omega
    exact Or.inl ⟨hq,rfl,rfl⟩
  · rcases h3 with ⟨hv3,ht8⟩
    subst v
    subst t
    have hk : K=12 := by omega
    subst K
    have hq : q=214 := by
      simp [equation,den,bias] at heq
      omega
    exact Or.inr (Or.inl ⟨hq,rfl,rfl⟩)
  · rcases h5 with ⟨hv5,ht8⟩
    subst v
    subst t
    have hk : K=22 := by omega
    subst K
    have hq : q=62600 := by
      simp [equation,den,bias] at heq
      omega
    exact Or.inr (Or.inr ⟨hq,rfl,rfl⟩)

/-- Uniform sixth-linear ceiling on the entire fifth-linear regular domain,
    with exactly two isolated mathematical exceptions. -/
theorem sixth_from_fifth (q v K : Nat)
    (heq : equation q v K) (h5 : 5*v≤K+3) :
    (q=214 ∧ v=3 ∧ K=12) ∨
    (q=62600 ∧ v=5 ∧ K=22) ∨
    6*v≤K+4 := by
  by_cases hhigh : 5*v+4≤K
  · let s := K-(5*v+4)
    have hs : 5*v+4+s=K := by dsimp [s]; omega
    have hh : equation q v (5*v+4+s) := by simpa only [hs] using heq
    have hb := high_sixth_bound q v s hh
    exact Or.inr (Or.inr (by dsimp [s] at hb; omega))
  · let t := 5*v+5-K
    have ht : 2≤t := by dsimp [t]; omega
    have ht8 : t≤8 := by dsimp [t]; omega
    have hKt : K+t=5*v+5 := by dsimp [t]; omega
    have hh := near_sixth_shapes q v K t heq ht ht8 hKt
    rcases hh with ⟨_,hv,hk⟩ | h3 | h5
    · exact Or.inr (Or.inr (by omega))
    · exact Or.inl h3
    · exact Or.inr (Or.inl h5)

#print axioms near_mod
#print axioms near_sixth_small
#print axioms sixth_from_fifth
end BB6.Agent48.SixthHigh
