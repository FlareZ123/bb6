import DyadicCover
namespace BB6.Agent21Dyadic

def highAffine (m : Nat) : Affine := ⟨6*(m:Int)+7-2*P (2*m+3),-P (2*m+3),-2,-1⟩

theorem high_good (m : Nat) : Good (highAffine m) := by
  have hpow : P (2*m+3)=P (2*m+1)*4 := by rw [show 2*m+3=2*m+1+2 by omega,P_add]; rfl
  unfold Good highAffine
  dsimp
  rw [hpow]
  have h : -(P (2*m+1)*4)%4=0 := by omega
  exact ⟨h,by decide⟩

theorem high_coords (m j y : Nat) (he : y+j+3*m+4=pow (2*m+2)*(j+2)) :
    S (2*j+1) y=mass (highAffine m) j ∧ Z (2*j+1) y=norm (highAffine m) j := by
  have he' := congrArg (fun n : Nat=>(n:Int)) he
  simp only [Int.natCast_add,Int.natCast_mul,Int.cast_ofNat_Int] at he'
  have hp : (pow (2*m+2):Int)=P (2*m+2) := by simp [pow,P]
  rw [hp] at he'
  have heP : P (2*m+3)=P (2*m+2)*2 := by rw [show 2*m+3=2*m+2+1 by omega,P_add]; rfl
  constructor
  · unfold S mass highAffine
    simp only [Int.natCast_add,Int.natCast_mul,Int.cast_ofNat_Int]
    rw [heP,Int.mul_add] at *
    have hmul : P (2*m+2)*(2*(j:Int))=P (2*m+2)*2*(j:Int) := by ac_rfl
    rw [Int.neg_mul,←hmul,Int.mul_left_comm (P (2*m+2)) 2,←Int.mul_assoc]
    omega
  · unfold Z S parity norm highAffine
    simp only [Int.natCast_add,Int.natCast_mul,Int.cast_ofNat_Int]
    omega

private theorem exp_bound (m : Nat) : 3*m+8≤2*pow (2*m+2) := by
  induction m with
  | zero => decide
  | succ m ih =>
    have hp : pow (2*(m+1)+2)=pow (2*m+2)*4 := by unfold pow; rw [show 2*(m+1)+2=2*m+2+2 by omega,Nat.pow_add]
    rw [hp]; omega

theorem high_size (m j y n : Nat) (hj : pow (n+2)≤j)
    (he : y+j+3*m+4=pow (2*m+2)*(j+2)) : Large (n+2) y := by
  have hp : 4≤pow (2*m+2) := Nat.pow_le_pow_right (by decide : 0<2) (by omega : 2≤2*m+2)
  have hm := Nat.mul_le_mul_right j hp
  have hb := exp_bound m
  rw [Nat.mul_add] at he
  unfold Large; omega

/-- A sparse cover of every high stopping family, with the same modulus for all m. -/
theorem high_sparse (reach : Nat→Nat→Prop) (parent : ParentLaw reach) (d : Nat) (hd : 0<d) :
    ∃ n, ∀ m, ∃ R : List Int, d*R.length≤2^n ∧ ∀ j y : Nat,
      pow (n+2)≤j → y+j+3*m+4=pow (2*m+2)*(j+2) → reach (2*j+1) y → (j:Int)%P n∈R := by
  obtain ⟨n,hn⟩ := sparse_cover d hd
  refine ⟨n,?_⟩
  intro m
  obtain ⟨R,hR,hr⟩ := hn (highAffine m) (good_admissible _ (high_good m))
  refine ⟨R,hR,?_⟩
  intro j y hj he hreach
  have ho := reach_open reach parent n (2*j+1) y (high_size m j y n hj he) hreach
  obtain ⟨hs,hz⟩ := high_coords m j y he
  rw [hs,hz] at ho
  exact hr _ ho

def lowAffine : Affine := ⟨7,6,-2,0⟩

theorem low_admissible : Admissible lowAffine := by unfold Admissible lowAffine; decide

theorem low_coords (m y n : Nat) (hm : n≤m)
    (he : y+3*m+4=pow (2*m+3)) :
    P (n+1)∣mass lowAffine m-S 1 y ∧ P n∣norm lowAffine m-Z 1 y := by
  have hE := congrArg (fun t:Nat=>(t:Int)) he
  simp only [Int.natCast_add,Int.natCast_mul,Int.cast_ofNat_Int] at hE
  have hp : (pow (2*m+3):Int)=P (2*m+3) := by simp [pow,P]
  rw [hp] at hE
  constructor
  · have heq : mass lowAffine m-S 1 y=2*P (2*m+3) := by unfold mass lowAffine S; dsimp; omega
    rw [heq,Int.mul_comm]
    exact Int.dvd_trans (P_dvd (n+1) (2*m+3) (by omega)) (Int.dvd_mul_right _ _)
  · have heq : norm lowAffine m-Z 1 y=0 := by unfold norm lowAffine Z S parity; dsimp; omega
    rw [heq]; exact Int.dvd_zero _

private theorem low_exp_bound (m : Nat) : 3*m+4≤pow (2*m+2) := by
  induction m with
  | zero => decide
  | succ m ih =>
    have hp : pow (2*(m+1)+2)=pow (2*m+2)*4 := by unfold pow; rw [show 2*(m+1)+2=2*m+2+2 by omega,Nat.pow_add]
    rw [hp]; omega

theorem low_size (m y n : Nat) (hm : n+2≤m) (he : y+3*m+4=pow (2*m+3)) : Large (n+2) y := by
  have hp : pow (2*m+3)=pow (2*m+2)*2 := by unfold pow; rw [show 2*m+3=2*m+2+1 by omega,Nat.pow_succ]
  have hle : pow (n+4)≤pow (2*m+2) := Nat.pow_le_pow_right (by decide : 0<2) (by omega)
  have heq : pow (n+4)=pow (n+2)*4 := by unfold pow; rw [show n+4=n+2+2 by omega,Nat.pow_add]
  have hb := low_exp_bound m
  rw [heq] at hle
  rw [hp] at he
  unfold Large; omega

/-- Sparse cover of the full low stopping family, including parameters outside
    the previously studied residual ray. -/
theorem low_sparse (reach : Nat→Nat→Prop) (parent : ParentLaw reach) (d : Nat) (hd : 0<d) :
    ∃ n, ∃ R : List Int, d*R.length≤2^n ∧ ∀ m y : Nat,
      n+2≤m → y+3*m+4=pow (2*m+3) → reach 1 y → (m:Int)%P n∈R := by
  obtain ⟨n,hn⟩ := sparse_cover d hd
  obtain ⟨R,hR,hr⟩ := hn lowAffine low_admissible
  refine ⟨n,R,hR,?_⟩
  intro m y hm he hreach
  have ho := reach_open reach parent n 1 y (low_size m y n hm he) hreach
  obtain ⟨hs,hz⟩ := low_coords m y n (by omega) he
  exact hr _ (open_congr _ _ _ _ n hs hz ho)

#print axioms low_sparse
#print axioms high_sparse
end BB6.Agent21Dyadic
