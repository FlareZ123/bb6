import Lean
import Lean.Elab.Tactic.Omega

namespace BB6.Agent12PureFan

/-- The source-independent arithmetic statement of a complete high-right
    predecessor fan. The special zero and one sectors are explicit. -/
def RawParent (a k x y : Nat) : Prop :=
  (y%2=0 ∧ a+2=x+y ∧ 2*k+2=y) ∨
  (a=0 ∧ 2≤k ∧ ∃ n : Nat, x+y=2^n*8 ∧ 2*k+9+3*n=x+2*y) ∨
  (a=1 ∧ 4≤k ∧ ∃ n : Nat, x+y+1=2^n*16 ∧ 2*k+11+3*n=x+2*y) ∨
  (2≤a ∧ a<2*k ∧ a%2=0 ∧ ∃ n : Nat,
    x+y=2^(n+1)*(a+2) ∧ 2*k+a+7+3*n=x+2*y) ∨
  (2≤a ∧ a<2*k ∧ a%2=1 ∧ ∃ n : Nat,
    x+y+1=2^(n+1)*(a+3) ∧ 2*k+a+7+3*n=x+2*y)

/-- Canonical compressed fan of a pure-power rounded target of odd left
    parity. All positive high-left coordinates are powers of four minus a
    fixed constant. The exponent and right coordinate are determined. -/
def Fan (a k x y v : Nat) : Prop :=
  let o := (x+y)%2
  (o=1 ∧ a+3=2^v ∧ 2*k+2=y) ∨
  (o=0 ∧ a=0 ∧ 2≤k ∧ 3≤v ∧ 2*k+3*v=x+2*y) ∨
  (∃ d : Nat, 1≤d ∧ 2*d+1≤v ∧ a+2+o=4^d ∧
     2*k+a+7+3*(v-1-2*d)=x+2*y ∧
     ((a=1 ∧ 4≤k) ∨ (2≤a ∧ a<2*k)))

private theorem pow_even (d : Nat) (hd : 1≤d) : 2^d%2=0 := by
  exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 hd)

private theorem factor_power (v n p : Nat) (_hp : 0<p)
    (h : 2^v=2^n*p) : n≤v ∧ p=2^(v-n) := by
  have hd : 2^n∣2^v := ⟨p,h⟩
  have hn := (Nat.pow_dvd_pow_iff_le_right (by decide : 1<2)).mp hd
  have h1 : 2^v=2^n*2^(v-n) := by
    rw [←Nat.pow_add,show n+(v-n)=v by omega]
  exact ⟨hn,Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) (h.symm.trans h1)⟩

private theorem high_factor (x y v o a k n : Nat)
    (hx : x%2=1) (ho : o≤1) (hv : v%2=1-o)
    (ha : a%2=o) (hA : 4≤a+2+o)
    (hQ : 2^v=2^(n+1)*(a+2+o))
    (hW : 2*k+a+7+3*n=x+2*y) :
    ∃ d : Nat, 1≤d ∧ 2*d+1≤v ∧ a+2+o=4^d ∧
      2*k+a+7+3*(v-1-2*d)=x+2*y := by
  obtain ⟨hn,hp⟩ := factor_power v (n+1) (a+2+o) (by omega) hQ
  have he : 2≤v-(n+1) := by
    by_cases h : 2≤v-(n+1)
    · exact h
    · have hle : 2^(v-(n+1))≤2^1 := Nat.pow_le_pow_right (by decide) (by omega)
      omega
  have hnpar : n%2=o := by omega
  let d := (v-(n+1))/2
  have hd : 2*d=v-(n+1) := by dsimp [d]; omega
  refine ⟨d,by omega,by omega,?_,by omega⟩
  rw [hp,←hd,Nat.pow_mul]

/-- Full necessary predecessor reduction, with no non-power assumption. -/
theorem raw_to_fan (a k x y v : Nat) (hx : x%2=1)
    (hQ : x+y+(x+y)%2=2^v) (hv : v%2=1-(x+y)%2)
    (h : RawParent a k x y) : Fan a k x y v := by
  let o := (x+y)%2
  have ho : o≤1 := by dsimp [o]; omega
  change v%2=1-o at hv
  change x+y+o=2^v at hQ
  change (o=1 ∧ a+3=2^v ∧ 2*k+2=y) ∨
    (o=0 ∧ a=0 ∧ 2≤k ∧ 3≤v ∧ 2*k+3*v=x+2*y) ∨ _
  rcases h with h|h|h|h|h
  · obtain ⟨hy,ha,hk⟩ := h
    have ho1 : o=1 := by dsimp [o]; omega
    exact Or.inl ⟨ho1,by omega,hk⟩
  · obtain ⟨ha,hk,n,hs,hw⟩ := h
    have hs' : x+y=2^(n+3) := by rw [Nat.pow_add]; exact hs
    have hp := pow_even (n+3) (by omega)
    have ho0 : o=0 := by dsimp [o]; omega
    have he : 2^(n+3)=2^v := by omega
    have hn : n+3=v := by
      have h1 := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (Nat.le_of_eq he)
      have h2 := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (Nat.le_of_eq he.symm)
      omega
    exact Or.inr (Or.inl ⟨ho0,ha,hk,by omega,by omega⟩)
  · obtain ⟨ha,hk,n,hs,hw⟩ := h
    have hs' : x+y+1=2^(n+4) := by rw [Nat.pow_add]; exact hs
    have hp := pow_even (n+4) (by omega)
    have ho1 : o=1 := by dsimp [o]; omega
    have he : 2^(n+4)=2^v := by omega
    have hn : n+4=v := by
      have h1 := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (Nat.le_of_eq he)
      have h2 := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (Nat.le_of_eq he.symm)
      omega
    refine Or.inr (Or.inr ⟨1,by decide,by omega,by omega,by omega,Or.inl ⟨ha,hk⟩⟩)
  · obtain ⟨ha,hak,hpar,n,hs,hw⟩ := h
    have hp : 2^(n+1)%2=0 := pow_even _ (by omega)
    have hmod := Nat.mul_mod (2^(n+1)) (a+2) 2
    rw [hp, Nat.zero_mul,Nat.zero_mod] at hmod
    have ho0 : o=0 := by dsimp [o]; omega
    have h1 : 2^v=2^(n+1)*(a+2+o) := by simpa [ho0] using hQ.symm.trans (by simpa [ho0] using hs)
    obtain ⟨d,hd,hdv,hda,hdW⟩ := high_factor x y v o a k n hx ho hv (by omega) (by omega) h1 hw
    exact Or.inr (Or.inr ⟨d,hd,hdv,hda,hdW,Or.inr ⟨ha,hak⟩⟩)
  · obtain ⟨ha,hak,hpar,n,hs,hw⟩ := h
    have hp : 2^(n+1)%2=0 := pow_even _ (by omega)
    have hmod := Nat.mul_mod (2^(n+1)) (a+3) 2
    rw [hp, Nat.zero_mul,Nat.zero_mod] at hmod
    have ho1 : o=1 := by dsimp [o]; omega
    have h1 : 2^v=2^(n+1)*(a+2+o) := by simpa [ho1] using hQ.symm.trans (by simpa [ho1] using hs)
    obtain ⟨d,hd,hdv,hda,hdW⟩ := high_factor x y v o a k n hx ho hv (by omega) (by omega) h1 hw
    exact Or.inr (Or.inr ⟨d,hd,hdv,hda,hdW,Or.inr ⟨ha,hak⟩⟩)

private theorem four_pow_ge (d : Nat) (hd : 1≤d) : 4≤4^d := by
  exact Nat.pow_le_pow_right (by decide : 0<4) hd

private theorem four_pow_mod (d : Nat) (hd : 1≤d) : 4^d%4=0 := by
  exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 4 hd)

/-- The fan is exact: every member is an arithmetic parent. -/
theorem fan_to_raw (a k x y v : Nat) (hx : x%2=1)
    (hQ : x+y+(x+y)%2=2^v) (hv : v%2=1-(x+y)%2)
    (h : Fan a k x y v) : RawParent a k x y := by
  let o := (x+y)%2
  have ho : o≤1 := by dsimp [o]; omega
  change v%2=1-o at hv
  change x+y+o=2^v at hQ
  rcases h with h|h|h
  · obtain ⟨ho1,ha,hk⟩ := h
    change o=1 at ho1
    exact Or.inl ⟨by dsimp [o] at ho1; omega,by omega,hk⟩
  · obtain ⟨ho0,ha,hk,hv3,hw⟩ := h
    change o=0 at ho0
    refine Or.inr (Or.inl ⟨ha,hk,v-3,?_,by omega⟩)
    have he : 2^v=2^(v-3)*8 := by rw [←show 2^3=8 by decide,←Nat.pow_add,show v-3+3=v by omega]
    omega
  · obtain ⟨d,hd,hdv,hda,hw,ha⟩ := h
    change a+2+o=4^d at hda
    have hf := four_pow_ge d hd
    have hm := four_pow_mod d hd
    let n := v-1-2*d
    change 2*k+a+7+3*n=x+2*y at hw
    have hpow : 2^v=2^(n+1)*4^d := by
      rw [←show 2^2=4 by decide,←Nat.pow_mul,←Nat.pow_add]
      congr 1
      dsimp [n]
      omega
    rcases ha with ⟨ha,hk⟩|⟨ha,hak⟩
    · have ho1 : o=1 := by omega
      have hd1 : d=1 := by
        by_cases hh : d=1
        · exact hh
        · have hg : 4^2≤4^d := Nat.pow_le_pow_right (by decide) (by omega)
          omega
      have hv4 : 4≤v := by omega
      refine Or.inr (Or.inr (Or.inl ⟨ha,hk,v-4,?_,by dsimp [n] at hw; omega⟩))
      have he : 2^v=2^(v-4)*16 := by rw [←show 2^4=16 by decide,←Nat.pow_add,show v-4+4=v by omega]
      omega
    · have hap : a%2=o := by omega
      by_cases ho0 : o=0
      · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨ha,hak,by omega,n,?_,hw⟩)))
        rw [←hda,ho0,Nat.add_zero] at hpow
        simpa [ho0] using hQ.trans hpow
      · have ho1 : o=1 := by omega
        refine Or.inr (Or.inr (Or.inr (Or.inr ⟨ha,hak,by omega,n,?_,hw⟩)))
        rw [←hda,ho1] at hpow
        simpa [ho1] using hQ.trans hpow

theorem fan_exact (a k x y v : Nat) (hx : x%2=1)
    (hQ : x+y+(x+y)%2=2^v) (hv : v%2=1-(x+y)%2) :
    RawParent a k x y ↔ Fan a k x y v :=
  ⟨raw_to_fan a k x y v hx hQ hv,fan_to_raw a k x y v hx hQ hv⟩

private theorem pow_ge_linear (n : Nat) : n+2≤2^(n+1) := by
  induction n with
  | zero => decide
  | succ n ih => rw [show n+1+1=n+1+1 by rfl,Nat.pow_succ]; omega

/-- Every d in the compressed fan yields a genuine arithmetic parent;
    no further feasibility test is required at height eight. -/
theorem fan_bounce_exists (x y v d : Nat) (hx : x%2=1) (hy : 8≤y)
    (hQ : x+y+(x+y)%2=2^v) (hv : v%2=1-(x+y)%2)
    (hd : 1≤d) (hdv : 2*d+1≤v) :
    ∃ a k, Fan a k x y v ∧ a+2+(x+y)%2=4^d ∧
      2*k+a+7+3*(v-1-2*d)=x+2*y := by
  let o := (x+y)%2
  have ho : o≤1 := by dsimp [o]; omega
  change v%2=1-o at hv
  change x+y+o=2^v at hQ
  let n := v-1-2*d
  let p := 4^d
  have hp : 4≤p := four_pow_ge d hd
  have hpmod : p%4=0 := four_pow_mod d hd
  let a := p-2-o
  have ha : a+2+o=p := by dsimp [a]; omega
  have hap : a%2=o := by omega
  have hnpar : n%2=o := by dsimp [n]; omega
  have hpow : 2^v=2^(n+1)*p := by
    dsimp [p]
    rw [←show 2^2=4 by decide,←Nat.pow_mul,←Nat.pow_add]
    congr 1
    dsimp [n]
    omega
  have hlin : n+2≤2^(n+1) := pow_ge_linear n
  have hgap := Nat.mul_le_mul_right p hlin
  rw [←hpow,Nat.add_mul] at hgap
  have hgap2 := Nat.mul_le_mul_left n hp
  have hineq : 2*p+3*n≤2^v := by omega
  have hbig : 2*a+7+3*n+5+o≤x+2*y := by omega
  let k := (x+2*y-a-7-3*n)/2
  have hw : 2*k+a+7+3*n=x+2*y := by dsimp [k]; omega
  have hfeas : (a=1 ∧ 4≤k) ∨ (2≤a ∧ a<2*k) := by
    by_cases ha1 : a=1
    · exact Or.inl ⟨ha1,by omega⟩
    · exact Or.inr ⟨by omega,by omega⟩
  refine ⟨a,k,Or.inr (Or.inr ⟨d,hd,hdv,ha,hw,hfeas⟩),ha,hw⟩

private theorem power_ge_triple (v : Nat) (hv : 4≤v) : 3*v≤2^v := by
  induction v with
  | zero => omega
  | succ v ih =>
    by_cases h : 4≤v
    · rw [Nat.pow_succ]; have := ih h; omega
    · have hv4 : v=3 := by omega
      subst v
      decide

/-- For odd valuation the exceptional zero-left parent always exists. -/
theorem fan_zero_exists (x y v : Nat) (hx : x%2=1) (hy : 8≤y)
    (hQ : x+y=2^v) (hv : v%2=1) :
    ∃ k, Fan 0 k x y v ∧ 2*k+3*v=x+2*y := by
  have hv4 : 4≤v := by
    by_cases h : 4≤v
    · exact h
    · have hle : 2^v≤2^3 := Nat.pow_le_pow_right (by decide) (by omega)
      omega
  have hq := pow_even v (by omega)
  have hlin := power_ge_triple v hv4
  let k := (x+2*y-3*v)/2
  have hw : 2*k+3*v=x+2*y := by dsimp [k]; omega
  exact ⟨k,Or.inr (Or.inl ⟨by omega,rfl,by omega,by omega,hw⟩),hw⟩

/-- For even valuation the direct parent always exists. -/
theorem fan_direct_exists (x y v : Nat) (hx : x%2=1) (hy : 8≤y)
    (hQ : x+y+1=2^v) (hpar : y%2=0) :
    ∃ a k, Fan a k x y v ∧ a+3=2^v ∧ 2*k+2=y := by
  let a := x+y-2
  let k := (y-2)/2
  have ha : a+3=2^v := by dsimp [a]; omega
  have hk : 2*k+2=y := by dsimp [k]; omega
  exact ⟨a,k,Or.inl ⟨by omega,ha,hk⟩,ha,hk⟩

/-- A single residue eliminates the direct parent of every positive-index
    even-exponent pure-power stopping target, regardless of size. -/
theorem even_pure_direct_excluded (reach : Nat → Nat → Prop)
    (direct : ∀ x y, 6≤y → y%2=0 → (x+y)%8≠0 → (x+y)%8≠7 →
      (reach x y ↔ reach (x+y-2) ((y-2)/2)))
    (forbid : ∀ x y, 5≤y → y%2=1 → ((x+y)%4=1 ∨ (x+y)%4=2) → ¬reach x y)
    (a k x y v : Nat) (hQ : x+y+1=2^v) (hx : x%16=13)
    (hv : 5≤v) (hy : 26≤y)
    (ha : a+3=2^v) (hk : 2*k+2=y) : ¬reach a k := by
  have hq : 2^v%32=0 := Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 hv)
  have hk8 : k%8=0 := by omega
  have ha8 : a%8=5 := by omega
  intro hr
  have hr1 := (direct a k (by omega) (by omega) (by omega) (by omega)).mp hr
  apply forbid (a+k-2) ((k-2)/2) (by omega) (by omega) (Or.inr (by omega)) hr1

#print axioms fan_exact
#print axioms fan_bounce_exists
#print axioms fan_zero_exists
#print axioms fan_direct_exists
#print axioms even_pure_direct_excluded
end BB6.Agent12PureFan
