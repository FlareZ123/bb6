import FirstInverseComplete

/-!
A kernel-reducible, exact enumeration of ResetParent predecessors.
The even dyadic band has a unique scale, and the odd arm only needs t below
v3Fast (2*u+5). The proof below establishes equivalence with ResetParent.
-/

set_option maxHeartbeats 0
namespace CascadeResetInverse

private def evenHeightFast (u k:Nat) := 2*u-8*2^k-k
private def oddHeightFast (u k t:Nat) := 2*(2^t*((2*u+5)/(3^(t+1))))-8*2^k-k-5

def v3AuxFast (z : Nat) : Nat → Nat
| 0 => 0
| fuel+1 => if z > 0 ∧ z % 3 = 0 then v3AuxFast (z/3) fuel + 1 else 0

def v3Fast (z:Nat) := v3AuxFast z (Nat.log2 z + 1)

theorem v3AuxFast_step (z fuel:Nat) (hz:0<z) (hm:z%3=0) :
    v3AuxFast z (fuel+1)=v3AuxFast (z/3) fuel+1 := by
  simp [v3AuxFast,hz,hm]

theorem pow_dvd_v3AuxFast (z t fuel:Nat) (hz:0<z)
    (hd:3^(t+1)∣z) (ht:t<fuel) : t<v3AuxFast z fuel := by
  induction t generalizing z fuel with
  | zero =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have h3:3∣z := by simpa using hd
      have hm:z%3=0:=Nat.mod_eq_zero_of_dvd h3
      rw [v3AuxFast_step z fuel hz hm]
      omega
  | succ t ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      rcases hd with ⟨m,hm⟩
      have hfactor:3^(t+2)=3^(t+1)*3:=by rw [Nat.pow_succ]
      have hquot:z/3=3^(t+1)*m:=by
        calc
          z/3=(3^(t+2)*m)/3:=by rw [hm]
          _=(3*(3^(t+1)*m))/3:=by rw [hfactor]; ac_rfl
          _=3^(t+1)*m:=Nat.mul_div_cancel_left _ (by decide)
      have hdiv:3^(t+1)∣z/3:=⟨m,hquot⟩
      have h3pow:3∣3^(t+2):=⟨3^(t+1),by rw [Nat.pow_succ]; ac_rfl⟩
      have h3:3∣z:=Nat.dvd_trans h3pow ⟨m,hm⟩
      have hmod:z%3=0:=Nat.mod_eq_zero_of_dvd h3
      have hmpos:0<m:=by
        by_cases hm0:m=0
        · simp [hm0] at hm
          omega
        · omega
      have hpos:0<z/3:=by rw [hquot]; exact Nat.mul_pos (Nat.pow_pos (by decide)) hmpos
      have ht':t<fuel:=by omega
      rw [v3AuxFast_step z fuel hz hmod]
      have hh:=ih (z/3) fuel hpos hdiv ht'
      omega

theorem pow2_le_pow3 (t:Nat) : 2^t≤3^t := by
  induction t with
  | zero => decide
  | succ t ih =>
    calc
      2^(t+1)=2^t*2 := by rw [Nat.pow_succ]
      _≤3^t*3 := Nat.mul_le_mul ih (by decide)
      _=3^(t+1) := by rw [Nat.pow_succ]

theorem pow_dvd_v3Fast (z t:Nat) (hz:0<z) (hd:3^(t+1)∣z) : t<v3Fast z := by
  have h23:2^(t+1)≤3^(t+1):=pow2_le_pow3 (t+1)
  have hle:3^(t+1)≤z:=Nat.le_of_dvd hz hd
  have hzne:z≠0:=by omega
  have hlog:t+1≤Nat.log2 z:=(Nat.le_log2 hzne).mpr (by omega)
  have ht:t<Nat.log2 z+1:=by omega
  exact pow_dvd_v3AuxFast z t (Nat.log2 z+1) hz hd ht

private theorem pow2_k_pos (k:Nat) : 1≤2^k := Nat.one_le_pow k 2 (by decide)
private theorem pow2_add2 (k:Nat) : 2^(k+2)=4*2^k := by
  rw [Nat.pow_add]
  simp only [show (2:Nat)^2=4 by decide]
  ac_rfl
private theorem pow2_add3 (k:Nat) : 2^(k+3)=8*2^k := by
  rw [Nat.pow_add]
  simp only [show (2:Nat)^3=8 by decide]
  ac_rfl

private theorem log2_even_band (u k:Nat)
    (hl:6*2^k-1≤u) (hh:u≤8*2^k-3) : Nat.log2 u=k+2 := by
  have hp:=pow2_k_pos k
  have hlo:2^(k+2)≤u := by rw [pow2_add2]; omega
  have hhi:u<2^(k+3) := by rw [pow2_add3]; omega
  exact (Nat.log2_eq_iff (by omega)).2 ⟨hlo,hhi⟩

private theorem log2_odd_band (x k:Nat)
    (hl:6*2^k+1≤x) (hh:x≤8*2^k-1) : Nat.log2 x=k+2 := by
  have hp:=pow2_k_pos k
  have hlo:2^(k+2)≤x := by rw [pow2_add2]; omega
  have hhi:x<2^(k+3) := by rw [pow2_add3]; omega
  exact (Nat.log2_eq_iff (by omega)).2 ⟨hlo,hhi⟩

private def evenParentsFast (u:Nat):List Nat :=
  let k:=Nat.log2 u-2
  let h:=evenHeightFast u k
  if decide (6*2^k-1≤u ∧ u≤8*2^k-3 ∧ 2*u=8*2^k+h+k) then [h] else []

private def oddCandidate (u t:Nat):Option Nat :=
  let d:=(2*u+5)/(3^(t+1))
  let x:=2^t*d
  let k:=Nat.log2 x-2
  let h:=oddHeightFast u k t
  if decide (d%2=1 ∧ 6*2^k+1≤x ∧ x≤8*2^k-1 ∧
      2*u+5=3^(t+1)*d ∧ 2*x=8*2^k+h+k+5) then some h else none

private def oddParentsFast (u:Nat):List Nat :=
  (List.range (v3Fast (2*u+5))).filterMap (oddCandidate u)

/-- All ResetParent predecessors, generated from one even scale and the
    exact 3-adic range of odd-parent exponents. -/
def parentsFast (u:Nat):List Nat := evenParentsFast u ++ oddParentsFast u

theorem parentsFast_iff (h u:Nat) : h∈parentsFast u ↔ ResetParent h u := by
  constructor
  · intro hmem
    rcases List.mem_append.mp hmem with he | ho
    · let k:=Nat.log2 u-2
      let v:=evenHeightFast u k
      have he' : (6*2^k-1≤u ∧ u≤8*2^k-3 ∧ 2*u=8*2^k+v+k) ∧ h=v := by
        simpa [evenParentsFast,k,v] using he
      rcases he' with ⟨hp,rfl⟩
      exact Or.inl ⟨k,⟨hp.1,hp.2.1⟩,hp.2.2⟩
    · obtain ⟨t,ht,hyes⟩ := List.mem_filterMap.mp ho
      let d:=(2*u+5)/(3^(t+1))
      let x:=2^t*d
      let k:=Nat.log2 x-2
      let v:=oddHeightFast u k t
      change (if decide (d%2=1 ∧ 6*2^k+1≤x ∧ x≤8*2^k-1 ∧
          2*u+5=3^(t+1)*d ∧ 2*x=8*2^k+v+k+5) then some v else none)=some h at hyes
      by_cases hcheck : d%2=1 ∧ 6*2^k+1≤x ∧ x≤8*2^k-1 ∧
          2*u+5=3^(t+1)*d ∧ 2*x=8*2^k+v+k+5
      · simp [hcheck] at hyes
        subst h
        exact Or.inr ⟨k,t,d,hcheck.1,⟨hcheck.2.1,hcheck.2.2.1⟩,hcheck.2.2.2.1,hcheck.2.2.2.2⟩
      · simp [hcheck] at hyes
  · intro hp
    rcases hp with ⟨k,⟨hl,hh⟩,heq⟩ | ⟨k,t,d,hd,⟨hl,hh⟩,hout,heq⟩
    · have hlog:=log2_even_band u k hl hh
      have hindex:Nat.log2 u-2=k := by omega
      have hheight:evenHeightFast u (Nat.log2 u-2)=h := by
        dsimp [evenHeightFast]
        rw [hindex]
        omega
      have hheight' : evenHeightFast u k = h := by simpa [hindex] using hheight
      have hcheck:6*2^(Nat.log2 u-2)-1≤u ∧
          u≤8*2^(Nat.log2 u-2)-3 ∧
          2*u=8*2^(Nat.log2 u-2)+evenHeightFast u (Nat.log2 u-2)+(Nat.log2 u-2) := by
        rw [hindex,hheight']
        omega
      have hcheck' : decide (6*2^k≤u+1 ∧ u≤8*2^k-3 ∧
          2*u=8*2^k+h+k)=true := by
        apply decide_eq_true_iff.mpr
        exact ⟨by omega,hh,heq⟩
      have he : h∈evenParentsFast u := by
        change h∈(if decide (6*2^(Nat.log2 u-2)-1≤u ∧
          u≤8*2^(Nat.log2 u-2)-3 ∧
          2*u=8*2^(Nat.log2 u-2)+evenHeightFast u (Nat.log2 u-2)+(Nat.log2 u-2))
          then [evenHeightFast u (Nat.log2 u-2)] else [])
        rw [hindex,hheight']
        simp [hcheck']
      exact List.mem_append.mpr (Or.inl he)
    · let x:=2^t*d
      have hlog:=log2_odd_band x k (by simpa [x] using hl) (by simpa [x] using hh)
      have hindex:Nat.log2 x-2=k := by simpa [hlog]
      have hdiv:(2*u+5)/(3^(t+1))=d := by
        rw [hout]
        exact Nat.mul_div_cancel_left d (Nat.pow_pos (by decide))
      have ht:t<v3Fast (2*u+5) := pow_dvd_v3Fast (2*u+5) t (by omega) ⟨d,hout⟩
      have hindex':Nat.log2 (2^t*d)-2=k := by simpa [x] using hindex
      have hheight' : oddHeightFast u k t=h := by
        dsimp [oddHeightFast]
        rw [hdiv]
        omega
      have hcheck' : decide (d%2=1 ∧ 6*2^k+1≤2^t*d ∧
          2^t*d≤8*2^k-1 ∧ 2*u+5=3^(t+1)*d ∧
          2*(2^t*d)=8*2^k+h+k+5)=true := by
        exact decide_eq_true_iff.mpr ⟨hd,hl,hh,hout,heq⟩
      have ho : h∈oddParentsFast u := by
        apply List.mem_filterMap.mpr
        refine ⟨t,List.mem_range.mpr ht,?_⟩
        change oddCandidate u t = some h
        dsimp [oddCandidate]
        rw [hdiv,hindex',hheight',hcheck']
        rfl
      exact List.mem_append.mpr (Or.inr ho)

#print axioms parentsFast_iff
end CascadeResetInverse
