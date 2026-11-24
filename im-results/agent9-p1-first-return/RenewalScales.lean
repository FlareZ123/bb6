import RenewalNumeric

namespace BB6.Agent9Renewal

set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option maxHeartbeats 1000000

theorem scale_bounds (n c p : Nat) (hn : 0<n) :
    2^c*n^p≤2^(c+p*(n.log2+1)) ∧ 2^(c+p*(n.log2+1))≤2^(c+p)*n^p := by
  obtain ⟨hl,hh⟩ := log_window n hn
  let t := n.log2+1
  change n<2^t at hl
  change 2^t≤2*n at hh
  have h1 := Nat.pow_le_pow_left (show n≤2^t by omega) p
  have h2 := Nat.pow_le_pow_left (show 2^t≤2*n by omega) p
  have h1' := Nat.mul_le_mul_left (2^c) h1
  have h2' := Nat.mul_le_mul_left (2^c) h2
  rw [Nat.mul_pow] at h2'
  have he : 2^(c+p*t)=2^c*(2^t)^p := by rw [Nat.pow_add,Nat.mul_comm p t,Nat.pow_mul]
  have he' : 2^c*(2^p*n^p)=2^(c+p)*n^p := by rw [Nat.pow_add]; ac_rfl
  rw [←he] at h1' h2'
  rw [he'] at h2'
  exact ⟨h1',h2'⟩

/-- A polynomial-sized state perturbation yields a certified split and the
next polynomial bound. All three concrete block scales use this lemma. -/
theorem polynomial_scale (n D M dExp mExp b p : Nat)
    (hn : 8000≤n) (hD : 0<D) (hM : 0<M)
    (hDmax : D≤2^dExp) (hMmax : M≤2^mExp)
    (hb : 3≤b) (hp : 1≤p) (hpmax : 2*p+1≤7)
    (hexp : dExp+mExp+2*(dExp+b+2+p)+5≤7740) :
    let c := dExp+b+2
    let ell := c+p*(n.log2+1)
    let S := 2^ell
    let B := 2^b*n^p
    let C := 5*n
    let Bnew := 2^(c+p+4)*n^(p+1)
    S≤2^n ∧ D*(B+C)<S ∧ D*M*S*(S*(2*C+2)+C+8)<2^n ∧ S*(2*C+2)≤Bnew := by
  dsimp only
  let c := dExp+b+2
  let ell := c+p*(n.log2+1)
  let S := 2^ell
  let B := 2^b*n^p
  let C := 5*n
  let Bnew := 2^(c+p+4)*n^(p+1)
  change S≤2^n ∧ D*(B+C)<S ∧ D*M*S*(S*(2*C+2)+C+8)<2^n ∧ S*(2*C+2)≤Bnew
  have hnp : n≤n^p := by
    simpa using Nat.pow_le_pow_right (show 0<n by omega) hp
  have h2b := Nat.pow_le_pow_right (show 0<2 by decide) hb
  have hC : C≤B := by
    have hh := Nat.mul_le_mul (show 5≤2^b by omega) hnp
    exact hh
  have hBpos : 0<B := Nat.mul_pos (Nat.two_pow_pos _) (Nat.pow_pos (by omega))
  have hSpos : 0<S := Nat.two_pow_pos _
  have hSb := scale_bounds n c p (by omega)
  change 2^c*n^p≤S ∧ S≤2^(c+p)*n^p at hSb
  have hsmall : D*(B+C)<S := by
    have hm := Nat.mul_le_mul hDmax (show B+C≤2*B by omega)
    have he : 2^dExp*(2*B)=2^(dExp+b+1)*n^p := by
      dsimp [B]
      rw [Nat.pow_succ,Nat.pow_add]
      ac_rfl
    rw [he] at hm
    have hpow := Nat.pow_lt_pow_right (show 1<2 by decide) (show dExp+b+1<c by dsimp [c]; omega)
    have hlt := Nat.mul_lt_mul_of_pos_right hpow (show 0<n^p by exact Nat.pow_pos (by omega))
    omega
  have hE : S*(2*C+2)≤Bnew := by
    have hm := Nat.mul_le_mul hSb.2 (show 2*C+2≤16*n by dsimp [C]; omega)
    have he : (2^(c+p)*n^p)*(16*n)=Bnew := by
      change (2^(c+p)*n^p)*(16*n)=2^(c+p+4)*n^(p+1)
      calc
        _ = (2^(c+p)*2^4)*(n^p*n) := by change (2^(c+p)*n^p)*(2^4*n)=_; ac_rfl
        _ = _ := by rw [←Nat.pow_add 2 (c+p) 4,←Nat.pow_succ n p]
    rwa [he] at hm
  have hCn : C+8≤Bnew := by
    have hn' := Nat.pow_le_pow_right (show 0<n by omega) (show 1≤p+1 by omega)
    have hp' := Nat.pow_le_pow_right (show 0<2 by decide) (show 4≤c+p+4 by omega)
    have hm := Nat.mul_le_mul hp' hn'
    simp only [Nat.pow_one] at hm
    dsimp [Bnew,C] at *
    omega
  have hgap : D*M*S*(S*(2*C+2)+C+8)<2^n := by
    have hR := Nat.mul_le_mul hDmax hMmax
    rw [←Nat.pow_add] at hR
    have hRS := Nat.mul_le_mul hR hSb.2
    have hsum : S*(2*C+2)+C+8≤2*Bnew := by omega
    have hm := Nat.mul_le_mul hRS hsum
    have he : 2^(dExp+mExp)*(2^(c+p)*n^p)*(2*Bnew)=2^(dExp+mExp+2*(c+p)+5)*n^(2*p+1) := by
      change 2^(dExp+mExp)*(2^(c+p)*n^p)*(2^1*(2^(c+p+4)*n^(p+1)))=_
      calc
        _ = (2^(dExp+mExp)*2^(c+p)*2^(c+p+4)*2^1)*(n^p*n^(p+1)) := by ac_rfl
        _ = _ := by
          rw [←Nat.pow_add 2 (dExp+mExp) (c+p),←Nat.pow_add 2 ((dExp+mExp)+(c+p)) (c+p+4),←Nat.pow_add 2 ((dExp+mExp)+(c+p)+(c+p+4)) 1,←Nat.pow_add n p (p+1)]
          rw [show dExp+mExp+(c+p)+(c+p+4)+1=dExp+mExp+2*(c+p)+5 by omega,show p+(p+1)=2*p+1 by omega]
    rw [he] at hm
    have hp1 := Nat.pow_le_pow_right (show 0<2 by decide) (show dExp+mExp+2*(c+p)+5≤7740 by dsimp [c]; omega)
    have hp2 := Nat.pow_le_pow_right (show 0<n by omega) hpmax
    have hdom := Nat.mul_le_mul hp1 hp2
    exact Nat.lt_of_le_of_lt (Nat.le_trans hm hdom) (numeric_dom n hn)
  have hSle : S≤2^n := by
    have hDM : 1≤D*M := by have := Nat.mul_pos hD hM; omega
    have hm := Nat.mul_le_mul_right S hDM
    simp only [Nat.one_mul] at hm
    have hs : 1≤S*(2*C+2)+C+8 := by omega
    have hm' := Nat.mul_le_mul_left (D*M*S) hs
    simp only [Nat.mul_one] at hm'
    exact Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.le_trans hm hm') hgap)
  exact ⟨hSle,hsmall,hgap,hE⟩

#print axioms polynomial_scale
end BB6.Agent9Renewal
