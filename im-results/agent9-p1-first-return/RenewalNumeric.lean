import RenewalBlock

namespace BB6.Agent9Renewal
open BB6P1Unit

set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option maxHeartbeats 1000000

/-- A small universal exponential margin, enough for all three blocks. -/
theorem numeric_dom (n : Nat) (hn : 8000≤n) : 2^7740*n^7 < 2^n := by
  have step (a : Nat) (ha : 16≤a) : (a+1)^7 ≤ 2*a^7 := by
    have h : 16*(a+1)≤17*a := by omega
    have hp := Nat.pow_le_pow_left h 7
    rw [Nat.mul_pow,Nat.mul_pow] at hp
    have hc : 17^7≤16^7*2 := by decide
    have hm := Nat.mul_le_mul_right (a^7) hc
    have he : 16^7*2*a^7=16^7*(2*a^7) := by ac_rfl
    rw [he] at hm
    exact Nat.le_of_mul_le_mul_left (Nat.le_trans hp hm) (by decide)
  have h : ∀ j : Nat, 2^7740*(8000+j)^7 < 2^(8000+j) := by
    intro j
    induction j with
    | zero => decide
    | succ j ih =>
      have hs := step (8000+j) (by omega)
      have hm := Nat.mul_le_mul_left (2^7740) hs
      have h2 := Nat.mul_lt_mul_of_pos_left ih (by decide : 0<2)
      rw [show 8000+(j+1)=8000+j+1 by omega,Nat.pow_succ]
      have he : 2^7740*(2*(8000+j)^7)=2*(2^7740*(8000+j)^7) := by ac_rfl
      rw [he] at hm
      omega
  have hh := h (n-8000)
  rw [show 8000+(n-8000)=n by omega] at hh
  exact hh

/-- ceil(log2(n+1)) gives a dyadic between n and 2n. -/
theorem log_window (n : Nat) (hn : 0<n) :
    n<2^(n.log2+1) ∧ 2^(n.log2+1)≤2*n := by
  have h := (Nat.log2_lt (by omega : n≠0)).mp (show n.log2<n.log2+1 by omega)
  have h' : 2^n.log2≤n := by
    by_cases hc : 2^n.log2≤n
    · exact hc
    · have hh := (Nat.log2_lt (by omega : n≠0)).mpr (show n<2^n.log2 by omega)
      omega
  refine ⟨h,?_⟩
  rw [Nat.pow_succ]
  omega

/-- Generic choice of split from a certified dyadic scale. -/
theorem window_from_scale (n ell : Nat) (D R B C : Int)
    (hscale : (2:Int)^ell≤(2:Int)^n)
    (hsmall : D*(B+C)<(2:Int)^ell)
    (hgap : R*(2:Int)^ell*((2:Int)^ell*(2*C+2)+C+8)<(2:Int)^n) :
    let K := n-ell
    K≤n ∧ n-K=ell ∧
    D*(2:Int)^K*(B+C)<(2:Int)^n ∧
    R*((2:Int)^(n-K)*(2*C+2)+C+8)<(2:Int)^K := by
  have hell : ell≤n := by
    by_cases hh : ell≤n
    · exact hh
    · have hp := Nat.pow_lt_pow_right (show 1<2 by decide) (show n<ell by omega)
      have hpi : (2:Int)^n<(2:Int)^ell := by exact_mod_cast hp
      omega
  let K := n-ell
  have hK : K≤n := by dsimp [K]; omega
  have hsub : n-K=ell := by dsimp [K]; omega
  have hP : (2:Int)^n=(2:Int)^K*(2:Int)^ell := by rw [←Int.pow_add,show K+ell=n by dsimp [K]; omega]
  refine ⟨hK,hsub,?_,?_⟩
  · have hm := Int.mul_lt_mul_of_pos_left hsmall (show 0<(2:Int)^K by exact Int.pow_pos (by decide))
    have hh : (2:Int)^K*(D*(B+C))=D*(2:Int)^K*(B+C) := by ac_rfl
    rw [hh,←hP] at hm
    exact hm
  · rw [hsub]
    have hh : R*(2:Int)^ell*((2:Int)^ell*(2*C+2)+C+8)=(2:Int)^ell*(R*((2:Int)^ell*(2*C+2)+C+8)) := by ac_rfl
    have hp' : (2:Int)^n=(2:Int)^ell*(2:Int)^K := by rw [hP]; ac_rfl
    rw [hh,hp'] at hgap
    exact Int.lt_of_mul_lt_mul_left hgap (Int.pow_nonneg (by decide))

-- Closed denominator data. The three orders are 3, 147 and 7203.
def D0 : Int := 7
def D1 : Int := 343
def D2 : Int := 49*((2:Int)^147-1)
def D3 : Int := 7*D2*((2:Int)^7203-1)/2401

-- Each certificate is small arithmetic even though D3 has 7348 bits.
structure CycleCertificate (D Dnew : Int) (L : Nat) (G : Int) where
  pos : 0<D
  odd : D%2=1
  divides : D ∣ (2:Int)^L-1
  Mpos : 0<(2:Int)^L-1
  Gpos : 0<G
  U : Int
  V : Int
  Dfactor : D=7*G*U
  Mfactor : (2:Int)^L-1=7*G*V
  l : Int
  Lfactor : (L:Int)=l*G
  lunit : l%7≠0
  next : 7*D*((2:Int)^L-1)=G*Dnew
  next7 : Dnew%7=0

def cert0 : CycleCertificate D0 D1 3 1 where
  pos := by decide
  odd := by decide
  divides := by decide
  Mpos := by decide
  Gpos := by decide
  U := 1
  V := 1
  Dfactor := by decide
  Mfactor := by decide
  l := 3
  Lfactor := by decide
  lunit := by decide
  next := by decide
  next7 := by decide

def cert1 : CycleCertificate D1 D2 147 49 where
  pos := by decide
  odd := by decide
  divides := by decide
  Mpos := by decide
  Gpos := by decide
  U := 1
  V := ((2:Int)^147-1)/343
  Dfactor := by decide
  Mfactor := by decide
  l := 3
  Lfactor := by decide
  lunit := by decide
  next := by decide
  next7 := by decide

def cert2 : CycleCertificate D2 D3 7203 2401 where
  pos := by decide
  odd := by decide
  divides := by decide
  Mpos := by decide
  Gpos := by decide
  U := D2/16807
  V := ((2:Int)^7203-1)/16807
  Dfactor := by decide
  Mfactor := by decide
  l := 3
  Lfactor := by decide
  lunit := by decide
  next := by decide
  next7 := by decide

/-- A numeric block accepts a phase certificate and certified dyadic scale. -/
theorem certified_block (q d n ell L : Nat) (D Dnew G p a B C Bnew : Int)
    (cert : CycleCertificate D Dnew L G)
    (hp : 0<p) (hpD : p<D) (hp7 : p%7≠0) (hdq : d<q)
    (hclock : (q:Int)=7*(2:Int)^n+a)
    (hC : 0≤C) (hB : 0≤B) (ha : ∀ j : Nat, j≤n → Bound (a+j) C)
    (hinit : Bound (D*(d:Int)-7*(2:Int)^n*p) (D*B))
    (hscale : (2:Int)^ell≤(2:Int)^n)
    (hsmall : D*(B+C)<(2:Int)^ell)
    (hgap : D*((2:Int)^L-1)*(2:Int)^ell*((2:Int)^ell*(2*C+2)+C+8)<(2:Int)^n)
    (hBnew : (2:Int)^ell*(2*C+2)≤Bnew) :
    (∀ j≤n, 2≤run q d j ∧ run q d j+8≤q+j) ∧
    ∃ p' : Int, 0<p' ∧ p'<Dnew ∧ p'%7≠0 ∧
      Bound (Dnew*(run q d n:Int)-7*(2:Int)^n*p') (Dnew*Bnew) := by
  let K := n-ell
  obtain ⟨hK,hsub,hs,hg⟩ := window_from_scale n ell D (D*((2:Int)^L-1)) B C hscale hsmall hgap
  obtain ⟨hall,p',hp',hp'D,hp'7,hbound⟩ := renewal_block q d n K L D p a C B G Dnew cert.U cert.V cert.l cert.pos cert.odd hp hpD hp7 hdq hclock cert.divides cert.Mpos cert.Gpos cert.Dfactor cert.Mfactor cert.Lfactor cert.lunit cert.next cert.next7 hC hB ha hinit hK hs hg
  refine ⟨hall,p',hp',hp'D,hp'7,?_⟩
  have hDn : 0≤Dnew := by omega
  rw [hsub] at hbound
  exact bound_weaken hbound (Int.mul_le_mul_of_nonneg_left hBnew hDn)

#print axioms numeric_dom
#print axioms window_from_scale
#print axioms cert0
#print axioms cert1
#print axioms cert2
#print axioms certified_block
end BB6.Agent9Renewal
