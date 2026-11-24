import RenewalScales

namespace BB6.Agent9Renewal
open BB6P1Unit
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option maxHeartbeats 2000000

theorem polynomial_block (q d n L dExp mExp b p : Nat) (D Dnew G v a : Int)
    (cert : CycleCertificate D Dnew L G)
    (hn : 8000≤n) (hDmax : D≤(2:Int)^dExp) (hMmax : (2:Int)^L-1≤(2:Int)^mExp)
    (hb : 3≤b) (hp : 1≤p) (hpmax : 2*p+1≤7)
    (hexp : dExp+mExp+2*(dExp+b+2+p)+5≤7740)
    (hv : 0<v) (hvD : v<D) (hv7 : v%7≠0) (hdq : d<q)
    (hclock : (q:Int)=7*(2:Int)^n+a)
    (ha : ∀ j : Nat, j≤n → Bound (a+j) (6*(n:Int)))
    (hinit : Bound (D*(d:Int)-7*(2:Int)^n*v) (D*((2:Int)^b*(n:Int)^p))) :
    (∀ j≤n, 2≤run q d j ∧ run q d j+8≤q+j) ∧
    ∃ v' : Int, 0<v' ∧ v'<Dnew ∧ v'%7≠0 ∧
      Bound (Dnew*(run q d n:Int)-7*(2:Int)^n*v') (Dnew*((2:Int)^(dExp+b+2+p+4)*(n:Int)^(p+1))) := by
  let M := (2:Int)^L-1
  have hDcast : (D.toNat:Int)=D := Int.toNat_of_nonneg (by omega)
  have hMcast : (M.toNat:Int)=M := Int.toNat_of_nonneg (by have := cert.Mpos; omega)
  have hDN : 0<D.toNat := by omega
  have hMN : 0<M.toNat := by have := cert.Mpos; omega
  have hDmaxN : D.toNat≤2^dExp := by
    have h : (D.toNat:Int)≤((2^dExp:Nat):Int) := by rw [hDcast,Int.natCast_pow]; exact hDmax
    exact_mod_cast h
  have hMmaxN : M.toNat≤2^mExp := by
    have h : (M.toNat:Int)≤((2^mExp:Nat):Int) := by rw [hMcast,Int.natCast_pow]; exact hMmax
    exact_mod_cast h
  let ell := dExp+b+2+p*(n.log2+1)
  obtain ⟨hs,hsml,hgap,hE⟩ := polynomial_scale n D.toNat M.toNat dExp mExp b p hn hDN hMN hDmaxN hMmaxN hb hp hpmax hexp
  change 2^ell≤2^n at hs
  change D.toNat*(2^b*n^p+6*n)<2^ell at hsml
  change D.toNat*M.toNat*2^ell*(2^ell*(2*(6*n)+2)+6*n+8)<2^n at hgap
  change 2^ell*(2*(6*n)+2)≤2^(dExp+b+2+p+4)*n^(p+1) at hE
  have hsI : (2:Int)^ell≤(2:Int)^n := by exact_mod_cast hs
  have hsmlI : D*((2:Int)^b*(n:Int)^p+6*(n:Int))<(2:Int)^ell := by
    rw [←hDcast]; exact_mod_cast hsml
  have hgapI : D*M*(2:Int)^ell*((2:Int)^ell*(2*(6*(n:Int))+2)+6*(n:Int)+8)<(2:Int)^n := by
    rw [←hDcast,←hMcast]; exact_mod_cast hgap
  have hEI : (2:Int)^ell*(2*(6*(n:Int))+2)≤(2:Int)^(dExp+b+2+p+4)*(n:Int)^(p+1) := by exact_mod_cast hE
  exact certified_block q d n ell L D Dnew G v a ((2:Int)^b*(n:Int)^p) (6*(n:Int)) ((2:Int)^(dExp+b+2+p+4)*(n:Int)^(p+1)) cert hv hvD hv7 hdq hclock (by omega) (Int.mul_nonneg (Int.pow_nonneg (by decide)) (Int.pow_nonneg (by omega))) ha hinit hsI hsmlI hgapI hEI

#print axioms polynomial_block

theorem large_power (n : Nat) (hn : 8000≤n) : 16*n<2^n := by
  have h1 : n≤n^7 := by simpa using Nat.pow_le_pow_right (show 0<n by omega) (show 1≤7 by decide)
  have h2 : 16≤2^7740 := Nat.pow_le_pow_right (show 0<2 by decide) (show 4≤7740 by decide)
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul h2 h1) (numeric_dom n hn)

theorem three_blocks_endpoint (n k : Nat) (hn : 8000≤n) (hk : k≤5*n+3) :
    (∀ j≤3*n, 2≤run (7*2^n-k) (2^n+k) j) ∧
    ∃ p : Int, 0<p ∧ p<D3 ∧ p%7≠0 ∧
      Bound (D3*(run (7*2^n-k) (2^n+k) (3*n):Int)-7*(2:Int)^n*p)
        (D3*((2:Int)^192*(n:Int)^4)) := by
  let P := 2^n
  let q0 := 7*P-k
  let d0 := P+k
  let q1 := q0+n
  let d1 := run q0 d0 n
  let q2 := q1+n
  let d2 := run q1 d1 n
  have hP : 16*n<P := large_power n hn
  have hq0 : q0+k=7*P := by dsimp [q0]; omega
  have hclock0 : (q0:Int)=7*(2:Int)^n-(k:Int) := by
    have h : (q0:Int)+(k:Int)=7*(2:Int)^n := by exact_mod_cast hq0
    omega
  have hd0q0 : d0<q0 := by dsimp [d0]; omega
  have hclock1 : (q1:Int)=7*(2:Int)^n+(-(k:Int)+(n:Int)) := by dsimp [q1]; push_cast; omega
  have hclock2 : (q2:Int)=7*(2:Int)^n+(-(k:Int)+2*(n:Int)) := by dsimp [q2,q1]; push_cast; omega
  have ha0 : ∀ j : Nat, j≤n → Bound (-(k:Int)+j) (6*(n:Int)) := by intro j hj; unfold Bound; omega
  have ha1 : ∀ j : Nat, j≤n → Bound (-(k:Int)+(n:Int)+j) (6*(n:Int)) := by intro j hj; unfold Bound; omega
  have ha2 : ∀ j : Nat, j≤n → Bound (-(k:Int)+2*(n:Int)+j) (6*(n:Int)) := by intro j hj; unfold Bound; omega
  have hst0 : Bound (D0*(d0:Int)-7*(2:Int)^n*1) (D0*((2:Int)^3*(n:Int)^1)) := by
    have he : (d0:Int)=(2:Int)^n+(k:Int) := by dsimp [d0,P]
    rw [he]; unfold Bound D0; simp only [Int.pow_one]; omega
  obtain ⟨hs0,v1,hv1,hv1D,hv17,hB1⟩ := polynomial_block q0 d0 n 3 3 3 3 1 D0 D1 1 1 (-(k:Int)) cert0 hn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd0q0 (by omega) ha0 hst0
  have hd1q1 : d1<q1 := run_lt q0 d0 n hd0q0
  obtain ⟨hs1,v2,hv2,hv2D,hv27,hB2⟩ := polynomial_block q1 d1 n 147 9 147 13 2 D1 D2 49 v1 (-(k:Int)+(n:Int)) cert1 hn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv1 hv1D hv17 hd1q1 hclock1 ha1 hB1
  have hd2q2 : d2<q2 := run_lt q1 d1 n hd1q1
  obtain ⟨hs2,v3,hv3,hv3D,hv37,hB3⟩ := polynomial_block q2 d2 n 7203 153 7203 30 3 D2 D3 2401 v2 (-(k:Int)+2*(n:Int)) cert2 hn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv2 hv2D hv27 hd2q2 hclock2 ha2 hB2
  constructor
  · intro j hj
    change 2≤run q0 d0 j
    by_cases h0 : j≤n
    · exact (hs0 j h0).1
    · by_cases h1 : j≤2*n
      · have he : n+(j-n)=j := by omega
        rw [←he,run_add]; exact (hs1 (j-n) (by omega)).1
      · have he : n+(n+(j-2*n))=j := by omega
        rw [←he,run_add,run_add]; exact (hs2 (j-2*n) (by omega)).1
  · refine ⟨v3,hv3,hv3D,hv37,?_⟩
    change Bound (D3*(run q0 d0 (3*n):Int)-7*(2:Int)^n*v3) (D3*((2:Int)^192*(n:Int)^4))
    rw [show 3*n=n+(n+n) by omega,run_add,run_add]
    exact hB3

theorem three_blocks (n k : Nat) (hn : 8000≤n) (hk : k≤4*n+3) :
    ∀ j≤3*n, 2≤run (7*2^n-k) (2^n+k) j :=
  (three_blocks_endpoint n k hn (by omega)).1

private theorem initial_doubling (n q j : Nat) (hq : 4*2^n<q+1)
    (hj : j≤n+2) : run q 1 j=2^j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hp := Nat.pow_le_pow_right (show 0<2 by decide) hj
    rw [show 2^(n+2)=4*2^n by rw [Nat.pow_add]; simp; omega] at hp
    have hp2 : 2*2^j=2^(j+1) := by rw [Nat.pow_succ]; ac_rfl
    rw [run,unit,ih (by omega),hp2,Nat.mod_eq_of_lt (by omega)]

theorem no_return_four_n (n q k : Nat) (hn : 8000≤n)
    (hclock : q+k=7*2^n-n-3) (hk : 0<k) (hcut : k≤4*n+3) : run q 1 k≠1 := by
  have hP := large_power n hn
  have hq : 4*2^n<q+1 := by omega
  by_cases h0 : k≤n+2
  · rw [initial_doubling n q k hq h0]
    have hp : 2≤2^k := Nat.pow_le_pow_right (show 0<2 by decide) (show 1≤k by omega)
    omega
  · have hclock' : q+n+3=7*2^n-k := by omega
    have hr : run q 1 (n+3)=2^n+k := by
      rw [show n+3=n+2+1 by omega,run,unit,initial_doubling n q (n+2) hq (by omega)]
      rw [show 2*2^(n+2)=8*2^n by rw [Nat.pow_add]; simp; omega]
      rw [show q+(n+2)+1=7*2^n-k by omega]
      rw [Nat.mod_eq_sub_mod (by omega),show 8*2^n-(7*2^n-k)=2^n+k by omega,Nat.mod_eq_of_lt (by omega)]
    have he : (n+3)+(k-(n+3))=k := by omega
    have hs := three_blocks n k hn hcut (k-(n+3)) (by omega)
    rw [←he,run_add,hr,show q+(n+3)=7*2^n-k by omega]
    omega

#print axioms three_blocks
#print axioms no_return_four_n
end BB6.Agent9Renewal
