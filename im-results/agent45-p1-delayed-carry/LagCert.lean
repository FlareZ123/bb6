import LagChecker
namespace BB6.Agent45.DelayedCarry

def marginSize (n K : Nat) := 2*(n+3*K+10)+6

def resMin (s B : Nat) : Nat := min ((7*B)%2^s) (2^s-((7*B)%2^s))

theorem resMin_extend (s j B R : Nat) (hsj : s≤j) :
    resMin s B ≤ resMin j (B+2^s*R) := by
  let D := 2^s
  let Q := 2^(j-s)
  let r := 7*B%D
  let z := 7*(B+D*R)%2^j
  have hpow : 2^j=D*Q := by
    dsimp [D,Q]; rw [← Nat.pow_add]; congr 1; omega
  have hD : 0<D := Nat.two_pow_pos _
  have hQ : 0<Q := Nat.two_pow_pos _
  have hz : z<2^j := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hdiv : D∣2^j := ⟨Q,hpow⟩
  have hmod : z%D=r := by
    dsimp [z,r]
    rw [Nat.mod_mod_of_dvd _ hdiv]
    have he : 7*(B+D*R)=7*B+D*(7*R) := by rw [Nat.mul_add]; congr 1; ac_rfl
    rw [he,Nat.add_mul_mod_self_left]
  have hle : r≤z := hmod ▸ Nat.mod_le z D
  have heq : D*(z/D)+r=z := by rw [← hmod]; exact Nat.div_add_mod _ _
  have hk : z/D<Q := by
    apply (Nat.div_lt_iff_lt_mul hD).2
    simpa [hpow,Nat.mul_comm] using hz
  have hprod : D*(z/D+1)≤2^j := by
    rw [hpow]; exact Nat.mul_le_mul_left _ (by omega)
  rw [Nat.mul_add,Nat.mul_one] at hprod
  have hc : D-r≤2^j-z := by omega
  change min r (D-r)≤min z (2^j-z)
  exact Nat.le_min.mpr ⟨Nat.le_trans (Nat.min_le_left _ _) hle, Nat.le_trans (Nat.min_le_right _ _) hc⟩

def MarginOK (n K s h : Nat) (ps : List Prefix) : Bool :=
  ps.all fun p => decide ((n+K+2)*marginSize n K*2^(s+h)<6*2^n*resMin s p.1)

def LateMargin (n K j : Nat) : Prop :=
  ∀ B a, Trace n (n+j) B a → (n+K+2)*marginSize n K*2^j<6*2^n*resMin j B

theorem margin_block (n K s h j : Nat) (ps : List Prefix) (hs : 1≤s)
    (hj : s≤j) (hjs : j≤s+h) (hcover : Covered n s ps)
    (hgood : MarginOK n K s h ps=true) : LateMargin n K j := by
  intro B a htr
  obtain ⟨C,c,hpre,hE⟩ := trace_split n (n+j) B a s htr hs (by omega)
  obtain ⟨D,d,hshort⟩ := extend_prefix n s C c (n+j-s) B a n hE (by omega)
  have hm := hcover C c D d hpre hshort
  have hgood' := (List.all_eq_true.mp hgood) (C,c) hm
  have hineq : (n+K+2)*marginSize n K*2^(s+h)<6*2^n*resMin s C := of_decide_eq_true hgood'
  obtain ⟨R,hR⟩ := extend_mod n s C c (n+j-s) B a hE
  have hr := resMin_extend s j C R hj
  rw [← hR] at hr
  have hL := Nat.mul_le_mul_left ((n+K+2)*marginSize n K) (Nat.pow_le_pow_right (show 0<2 by decide) hjs)
  have hR := Nat.mul_le_mul_left (6*2^n) hr
  omega

structure Cert (n K s : Nat) (ps : List Prefix) : Prop where
  cover : Covered n s ps
  margins : ∀ j, 1≤j → j≤s → LateMargin n K j

theorem cert_first (n K : Nat) (hgood : MarginOK n K 1 0 [(1,(n+2)/2)]=true) :
    Cert n K 1 [(1,(n+2)/2)] := by
  refine ⟨covered_first n,?_⟩
  intro j hj hjs
  exact margin_block n K 1 0 j _ (by decide) (by omega) (by omega) (covered_first n) hgood

theorem cert_next (L n K s h : Nat) (ps : List Prefix) (hs : 1≤s)
    (hb : 2*n+s+h+2<2^L) (hcert : Cert n K s ps)
    (hgood : MarginOK n K s h ps=true) :
    Cert n K (s+h) (nextBlock L n s h ps) := by
  refine ⟨covered_next L n s h ps hs hb hcert.cover,?_⟩
  intro j hj hjs
  by_cases hle : j≤s
  · exact hcert.margins j hj hle
  · exact margin_block n K s h j ps hs (by omega) hjs hcert.cover hgood

#print axioms resMin_extend
#print axioms cert_next
end BB6.Agent45.DelayedCarry
