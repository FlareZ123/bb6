import RenewalBounds

namespace BB6.Agent9Renewal
open BB6P1Unit
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

def grid0 : RenewalGrid D0 1 3 where
  pos := by decide
  odd := by decide
  Gpos := by decide
  divides := by decide
  Mpos := by decide
  U := 1
  V := 1
  l := 3
  Dfactor := by decide
  Mfactor := by decide
  Lfactor := by decide
  Uunit := by decide
  Vunit := by decide
  lunit := by decide

def grid1 : RenewalGrid D1 49 147 where
  pos := by decide
  odd := by decide
  Gpos := by decide
  divides := by decide
  Mpos := by decide
  U := 1
  V := ((2:Int)^147-1)/343
  l := 3
  Dfactor := by decide
  Mfactor := by decide
  Lfactor := by decide
  Uunit := by decide
  Vunit := by decide
  lunit := by decide

def grid_cert (D G : Int) (L : Nat) (g : RenewalGrid D G L) :
    CycleCertificate D (49*g.U*((2:Int)^L-1)) L G where
  pos := g.pos
  odd := g.odd
  divides := g.divides
  Mpos := g.Mpos
  Gpos := g.Gpos
  U := g.U
  V := g.V
  Dfactor := g.Dfactor
  Mfactor := g.Mfactor
  l := g.l
  Lfactor := g.Lfactor
  lunit := g.lunit
  next := by
    calc
      7*D*((2:Int)^L-1)=7*(7*G*g.U)*((2:Int)^L-1) := congrArg (fun x : Int => 7*x*((2:Int)^L-1)) g.Dfactor
      _ = _ := by grind only
  next7 := by
    have he : 49*g.U*((2:Int)^L-1)=7*(7*g.U*((2:Int)^L-1)) := by grind only
    rw [he,Int.mul_emod]
    simp

def blockThreshold (D : Int) (L B C p : Nat) : Nat :=
  coefficientThreshold (gapCoeff D.toNat (((2:Int)^L-1).toNat) B C) (2*p+1)

/-- A general block with a polynomial initial error envelope and a fixed
linear clock envelope. The next envelope is explicit. -/
theorem generic_block (q d n L B C s : Nat) (D G p a : Int) (g : RenewalGrid D G L)
    (hn : 1≤n) (hB : 0<B) (hs : 1≤s)
    (hdom : blockThreshold D L B C s≤n)
    (hp : 0<p) (hpD : p<D) (hp7 : p%7≠0) (hdq : d<q)
    (hclock : (q:Int)=7*(2:Int)^n+a)
    (ha : ∀ j : Nat, j≤n → Bound (a+j) ((C:Int)*n))
    (hinit : Bound (D*(d:Int)-7*(2:Int)^n*p) (D*((B:Int)*(n:Int)^s))) :
    (∀ j≤n, 2≤run q d j ∧ run q d j+8≤q+j) ∧
    ∃ p' : Int, 0<p' ∧ p'<49*g.U*((2:Int)^L-1) ∧ p'%7≠0 ∧
      Bound ((49*g.U*((2:Int)^L-1))*(run q d n:Int)-7*(2:Int)^n*p')
        ((49*g.U*((2:Int)^L-1))*((nextCoeff D.toNat B C:Int)*(n:Int)^(s+1))) := by
  let M := (2:Int)^L-1
  have hD := g.pos
  have hM : 0<M := g.Mpos
  have hDcast : (D.toNat:Int)=D := Int.toNat_of_nonneg (by omega)
  have hMcast : (M.toNat:Int)=M := Int.toNat_of_nonneg (by omega)
  have hDN : 0<D.toNat := by omega
  have hMN : 0<M.toNat := by omega
  obtain ⟨ell,hscale,hsmall,hgap,hE⟩ := generic_scale n D.toNat M.toNat B C s hn hDN hMN hB hs hdom
  have hscaleI : (2:Int)^ell≤(2:Int)^n := by exact_mod_cast hscale
  have hsmallI : D*((B:Int)*(n:Int)^s+(C:Int)*n)<(2:Int)^ell := by
    rw [←hDcast]
    exact_mod_cast hsmall
  have hgapI : D*M*(2:Int)^ell*((2:Int)^ell*(2*((C:Int)*n)+2)+(C:Int)*n+8)<(2:Int)^n := by
    rw [←hDcast,←hMcast]
    exact_mod_cast hgap
  have hEI : (2:Int)^ell*(2*((C:Int)*n)+2)≤(nextCoeff D.toNat B C:Int)*(n:Int)^(s+1) := by exact_mod_cast hE
  exact certified_block q d n ell L D (49*g.U*M) G p a ((B:Int)*(n:Int)^s) ((C:Int)*n) ((nextCoeff D.toNat B C:Int)*(n:Int)^(s+1)) (grid_cert D G L g) hp hpD hp7 hdq hclock (Int.mul_nonneg (by omega) (by omega)) (Int.mul_nonneg (by omega) (Int.pow_nonneg (by omega))) ha hinit hscaleI hsmallI hgapI hEI

#print axioms generic_block
/-- Computable period/denominator data. The quotient is exact on valid grids. -/
structure GridIndex where
  D : Int
  G : Int
  L : Nat

def firstGrid : GridIndex := ⟨7,1,3⟩
def GridIndex.advance (i : GridIndex) : GridIndex :=
  let U := i.D/(7*i.G)
  ⟨49*U*((2:Int)^i.L-1),49*i.G,i.L*49*U.toNat⟩

def GridIndex.valid (i : GridIndex) : Prop :=
  Nonempty (RenewalGrid i.D i.G i.L) ∧ (i=firstGrid ∨ i.G%7=0)

theorem firstGrid_valid : firstGrid.valid := ⟨⟨grid0⟩,Or.inl rfl⟩

theorem grid_quotient (i : GridIndex) (g : RenewalGrid i.D i.G i.L) : i.D/(7*i.G)=g.U := by
  have h := congrArg (fun x : Int => x/(7*i.G)) g.Dfactor
  rw [Int.mul_ediv_cancel_left _ (by have := g.Gpos; omega)] at h
  exact h

theorem advance_valid (i : GridIndex) (hi : i.valid) : i.advance.valid := by
  obtain ⟨⟨g⟩,h⟩ := hi
  rcases h with he|h7
  · subst i
    exact ⟨⟨grid1⟩,Or.inr (by decide)⟩
  · constructor
    · have hnew := grid_next i.D i.G i.L g h7
      unfold GridIndex.advance
      rw [grid_quotient i g]
      exact hnew
    · right
      change (49*i.G)%7=0
      omega

/-- A threshold that is computed from a fixed number of renewal blocks,
without searching over index n or any orbit. -/
def manyThreshold : Nat → GridIndex → Nat → Nat → Nat → Nat
  | 0,_,_,_,_ => 1
  | h+1,i,B,C,s => max (blockThreshold i.D i.L B C s)
      (manyThreshold h i.advance (nextCoeff i.D.toNat B C) C (s+1))

theorem many_blocks (h : Nat) (i : GridIndex) (B C s : Nat) (hi : i.valid)
    (hB : 0<B) (hs : 1≤s) (n q d : Nat) (p a : Int)
    (hn : 1≤n) (hdom : manyThreshold h i B C s≤n)
    (hp : 0<p) (hpD : p<i.D) (hp7 : p%7≠0) (hdq : d<q)
    (hclock : (q:Int)=7*(2:Int)^n+a)
    (ha : ∀ j : Nat, j≤h*n → Bound (a+j) ((C:Int)*n))
    (hinit : Bound (i.D*(d:Int)-7*(2:Int)^n*p) (i.D*((B:Int)*(n:Int)^s))) :
    ∀ j : Nat, 0<j → j≤h*n → 2≤run q d j ∧ run q d j+8≤q+j := by
  induction h generalizing i B s q d p a with
  | zero => intro j hj hj'; simp at hj'; omega
  | succ h ih =>
    obtain ⟨⟨g⟩,hig⟩ := hi
    have hdom0 : blockThreshold i.D i.L B C s≤n := Nat.le_trans (Nat.le_max_left _ _) hdom
    have hdom1 : manyThreshold h i.advance (nextCoeff i.D.toNat B C) C (s+1)≤n := Nat.le_trans (Nat.le_max_right _ _) hdom
    have hhn : (h+1)*n=h*n+n := by rw [Nat.add_mul]; simp
    have ha0 : ∀ j : Nat, j≤n → Bound (a+j) ((C:Int)*n) := by
      intro j hj
      exact ha j (by omega)
    obtain ⟨hblock,p',hp',hp'D,hp'7,hinit'⟩ := generic_block q d n i.L B C s i.D i.G p a g hn hB hs hdom0 hp hpD hp7 hdq hclock ha0 hinit
    have hD' : i.advance.D=49*g.U*((2:Int)^i.L-1) := by
      change 49*(i.D/(7*i.G))*((2:Int)^i.L-1)=_
      rw [grid_quotient i g]
    have hB' : 0<nextCoeff i.D.toNat B C := by
      have hD := g.pos
      have hDnat : 0<i.D.toNat := by omega
      unfold nextCoeff scaleCoeff
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) hDnat) (by omega)) (by omega)
    have ha' : ∀ j : Nat, j≤h*n → Bound (a+(n:Int)+j) ((C:Int)*n) := by
      intro j hj
      have hh := ha (n+j) (by omega)
      push_cast at hh
      rwa [Int.add_assoc]
    have hclock' : ((q+n:Nat):Int)=7*(2:Int)^n+(a+(n:Int)) := by push_cast; omega
    have hh := ih i.advance (nextCoeff i.D.toNat B C) (s+1) (advance_valid i ⟨⟨g⟩,hig⟩)
      hB' (by omega) (q+n) (run q d n) p' (a+(n:Int)) hdom1 hp' (by rwa [hD']) hp'7
      (run_lt q d n hdq) hclock' ha' (by rwa [hD'])
    intro j hj hj'
    by_cases hle : j≤n
    · exact hblock j hle
    · have he : n+(j-n)=j := by omega
      have hrest := hh (j-n) (by omega) (by omega)
      rw [←he,run_add]
      simpa [Nat.add_assoc] using hrest

#print axioms advance_valid
#print axioms many_blocks
end BB6.Agent9Renewal
