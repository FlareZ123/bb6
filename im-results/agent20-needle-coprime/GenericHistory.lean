import GenericAffineSource

namespace NeedleRotation.Asymmetric

/-- The exact shifted source predecessor relation, recording the original
    valuation and odd cofactor. -/
def inverseEdge (b q w : Nat) : Prop :=
  b=2^w*(2*q+3)+w+3*(q+1)

def prev (q w : Nat) : Nat := 2^w*(2*q+3)

/-- Affine reverse node. Every step uses a genuine high-level inverse edge. -/
inductive AffineNode (a P : Nat) : Nat → Nat → Nat → Int → Prop
  | root (b : Nat) (hb : 2*b=2^a*P) : AffineNode a P b 1 0 0
  | step {b L x : Nat} {d : Int} (h : AffineNode a P b L x d)
      (q w : Nat) (he : inverseEdge b q w) :
      AffineNode a P (prev q w) (L*(2^(w+1)+3)) (x+(w+1))
        ((2:Int)^(w+1)*(d+(L:Int)*(5-2*((w+1:Nat):Int))))

/-- Unannotated ancestry, to ensure the affine representation covers all
    legal inverse histories, not merely a subset of convenient histories. -/
inductive Ancestor (a P : Nat) : Nat → Prop
  | root (b : Nat) (hb : 2*b=2^a*P) : Ancestor a P b
  | step {b : Nat} (h : Ancestor a P b) (q w : Nat)
      (he : inverseEdge b q w) : Ancestor a P (prev q w)

theorem ancestor_has_affine (a P b : Nat) (h : Ancestor a P b) :
    ∃ L x d, AffineNode a P b L x d := by
  induction h with
  | root b hb => exact ⟨1,0,0,AffineNode.root b hb⟩
  | step h q w he ih =>
    obtain ⟨L,x,d,hh⟩:=ih
    exact ⟨_,_,_,AffineNode.step hh q w he⟩

theorem edge_eq (b q w : Nat) (he : inverseEdge b q w) :
    b=(2^(w+1)+3)*q+3*2^w+w+3 := by
  unfold inverseEdge at he
  rw [Nat.pow_succ]
  grind

theorem edge_drift (b q w : Nat) (he : inverseEdge b q w) : prev q w<b := by
  unfold inverseEdge prev at *
  omega

theorem edge_factor (b q w : Nat) (he : inverseEdge b q w) :
    2*(b:Int)+5-2*((w+1:Nat):Int)=((2:Int)^(w+1)+3)*(2*(q:Int)+3) := by
  have h:=edge_eq b q w he
  have hh : (b:Int)=((2:Int)^(w+1)+3)*(q:Int)+3*(2:Int)^w+(w:Int)+3 := by exact_mod_cast h
  rw [Int.pow_succ] at *
  simp only [Int.natCast_add,Int.natCast_one]
  grind

theorem prev_factor (q w : Nat) : 2*(prev q w:Int)=(2:Int)^(w+1)*(2*(q:Int)+3) := by
  unfold prev
  simp only [Int.natCast_mul,Int.natCast_add,Int.natCast_pow,Int.pow_succ]
  grind

/-- Physical bound and parity invariant at every reverse depth. -/
theorem affine_invariants (a P M b L x : Nat) (d : Int)
    (hAP : 2^a*P<2^M) (h : AffineNode a P b L x d) :
    2*(L:Int)*(b:Int)=(2:Int)^x*2^a*(P:Int)+d ∧
      L%2=1 ∧ d%2=0 ∧ b<2^M := by
  induction h with
  | root b hb =>
    have hbi : 2*(b:Int)=(2:Int)^a*(P:Int) := by exact_mod_cast hb
    exact ⟨by simpa using hbi,by decide,by decide,by omega⟩
  | @step b L x d h q w he ih =>
    obtain ⟨hEq,hL,hd,hB⟩:=ih
    have hfactor := edge_factor b q w he
    have hprev := prev_factor q w
    have hpow : (2:Int)^(w+1)%2=0 := by rw [Int.pow_succ,Int.mul_emod]; simp
    have hpowN : (2:Nat)^(w+1)%2=0 := by rw [Nat.pow_succ,Nat.mul_mod]; simp
    have hL' : (L*(2^(w+1)+3))%2=1 := by
      rw [Nat.mul_mod, hL, Nat.add_mod, hpowN]
    have hd' : ((2:Int)^(w+1)*(d+(L:Int)*(5-2*((w+1:Nat):Int))))%2=0 := by
      rw [Int.mul_emod,hpow]; simp
    refine ⟨?_,hL',hd',Nat.lt_trans (edge_drift b q w he) hB⟩
    change 2*((L:Int)*((2:Int)^(w+1)+3))*(prev q w:Int) = (2:Int)^(x+(w+1))*2^a*(P:Int)+(2:Int)^(w+1)*(d+(L:Int)*(5-2*((w+1:Nat):Int)))
    rw [Int.pow_add (2:Int) x (w+1)]
    have h1 : 2*(L:Int)*((2:Int)^(w+1)+3)*(prev q w:Int) =
        (2:Int)^(w+1)*(L:Int)*(2*(b:Int)+5-2*((w+1:Nat):Int)) := by
      rw [show 2*(L:Int)*((2:Int)^(w+1)+3)*(prev q w:Int)= (L:Int)*((2:Int)^(w+1)+3)*(2*(prev q w:Int)) by grind,
          hprev,hfactor]
      grind
    rw [show 2*((L:Int)*((2:Int)^(w+1)+3))*(prev q w:Int)=2*(L:Int)*((2:Int)^(w+1)+3)*(prev q w:Int) by grind,h1]
    grind

/-- Lossless quadratic-or-divisors filter for every non-root cancellation
    ancestor, at arbitrary reverse depth. -/
theorem all_depth_affine_cutoff
    (r a N P b L x q w H₂ H₃ : Nat) (d : Int)
    (hP : ((2:Int)^a+3)*(P:Int)+(N:Int)=((2:Int)^a)^(2*r))
    (hAP : 2^a*P<2^(2*r*a)) (h : AffineNode a P b L x d)
    (hx : 0<x) (he : inverseEdge b q w)
    (hH₂ : d.natAbs+L*(2*(2*r*a)+5)+2^x*N<2^H₂)
    (hH₃ : 3*(d.natAbs+L*(2*(2*r*a)+5))<2^H₃) :
    5*((w+1)*(w+1))≤5*(x+1+H₂+H₃+22)*(w+1)+8*((2*r+1)*a+a) ∨
      (w+1)∣(2*r+1)*a+x-a ∨ (w+1)∣(2*r+1)*a+x ∨ (w+1)∣a := by
  obtain ⟨hb,hL,hd,hsize⟩ := affine_invariants a P (2*r*a) b L x d hAP h
  exact generic_affine_source_quadratic r a N P b q w L x H₂ H₃ d hx hL hd hP hb hsize (edge_eq b q w he) hH₂ hH₃

#print axioms ancestor_has_affine
#print axioms affine_invariants
#print axioms all_depth_affine_cutoff
end NeedleRotation.Asymmetric
