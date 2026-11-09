import CThreeToFourSource
import ThreeConeProper
import Lean.Elab.Tactic.Omega

namespace BB6.Agent4Four
open BB6.Agent46

/-- The image of n original (successful) section returns. -/
def InImage (n x y : Nat) : Prop :=
  ∃ start : Nat × Nat,
    BB6.Agent8Section.run secNext n (some start) = some (x,y)

private theorem image_succ_iff (n x y : Nat) :
    InImage (n+1) x y ↔
    ∃ a k, InImage n a k ∧ secNext (a,k)=some (x,y) := by
  constructor
  · rintro ⟨start,h⟩
    change (BB6.Agent8Section.run secNext n (some start)).bind secNext =
      some (x,y) at h
    cases hp : BB6.Agent8Section.run secNext n (some start) with
    | none => simp [hp] at h
    | some p =>
      rcases p with ⟨a,k⟩
      exact ⟨a,k,⟨start,hp⟩,by simpa [hp] using h⟩
  · rintro ⟨a,k,⟨start,hprev⟩,hnext⟩
    exact ⟨start, by simpa [BB6.Agent8Section.run,hprev,hnext]⟩

private theorem lift_gap (n a k x y : Nat)
    (hyes : InImage n a k)
    (hno : ¬ InImage (n+1) a k)
    (hstep : secNext (a,k)=some (x,y))
    (hunique : ∀ b l, secNext (b,l)=some (x,y) → b=a ∧ l=k) :
    InImage (n+1) x y ∧ ¬ InImage (n+2) x y := by
  constructor
  · exact (image_succ_iff n x y).mpr ⟨a,k,hyes,hstep⟩
  · intro h
    obtain ⟨b,l,hparent,hstep'⟩ := (image_succ_iff (n+1) x y).mp h
    obtain ⟨hb,hl⟩ := hunique b l hstep'
    subst b
    subst l
    exact hno hparent

/-- Recursive positive-density cylinders of sharp image separation. -/
def Cone : Nat → Nat → Nat → Prop
  | 0,x,y => 42≤y ∧ y%16=10 ∧ (x+y)%8=1
  | n+1,x,y => 6≤y ∧ y%2=0 ∧ (x+y)%4=1 ∧
      Cone n (x+y-2) ((y-2)/2)

/-- Every level r is exactly present in I_(r+2) and absent from I_(r+3). -/
theorem cone_strict_image (r x y : Nat) (h : Cone r x y) :
    InImage (r+2) x y ∧ ¬ InImage (r+3) x y := by
  induction r generalizing x y with
  | zero =>
      have hy : 34≤y := by exact Nat.le_trans (by omega) h.1
      have hsec : ((x+y)%8=1 ∧ y%16=10) ∨
          ((x+y)%8=3 ∧ y%16=2) := by
        left
        exact ⟨h.2.2,h.2.1⟩
      obtain ⟨⟨a,k,b,l,hsecond,hfirst⟩,hthird⟩ :=
        BB6.Agent34ThreeProper.exactly_two_not_three x y hy hsec
      constructor
      · exact ⟨(b,l), by simp [BB6.Agent8Section.run,hsecond,hfirst]⟩
      · intro hreach
        rcases (image_succ_iff 2 x y).mp hreach with ⟨a',k',h2,h1⟩
        rcases (image_succ_iff 1 a' k').mp h2 with ⟨b',l',h1',h2'⟩
        rcases (image_succ_iff 0 b' l').mp h1' with ⟨u,v,_,h3'⟩
        exact BB6.Agent34Three.no_three_edges u v b' l' a' k' x y
          hy hsec h3' h2' h1
  | succ r ih =>
      change 6≤y ∧ y%2=0 ∧ (x+y)%4=1 ∧
        Cone r (x+y-2) ((y-2)/2) at h
      let a := x+y-2
      let k := (y-2)/2
      have hgap := ih a k h.2.2.2
      have hstep : secNext (a,k)=some (x,y) := by
        dsimp [a,k]
        exact BB6.Agent34ThreeProper.direct_predecessor x y h.1 h.2.1
      have hunique : ∀ b l,
          secNext (b,l)=some (x,y) → b=a ∧ l=k := by
        intro b l hb
        have hp : sectionPreimageAll b l x y :=
          (section_preimage_all_iff b l x y).mp hb
        obtain ⟨ha,hk⟩ := BB6.Agent4Three.only_direct_mod4_one
          b l x y h.1 h.2.1 h.2.2.1 hp
        dsimp [a,k]
        constructor
        · exact ha
        · omega
      have lifted := lift_gap (r+2) a k x y hgap.1 hgap.2 hstep hunique
      simpa only [show r+2+1=r+1+2 by omega,
        show r+2+2=r+1+3 by omega] using lifted

/-- The right-coordinate progression for each cone level. -/
def bandY (r t : Nat) : Nat := 2^r*(16*t+44)-2

/-- Every level contains an entire two-dimensional lattice of targets. -/
theorem each_cone_has_cylinder (r s t : Nat) :
    Cone r (8*s+7+4*r) (bandY r t) := by
  induction r generalizing s with
  | zero =>
      change 42≤bandY 0 t ∧ (bandY 0 t)%16=10 ∧
        (8*s+7+4*0+bandY 0 t)%8=1
      simp only [bandY, Nat.pow_zero, Nat.one_mul]
      omega
  | succ r ih =>
      let B := 16*t+44
      have hB : B=4*(4*t+11) := by dsimp [B]; omega
      have hp : (2:Nat)^(r+1)*B = 2*(2^r*B) := by
        rw [Nat.pow_succ]
        ac_rfl
      have h8 : (2:Nat)^(r+1)*B = 8*(2^r*(4*t+11)) := by
        calc
          (2:Nat)^(r+1)*B = (2*4)*(2^r*(4*t+11)) := by
            rw [hB,Nat.pow_succ]
            ac_rfl
          _ = 8*(2^r*(4*t+11)) := by simp
      have hsize : 88≤2^(r+1)*B := by
        have h2 : 1≤2^r := Nat.pow_pos (by decide)
        have hB44 : 44≤B := by dsimp [B]; omega
        have hmult : B≤2^r*B := by
          simpa only [Nat.one_mul] using Nat.mul_le_mul_right B h2
        omega
      have hfactor : 2^(r+1)*(16*t+44)=8*(2^r*(4*t+11)) := by
        simpa [B] using h8
      have hdouble : 2^(r+1)*(16*t+44)=2*(2^r*(16*t+44)) := by
        simpa [B] using hp
      have hsize8 : 88≤8*(2^r*(4*t+11)) := by
        simpa [B,h8] using hsize
      have hper : (bandY (r+1) t)%2=0 := by
        dsimp [bandY]
        rw [hfactor]
        omega
      have hsum : (8*s+7+4*(r+1)+bandY (r+1) t)%4=1 := by
        dsimp [bandY]
        rw [hfactor]
        omega
      have hyParent : (bandY (r+1) t-2)/2=bandY r t := by
        dsimp [bandY]
        rw [hdouble]
        have hsize' : 44≤2^r*(16*t+44) := by omega
        omega
      have hxParent : (8*s+7+4*(r+1)+bandY (r+1) t)-2 =
          8*(s+2^r*(4*t+11))+7+4*r := by
        dsimp [bandY]
        rw [hfactor]
        omega
      change 6≤bandY (r+1) t ∧ (bandY (r+1) t)%2=0 ∧
        (8*s+7+4*(r+1)+bandY (r+1) t)%4=1 ∧
        Cone r ((8*s+7+4*(r+1)+bandY (r+1) t)-2)
          ((bandY (r+1) t-2)/2)
      refine ⟨by dsimp [bandY]; omega,hper,hsum,?_⟩
      rw [hxParent,hyParent]
      exact ih (s+2^r*(4*t+11))

/-- For every image depth n>=2, I_n strictly contains I_(n+1). -/
theorem all_image_depths_strict (r : Nat) :
    ∃ x y, InImage (r+2) x y ∧ ¬ InImage (r+3) x y := by
  refine ⟨8*0+7+4*r,bandY r 0,?_⟩
  exact cone_strict_image r _ _ (each_cone_has_cylinder r 0 0)

#print axioms image_succ_iff
#print axioms cone_strict_image
#print axioms each_cone_has_cylinder
#print axioms all_image_depths_strict
end BB6.Agent4Four
