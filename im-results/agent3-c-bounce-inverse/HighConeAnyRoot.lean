import FullForcedFilter
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Exact one-step backward transport for any deterministic initial section. -/
theorem run_succ_unique_predecessor (start : Nat × Nat)
    (n x y a k : Nat)
    (hu : ∀ u v, secNext (u,v)=some (x,y) → u=a ∧ v=k)
    (h : BB6.Agent8Section.run secNext (n+1) (some start)=some (x,y)) :
    BB6.Agent8Section.run secNext n (some start)=some (a,k) := by
  cases hr : BB6.Agent8Section.run secNext n (some start) with
  | none => simp [BB6.Agent8Section.run,hr] at h
  | some p =>
      obtain ⟨u,v⟩ := p
      have hed : secNext (u,v)=some (x,y) := by
        simpa [BB6.Agent8Section.run,hr] using h
      obtain ⟨rfl,rfl⟩ := hu u v hed
      rfl

/-- From ANY initial section, every member of the infinite cone is
    unreachable after four or more successful returns. Its maximal legal
    predecessor ancestry has length exactly three. -/
theorem affine_three_cone_no_four_or_more
    (start : Nat × Nat) (n x y : Nat)
    (hx : x%8=5) (hxy : (2*x+y)%128=6) :
    BB6.Agent8Section.run secNext (n+4) (some start) ≠ some (x,y) := by
  let a := x+y-2
  let b := (y-2)/2
  let c := (a+b-4)/2
  let d := (a+3*b-10)/4
  let e := (c+d-5)/2
  let f := (c+3*d-9)/4
  have hall :
    4≤y ∧ y%2=0 ∧ (x+y)%4=1 ∧
    a%2=1 ∧ b%2=1 ∧ 5≤b ∧ (a+b)%4=0 ∧ (a+b)%16≠0 ∧ 24≤a+b ∧
    c%2=0 ∧ d%2=1 ∧ 5≤d ∧ (c+d+1)%16=8 ∧ 23≤c+d ∧
    5≤f ∧ f%2=1 ∧ (e+f)%4=2 := by
    dsimp [a,b,c,d,e,f]
    omega
  rcases hall with ⟨hy4,hye,hs1,haodd,hbodd,hb5,hs2,hs16,hab24,
     hceven,hdodd,hd5,hs3,hcd23,hf5,hfodd,hs4⟩
  intro ht
  have h3 : BB6.Agent8Section.run secNext (n+3) (some start)=some (a,b) :=
    run_succ_unique_predecessor start (n+3) x y a b
      (by
        intro u v hv
        simpa [a,b] using (BB6.Agent15.section_sum_one_even_iff_affine u v x y hy4 hye hs1).mp hv)
      (by
        simpa only [show n+3+1=n+4 by omega] using ht)
  have h2 : BB6.Agent8Section.run secNext (n+2) (some start)=some (c,d) :=
    run_succ_unique_predecessor start (n+2) a b c d
      (by
        intro u v hv
        have hh := (oddodd_lowval_parent_iff u v a b haodd hbodd hb5 hs2 hs16 hab24).mp hv
        dsimp [c,d]
        omega)
      (by
        simpa only [show n+2+1=n+3 by omega] using h3)
  have h1 : BB6.Agent8Section.run secNext (n+1) (some start)=some (e,f) :=
    run_succ_unique_predecessor start (n+1) c d e f
      (by
        intro u v hv
        have hh := (odd_seven_parent_iff u v c d hceven hdodd hd5 hs3 hcd23).mp hv
        dsimp [e,f]
        omega)
      (by
        simpa only [show n+1+1=n+2 by omega] using h2)
  cases hp : BB6.Agent8Section.run secNext n (some start) with
  | none => simp [BB6.Agent8Section.run,hp] at h1
  | some p =>
      obtain ⟨u,v⟩ := p
      have hed : secNext (u,v)=some (e,f) := by
        simpa [BB6.Agent8Section.run,hp] using h1
      have hi := section_odd_image u v e f hed hf5 hfodd
      omega

/-- Every cone point has a source-exact legal three-return predecessor
    chain, even though no state has a four-return path to that point.
    Consequently the bounded ancestry-height statement is sharp. -/
theorem affine_three_cone_depth_three_witness (x y : Nat)
    (hx : x%8=5) (hxy : (2*x+y)%128=6) :
    let a := x+y-2
    let b := (y-2)/2
    let c := (a+b-4)/2
    let d := (a+3*b-10)/4
    let e := (c+d-5)/2
    let f := (c+3*d-9)/4
    BB6.Agent8Section.run secNext 3 (some (e,f))=some (x,y) := by
  dsimp
  let a := x+y-2
  let b := (y-2)/2
  let c := (a+b-4)/2
  let d := (a+3*b-10)/4
  let e := (c+d-5)/2
  let f := (c+3*d-9)/4
  have hall :
    4≤y ∧ y%2=0 ∧ (x+y)%4=1 ∧
    a%2=1 ∧ b%2=1 ∧ 5≤b ∧ (a+b)%4=0 ∧ (a+b)%16≠0 ∧ 24≤a+b ∧
    c%2=0 ∧ d%2=1 ∧ 5≤d ∧ (c+d+1)%16=8 ∧ 23≤c+d := by
    dsimp [a,b,c,d,e,f]
    omega
  rcases hall with ⟨hy4,hye,hs1,haodd,hbodd,hb5,hs2,hs16,hab24,
     hceven,hdodd,hd5,hs3,hcd23⟩
  have htop : secNext (a,b)=some (x,y) := by
    apply (BB6.Agent15.section_sum_one_even_iff_affine a b x y hy4 hye hs1).mpr
    simp [a,b]
  have hmid : secNext (c,d)=some (a,b) := by
    apply (oddodd_lowval_parent_iff c d a b haodd hbodd hb5 hs2 hs16 hab24).mpr
    constructor <;> dsimp [c,d] <;> omega
  have hbase : secNext (e,f)=some (c,d) := by
    apply (odd_seven_parent_iff e f c d hceven hdodd hd5 hs3 hcd23).mpr
    constructor <;> dsimp [e,f] <;> omega
  change BB6.Agent8Section.run secNext 3 (some (e,f))=some (x,y)
  simp [BB6.Agent8Section.run,hbase,hmid,htop]

#print axioms affine_three_cone_depth_three_witness
#print axioms run_succ_unique_predecessor
#print axioms affine_three_cone_no_four_or_more
end BB6.Agent3
