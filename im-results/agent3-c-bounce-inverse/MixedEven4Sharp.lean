import MixedEven4TwentyTwo
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Generic fixed-time extraction of an exact unique source section
    predecessor, uniformly over arbitrary start states. -/
private theorem one_exact_parent_any_start_broad (x y u v : Nat)
    (huni : ∀ a k, secNext (a,k)=some (x,y) → a=u ∧ k=v)
    (time : Nat) (start : Nat×Nat)
    (h : BB6.Agent8Section.run secNext (time+1) (some start)=some (x,y)) :
    BB6.Agent8Section.run secNext time (some start)=some (u,v) := by
  change (BB6.Agent8Section.run secNext time (some start)).bind secNext =
    some (x,y) at h
  cases hp : BB6.Agent8Section.run secNext time (some start) with
  | none => simp [hp] at h
  | some p =>
      rcases p with ⟨a,k⟩
      have hedge : secNext (a,k)=some (x,y) := by simpa [hp] using h
      obtain ⟨ha,hk⟩ := huni a k hedge
      simpa only [ha,hk] using hp

/-- The broad source-exact even4/22 forbidden union of twelve rectangles has exactly two
    genuinely traversable incoming section edges from some arbitrary
    starting point, yet NO path of length 3 or more can enter it from
    any starting point whatsoever. Blank-origin nonreachability follows. -/
theorem even4_twenty_two_sharp (x y : Nat)
    (hy : y%4=0) (h8 : y%16≠8) (h22 : (2*x+y)%32=22) (hsize : 64≤y) :
    (∃ start : Nat×Nat,
      BB6.Agent8Section.run secNext 2 (some start)=some (x,y)) ∧
    (∀ (start : Nat×Nat) (time : Nat),
      BB6.Agent8Section.run secNext (time+3) (some start) ≠ some (x,y)) ∧
    ¬ CReach x y := by
  have hg : 6≤y ∧ y%2=0 ∧ (x+y)%8≠0 ∧ (x+y)%8≠7 := by omega
  let a := x+y-2
  let k := (y-2)/2
  have hgate : a%2=1 ∧ k%2=1 ∧ 5≤k ∧
      (a+k)%4=0 ∧ (a+k)%16≠0 ∧ 24≤a+k := by
    dsimp [a,k]
    omega
  let b := (a+k-4)/2
  let c := (a+3*k-10)/4
  have hbad : 5≤c ∧ c%2=1 ∧ (b+c)%4=1 := by
    dsimp [a,k,b,c]
    omega
  have he1 : secNext (a,k)=some (x,y) := by
    exact (section_even_right_six_iff a k x y
      hg.1 hg.2.1 hg.2.2.1 hg.2.2.2).mpr ⟨rfl,rfl⟩
  have he2 : secNext (b,c)=some (a,k) := by
    apply (oddodd_lowval_parent_iff b c a k
      hgate.1 hgate.2.1 hgate.2.2.1 hgate.2.2.2.1
      hgate.2.2.2.2.1 hgate.2.2.2.2.2).mpr
    dsimp [b,c,a,k]
    omega
  have huni1 : ∀ u v, secNext (u,v)=some (x,y) → u=a ∧ v=k := by
    intro u v hed
    have hi := (section_even_right_six_iff u v x y
      hg.1 hg.2.1 hg.2.2.1 hg.2.2.2).mp hed
    simpa only [a,k] using hi
  have huni2 : ∀ u v, secNext (u,v)=some (a,k) → u=b ∧ v=c := by
    intro u v hed
    have hi := (oddodd_lowval_parent_iff u v a k
      hgate.1 hgate.2.1 hgate.2.2.1 hgate.2.2.2.1
      hgate.2.2.2.2.1 hgate.2.2.2.2.2).mp hed
    dsimp [b,c]
    omega
  refine ⟨?_,?_,blank_no_even4_exeight_twenty_two x y hy h8 h22 hsize⟩
  · refine ⟨(b,c),?_⟩
    simp [BB6.Agent8Section.run,he1,he2]
  · intro start time ht
    have ht2 : BB6.Agent8Section.run secNext ((time+2)+1) (some start)=
        some (x,y) := by
      simpa only [show (time+2)+1=time+3 by omega] using ht
    have h1 := one_exact_parent_any_start_broad x y a k huni1 (time+2) start ht2
    have ht1 : BB6.Agent8Section.run secNext ((time+1)+1) (some start)=
        some (a,k) := by
      simpa only [show (time+1)+1=time+2 by omega] using h1
    have h2 := one_exact_parent_any_start_broad a k b c huni2 (time+1) start ht1
    change (BB6.Agent8Section.run secNext time (some start)).bind secNext =
      some (b,c) at h2
    cases hp : BB6.Agent8Section.run secNext time (some start) with
    | none => simp [hp] at h2
    | some p =>
        rcases p with ⟨u,v⟩
        have he : secNext (u,v)=some (b,c) := by simpa [hp] using h2
        have hi := section_odd_image u v b c he hbad.1 hbad.2.1
        omega

#print axioms even4_twenty_two_sharp
end BB6.Agent3
