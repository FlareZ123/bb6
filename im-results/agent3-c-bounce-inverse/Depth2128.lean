import COneFiveDepth
import Feeder56
import AffineTargetReach56
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46
open BB6.Agent3

/-- The entire second affine feeder family is unreachable from the
    authentic Machine C blank section at every finite return index. -/
theorem blank_no_feeder56 (q : Nat) :
    ¬ CReach (2048*q+899) (1024*q+449) := by
  rintro ⟨time,hr⟩
  cases time with
  | zero =>
    simp [BB6.Agent8Section.run] at hr
  | succ t =>
    cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
    | none => simp [BB6.Agent8Section.run,hp] at hr
    | some p =>
      rcases p with ⟨a,k⟩
      have ht : secNext (a,k)=some (2048*q+899,1024*q+449) := by
        simpa [BB6.Agent8Section.run,hp] using hr
      obtain ⟨ha,hk⟩ := feeder_inverse56 q a k ht
      have hprec : BB6.Agent8Section.run secNext t (some (5,1))=
          some (1536*q+672,1280*q+559) := by
        rw [ha,hk] at hp
        exact hp
      exact blank_no_affine_target56 q t hprec

/-- A further infinite family of genuine a=1 stopping candidates is
    inaccessible to the original blank section. -/
theorem blank_no_one_index225 (q : Nat) :
    ¬ CReach 1 (4*(512*q+225)) := by
  intro h
  have hf := (blank_one_four_iff_feeder (512*q+225) (by omega)).mp h
  have ha : 4*(512*q+225)-1=2048*q+899 := by omega
  have hk : 2*(512*q+225)-1=1024*q+449 := by omega
  rw [ha,hk] at hf
  exact blank_no_feeder56 q hf

private theorem depth2128_implies_k900 (depth k : Nat)
    (hd:depth%4096=2128)
    (hrel:2*k+3*depth+8=2^(depth+1)*8) : k%2048=900 := by
  have hp : 512 ∣ 2^(depth+1) := by
    change 2^9 ∣ 2^(depth+1)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨u,hu⟩ := hp
  have hdvd : 4096 ∣ 2^(depth+1)*8 := by
    refine ⟨u,?_⟩
    rw [hu]
    omega
  have hmod : (2*k+3*depth+8)%4096=0 := by
    rw [hrel]
    exact Nat.mod_eq_zero_of_dvd hdvd
  omega

/-- Any genuine Machine C one-left stopping level with depth congruent
    to 2128 modulo 4096 is impossible from blank entry. -/
theorem dyadic_one_depth2128_mod4096_excluded
    (k depth time:Nat) (hk:4≤k)
    (hlevel:2*k-3=haltLevel 4 depth)
    (hd:depth%4096=2128)
    (hr: BB6.Agent8Section.run secNext time (some (5,1))=some (1,k)) :
    False := by
  have hc := haltLevel_closed 4 depth
  have hrel : 2*k+3*depth+8=2^(depth+1)*8 := by omega
  have hmod := depth2128_implies_k900 depth k hd hrel
  have heq : k=4*(512*(k/2048)+225) := by omega
  have hreach : CReach 1 k := ⟨time,hr⟩
  rw [heq] at hreach
  exact blank_no_one_index225 (k/2048) hreach

#print axioms blank_no_feeder56
#print axioms blank_no_one_index225
#print axioms dyadic_one_depth2128_mod4096_excluded
end BB6.Agent46
