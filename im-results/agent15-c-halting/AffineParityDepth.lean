import AffineNormalize
import Lean.Elab.Tactic.Omega
namespace BB6.Agent15

def oddDepth (k : Nat) : Nat :=
  if h : 4≤k ∧ k%4=2 then 1+oddDepth ((k-2)/2) else 0
termination_by k
decreasing_by omega

theorem normalize_a_three_mod4 (a k : Nat) (ha : a%4=3) :
  affineNormalize a k =
    if h : 4≤k ∧ k%4=2 then affineNormalize (a+k-2) ((k-2)/2) else (a,k) := by
  rw [affineNormalize]
  have heq : (4≤k ∧ k%2=0 ∧ (a+k)%4=1) ↔ (4≤k ∧ k%4=2) := by omega
  exact dite_congr (propext heq) (fun _ => rfl) (fun _ => rfl)

theorem normalize_three_depth_invariants (a k : Nat) (ha : a%4=3) :
    let p := affineNormalize a k
    p.1+2*p.2+4*oddDepth k=a+2*k ∧
      2^(oddDepth k)*(p.2+2)=k+2 ∧
      ¬(4≤p.2 ∧ p.2%4=2) := by
  induction k using Nat.strongRecOn generalizing a with
  | ind k ih =>
      by_cases h : 4≤k ∧ k%4=2
      · have ha' : (a+k-2)%4=3 := by omega
        have hk' : (k-2)/2<k := by omega
        have ih' := ih ((k-2)/2) hk' (a+k-2) ha'
        have hn : affineNormalize a k = affineNormalize (a+k-2) ((k-2)/2) := by
          simpa [h] using normalize_a_three_mod4 a k ha
        have hd : oddDepth k = 1 + oddDepth ((k-2)/2) := by
          rw [oddDepth, dif_pos h]
        rw [hn,hd]
        dsimp at ih' ⊢
        rcases ih' with ⟨hr,hs,ht⟩
        have hkFormula : 2*((k-2)/2+2)=k+2 := by omega
        have hcenter : (a+k-2)+2*((k-2)/2)+4=a+2*k := by omega
        constructor
        · omega
        constructor
        · calc
            2^(1+oddDepth ((k-2)/2)) * ((affineNormalize (a+k-2) ((k-2)/2)).2+2)
                = 2*(2^(oddDepth ((k-2)/2)) * ((affineNormalize (a+k-2) ((k-2)/2)).2+2)) := by
                   rw [Nat.pow_add]
                   simp [Nat.mul_assoc]
            _ = 2*((k-2)/2+2) := by rw [hs]
            _ = k+2 := hkFormula
        · exact ht
      · have hn : affineNormalize a k=(a,k) := by
          simpa [h] using normalize_a_three_mod4 a k ha
        have hd : oddDepth k=0 := by
          rw [oddDepth, dif_neg h]
        simp only [hn,hd, Prod.fst, Prod.snd]
        constructor
        · omega
        constructor
        · simp
        · exact h

#print axioms normalize_three_depth_invariants

theorem normalize_three_even_ge_two (a k : Nat)
    (ha : a%4=3) (he : k%2=0) (hk : 2≤k) :
    (affineNormalize a k).2%2=0 ∧ 2≤(affineNormalize a k).2 := by
  induction k using Nat.strongRecOn generalizing a with
  | ind k ih =>
      by_cases h : 4≤k ∧ k%4=2
      · have ha' : (a+k-2)%4=3 := by omega
        have hk' : (k-2)/2 < k := by omega
        have hke : ((k-2)/2)%2=0 := by omega
        have hk2 : 2≤(k-2)/2 := by omega
        have hnext := ih ((k-2)/2) hk' (a+k-2) ha' hke hk2
        have hn : affineNormalize a k=affineNormalize (a+k-2) ((k-2)/2) := by
          simpa [h] using normalize_a_three_mod4 a k ha
        rw [hn]
        exact hnext
      · have hn : affineNormalize a k=(a,k) := by
          simpa [h] using normalize_a_three_mod4 a k ha
        simpa [hn] using And.intro he hk

theorem normalize_three_deep_right_0_or_2_mod4 (a k : Nat)
    (ha : a%4=3) (hfirst : 4≤k ∧ k%4=2) :
    (affineNormalize a k).2=2 ∨ (affineNormalize a k).2%4=0 := by
  have hk' : 2≤(k-2)/2 := by omega
  have he' : ((k-2)/2)%2=0 := by omega
  have ha' : (a+k-2)%4=3 := by omega
  have hn : affineNormalize a k=affineNormalize (a+k-2) ((k-2)/2) := by
    simpa [hfirst] using normalize_a_three_mod4 a k ha
  have hnorm := normalize_three_even_ge_two (a+k-2) ((k-2)/2) ha' he' hk'
  have hterm := (normalize_three_depth_invariants (a+k-2) ((k-2)/2) ha').2.2
  rw [hn]
  rcases hnorm with ⟨he,hge⟩
  omega

#print axioms normalize_three_deep_right_0_or_2_mod4
end BB6.Agent15
