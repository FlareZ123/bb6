import OddSliver
import ZeroOddUniversal
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Exact original-source entire inverse fiber of the infinite line
    (0,64t+23), even though the B8/M32 quotient admits its abstraction. -/
theorem zero_twenty_three_parent_iff (t a k : Nat) :
    secNext (a,k)=some (0,64*t+23) ↔
      a=32*t+9 ∧ k=48*t+15 := by
  constructor
  · intro h
    have hi := (zero_odd_preimages_iff a k (64*t+23) (by omega)).mp h
    rcases hi with h0 | ⟨r,hy,_,_⟩ | ⟨r,u,hu,hy,ha,hk⟩
    · omega
    · have hd : 16 ∣ 32*4^r := ⟨2*4^r,by omega⟩
      have hp : 1≤4^r := Nat.one_le_pow r 4 (by decide)
      have hm : (32*4^r)%16=0 := Nat.mod_eq_zero_of_dvd hd
      omega
    · cases r with
      | zero => simp at hy ha hk; omega
      | succ r =>
          have hd : 16 ∣ 4*4^(r+1)*(u+2) := by
            refine ⟨4^r*(u+2),?_⟩
            rw [Nat.pow_succ, show (16:Nat)=4*4 by decide]
            ac_rfl
          have hpow : 1≤4^(r+1) := Nat.one_le_pow (r+1) 4 (by decide)
          have hge : 1≤4*4^(r+1)*(u+2) := by
            have hh := Nat.le_mul_of_pos_right (4*4^(r+1)) (by omega : 1≤u+2)
            omega
          have hm : (4*4^(r+1)*(u+2))%16=0 := Nat.mod_eq_zero_of_dvd hd
          omega
  · rintro ⟨rfl,rfl⟩
    apply (zero_odd_preimages_iff _ _ (64*t+23) (by omega)).mpr
    right; right
    refine ⟨0,16*t+4,by omega,?_,?_,?_⟩ <;> simp <;> omega

/-- A source-exact nonreachability result strictly stronger than
    the B8/M32 quotient resolution, which marks (0,23,0) as present. -/
theorem zero_twenty_three_blank_unreachable (t time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (0,64*t+23) := by
  intro h
  cases time with
  | zero => simp [BB6.Agent8Section.run] at h
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at h
      | some s =>
          rcases s with ⟨a,k⟩
          have ht : secNext (a,k)=some (0,64*t+23) := by
            simpa [BB6.Agent8Section.run,hp] using h
          obtain ⟨ha,hk⟩ := (zero_twenty_three_parent_iff t a k).mp ht
          have hh : BB6.Agent8Section.run secNext n (some (5,1))=
              some (32*t+9,48*t+15) := by rwa [ha,hk] at hp
          exact odd_sliver_blank_unreachable (32*t+9) (48*t+15) n
            (by omega) (by omega) (by omega) (by omega) (by omega) hh

#print axioms zero_twenty_three_parent_iff
#print axioms zero_twenty_three_blank_unreachable
end BB6.Agent3
