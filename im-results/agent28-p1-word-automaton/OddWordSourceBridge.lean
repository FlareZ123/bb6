import OddWordCost
import OddConeMass
import InverseIff

namespace BB6.Agent28
open BB6.Agent1Quarter BB6.Agent47P1

/-- Faithful transport of a genuine source-defined OddCone to exact binary
    inverse words, conditional only on the root mass b0+10=2K. -/
theorem source_oddcone_has_word (b0 K b d m : Nat)
    (hroot : b0+10=2*K)
    (h : OddCone b0 3 b d m) :
    ∃ D A T : Nat,
      d=2*D+1 ∧ b+2*D+2*m+8=2*K ∧ OddWord K D m A T := by
  induction h with
  | root =>
      refine ⟨1,0,0,by decide, ?_, OddWord.base⟩
      omega
  | parent b d m t k c hcone hb hb4 hd hi hk hc ih =>
      obtain ⟨D,A,T,hdD,hmass,hword⟩ := ih
      let D' : Nat := (c+3)/2
      have hcd : c+3 = 2*D' := by dsimp [D']; omega
      have hnewd : c+4 = 2*D'+1 := by omega
      have hb2 : b = 2*(b/2) := by omega
      have hsource := (inverseAt_iff_power_mass b d t k c (by omega) hb4 hd).mp hi
      have hp : d+b/2+3 = 2^t*(c+3) := hsource.1
      have hlin : d+b/2+3+m = K+D := by omega
      have hpow : 2^(t+1)*D' = 2^t*(c+3) := by
        rw [Nat.pow_succ]
        rw [hcd]
        ac_rfl
      have htransition : 2^(t+1)*D'+m = K+D := by omega
      have hnewcone : OddCone b0 3 (2*k-4) (c+4) (m+t+1) :=
        OddCone.parent b d m t k c hcone hb hb4 hd hi hk hc
      have hnewmass := odd_cone_mass b0 3 (2*k-4) (c+4) (m+t+1) hnewcone
      have hnewbalance : (2*k-4)+2*D'+2*(m+t+1)+8=2*K := by omega
      refine ⟨D', A+2^m, T+m*2^m, hnewd, hnewbalance, ?_⟩
      have hnext := OddWord.next hword (show 1 ≤ t+1 by omega) htransition
      simpa only [Nat.add_assoc] using hnext

/-- Original-source, all-word necessary condition for the affine wall. -/
theorem source_oddcone_wall_cost_logarithmic_gap
    (b0 K n b d m : Nat)
    (hroot : b0+10=2*K) (hn : 14 ≤ n)
    (hK : K+n+3=7*2^n)
    (hcone : OddCone b0 3 b d m)
    (hwall : b=4*(m+n)) : 2^(n-m)<n := by
  obtain ⟨D,A,T,hdD,hbalance,hword⟩ :=
    source_oddcone_has_word b0 K b d m hroot hcone
  have hwallD : D+3*m+2*n+4=K := by omega
  exact hword.wall_cost_logarithmic_gap hn hK hwallD

private theorem source_dom_pow (n : Nat) (hn : 4 ≤ n) : n+4 ≤ 2^n := by
  have hb : ∀ t:Nat, (t+4)+4 ≤ 2^(t+4) := by
    intro t
    induction t with
    | zero => decide
    | succ t ih =>
        have hidx : (t+1)+4 = (t+4)+1 := by omega
        rw [hidx, Nat.pow_succ]
        omega
  have heq : (n-4)+4 = n := by omega
  simpa only [heq] using hb (n-4)

/-- Direct instantiation for the n-critical genuine source odd inverse cone.
    This includes every n=16*q+14. -/
theorem source_critical_wall_cost_logarithmic_gap
    (n b d m : Nat) (hn : 14 ≤ n)
    (hcone : OddCone (14*2^n-2*n-16) 3 b d m)
    (hwall : b=4*(m+n)) : 2^(n-m)<n := by
  let K : Nat := 7*2^n-n-3
  have hdom : n+4 ≤ 2^n := source_dom_pow n (by omega)
  have hK : K+n+3=7*2^n := by dsimp [K]; omega
  have hroot : (14*2^n-2*n-16)+10=2*K := by dsimp [K]; omega
  exact source_oddcone_wall_cost_logarithmic_gap
    (14*2^n-2*n-16) K n b d m hroot hn hK hcone hwall

#print axioms BB6.Agent28.source_critical_wall_cost_logarithmic_gap

#print axioms BB6.Agent28.source_oddcone_has_word
#print axioms BB6.Agent28.source_oddcone_wall_cost_logarithmic_gap
end BB6.Agent28
