import LastFarExact
import Lean.Elab.Tactic.Omega

namespace BB6.Agent2F321SingleFarTail
open BB6.Agent2F321Bulk
open BB6.Agent2F321Diagonal
open BB6.Agent2F321LastFarExact

/-- A complete suffix H^h F H^b from an arbitrary anchor. -/
def SingleFarTail (h b R c t : Nat) : Prop :=
  ∃ a d, HighRun h R c a d ∧ Feeder b a d t

def shiftedHigh (h c : Nat) : Nat := 2^h*(c+3)

/-- Exact necessary and sufficient Diophantine conditions for a single Far
    with arbitrary initial and trailing High lengths. The only remaining
    existential is the shifted second counter z immediately after Far. -/
theorem singleFarTail_iff (h b R c t : Nat) : SingleFarTail h b R c t ↔
    ∃ z : Nat, 4 ≤ z ∧ z ≤ shiftedHigh h c ∧
      t+3 = 2^b*z ∧
      (6*2^b+1)*z = 4*shiftedHigh h c + 3*b+24 ∧
      R+c+h+b+5 = 2*t := by
  constructor
  · rintro ⟨a,d,hh,hf⟩
    rcases (feeder_iff b a d t).mp hf with ⟨z,hz,hd,ht,hs⟩
    have hc := high_run_coordinates hh
    unfold X Y at hc
    have hmul : 2^h*(2*(c+3)) = 2*shiftedHigh h c := by
      unfold shiftedHigh
      ac_rfl
    rw [hmul] at hc
    have hP : d+3=shiftedHigh h c := by omega
    refine ⟨z,hz,by omega,ht,?_,by omega⟩
    have he : (6*2^b+1)*z=6*(t+3)+z := by
      rw [ht, Nat.add_mul, Nat.mul_assoc, Nat.one_mul]
    rw [he]
    omega
  · rintro ⟨z,hz,hzP,ht,he,hR⟩
    let P := shiftedHigh h c
    have hlin : 6*(t+3)+z=4*P+3*b+24 := by
      rw [ht]
      simpa [P,Nat.add_mul,Nat.mul_assoc] using he
    have hmod : (P-z)%3=0 := by omega
    let a := (P-z)/3
    let d := P-3
    have ha : 3*a+z=P := by dsimp [a]; omega
    have hd : d+3=P := by dsimp [d]; omega
    refine ⟨a,d,?_,?_⟩
    · apply highRun_of_balances
      · omega
      · exact hd
    · exact (feeder_iff b a d t).mpr ⟨z,hz,by omega,ht,by omega⟩

/-- Every actual single-Far suffix determines exactly one terminal parameter
    from its initial small second counter and its two High lengths. -/
theorem singleFarTail_unique {h b R R' c t t' : Nat}
    (hf : SingleFarTail h b R c t) (hf' : SingleFarTail h b R' c t') : t=t' ∧ R=R' := by
  rcases (singleFarTail_iff h b R c t).mp hf with ⟨z,hz,hzP,ht,he,hR⟩
  rcases (singleFarTail_iff h b R' c t').mp hf' with ⟨w,hw,hwP,ht',he',hR'⟩
  have hp : 0 < 6*2^b+1 := by omega
  have hzw := Nat.eq_of_mul_eq_mul_left hp (he.trans he'.symm)
  subst w
  omega

/-- In any single-Far tail where the leading High run is at least b long,
    the terminal is pinned to a much finer dyadic residue than mere
    last-Far parity: z = 3(b+8) modulo 2^b. -/
theorem singleFarTail_refined_residue {h b R c t : Nat}
    (hf : SingleFarTail h b R c t) (hb : b≤h) :
    ∃ z : Nat, t+3=2^b*z ∧ z % (2^b)=(3*b+24) % (2^b) := by
  rcases (singleFarTail_iff h b R c t).mp hf with ⟨z,hz,hzP,ht,he,hR⟩
  refine ⟨z,ht,?_⟩
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hb
  have hP : shiftedHigh (b+k) c = 2^b*(2^k*(c+3)) := by
    unfold shiftedHigh
    rw [Nat.pow_add,Nat.mul_assoc]
  rw [hP] at he
  have hl : (6*2^b+1)*z = 2^b*(6*z)+z := by
    rw [Nat.add_mul,Nat.one_mul]
    congr 1
    ac_rfl
  have hr : 4*(2^b*(2^k*(c+3))) = 2^b*(4*(2^k*(c+3))) := by ac_rfl
  rw [hl,hr] at he
  have hm := congrArg (fun x : Nat => x % (2^b)) he
  simpa [Nat.add_mod] using hm

#print axioms singleFarTail_iff
#print axioms singleFarTail_unique
#print axioms singleFarTail_refined_residue
end BB6.Agent2F321SingleFarTail
