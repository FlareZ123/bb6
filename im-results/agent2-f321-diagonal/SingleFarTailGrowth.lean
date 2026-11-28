import SingleFarTail
import Lean.Elab.Tactic.Omega

namespace BB6.Agent2F321SingleFarGrowth
open BB6.Agent2F321SingleFarTail

private theorem pow_mod_congr (u v q : Int) (k : Nat) (h : u%q=v%q) :
    u^k%q=v^k%q := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Int.pow_succ, Int.pow_succ, Int.mul_emod (u^k) u,
          Int.mul_emod (v^k) v, ih, h]

private theorem fold_dvd (B A C : Int) (k : Nat)
    (h : 6*B+1 ∣ A*B^k+C) : 6*B+1 ∣ A*(-1)^k+C*6^k := by
  let q := 6*B+1
  have hm : q ∣ (A*B^k+C)*6^k :=
    Int.dvd_trans h (Int.dvd_mul_right _ _)
  have he : (A*B^k+C)*6^k=A*(6*B)^k+C*6^k := by
    rw [Int.add_mul, Int.mul_pow]
    congr 1
    ac_rfl
  rw [he] at hm
  have hbase : (6*B)%q=(-1)%q := by
    apply (Int.emod_eq_emod_iff_emod_sub_eq_zero).mpr
    rw [show 6*B-(-1)=q by dsimp [q]; omega]
    simp
  have hpow := pow_mod_congr (6*B) (-1) q k hbase
  have hterm : (A*(6*B)^k)%q=(A*(-1)^k)%q := by
    rw [Int.mul_emod A ((6*B)^k), Int.mul_emod A ((-1)^k), hpow]
  apply Int.dvd_of_emod_eq_zero
  change (A*(-1)^k+C*6^k)%q=0
  rw [Int.add_emod, ←hterm, ←Int.add_emod]
  exact Int.emod_eq_zero_of_dvd hm

private theorem sign_pow (k : Nat) : (-1:Int)^k=1 ∨ (-1:Int)^k= -1 := by
  induction k with
  | zero => left; decide
  | succ k ih =>
      rw [Int.pow_succ]
      rcases ih with h | h <;> rw [h] <;> decide

private theorem no_small_multiple (q x : Int) (hlo : 0<x) (hhi : x<q) : ¬q∣x := by
  intro hd
  have hm := Int.emod_eq_zero_of_dvd hd
  rw [Int.emod_eq_of_lt (by omega) hhi] at hm
  omega

private theorem no_between_multiple (q x : Int) (hlo : q<x) (hhi : x<2*q) : ¬q∣x := by
  intro hd
  have hq : q∣q := ⟨1,by simp⟩
  exact no_small_multiple q (x-q) (by omega) (by omega) (Int.dvd_sub hd hq)

private theorem pow2_mod3 (r : Nat) : 2^r%3=1 ∨ 2^r%3=2 := by
  induction r with
  | zero => left; decide
  | succ r ih =>
      rw [Nat.pow_succ, Nat.mul_mod]
      rcases ih with h | h <;> rw [h] <;> decide

/-- A single Far forces a quantitative separation between the two High lengths.
    If h=k*b+r, r<b, and b>0, then 6^k*(3*b+24) must exceed 2^b.
    This excludes an asymptotically quadratic region of (h,b) uniformly,
    without enumerating residues or making a root-reachability assumption. -/
theorem singleFarTail_growth {h b R c t : Nat}
    (hf : SingleFarTail h b R c t) (hc : c=1 ∨ c=2) (hb : 0<b) :
    2^b < (3*b+24)*6^(h/b) := by
  by_cases hlt : 2^b < (3*b+24)*6^(h/b)
  · exact hlt
  exfalso
  have hbound : (3*b+24)*6^(h/b) ≤ 2^b := by omega
  let B := 2^b
  let C := 3*b+24
  let k := h/b
  let r := h%b
  let A := 4*(c+3)*2^r
  have hr : r<b := Nat.mod_lt _ hb
  have hh : h=b*k+r := (Nat.div_add_mod h b).symm
  have hpow : 2^h=B^k*2^r := by
    rw [hh,Nat.pow_add,Nat.pow_mul]
  rcases (singleFarTail_iff h b R c t).mp hf with ⟨z,hz,hzP,ht,he,hR⟩
  have heq : (6*B+1)*z=A*B^k+C := by
    unfold shiftedHigh at he
    rw [hpow] at he
    have hmul : 4*(B^k*2^r*(c+3))=A*B^k := by
      dsimp [A]
      ac_rfl
    rw [hmul] at he
    simpa [B,C,Nat.add_assoc] using he
  have hd : 6*B+1 ∣ A*B^k+C := ⟨z,heq.symm⟩
  have hdi : 6*(B:Int)+1 ∣ (A:Int)*(B:Int)^k+(C:Int) := by
    exact_mod_cast hd
  have hfold := fold_dvd (B:Int) (A:Int) (C:Int) k hdi
  let Q : Int := 6*(B:Int)+1
  let V : Int := (C:Int)*6^k
  have hV : V≤(B:Int) := by
    dsimp [V,B,C,k]
    exact_mod_cast hbound
  have hVpos : 0<V := by
    apply Int.mul_pos
    · dsimp [C]; omega
    · exact_mod_cast (Nat.pow_pos (n:=k) (by decide : 0<6))
  have hApos : 0<(A:Int) := by
    have hp : 0<2^r := Nat.pow_pos (by decide)
    have hp' : 0<4*(c+3) := by omega
    exact_mod_cast Nat.mul_pos hp' hp
  have hAmod : A%3≠0 := by
    dsimp [A]
    rw [Nat.mul_mod (4*(c+3)) (2^r), Nat.mul_mod 4 (c+3)]
    rcases hc with hc | hc <;> rw [hc] <;> rcases pow2_mod3 r with hp | hp <;> rw [hp] <;> decide
  have hAneqV : (A:Int)≠V := by
    intro h
    have hnat : A=C*6^k := by
      dsimp [V] at h
      exact_mod_cast h
    have hC : C%3=0 := by dsimp [C]; omega
    apply hAmod
    rw [hnat,Nat.mul_mod,hC]
    simp
  have hBpos : 2≤B := by
    exact Nat.pow_le_pow_right (by decide : 0<2) hb
  have hsign := sign_pow k
  by_cases hlast : r+1=b
  · have hB : B=2^r*2 := by
      dsimp [B]
      rw [←hlast,Nat.pow_succ]
    have hlo : 8*B≤A := by
      rw [hB]
      dsimp [A]
      rcases hc with hc | hc <;> rw [hc] <;> omega
    have hhi : A≤10*B := by
      rw [hB]
      dsimp [A]
      rcases hc with hc | hc <;> rw [hc] <;> omega
    have hloI : 8*(B:Int)≤(A:Int) := by exact_mod_cast hlo
    have hhiI : (A:Int)≤10*(B:Int) := by exact_mod_cast hhi
    rcases hsign with hsign | hsign
    · rw [hsign,Int.mul_one] at hfold
      exact no_between_multiple Q ((A:Int)+V) (by dsimp [Q]; omega) (by dsimp [Q]; omega) hfold
    · rw [hsign,Int.mul_neg,Int.mul_one] at hfold
      have hneg : Q∣(A:Int)-V := by
        have hh := Int.dvd_neg.mpr hfold
        change Q∣-(-(A:Int)+V) at hh
        simpa only [Int.neg_add,Int.neg_neg,Int.sub_eq_add_neg] using hh
      exact no_between_multiple Q ((A:Int)-V) (by dsimp [Q]; omega) (by dsimp [Q]; omega) hneg
  · have hr2 : r+2≤b := by omega
    have hpowle : 2^(r+2)≤B := Nat.pow_le_pow_right (by decide) hr2
    rw [Nat.pow_add] at hpowle
    have hAhi : A≤5*B := by
      dsimp [A]
      rcases hc with hc | hc <;> rw [hc] <;> omega
    have hAhiI : (A:Int)≤5*(B:Int) := by exact_mod_cast hAhi
    rcases hsign with hsign | hsign
    · rw [hsign,Int.mul_one] at hfold
      exact no_small_multiple Q ((A:Int)+V) (by omega) (by dsimp [Q]; omega) hfold
    · rw [hsign,Int.mul_neg,Int.mul_one] at hfold
      by_cases hlt : (A:Int)<V
      · exact no_small_multiple Q (-(A:Int)+V) (by omega) (by dsimp [Q]; omega) hfold
      · have hneg : Q∣(A:Int)-V := by
          have hh := Int.dvd_neg.mpr hfold
          change Q∣-(-(A:Int)+V) at hh
          simpa only [Int.neg_add,Int.neg_neg,Int.sub_eq_add_neg] using hh
        exact no_small_multiple Q ((A:Int)-V) (by omega) (by dsimp [Q]; omega) hneg

#print axioms singleFarTail_growth
end BB6.Agent2F321SingleFarGrowth
