import DyadicExactGaps
import DyadicHighEdge
import DyadicStripSigned

namespace BB6.Agent21Duality
open BB6.Agent42ModularCone
open BB6.Agent21Dyadic

private theorem I_dvd' (m n : Nat) (hm : m≤n) : I m∣I n := by
  refine ⟨I (n-m),?_⟩
  rw [I_split hm]
  ac_rfl

/-- The exact valuation gate implies that the adjusted mass does not
    vanish at the entire available bit precision. -/
theorem valid_not_full (b v : Nat) (s : Pair)
    (hv : ValValid b s v) :
    ¬P b∣-(q s) := by
  intro hd
  have hp : P b=I b := by simp [P,I,BB6.Agent42ModularCone.P]
  rw [hp] at hd
  have hdI : I b∣q s := dvd_neg.mp hd
  have hsmall : I (v+1)∣I b := I_dvd' (v+1) b hv.1
  have hvdiv : I (v+1)∣q s := Int.dvd_trans hsmall hdI
  have hz := Int.emod_eq_zero_of_dvd hvdiv
  rw [hv.2] at hz
  have hpos := I_pos v
  omega

/-- Exact *two-sided* recursive decomposition of the signed normalized
    inverse-word language. This lemma reduces the proposed checker /
    word duality to a direct induction over the same exhaustive
    modular-cone direct/high child enumeration. -/
theorem open_iff_children (b v : Nat) (s : Pair)
    (hv : ValValid b s v) :
    OpenAt (signedS s.x s.y) (signedZ s.x s.y) b ↔
    (s.y%2=0 ∧
      OpenAt (signedS (direct s).x (direct s).y)
        (signedZ (direct s).x (direct s).y) (b-1)) ∨
    (∃ n : Nat, Allowed s v n ∧
      OpenAt (signedS (high s n).x (high s n).y)
        (signedZ (high s n).x (high s n).y) (b-(n+2))) := by
  have hb : 0<b := by have h := hv.1; omega
  constructor
  · intro ho
    have hnot := valid_not_full b v s hv
    obtain ⟨r,z',hr,hrb,hpar,hprefix,hchild⟩ :=
      signed_open_descends s.x s.y b hb hnot ho
    have hone : signedZ s.x s.y+offset (signedS s.x s.y) r=-(q s) := by
      rw [signed_one_numer,signed_parity_cost s.x s.y r hpar]
      simp only [q,odd]
    have hdiv : P r∣-(q s) := ⟨z',(hprefix.trans hone).symm⟩
    rcases valuation_first_gap_classification b v r s hv hr hpar hdiv with
      ⟨h1,hy⟩|⟨n,hn,ha⟩
    · left
      have hedge := direct_edge_source_pair s hy
      have hs := hedge.1
      have hz := hedge.2
      rw [h1] at hprefix hchild
      have hze : z'=signedZ (direct s).x (direct s).y := by
        rw [←hz] at hprefix
        change (2:Int)*z'=(2:Int)*signedZ (direct s).x (direct s).y at hprefix
        omega
      rw [←hs,hze] at hchild
      exact ⟨hy,hchild⟩
    · right
      refine ⟨n,ha,?_⟩
      rw [hn] at hprefix hchild
      have hq : I (n+2)∣q s := valvalid_divisor b v n s hv ha.1
      have hedge := signed_high_edge s n hq ha.2
      have hs := hedge.1
      have hz := hedge.2
      have hze : z'=signedZ (high s n).x (high s n).y := by
        have heq : P (n+2)*z'=P (n+2)*signedZ (high s n).x (high s n).y :=
          hprefix.trans hz.symm
        have hd : P (n+2)*(z'-signedZ (high s n).x (high s n).y)=0 := by
          rw [Int.mul_sub]
          omega
        rcases mul_eq_zero.mp hd with h0 | h0
        · exact False.elim ((P_ne (n+2)) h0)
        · omega
      rw [←hs,hze] at hchild
      exact hchild
  · rintro (⟨hy,hchild⟩|⟨n,ha,hchild⟩)
    · obtain ⟨hs,hz⟩ := direct_edge_source_pair s hy
      have ho := open_prepend (signedS s.x s.y) (signedZ s.x s.y)
        (signedS (direct s).x (direct s).y)
        (signedZ (direct s).x (direct s).y)
        1 (b-1) (by decide) hs hz hchild
      simpa only [show b-1+1=b by omega] using ho
    · have hq : I (n+2)∣q s := valvalid_divisor b v n s hv ha.1
      obtain ⟨hs,hz⟩ := signed_high_edge s n hq ha.2
      have ho := open_prepend (signedS s.x s.y) (signedZ s.x s.y)
        (signedS (high s n).x (high s n).y)
        (signedZ (high s n).x (high s n).y)
        (n+2) (b-(n+2)) (by omega) hs hz hchild
      simpa only [show b-(n+2)+(n+2)=b by omega] using ho

#print axioms open_iff_children
end BB6.Agent21Duality
