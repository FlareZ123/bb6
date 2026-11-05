import S4TripleHead
import Lean.Elab.Tactic.Omega

namespace S4TripleResidue
open S4Power S4Octet S4Toggle S4TripleHead
set_option maxHeartbeats 0

private theorem pow2_mod8 (x : Nat) (hx:8<x) (hp:Pow2 x) : x%8=0 := by
  obtain ⟨k,rfl⟩ := hp
  by_cases hb:3≤k
  · have heq : k=3+(k-3) := by omega
    rw [heq, Nat.pow_add]
    simp
  · rcases (show k=0∨k=1∨k=2 by omega) with h|h|h
    · subst k; simp at hx
    · subst k; simp at hx
    · subst k; simp at hx

private theorem W_mod8 (a b d c : Nat) (T : List Nat) :
    (W (a::b::d::T)+c)%8=(a+2*b+4*d+7+c)%8 := by
  simp only [W]
  omega

theorem G_safe_if_nonzero (k a b d : Nat) (T : List Nat)
    (hk:8<k) (h : (a+2*b+4*d+7+k)%8 ≠ 0) :
    G k (a::b::d::T) ≠ none := by
  intro hnone
  have hp : Pow2 (W (a::b::d::T)+k) :=
    (G_none_iff_power k (a::b::d::T) (by omega)).mp hnone
  have hgt : 8<W (a::b::d::T)+k := by omega
  have hmod := pow2_mod8 _ hgt hp
  rw [W_mod8] at hmod
  exact h hmod

def r3 (k : Nat) (v : List Nat) : Nat :=
  (v[0]!+2*v[1]!+4*v[2]!+7+k)%8

theorem P_safe_if_residues (a b d : Nat) (S : List Nat)
    (h0 : (a+2*b+4*d+7+509)%8≠0)
    (h1 : r3 290 (g3 509 a b d)≠0)
    (h2 : r3 219 (g3 290
       ((g3 509 a b d)[0]!) ((g3 509 a b d)[1]!) ((g3 509 a b d)[2]!))≠0) :
    P (a::b::d::S)≠none := by
  have hg0 := G_safe_if_nonzero 509 a b d S (by omega) h0
  cases he0 : G 509 (a::b::d::S) with
  | none => exact False.elim (hg0 he0)
  | some X =>
      obtain ⟨T1,hX⟩ := G_prefix3 509 a b d S X he0
      rw [g3_shape] at hX
      subst X
      let v := g3 509 a b d
      have hv : G 509 (a::b::d::S) = some (v[0]!::v[1]!::v[2]!::T1) := by
        simpa [v] using he0
      have h1' : ((v[0]!)+2*(v[1]!)+4*(v[2]!)+7+290)%8≠0 := by
        simpa [r3,v] using h1
      have hg1 := G_safe_if_nonzero 290 v[0]! v[1]! v[2]! T1 (by omega) h1'
      cases he1 : G 290 (v[0]!::v[1]!::v[2]!::T1) with
      | none => exact False.elim (hg1 he1)
      | some Y =>
          obtain ⟨T2,hY⟩ := G_prefix3 290 v[0]! v[1]! v[2]! T1 Y he1
          rw [g3_shape] at hY
          subst Y
          let w := g3 290 v[0]! v[1]! v[2]!
          have hw : G 290 (v[0]!::v[1]!::v[2]!::T1) =
              some (w[0]!::w[1]!::w[2]!::T2) := by simpa [w] using he1
          have h2' : (w[0]!+2*w[1]!+4*w[2]!+7+219)%8≠0 := by
            simpa [r3,v,w] using h2
          have hg2 := G_safe_if_nonzero 219 w[0]! w[1]! w[2]! T2 (by omega) h2'
          intro hnone
          have hfinal : G 219 (w[0]!::w[1]!::w[2]!::T2)=none := by
            unfold P at hnone
            rw [hv] at hnone
            simp only [Option.bind_some] at hnone
            change (G 290 (v[0]!::v[1]!::v[2]!::T1)).bind (G 219)=none at hnone
            rw [hw] at hnone
            simpa using hnone
          exact hg2 hfinal

#print axioms pow2_mod8
#print axioms W_mod8
#print axioms G_safe_if_nonzero
end S4TripleResidue
