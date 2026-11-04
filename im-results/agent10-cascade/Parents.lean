import ParentCheck

namespace CascadeResetInverse

private def bound (u:Nat) := Nat.log2 (2*u+6)+1

private theorem pow_small (u k:Nat) (hk:2^k≤2*u+6):k<bound u := by
  have hn:2*u+6≠0 := by omega
  have hh := (Nat.le_log2 hn).mpr hk
  dsimp [bound]
  omega

private def evenHeight (u k:Nat) := 2*u-8*2^k-k
private def oddHeight (u k t:Nat) :=
  2*(2^t*((2*u+5)/(3^(t+1))))-8*2^k-k-5

def candidateParents (u:Nat): List Nat :=
  (List.range (bound u)).flatMap fun k =>
    evenHeight u k :: (List.range (bound u)).map (oddHeight u k)

def parents (u:Nat): List Nat :=
  (candidateParents u).filter (fun h => parentCheck h u)

private theorem three_base (t:Nat):2^t≤3^(t+1):=by
  induction t with
  | zero => decide
  | succ t ih => rw [Nat.pow_succ,Nat.pow_succ];omega

private theorem factor_div (u t d:Nat) (he:2*u+5=3^(t+1)*d) :
  (2*u+5)/3^(t+1)=d := by
  rw [he]
  exact Nat.mul_div_cancel_left d (Nat.pow_pos (by decide))

theorem candidateParents_complete (h u:Nat) (hp:ResetParent h u):
    h∈candidateParents u := by
  apply List.mem_flatMap.mpr
  rcases hp with ⟨k,⟨hl,hh⟩,heq⟩ | ⟨k,t,d,hd,⟨hl,hh⟩,heq,hq⟩
  · have hpow:1≤2^k := Nat.one_le_pow k 2 (by decide)
    have hkb:2^k≤2*u+6 := by omega
    have heven:h=evenHeight u k := by dsimp [evenHeight];omega
    refine ⟨k,List.mem_range.mpr (pow_small u k hkb),?_⟩
    simp only [List.mem_cons]
    exact Or.inl heven
  · have hd1:1≤d := by omega
    have hb1:=Nat.mul_le_mul_right d (three_base t)
    have hqbounded:2^t*d≤2*u+5 := by omega
    have hkbound:2^k≤2*u+6 := by omega
    have htp:=Nat.mul_le_mul_left (2^t) hd1
    have htbound:2^t≤2*u+6 := by omega
    have hdiv:=factor_div u t d heq
    have hodd:h=oddHeight u k t := by
      dsimp [oddHeight]
      rw [hdiv]
      omega
    refine ⟨k,List.mem_range.mpr (pow_small u k hkbound),?_⟩
    simp only [List.mem_cons]
    right
    apply List.mem_map.mpr
    exact ⟨t,List.mem_range.mpr (pow_small u t htbound),hodd.symm⟩

theorem parents_iff (h u:Nat) : h∈parents u ↔ ResetParent h u := by
  constructor
  · intro hc
    have hh := (List.mem_filter.mp hc).2
    exact (parentCheck_iff h u).mp hh
  · intro hc
    exact List.mem_filter.mpr ⟨candidateParents_complete h u hc,
      (parentCheck_iff h u).mpr hc⟩

theorem parents_strict (h u:Nat) (hm:h∈parents u):h<u :=
  reset_parent_strict h u ((parents_iff h u).mp hm)

#print axioms parents_iff
#print axioms parents_strict
end CascadeResetInverse
