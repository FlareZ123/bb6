import R110Final
import R158Final
import R190Proof
import R206Proof
import R366Proof
import R414Proof
import R446Proof
import R462Proof

namespace BB6.Agent47P1

/-- Eight additional uniformly excluded P1 critical-reset classes in n%512.
    All earlier raw-machine equivalence assumptions are discharged in the
    original-source reachability model, as for each imported theorem. -/
theorem blank_no_critical_eight_mod512 (h r : Nat)
    (hr : r ∈ [110, 158, 190, 206, 366, 414, 446, 462]) :
    ¬BB6.Agent1.Reach 2
      (14*2^(512*h+r)-2*(512*h+r)-10) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h110 | h158 | h190 | h206 | h366 | h414 | h446 | h462
  · subst r; exact blank_no_critical_110_mod512 h
  · subst r; exact blank_no_critical_158_mod512 h
  · subst r; exact blank_no_critical_190_mod512 h
  · subst r; exact blank_no_critical_206_mod512 h
  · subst r; exact blank_no_critical_366_mod512 h
  · subst r; exact blank_no_critical_414_mod512 h
  · subst r; exact blank_no_critical_446_mod512 h
  · subst r; exact blank_no_critical_462_mod512 h

#print axioms BB6.Agent47P1.blank_no_critical_eight_mod512

/-- Eight mod-512 classes coalesce into four complete mod-256 classes by
    splitting the quotient parameter into its two parities. -/
theorem blank_no_critical_four_mod256 (h r : Nat)
    (hr : r ∈ [110, 158, 190, 206]) :
    ¬BB6.Agent1.Reach 2
      (14*2^(256*h+r)-2*(256*h+r)-10) := by
  let q := h/2
  let s := h%2
  have hdiv : h = 2*q+s := by dsimp [q,s]; omega
  have hs : s=0 ∨ s=1 := by dsimp [s]; omega
  rcases hs with hz | ho
  · have heq : 256*h+r=512*q+r := by omega
    have hh : r∈[110, 158, 190, 206, 366, 414, 446, 462] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h1|h2|h3|h4 <;> omega
    simpa [heq] using blank_no_critical_eight_mod512 q r hh
  · have heq : 256*h+r=512*q+(r+256) := by omega
    have hh : r+256∈[110, 158, 190, 206, 366, 414, 446, 462] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h1|h2|h3|h4 <;> omega
    simpa [heq] using blank_no_critical_eight_mod512 q (r+256) hh

#print axioms BB6.Agent47P1.blank_no_critical_four_mod256

end BB6.Agent47P1
