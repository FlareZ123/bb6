import SmallMany

namespace BB6.Agent9Renewal
open BB6P1Unit
set_option maxHeartbeats 1000000

/-- Shifted reflection is the exact complement for a growing modulus.
A positive ordinary orbit cannot meet the two-endpoint sum 2 when the
reflected orbit stays at least two. -/
theorem unit_complement (q v z : Nat) (hv : v<q) (hz : z<q)
    (hsum : v+z=q+2) (hvp : 0<unit q v) (hzp : 2≤unit q z) :
    unit q v+unit q z=q+3 := by
  have he := unit_equation q v hv
  have hf := unit_equation q z hz
  have hu : unit q v<q+1 := Nat.mod_lt _ (by omega)
  have hw : unit q z<q+1 := Nat.mod_lt _ (by omega)
  by_cases hb : q+1≤2*v <;> by_cases hc : q+1≤2*z <;> simp [bit,hb,hc] at he hf <;> omega

theorem run_complement (q v z m : Nat) (hv : v<q) (hz : z<q)
    (hsum : v+z=q+2) (hvp : ∀ j≤m, 0<run q v j)
    (hzp : ∀ j≤m, 2≤run q z j) : run q v m+run q z m=q+m+2 := by
  induction m with
  | zero => simpa [run] using hsum
  | succ m ih =>
    have hi := ih (fun j hj => hvp j (by omega)) (fun j hj => hzp j (by omega))
    have he : run q v (m+1)=unit (q+m) (run q v m) := rfl
    have hf : run q z (m+1)=unit (q+m) (run q z m) := rfl
    have h := unit_complement (q+m) (run q v m) (run q z m) (run_lt q v m hv) (run_lt q z m hz) hi (by rw [←he]; exact hvp _ (by omega)) (by rw [←hf]; exact hzp _ (by omega))
    rw [he,hf]
    omega

/-- The small-seed exclusion works at either boundary of the critical
return orbit, not only at the special seed 2. -/
theorem short_endpoint_margins (h B p n q v m : Nat)
    (hn : 8000≤n) (hB : 2≤B) (hp : 1≤p)
    (hdom : smallThreshold h B (h+4) p≤n)
    (hclock : q+m=7*2^n-n-3) (hv : v<q) (hm : m≤h*n)
    (hvp : ∀ j<m, 2≤run q v j) (hend : run q v m=1) :
    (0<m → B*n^p<v) ∧ B*n^p<q+2-v := by
  let s := n+m+3
  have hP := large_power n hn
  have hq : q+s=7*2^n := by dsimp [s]; omega
  have hs : s≤(h+4)*n := by dsimp [s]; rw [Nat.add_mul]; omega
  constructor
  · intro hpos
    by_cases hle : B*n^p<v
    · exact hle
    · have hv2 : 2≤v := by simpa [run] using hvp 0 hpos
      have hsafe := small_seed_safe h B (h+4) p n q v s m (by omega) (by omega) (by omega) hp (by omega) hdom hq hv2 (by omega) hs hm (by dsimp [s]; omega)
      omega
  · let z := q+2-v
    by_cases hle : B*n^p<z
    · exact hle
    · have hz2 : 2≤z := by dsimp [z]; omega
      have hzs : ∀ j≤m, 2≤run q z j ∧ run q z j+8≤q+j := by
        intro j hj
        exact small_seed_safe h B (h+4) p n q z s j (by omega) (by omega) (by omega) hp (by omega) hdom hq hz2 (by omega) hs (by omega) (by dsimp [s]; omega)
      have hzq : z<q := by have hh := (hzs 0 (by omega)).2; simp [run] at hh; omega
      have hvpos : ∀ j≤m, 0<run q v j := by
        intro j hj
        by_cases heq : j=m
        · rw [heq,hend]; decide
        · have hh := hvp j (by omega); omega
      have hsum : v+z=q+2 := by dsimp [z]; omega
      have hh := run_complement q v z m hv hzq hsum hvpos (fun j hj => (hzs j hj).1)
      have hlt := run_lt q z m hzq
      omega

#print axioms unit_complement
#print axioms run_complement
#print axioms short_endpoint_margins
end BB6.Agent9Renewal
