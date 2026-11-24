import Q0SlopePacking

namespace BB429Q0Macro
set_option maxHeartbeats 2000000

/-- An arbitrary-depth version of slope packing. Each possible word
of length h contributes at most L/(3*16^h)+1 integer slopes. -/
def deepSlopeBand (L h D : Nat) : List Nat :=
  (List.range (L/(3*16^h)+1)).map (fun i => (L*D+16^h-1)/16^h+i)

def deepSlopeBands (L h : Nat) : List Nat :=
  (allWords h).flatMap (fun ds => deepSlopeBand L h (digitWord ds))

theorem allWords_length (h : Nat) : (allWords h).length=4^h := by
  induction h with
  | zero => rfl
  | succ h ih => simp [allWords,allDigits,ih,Nat.pow_succ]; omega

private theorem flatMap_length_constant {α β : Type} (xs : List α)
    (f : α → List β) (n : Nat) (hf : ∀ x, (f x).length=n) :
    (xs.flatMap f).length=xs.length*n := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [hf,ih,Nat.succ_mul,Nat.add_comm]

theorem deepSlopeBands_length (L h : Nat) :
    (deepSlopeBands L h).length=4^h*(L/(3*16^h)+1) := by
  unfold deepSlopeBands
  rw [flatMap_length_constant _ _ (L/(3*16^h)+1),allWords_length]
  intro ds
  simp [deepSlopeBand]

theorem deepSlopeBand_mem (L h D a b : Nat) (ha : 3*a≤L)
    (he : 16^h*b=a+L*D) : b∈deepSlopeBand L h D := by
  let B := 16^h
  let M := L*D
  let lo := (M+B-1)/B
  have hB : 0<B := Nat.pow_pos (by decide)
  change B*b=a+M at he
  have hlo : lo≤b := by
    apply (Nat.div_le_iff_le_mul hB).2
    rw [Nat.mul_comm b B]
    omega
  have hceil : M≤B*lo := by
    have hdiv := Nat.div_add_mod (M+B-1) B
    have hr := Nat.mod_lt (M+B-1) hB
    change B*lo+(M+B-1)%B=M+B-1 at hdiv
    omega
  have hdiff : B*(b-lo)≤a := by
    rw [Nat.mul_sub_left_distrib]
    omega
  have hprod : (b-lo)*(3*B)≤L := by
    calc
      (b-lo)*(3*B)=3*(B*(b-lo)) := by ac_rfl
      _≤3*a := Nat.mul_le_mul_left 3 hdiff
      _≤L := ha
  have hq := (Nat.le_div_iff_mul_le (show 0<3*B from Nat.mul_pos (by decide) hB)).2 hprod
  change b-lo≤L/(3*16^h) at hq
  simp only [deepSlopeBand,List.mem_map,List.mem_range]
  exact ⟨b-lo,by omega,by change lo+(b-lo)=b; omega⟩

theorem deepSlopeWalk_mem {L ds ts a b : _} (hw : SlopeWalk L ds ts a b)
    (ha : 3*a≤L) : b∈deepSlopeBands L ds.length := by
  unfold deepSlopeBands
  apply List.mem_flatMap.mpr
  exact ⟨ds,allWords_complete ds,deepSlopeBand_mem L ds.length (digitWord ds) a b ha (walk_equation hw)⟩

/-- Any list of pairwise-distinct slopes, each with a length-h valid
prehistory in [0,L/3], has size at most the depth-h band count. -/
theorem deep_slope_packing (L h : Nat) (ts : List Nat)
    (hn : ts.Nodup)
    (hw : ∀ b∈ts, ∃ ds ss a, ds.length=h ∧ 3*a≤L ∧ SlopeWalk L ds ss a b) :
    ts.length≤4^h*(L/(3*16^h)+1) := by
  have hsub : ts ⊆ deepSlopeBands L h := by
    intro b hb
    obtain ⟨ds,ss,a,hl,ha,hw'⟩ := hw b hb
    simpa [hl] using deepSlopeWalk_mem hw' ha
  have hle := List.Nodup.length_le_of_subset hn hsub
  simpa [deepSlopeBands_length] using hle

#print axioms deep_slope_packing
end BB429Q0Macro
