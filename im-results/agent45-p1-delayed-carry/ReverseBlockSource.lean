import ReverseBlock
import BatchCarry
namespace BB6.Agent45ReverseBlock
open BB6.Agent9BatchCarry (Interior Edge)
abbrev SourceWalk := BB6.Agent9BatchCarry.Walk

theorem source_to_reverse {q c k z : Nat} (h : SourceWalk q c k z) :
    Walk (q+k) z (List.replicate k 0) c := by
  induction h with
  | nil q c hi =>
    exact Walk.nil (by simp; unfold Interior at hi; omega)
  | cons q c d k z he ht ih =>
    have hi : Walk (q+(k+1)) z (List.replicate k 0) d := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih
    obtain ⟨hc,hd,he⟩ := he
    unfold Interior at hc hd
    rw [List.replicate_succ]
    rcases he with he|he
    · apply Walk.step _ d 0 0 c hi (by omega) (by omega) <;> simp <;> omega
    · apply Walk.step _ d 0 1 c hi (by omega) (by omega) <;> simp <;> omega

theorem reverse_to_source {q c k z : Nat} (hc : Interior q c)
    (h : Walk (q+k) z (List.replicate k 0) c) : SourceWalk q c k z := by
  induction k generalizing q c with
  | zero =>
    simp only [List.replicate_zero,Nat.add_zero] at h
    cases h
    exact BB6.Agent9BatchCarry.Walk.nil q z hc
  | succ k ih =>
    rw [List.replicate_succ] at h
    cases h with
    | step ys d y b r ht hy hb hd hr he =>
      simp only [List.length_replicate, Nat.add_sub_cancel, Nat.add_zero] at he
      have he' : 2*d=c ∨ 2*d=c+q := by
        rcases (show b=0 ∨ b=1 by omega) with h0|h1
        · left; simpa [h0] using he
        · right; simpa [h1] using he
      have hd' : Interior (q+1) d := by
        unfold Interior at hc ⊢
        rcases he' with h0|h1 <;> omega
      have ht' : Walk (q+1+k) z (List.replicate k 0) d := by
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht
      exact BB6.Agent9BatchCarry.Walk.cons q c d k z ⟨hc,hd',he'⟩ (ih hd' ht')

theorem digits_zero (k : Nat) : digits (List.replicate k 0)=0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ,digits,ih]

theorem source_fast_iff (q c k z : Nat) (hc : Interior q c)
    (hfit : 2^(k+1)≤q+k) :
    fast (q+k) k (2^k*z)=some c ↔ SourceWalk q c k z := by
  have h := fast_iff_walk (q+k) z (List.replicate k 0) c (by simp) (by simpa using hfit)
  simp only [List.length_replicate,digits_zero,Nat.add_zero] at h
  exact ⟨fun hf => reverse_to_source hc (h.mp hf),fun hs => h.mpr (source_to_reverse hs)⟩

def backBlock (q k : Nat) (ends : List Nat) : List Nat :=
  (ends.filterMap (fun z => fast (q+k) k (2^k*z))).filter (fun c => decide (1≤c ∧ c+3≤q))

theorem source_interior {q c k z : Nat} (h : SourceWalk q c k z) : Interior q c := by
  cases h with
  | nil q c hi => exact hi
  | cons q c d k z he ht => exact he.1

theorem mem_backBlock (q k c : Nat) (ends : List Nat) (hfit : 2^(k+1)≤q+k) :
    c ∈ backBlock q k ends ↔ ∃ z∈ends, SourceWalk q c k z := by
  simp only [backBlock,List.mem_filter,List.mem_filterMap,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨z,hz,hf⟩,hc⟩
    exact ⟨z,hz,(source_fast_iff q c k z hc hfit).mp hf⟩
  · rintro ⟨z,hz,hw⟩
    have hc := source_interior hw
    exact ⟨⟨z,hz,(source_fast_iff q c k z hc hfit).mpr hw⟩,hc⟩

theorem source_append {q c k z : Nat} (h : SourceWalk q c k z)
    {j w : Nat} (ht : SourceWalk (q+k) z j w) : SourceWalk q c (k+j) w := by
  induction h with
  | nil q c hi => simpa using ht
  | cons q c d k z he hs ih =>
    have hh : SourceWalk (q+1+k) z j w := by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht
    have htail := ih hh
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using BB6.Agent9BatchCarry.Walk.cons q c d (k+j) w he htail

theorem source_split (q c k j w : Nat) (h : SourceWalk q c (k+j) w) :
    ∃ z, SourceWalk q c k z ∧ SourceWalk (q+k) z j w := by
  induction k generalizing q c with
  | zero =>
    simp only [Nat.zero_add,Nat.add_zero] at h ⊢
    exact ⟨c,BB6.Agent9BatchCarry.Walk.nil q c (source_interior h),h⟩
  | succ k ih =>
    have hh : SourceWalk q c (k+j+1) w := by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
    cases hh with
    | cons q c d len w he ht =>
      obtain ⟨z,h1,h2⟩ := ih (q+1) d ht
      exact ⟨z,BB6.Agent9BatchCarry.Walk.cons q c d k z he h1,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h2⟩

/-- Exact drop-in for k single reverse steps in the existing live-set proof. -/
theorem live_block (q k j c : Nat) (hfit : 2^(k+1)≤q+k) :
    c∈backBlock q k (BB6.Agent9BatchCarry.live (q+k) j) ↔
    c∈BB6.Agent9BatchCarry.live q (k+j) := by
  rw [mem_backBlock q k c _ hfit, BB6.Agent9BatchCarry.mem_live]
  constructor
  · rintro ⟨z,hz,h1⟩
    obtain ⟨w,h2⟩ := (BB6.Agent9BatchCarry.mem_live (q+k) z j).mp hz
    exact ⟨w,source_append h1 h2⟩
  · rintro ⟨w,hw⟩
    obtain ⟨z,h1,h2⟩ := source_split q c k j w hw
    exact ⟨z,(BB6.Agent9BatchCarry.mem_live (q+k) z j).mpr ⟨w,h2⟩,h1⟩

#print axioms source_fast_iff
#print axioms mem_backBlock
#print axioms live_block
end BB6.Agent45ReverseBlock
