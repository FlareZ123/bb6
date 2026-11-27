import M62Carry
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BB6.Agent38M62
open BB6Coverage BB6Coverage.Agent31Pump

def w2 (k : Nat) : List Bool := zeros (5*k+2)++bits "101"

/-- Every right suffix is a finite sequence of 2/4-mod-5 zero packets. -/
inductive Word : List Bool → Prop
  | nil : Word []
  | two (k : Nat) (w : List Bool) (hw : Word w) : Word (w2 k++w)
  | four (k : Nat) (w : List Bool) (hw : Word w) : Word (w4 k++w)

/-- Right A has a leading 01, optionally one 1-mod-5 zero packet and W. -/
inductive RightA : List Bool → Prop
  | simple : RightA (bits "01")
  | extended (k : Nat) (w : List Bool) (hw : Word w) :
      RightA (bits "01"++zeros (5*k+1)++bits "101"++w)

theorem word_head_zero {w : List Bool} (h : Word w) : w.headD false = false := by
  cases h <;> rfl

theorem ra_head_zero {w : List Bool} (h : RightA w) : w.headD false = false := by
  cases h <;> rfl

theorem word_append_w4 {w : List Bool} (h : Word w) (k : Nat) :
    Word (w++w4 k) := by
  induction h with
  | nil =>
      simpa using (Word.four k [] Word.nil)
  | two j w hw ih =>
      simpa only [List.append_assoc] using (Word.two j (w++w4 k) ih)
  | four j w hw ih =>
      simpa only [List.append_assoc] using (Word.four j (w++w4 k) ih)

/-- All outputs of scan_a have 1-mod-5 first gap and zero or more W4 packets. -/
theorem ac_as_prefix {c : List Bool} (hc : ACode c) :
    ∃ a w, Word w ∧ c = zeros (5*a+1)++bits "101"++w := by
  induction hc with
  | base a =>
      exact ⟨a,[],Word.nil,by simp⟩
  | more k c hc ih =>
      obtain ⟨a,w,hw,he⟩ := ih
      refine ⟨a,w++w4 k,word_append_w4 hw k,?_⟩
      rw [he]
      simp only [List.append_assoc]

def section (L R : List Bool) : Z0 := ⟨5,false::L,R.tail⟩

theorem section_blank : run0 table 12 ⟨0,[],[]⟩ =
    some (section (bits "111") (bits "01")) := by
  simpa only [section,bits,List.tail_cons] using blank_entry

/-- Straight A→B branch when the right word is exactly 01. -/
theorem phase_a_simple (L : List Bool) :
    run0 table 18 (section L (bits "01")) =
      some (section (bits "110011"++L) []) := by
  simpa only [section,bits,List.tail_cons,List.tail_nil] using forward18_blank L

/-- Eight-step A→B rule when the next right digit has 1 zero. -/
theorem phase_a_short (L w : List Bool) (hw : Word w) :
    run0 table 8
      (section L (bits "01"++zeros 1++bits "101"++w)) =
      some (section (bits "111110"++L) w) := by
  have hh := word_head_zero hw
  simpa [section,bits,zeros,hh,List.append_assoc] using forward8 L w

/-- Eighteen-step A→B rule when the next right zero count >=6. -/
theorem phase_a_long (L w : List Bool) (hw : Word w) (k : Nat) :
    run0 table 18
      (section L (bits "01"++zeros (5*(k+1)+1)++bits "101"++w)) =
      some (section (bits "110011"++L) (w2 k++w)) := by
  have hn : 5*(k+1)+1 = 4+(5*k+2) := by omega
  have hz : zeros (5*(k+1)+1) = zeros 4++zeros (5*k+2) := by
    rw [hn,zeros_add]
  have hw2 : Word (w2 k++w) := Word.two k w hw
  have hh := word_head_zero hw2
  simpa [section,hh,w2,bits,zeros,hz,List.append_assoc] using
    forward18 L (w2 k++w)

/-- The 11-step B→B first W2(0) packet. -/
theorem phase_b_two (L w : List Bool) (hw : Word w) :
    run0 table 11 (section L (w2 0++w)) =
      some (section (bits "11111"++L) w) := by
  have hh := word_head_zero hw
  simpa [section,hh,w2,bits,zeros,List.append_assoc] using forward11a L w

/-- The 11-step B→B first W4(0) packet. -/
theorem phase_b_four (L w : List Bool) (hw : Word w) :
    run0 table 11 (section L (w4 0++w)) =
      some (section (bits "1100111"++L) w) := by
  have hh := word_head_zero hw
  simpa [section,hh,w4,bits,zeros,List.append_assoc] using forward11b L w

/-- Exhaustive phase A forward closure, before the B carry obligations. -/
theorem phase_a_step (L R : List Bool) (hL : LeftA L) (hR : RightA R) :
    ∃ n L' R', 0 < n ∧ LeftB L' ∧ Word R' ∧
      run0 table n (section L R) = some (section L' R') := by
  cases hR with
  | simple =>
      exact ⟨18,bits "110011"++L,[],by omega,left_a_eighteen hL,
        Word.nil,phase_a_simple L⟩
  | extended k w hw =>
      cases k with
      | zero =>
          exact ⟨8,bits "111110"++L,w,by omega,
            left_a_eight hL,hw,by simpa using phase_a_short L w hw⟩
      | succ k =>
          exact ⟨18,bits "110011"++L,w2 k++w,by omega,
            left_a_eighteen hL,Word.two k w hw,
            by simpa only [Nat.succ_eq_add_one] using phase_a_long L w hw k⟩

#print axioms word_head_zero
#print axioms ac_as_prefix
#print axioms phase_a_step
#print axioms phase_b_two
#print axioms phase_b_four
end BB6.Agent38M62
