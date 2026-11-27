import M62Core
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BB6.Agent38M62
open BB6Coverage BB6Coverage.Agent31Pump

theorem ones_add (a b : Nat) : ones (a+b) = ones a ++ ones b := by
  unfold ones
  rw [List.replicate_append_replicate]

theorem zeros_add (a b : Nat) : zeros (a+b) = zeros a ++ zeros b := by
  unfold zeros
  rw [List.replicate_append_replicate]

/-- Near-head-first unary A frame, separated internally by single blanks. -/
inductive AFrame : List Bool → Prop
  | base (a : Nat) : AFrame (ones (5*a+3))
  | more (b : Nat) (w : List Bool) (hw : AFrame w) :
      AFrame (ones (5*(b+1)+1) ++ false::w)

/-- A completed O frame, to be separated from its neighbors by two blanks. -/
inductive OFrame : List Bool → Prop
  | base (a : Nat) : OFrame (ones (5*(a+1)))
  | more (c : Nat) (w : List Bool) (hw : AFrame w) :
      OFrame (ones (5*c+3) ++ false::w)

/-- B terminal frame. -/
inductive BFrame : List Bool → Prop
  | base (a : Nat) : BFrame (ones (5*a+2))
  | more (c : Nat) (w : List Bool) (hw : AFrame w) :
      BFrame (ones (5*(c+1)) ++ false::w)

/-- All remaining O frames, including their separating double zero. -/
inductive OuterTail : List Bool → Prop
  | nil : OuterTail []
  | cons (o s : List Bool) (ho : OFrame o) (hs : OuterTail s) :
      OuterTail (zeros 2 ++ o ++ s)

/-- A/B complete left words, nearest bit first, with no scanned bit. -/
inductive LeftA : List Bool → Prop
  | mk (t s : List Bool) (ht : AFrame t) (hs : OuterTail s) : LeftA (t++s)
inductive LeftB : List Bool → Prop
  | mk (t s : List Bool) (ht : BFrame t) (hs : OuterTail s) : LeftB (t++s)

/-- Adding 2 ones to an A frame turns it into a completed O frame. -/
theorem a_to_outer {t : List Bool} (h : AFrame t) :
    OFrame (ones 2 ++ t) := by
  cases h with
  | base a =>
      have he : ones 2 ++ ones (5*a+3) = ones (5*(a+1)) := by
        rw [← ones_add]
        congr 1
        omega
      rw [he]
      exact OFrame.base a
  | more b w hw =>
      have he : ones 2 ++ (ones (5*(b+1)+1) ++ false::w) =
          ones (5*(b+1)+3) ++ false::w := by
        rw [← List.append_assoc, ← ones_add]
        have hnum : 2+(5*(b+1)+1) = 5*(b+1)+3 := by omega
        rw [hnum]
      rw [he]
      exact OFrame.more (b+1) w hw

/-- Adding 3 ones to a B terminal closes an O frame. -/
theorem b_to_outer {t : List Bool} (h : BFrame t) :
    OFrame (ones 3 ++ t) := by
  cases h with
  | base a =>
      have he : ones 3 ++ ones (5*a+2) = ones (5*(a+1)) := by
        rw [← ones_add]
        congr 1
        omega
      rw [he]
      exact OFrame.base a
  | more c w hw =>
      have he : ones 3 ++ (ones (5*(c+1)) ++ false::w) =
          ones (5*(c+1)+3) ++ false::w := by
        rw [← List.append_assoc, ← ones_add]
      rw [he]
      exact OFrame.more (c+1) w hw

/-- Adding 3 ones to a completed O frame starts a fresh A terminal. -/
theorem o_to_a {t : List Bool} (h : OFrame t) :
    AFrame (ones 3 ++ t) := by
  cases h with
  | base a =>
      have he : ones 3 ++ ones (5*(a+1)) = ones (5*(a+1)+3) := by
        rw [← ones_add]
      rw [he]
      exact AFrame.base (a+1)
  | more c w hw =>
      have he : ones 3 ++ (ones (5*c+3) ++ false::w) =
          ones (5*(c+1)+1) ++ false::w := by
        rw [← List.append_assoc, ← ones_add]
        have hnum : 3+(5*c+3) = 5*(c+1)+1 := by omega
        rw [hnum]
      rw [he]
      exact AFrame.more c w hw

/-- Adding five ones to B preserves its terminal grammar. -/
theorem b_plus_five {t : List Bool} (h : BFrame t) :
    BFrame (ones 5 ++ t) := by
  cases h with
  | base a =>
      have he : ones 5 ++ ones (5*a+2) = ones (5*(a+1)+2) := by
        rw [← ones_add]
        congr 1
        omega
      rw [he]
      exact BFrame.base (a+1)
  | more c w hw =>
      have he : ones 5 ++ (ones (5*(c+1)) ++ false::w) =
          ones (5*((c+1)+1)) ++ false::w := by
        rw [← List.append_assoc, ← ones_add]
        have hnum : 5+(5*(c+1)) = 5*((c+1)+1) := by omega
        rw [hnum]
      rw [he]
      exact BFrame.more (c+1) w hw

/-- The A→B eighteen-move rewrite, at the level of near-first left grammar. -/
theorem left_a_eighteen {l : List Bool} (h : LeftA l) :
    LeftB (bits "110011" ++ l) := by
  cases h with
  | mk t s ht hs =>
      have ho := a_to_outer ht
      have hb : LeftB (ones 2 ++ (zeros 2 ++ (ones 2 ++ t) ++ s)) :=
        LeftB.mk (ones 2) (zeros 2 ++ (ones 2 ++ t) ++ s)
          (BFrame.base 0) (OuterTail.cons (ones 2 ++ t) s ho hs)
      simpa [bits,ones,zeros,List.append_assoc] using hb

/-- The A→B eight-move rewrite, at the level of near-first left grammar. -/
theorem left_a_eight {l : List Bool} (h : LeftA l) :
    LeftB (bits "111110" ++ l) := by
  cases h with
  | mk t s ht hs =>
      have hb : LeftB ((ones 5 ++ false::t) ++ s) :=
        LeftB.mk (ones 5 ++ false::t) s (BFrame.more 0 t ht) hs
      simpa [bits,ones,zeros,List.append_assoc] using hb

/-- The B→B eleven-move W2(0) rewrite. -/
theorem left_b_five {l : List Bool} (h : LeftB l) :
    LeftB (bits "11111" ++ l) := by
  cases h with
  | mk t s ht hs =>
      have hb : LeftB ((ones 5 ++ t) ++ s) :=
        LeftB.mk (ones 5 ++ t) s (b_plus_five ht) hs
      simpa [bits,ones,zeros,List.append_assoc] using hb

/-- The B→B eleven-move W4(0) rewrite. -/
theorem left_b_eleven {l : List Bool} (h : LeftB l) :
    LeftB (bits "1100111" ++ l) := by
  cases h with
  | mk t s ht hs =>
      have ho := b_to_outer ht
      have hb : LeftB (ones 2 ++ (zeros 2 ++ (ones 3 ++ t) ++ s)) :=
        LeftB.mk (ones 2) (zeros 2 ++ (ones 3 ++ t) ++ s)
          (BFrame.base 0) (OuterTail.cons (ones 3 ++ t) s ho hs)
      simpa [bits,ones,zeros,List.append_assoc] using hb

/-- Consume the B terminal and its old double-zero separator. -/
theorem carry_left {s : List Bool} (hs : OuterTail s) :
    LeftA (ones 3 ++ s.drop 2) := by
  cases hs with
  | nil =>
      have ha : LeftA (ones 3 ++ []) :=
        LeftA.mk (ones 3) [] (AFrame.base 0) OuterTail.nil
      simpa using ha
  | cons o s ho ht =>
      have ha : LeftA ((ones 3 ++ o) ++ s) :=
        LeftA.mk (ones 3 ++ o) s (o_to_a ho) ht
      simpa [zeros,List.append_assoc] using ha

#print axioms a_to_outer
#print axioms b_to_outer
#print axioms o_to_a
#print axioms b_plus_five
#print axioms left_a_eighteen
#print axioms left_a_eight
#print axioms left_b_five
#print axioms left_b_eleven
#print axioms carry_left
end BB6.Agent38M62
