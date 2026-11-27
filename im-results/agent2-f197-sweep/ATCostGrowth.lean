import ATPaired

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace F197
open Q

/-- Number of T symbols in the Boolean paired-reset data. -/
def atCountT : List Bool → Nat
  | [] => 0
  | false::cs => atCountT cs
  | true::cs => 1 + atCountT cs

theorem atCountT_append (a b : List Bool) :
    atCountT (a ++ b) = atCountT a + atCountT b := by
  induction a with
  | nil => simp [atCountT]
  | cons c cs ih =>
      cases c <;> simp [atCountT, ih, Nat.add_assoc]

theorem atCountT_reverse (cs : List Bool) :
    atCountT cs.reverse = atCountT cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      rw [List.reverse_cons, atCountT_append]
      cases c <;> simp [atCountT, ih, Nat.add_comm]

/-- Scanner total: 39 + 8 per data symbol + 10 per T. -/
theorem atpScanCost_formula (cs : List Bool) (hne : cs ≠ []) :
    atpScanCost cs = 39 + 8 * cs.length + 10 * atCountT cs := by
  induction cs with
  | nil => exact (hne rfl).elim
  | cons c rest ih =>
      cases rest with
      | nil => cases c <;> decide
      | cons d ds =>
          have hh : d::ds ≠ [] := by simp
          have ht := ih hh
          cases c <;> simp [atpScanCost, atCountT] at * <;> omega

/-- Decoder total: 3 + 60 per data symbol + 4 per T. -/
theorem atpDecCost_formula (cs : List Bool) (hne : cs ≠ []) :
    atpDecCost cs = 3 + 60 * cs.length + 4 * atCountT cs := by
  induction cs with
  | nil => exact (hne rfl).elim
  | cons c rest ih =>
      cases rest with
      | nil => cases c <;> decide
      | cons d ds =>
          have hh : d::ds ≠ [] := by simp
          have ht := ih hh
          cases c <;> simp [atpDecCost, atCountT] at * <;> omega

/-- Closed exact primitive-transition cost, 156 + 68q +14t for q+1 data. -/
theorem atpTotalCost_formula (cs : List Bool) (hne : cs ≠ []) :
    46 + (atpScanCost cs + atpDecCost cs.reverse) =
      88 + 68 * cs.length + 14 * atCountT cs := by
  have hr : cs.reverse ≠ [] := by simpa using hne
  rw [atpScanCost_formula cs hne, atpDecCost_formula cs.reverse hr]
  simp only [List.length_reverse, atCountT_reverse]
  omega

theorem atp_family_closed_cost (cs : List Bool) (l : Tape)
    (hne : cs ≠ []) (hl : l 0 = true) :
    run (88 + 68 * cs.length + 14 * atCountT cs)
      (other B
        (pre [true,true,false,false,true,false,true,true,false,false]
          (atpSource cs l))
        (pre [false,false,true] blank)) =
    some (other B (atpOut cs.reverse l) (pre [false,false,true] blank)) := by
  rw [← atpTotalCost_formula cs hne]
  exact atp_family cs l hne hl

/-- The actual prefix encoding consumed by the scanner, Z(data) A A. -/
def atpSourceBits : List Bool → List Bool
  | [] => []
  | [false] => [true,false,true,false,true,false]
  | [true] => [true,true,false,false,true,false,true,false]
  | false::d::ds =>
      [true,false,true,true,false,false] ++ atpSourceBits (d::ds)
  | true::d::ds =>
      [true,true,false,false,true,true,false,false] ++ atpSourceBits (d::ds)

/-- Output prefix AAAT A H(data), with reversed input data. -/
def atpOutBits : List Bool → List Bool
  | [] => []
  | [false] =>
      [true,false,true,false,true,false,true,true,false,false,
       true,false,true,false,true,true,false,false]
  | [true] =>
      [true,false,true,false,true,false,true,true,false,false,
       true,false,true,false,true,false,true,true,false,false]
  | false::d::ds =>
      atpOutBits (d::ds) ++ [true,false,true,true,false,false]
  | true::d::ds =>
      atpOutBits (d::ds) ++ [true,false,true,false,true,true,false,false]

theorem atpPre_append (a b : List Bool) (l : Tape) :
    pre (a ++ b) l = pre a (pre b l) := by
  induction a with
  | nil => rfl
  | cons c cs ih =>
      change cons c (pre (cs ++ b) l) = cons c (pre cs (pre b l))
      rw [ih]

theorem atpSourceBits_sound (data : List Bool) (l : Tape) :
    atpSource data l = pre (atpSourceBits data) l := by
  induction data with
  | nil => rfl
  | cons c cs ih =>
      cases cs with
      | nil => cases c <;> rfl
      | cons d ds =>
          cases c <;>
            simp [atpSource, atpSourceBits, ih, pre]

theorem atpOutBits_sound (data : List Bool) (l : Tape) :
    atpOut data l = pre (atpOutBits data) l := by
  induction data generalizing l with
  | nil => rfl
  | cons c cs ih =>
      cases cs with
      | nil => cases c <;> rfl
      | cons d ds =>
          cases c with
          | false =>
              change atpOut (d::ds) (atpH false l) =
                pre (atpOutBits (d::ds) ++
                  [true,false,true,true,false,false]) l
              rw [ih (atpH false l), atpPre_append]
              rfl
          | true =>
              change atpOut (d::ds) (atpH true l) =
                pre (atpOutBits (d::ds) ++
                  [true,false,true,false,true,true,false,false]) l
              rw [ih (atpH true l), atpPre_append]
              rfl

theorem atpSourceBits_length (cs : List Bool) (hne : cs ≠ []) :
    (atpSourceBits cs).length =
      6 * cs.length + 2 * atCountT cs := by
  induction cs with
  | nil => exact (hne rfl).elim
  | cons c rest ih =>
      cases rest with
      | nil => cases c <;> decide
      | cons d ds =>
          have hh : d::ds ≠ [] := by simp
          have ht := ih hh
          cases c <;> simp [atpSourceBits, atCountT] at * <;> omega

theorem atpOutBits_length (cs : List Bool) (hne : cs ≠ []) :
    (atpOutBits cs).length =
      12 + 6 * cs.length + 2 * atCountT cs := by
  induction cs with
  | nil => exact (hne rfl).elim
  | cons c rest ih =>
      cases rest with
      | nil => cases c <;> decide
      | cons d ds =>
          have hh : d::ds ≠ [] := by simp
          have ht := ih hh
          cases c <;> simp [atpOutBits, atCountT] at * <;> omega

/-- Every member of the unbounded exact reset family increases the encoded
    left prefix length by precisely two bits. -/
theorem atpBitGrowth (cs : List Bool) (hne : cs ≠ []) :
    (atpOutBits cs.reverse).length =
      10 + (atpSourceBits cs).length + 2 := by
  have hr : cs.reverse ≠ [] := by simpa using hne
  rw [atpOutBits_length cs.reverse hr, atpSourceBits_length cs hne]
  simp only [List.length_reverse, atCountT_reverse]
  omega

/-- Exact literal source theorem with both sides as finite bit strings:
    the cost is closed-form and the very prefixes satisfy atpBitGrowth. -/
theorem atp_family_bits (cs : List Bool) (l : Tape)
    (hne : cs ≠ []) (hl : l 0 = true) :
    run (88 + 68 * cs.length + 14 * atCountT cs)
      (other B
        (pre [true,true,false,false,true,false,true,true,false,false]
          (pre (atpSourceBits cs) l))
        (pre [false,false,true] blank)) =
    some
      (other B (pre (atpOutBits cs.reverse) l)
        (pre [false,false,true] blank)) := by
  rw [← atpSourceBits_sound, ← atpOutBits_sound]
  exact atp_family_closed_cost cs l hne hl

#print axioms atpTotalCost_formula
#print axioms atp_family_closed_cost
#print axioms atpBitGrowth
#print axioms atp_family_bits

end F197
