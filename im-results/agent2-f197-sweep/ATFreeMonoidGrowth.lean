import ATFreeMonoid

set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace F197
open Q

/- Finite bitword source and target of the mixed P/Q free-monoid reset.
   The lengths count explicit run-prefix bits, not the infinite blank tape.
   A genuine source-level theorem is obtained by combining the list
   encoders with fmFullFamilyClosed. -/

def fmInputTokenBits (b : Bool) : List Bool :=
  if b then
    [true,true,false,false,true,false,true,true,false,false]
  else [true,false,true,false,true,true,false,false]

def fmOutputTokenBits (b : Bool) : List Bool :=
  if b then
    [true,false,true,false,true,false,true,true,false,false]
  else [true,false,true,false,true,true,false,false]

def fmWordInBits : List Bool → List Bool
  | [] => []
  | b::bs => fmInputTokenBits b ++ fmWordInBits bs

def fmWordOutBits : List Bool → List Bool
  | [] => []
  | b::bs => fmOutputTokenBits b ++ fmWordOutBits bs

theorem fmWordInBits_sound (ws : List Bool) (l : Tape) :
    fmWordIn ws l = pre (fmWordInBits ws) l := by
  induction ws with
  | nil => rfl
  | cons b bs ih =>
      cases b with
      | false =>
          change pre [true,false,true,false,true,true,false,false]
            (fmWordIn bs l) =
            pre ([true,false,true,false,true,true,false,false] ++
              fmWordInBits bs) l
          rw [ih,atpPre_append]
      | true =>
          change pre [true,true,false,false,true,false,true,true,false,false]
            (fmWordIn bs l) =
            pre ([true,true,false,false,true,false,true,true,false,false] ++
              fmWordInBits bs) l
          rw [ih,atpPre_append]

theorem fmWordOutBits_sound (ws : List Bool) (l : Tape) :
    fmWordOut ws l = pre (fmWordOutBits ws) l := by
  induction ws with
  | nil => rfl
  | cons b bs ih =>
      cases b with
      | false =>
          change pre [true,false,true,false,true,true,false,false]
            (fmWordOut bs l) =
            pre ([true,false,true,false,true,true,false,false] ++
              fmWordOutBits bs) l
          rw [ih,atpPre_append]
      | true =>
          change pre [true,false,true,false,true,false,true,true,false,false]
            (fmWordOut bs l) =
            pre ([true,false,true,false,true,false,true,true,false,false] ++
              fmWordOutBits bs) l
          rw [ih,atpPre_append]

/-- Substitution P->P, Q->AAAT preserves the total number of bits in the
    arbitrary input blockword, even though it changes its run symbols. -/
theorem fmBlockwordLength (ws : List Bool) :
    (fmWordOutBits ws).length = (fmWordInBits ws).length := by
  induction ws with
  | nil => rfl
  | cons b bs ih =>
      cases b <;>
        simp [fmWordOutBits,fmWordInBits,
          fmInputTokenBits,fmOutputTokenBits,List.length_append] at * <;>
        omega

/-- The data expansion Phi=A H(data), with
    H(A)=AT and H(T)=AAT, as a finite bitword. -/
def fmPhiBits : List Bool → List Bool
  | [] => []
  | [false] => [true,false,true,false,true,true,false,false]
  | [true] => [true,false,true,false,true,false,true,true,false,false]
  | false::d::ds =>
      fmPhiBits (d::ds) ++
        [true,false,true,true,false,false]
  | true::d::ds =>
      fmPhiBits (d::ds) ++
        [true,false,true,false,true,true,false,false]

theorem fmPhiBits_sound (data : List Bool) (l : Tape) :
    atpPhi data l = pre (fmPhiBits data) l := by
  induction data generalizing l with
  | nil => rfl
  | cons b cs ih =>
      cases cs with
      | nil => cases b <;> rfl
      | cons d ds =>
          cases b with
          | false =>
              change atpPhi (d::ds) (atpH false l) =
                pre (fmPhiBits (d::ds) ++
                  [true,false,true,true,false,false]) l
              rw [ih (atpH false l),atpPre_append]
              rfl
          | true =>
              change atpPhi (d::ds) (atpH true l) =
                pre (fmPhiBits (d::ds) ++
                  [true,false,true,false,true,true,false,false]) l
              rw [ih (atpH true l),atpPre_append]
              rfl

theorem fmPhiBits_length (data : List Bool) (hne : data ≠ []) :
    (fmPhiBits data).length =
      2 + 6 * data.length + 2 * atCountT data := by
  induction data with
  | nil => exact (hne rfl).elim
  | cons c rest ih =>
      cases rest with
      | nil => cases c <;> decide
      | cons d ds =>
          have hh : d::ds ≠ [] := by simp
          have h := ih hh
          cases c <;>
            simp [fmPhiBits,atCountT,List.length_append] at * <;>
            omega

def fmInputBits (ws data : List Bool) : List Bool :=
  fmWordInBits ws ++ atpSourceBits data

def fmOutputBits (ws data : List Bool) : List Bool :=
  fmWordOutBits ws ++ fmPhiBits data.reverse

theorem fmInputBits_sound (ws data : List Bool) (l : Tape) :
    fmWordIn ws (atpSource data l) =
      pre (fmInputBits ws data) l := by
  calc
    fmWordIn ws (atpSource data l) =
        pre (fmWordInBits ws) (atpSource data l) :=
      fmWordInBits_sound ws _
    _ = pre (fmWordInBits ws) (pre (atpSourceBits data) l) := by
      rw [atpSourceBits_sound]
    _ = pre (fmInputBits ws data) l := by
      simp [fmInputBits,atpPre_append]

theorem fmOutputBits_sound (ws data : List Bool) (l : Tape) :
    fmWordOut ws (atpPhi data.reverse l) =
      pre (fmOutputBits ws data) l := by
  calc
    fmWordOut ws (atpPhi data.reverse l) =
        pre (fmWordOutBits ws) (atpPhi data.reverse l) :=
      fmWordOutBits_sound ws _
    _ = pre (fmWordOutBits ws) (pre (fmPhiBits data.reverse) l) := by
      rw [fmPhiBits_sound]
    _ = pre (fmOutputBits ws data) l := by
      simp [fmOutputBits,atpPre_append]

/-- **Strict +2 explicit-bit growth**, for any nonempty data and any
    mixed P/Q prefix, with no finite upper bound on either word. -/
theorem fmStrictBitGrowth (ws data : List Bool) (hne : data ≠ []) :
    (fmOutputBits ws data).length =
      (fmInputBits ws data).length + 2 := by
  have hb := fmBlockwordLength ws
  have hi := atpSourceBits_length data hne
  have hr : data.reverse ≠ [] := by simpa using hne
  have ho := fmPhiBits_length data.reverse hr
  have ht := atCountT_reverse data
  simp [fmInputBits,fmOutputBits,List.length_append] at *
  omega

/-- Exact uniform source certificate, with closed primitive step
    count and both sides represented by finite Boolean bitwords. -/
theorem fmFullFamilyBits (b : Bool) (bs data : List Bool)
    (l : Tape) (hne : data ≠ []) (hl : l 0 = true) :
    run ((6 + 68 * data.length + 14 * atCountT data) +
      (68 * (b::bs).length + 14 * fmCountQ (b::bs)))
      (other B
        (pre (fmInputBits (b::bs) data) l)
        (atpRight (pre [true] blank))) =
    some
      (other B
        (pre (fmOutputBits (b::bs) data) l)
        (atpRight (pre [true] blank))) := by
  have hs := fmInputBits_sound (b::bs) data l
  have ho := fmOutputBits_sound (b::bs) data l
  simpa only [hs,ho] using
    fmFullFamilyClosed b bs data l hne hl

#print axioms fmBlockwordLength
#print axioms fmStrictBitGrowth
#print axioms fmFullFamilyBits

end F197
