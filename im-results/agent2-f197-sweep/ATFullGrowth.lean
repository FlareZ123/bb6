import ATCounter

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace F197
open Q

/- Strict +2-bit growth for the full two-parameter P^n TAT family.
   The finite prefixes below, not the infinite right blank tape, are
   the measured words. n and data are arbitrary; data must be nonempty. -/

def atPBits : Nat → List Bool
  | 0 => []
  | n+1 =>
      [true,false,true,false,true,true,false,false] ++ atPBits n

theorem atPBits_length (n : Nat) :
    (atPBits n).length = 8*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [atPBits,ih]
      omega

theorem atPBits_sound (n : Nat) (l : Tape) :
    atPreP n l = pre (atPBits n) l := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change pre [true,false,true,false,true,true,false,false]
        (atPreP n l) =
        pre ([true,false,true,false,true,true,false,false] ++
          atPBits n) l
      rw [ih,atpPre_append]

/-- The recursive decoder's final Phi gets AAAT prefixed by the
    counter decoder; this is the exact same prefix as the n=0 output
    atpOut, when at least one data letter exists. -/
theorem atpOut_eq_Phi (data : List Bool) (l : Tape)
    (hne : data ≠ []) :
    atpOut data l =
      pre [true,false,true,false,true,false,true,true,false,false]
        (atpPhi data l) := by
  induction data generalizing l with
  | nil => exact (hne rfl).elim
  | cons c cs ih =>
      cases cs with
      | nil =>
          cases c <;>
            simp [atpOut,atpPhi,atpH,pre]
      | cons d ds =>
          cases c with
          | false =>
              simpa [atpOut,atpPhi] using
                ih (l := atpH false l) (by simp)
          | true =>
              simpa [atpOut,atpPhi] using
                ih (l := atpH true l) (by simp)

/-- Finite input prefix P^n TAT Z AA. -/
def atFullInputBits (n : Nat) (data : List Bool) : List Bool :=
  atPBits n ++
    ([true,true,false,false,true,false,true,true,false,false] ++
      atpSourceBits data)

/-- Finite output prefix P^n AAAT Phi. -/
def atFullOutputBits (n : Nat) (data : List Bool) : List Bool :=
  atPBits n ++ atpOutBits data.reverse

theorem atFullInput_sound (n : Nat) (data : List Bool) (l : Tape) :
    atPreP n
      (pre [true,true,false,false,true,false,true,true,false,false]
        (atpSource data l)) =
    pre (atFullInputBits n data) l := by
  rw [atPBits_sound,atpSourceBits_sound]
  simp [atFullInputBits,atpPre_append]

theorem atFullOutput_sound (n : Nat) (data : List Bool)
    (l : Tape) (hne : data ≠ []) :
    atPreP n
      (pre [true,false,true,false,true,false,true,true,false,false]
        (atpPhi data.reverse l)) =
    pre (atFullOutputBits n data) l := by
  have hd : data.reverse ≠ [] := by simpa using hne
  rw [atPBits_sound,← atpOut_eq_Phi data.reverse l hd]
  rw [atpOutBits_sound]
  simp [atFullOutputBits,atpPre_append]

theorem atFullBitGrowth (n : Nat) (data : List Bool)
    (hne : data ≠ []) :
    (atFullOutputBits n data).length =
      (atFullInputBits n data).length + 2 := by
  have hg := atpBitGrowth data hne
  simp [atFullOutputBits,atFullInputBits,List.length_append] at *
  omega

/-- Full source-level finite-bit normal form, with the closed step count
    and exact two-bit growth of its input and output prefixes. -/
theorem atp_full_family_bits (n : Nat) (data : List Bool) (l : Tape)
    (hne : data ≠ []) (hl : l 0 = true) :
    run (68*n + 88 + 68*data.length + 14*atCountT data)
      (other B (pre (atFullInputBits n data) l)
        (atpRight (atQ 0))) =
    some
      (other B (pre (atFullOutputBits n data) l)
        (atpRight (atQ 0))) := by
  rw [← atFullInput_sound n data l,
      ← atFullOutput_sound n data l hne]
  exact atp_full_family_closed n data l hne hl

#print axioms atpOut_eq_Phi
#print axioms atFullBitGrowth
#print axioms atp_full_family_bits

end F197
