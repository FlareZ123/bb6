import ResetTransport
import PairedDecoderCore

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace F197
open Q

/-
A fully parametric decoder for the paired-prefix reset family.

The Boolean base bit b is c_0 (false=A, true=T).  The list cs stores
[c_q,...,c_1], newest data bit first.  This order makes the right-side
counter encoding structurally recursive while pdOut/pdTail restore the
left-side data in the original c_0,...,c_q order.
-/

def pdJ (l : Tape) : Tape := pre [true,false,false] l

def pdH : Bool → Tape → Tape
  | false, l => pre [true,false,true,true,false,false] l
  | true,  l => pre [true,false,true,false,true,true,false,false] l

def pdOut : Bool → Tape → Tape
  | false, l => pre [true,false,true,false,true,true,false,false] l
  | true,  l => pre [true,false,true,false,true,false,true,true,false,false] l

def pdTail : List Bool → Tape → Tape
  | [], l => l
  | c::cs, l => pdTail cs (pdH c l)

/-- E encoding used underneath the outer R symbol. -/
def pdE : Bool → List Bool → Tape
  | false, [] => pre [true] blank
  | true,  [] => pre [true,false,true] blank
  | b, false::cs =>
      pre [true,true,true,false,false,false] (pdE b cs)
  | b, true::cs =>
      pre [true,false,true,true,true,false,false,false] (pdE b cs)

/-- R encoding consumed by the decoder. -/
def pdR : Bool → List Bool → Tape
  | false, [] => pre [true,true] blank
  | true,  [] => pre [true,true,false,true] blank
  | b, false::cs =>
      pre [true,true,true,true,false,false,false] (pdE b cs)
  | b, true::cs =>
      pre [true,true,false,true,true,true,false,false,false] (pdE b cs)

/-- Literal B-boundary right stack 0 :: shortenedRight, with shortenedRight=xR. -/
def pdRight (r : Tape) : Tape := pre [false,false,true,false] r

def pdPeelCost : Bool → Nat
  | false => 60
  | true => 64

def pdCost : Bool → List Bool → Nat
  | false, [] => 27
  | true,  [] => 31
  | b, c::cs => pdPeelCost c + pdCost b cs

/-- One data bit can always be peeled from the decoder, independently of the
    earlier data.  The eight exact local cases are PairedDecoderCore. -/
theorem pd_peel (b c : Bool) (cs : List Bool) (l : Tape) :
    run (pdPeelCost c)
      (other B (pdJ l) (pdRight (pdR b (c::cs)))) =
    some
      (other B (pdJ (pdH c l)) (pdRight (pdR b cs))) := by
  cases c with
  | false =>
      cases cs with
      | nil =>
          cases b with
          | false =>
              simpa [pdPeelCost, pdJ, pdH, pdRight, pdR, pdE] using
                peelA_u_e l
          | true =>
              simpa [pdPeelCost, pdJ, pdH, pdRight, pdR, pdE] using
                peelA_u_Ae l
      | cons d ds =>
          cases d with
          | false =>
              simpa [pdPeelCost, pdJ, pdH, pdRight, pdR, pdE] using
                peelA_u_t l (pdE b ds)
          | true =>
              simpa [pdPeelCost, pdJ, pdH, pdRight, pdR, pdE] using
                peelA_u_At l (pdE b ds)
  | true =>
      cases cs with
      | nil =>
          cases b with
          | false =>
              simpa [pdPeelCost, pdJ, pdH, pdRight, pdR, pdE] using
                peelT_Ct_e l
          | true =>
              simpa [pdPeelCost, pdJ, pdH, pdRight, pdR, pdE] using
                peelT_Ct_Ae l
      | cons d ds =>
          cases d with
          | false =>
              simpa [pdPeelCost, pdJ, pdH, pdRight, pdR, pdE] using
                peelT_Ct_t l (pdE b ds)
          | true =>
              simpa [pdPeelCost, pdJ, pdH, pdRight, pdR, pdE] using
                peelT_Ct_At l (pdE b ds)

/-- Complete exact decoder for an arbitrary nonempty paired-prefix data word. -/
theorem pd_decode (b : Bool) (cs : List Bool) (l : Tape) (hl : l 0 = true) :
    run (pdCost b cs)
      (other B (pdJ l) (pdRight (pdR b cs))) =
    some
      (other B (pdOut b (pdTail cs l))
        (pre [false,false,true] blank)) := by
  induction cs generalizing l with
  | nil =>
      cases b with
      | false =>
          simpa [pdCost, pdJ, pdRight, pdR, pdOut, pdTail] using
            reset_decoder_d l hl
      | true =>
          simpa [pdCost, pdJ, pdRight, pdR, pdOut, pdTail] using
            decoder_base_T l hl
  | cons c cs ih =>
      change run (pdPeelCost c + pdCost b cs)
        (other B (pdJ l) (pdRight (pdR b (c::cs)))) =
        some
          (other B (pdOut b (pdTail (c::cs) l))
            (pre [false,false,true] blank))
      rw [run_add, pd_peel b c cs l]
      simp only [Option.bind_some]
      simpa [pdTail] using ih (l := pdH c l) (by cases c <;> rfl)

def pdTrueCount : List Bool → Nat
  | [] => 0
  | c::cs => (if c then 1 else 0) + pdTrueCount cs

/-- Closed form for the decoder cost:
    27 + 60*q + 4*(number of T data bits). -/
theorem pdCost_formula (b : Bool) (cs : List Bool) :
    pdCost b cs =
      27 + 60 * cs.length +
        4 * ((if b then 1 else 0) + pdTrueCount cs) := by
  induction cs with
  | nil =>
      cases b <;> rfl
  | cons c cs ih =>
      cases c <;>
        simp [pdCost, pdPeelCost, pdTrueCount, ih, Nat.mul_add,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

#print axioms pd_peel
#print axioms pd_decode
#print axioms pdCost_formula

end F197
