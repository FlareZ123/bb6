import PairedScan
import PairedDecoderCore
import ResetTransport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace F197
open Q

def prH : Bool → Tape → Tape
  | false, l => pre [true,false,true,true,false,false] l
  | true,  l => pre [true,false,true,false,true,true,false,false] l

def prOut : List Bool → Tape → Tape
  | [], l => l
  | [false], l => pre [true,false,true,false,true,true,false,false] l
  | [true], l =>
      pre [true,false,true,false,true,false,true,true,false,false] l
  | false::d::ds, l => prOut (d::ds) (prH false l)
  | true::d::ds, l => prOut (d::ds) (prH true l)

def prPeelCost : Bool → Nat
  | false => 60
  | true => 64

def prDecCost : List Bool → Nat
  | [] => 0
  | [false] => 27
  | [true] => 31
  | false::d::ds => 60 + prDecCost (d::ds)
  | true::d::ds => 64 + prDecCost (d::ds)

/-- Peel the newest data bit from any decoder word with at least two bits. -/
theorem pr_peel (c d : Bool) (ds : List Bool) (l : Tape) :
    run (prPeelCost c)
      (other B (prJ l) (prXRight (prR (c::d::ds)))) =
    some
      (other B (prJ (prH c l)) (prXRight (prR (d::ds)))) := by
  cases c with
  | false =>
      cases ds with
      | nil =>
          cases d with
          | false =>
              simpa [prPeelCost, prJ, prH, prXRight, prR, prE] using
                peelA_u_e l
          | true =>
              simpa [prPeelCost, prJ, prH, prXRight, prR, prE] using
                peelA_u_Ae l
      | cons e es =>
          cases d with
          | false =>
              simpa [prPeelCost, prJ, prH, prXRight, prR, prE] using
                peelA_u_t l (prE (e::es))
          | true =>
              simpa [prPeelCost, prJ, prH, prXRight, prR, prE] using
                peelA_u_At l (prE (e::es))
  | true =>
      cases ds with
      | nil =>
          cases d with
          | false =>
              simpa [prPeelCost, prJ, prH, prXRight, prR, prE] using
                peelT_Ct_e l
          | true =>
              simpa [prPeelCost, prJ, prH, prXRight, prR, prE] using
                peelT_Ct_Ae l
      | cons e es =>
          cases d with
          | false =>
              simpa [prPeelCost, prJ, prH, prXRight, prR, prE] using
                peelT_Ct_t l (prE (e::es))
          | true =>
              simpa [prPeelCost, prJ, prH, prXRight, prR, prE] using
                peelT_Ct_At l (prE (e::es))

/-- Exact decoder for every nonempty reversed A/T data word. -/
theorem pr_decode (data : List Bool) (l : Tape)
    (hne : data ≠ []) (hl : l 0 = true) :
    run (prDecCost data)
      (other B (prJ l) (prXRight (prR data))) =
    some
      (other B (prOut data l) (pre [false,false,true] blank)) := by
  induction data generalizing l with
  | nil => exact (hne rfl).elim
  | cons c tail ih =>
      cases tail with
      | nil =>
          cases c with
          | false =>
              simpa [prDecCost, prJ, prXRight, prR, prOut] using
                reset_decoder_d l hl
          | true =>
              simpa [prDecCost, prJ, prXRight, prR, prOut] using
                decoder_base_T l hl
      | cons d ds =>
          have htail : d::ds ≠ [] := by simp
          change run (prPeelCost c + prDecCost (d::ds))
            (other B (prJ l) (prXRight (prR (c::d::ds)))) =
            some
              (other B (prOut (c::d::ds) l)
                (pre [false,false,true] blank))
          rw [run_add, pr_peel c d ds l]
          simp only [Option.bind_some]
          have hh : (prH c l) 0 = true := by
            cases c <;> rfl
          simpa [prOut] using ih (l := prH c l) htail hh

/-- Full paired-prefix reset theorem in recursive transducer form.
    data is the forward list c0,...,cq (false=A, true=T). -/
theorem paired_reset (data : List Bool) (l : Tape)
    (hne : data ≠ []) (hl : l 0 = true) :
    run (prScanCost data + prDecCost data.reverse)
      (other B (prSource data l) (pre [false,false,true] blank)) =
    some
      (other B (prOut data.reverse l) (pre [false,false,true] blank)) := by
  have hr : data.reverse ≠ [] := by
    simpa using hne
  rw [show (pre [false,false,true] blank : Tape) =
      prRight (prAcc []) by rfl]
  rw [run_add, pr_scan data [] l hne]
  simp only [Option.bind_some]
  simpa [prJ] using pr_decode data.reverse l hr hl

#print axioms pr_peel
#print axioms pr_decode
#print axioms paired_reset

end F197
