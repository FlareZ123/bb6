import PairedScanCore
import PairedTerminalCore

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace F197
open Q

def prJ (l : Tape) : Tape := pre [true,false,false] l

/-- Decoder-side E code for a nonempty reversed data list.
    false=A, true=T.  [] is an unused sentinel. -/
def prE : List Bool → Tape
  | [] => blank
  | [false] => pre [true] blank
  | [true] => pre [true,false,true] blank
  | false::d::ds =>
      pre [true,true,true,false,false,false] (prE (d::ds))
  | true::d::ds =>
      pre [true,false,true,true,true,false,false,false] (prE (d::ds))

/-- Decoder-side R code for a nonempty reversed data list. -/
def prR : List Bool → Tape
  | [] => blank
  | [false] => pre [true,true] blank
  | [true] => pre [true,true,false,true] blank
  | false::d::ds =>
      pre [true,true,true,true,false,false,false] (prE (d::ds))
  | true::d::ds =>
      pre [true,true,false,true,true,true,false,false,false] (prE (d::ds))

/-- Scanner accumulator.  For nonempty rs this is t · E(rs); for [] it is e. -/
def prAcc : List Bool → Tape
  | [] => pre [true] blank
  | c::cs =>
      pre [true,true,true,false,false,false] (prE (c::cs))

def prRight (r : Tape) : Tape := pre [false,false] r
def prXRight (r : Tape) : Tape := pre [false,false,true,false] r

/-- Source word c0 (T c1) ... (T cq) A A X, represented by the
    remaining forward data list. -/
def prSource : List Bool → Tape → Tape
  | [], l => l
  | [false], l => pre [true,false,true,false,true,false] l
  | [true], l =>
      pre [true,true,false,false,true,false,true,false] l
  | false::d::ds, l =>
      pre [true,false,true,true,false,false] (prSource (d::ds) l)
  | true::d::ds, l =>
      pre [true,true,false,false,true,true,false,false] (prSource (d::ds) l)

def prScanCost : List Bool → Nat
  | [] => 0
  | [false] => 47
  | [true] => 57
  | false::d::ds => 8 + prScanCost (d::ds)
  | true::d::ds => 18 + prScanCost (d::ds)

theorem prAcc_false (ps : List Bool) :
    prAcc (false::ps) =
      pre [true,true,true,false,false,false] (prAcc ps) := by
  cases ps with
  | nil => rfl
  | cons d ds =>
      cases d <;> rfl

theorem prAcc_true (ps : List Bool) :
    prAcc (true::ps) =
      pre [true,true,true,false,false,false,true,false] (prAcc ps) := by
  cases ps with
  | nil => rfl
  | cons d ds =>
      cases d <;> rfl

/-- Complete exact scanner.  ps is the already-scanned prefix in reverse
    order.  The result is J on the left and x·R(reverse(data)++ps) on the
    right. -/
theorem pr_scan (data ps : List Bool) (l : Tape) (hne : data ≠ []) :
    run (prScanCost data)
      (other B (prSource data l) (prRight (prAcc ps))) =
    some
      (other B (prJ l)
        (prXRight (prR (data.reverse ++ ps)))) := by
  induction data generalizing ps with
  | nil =>
      exact (hne rfl).elim
  | cons c tail ih =>
      cases tail with
      | nil =>
          cases c with
          | false =>
              cases ps with
              | nil =>
                  simpa [prScanCost, prSource, prRight, prAcc, prJ,
                    prXRight, prR] using terminal_A_e l
              | cons d ds =>
                  simpa [prScanCost, prSource, prRight, prAcc, prJ,
                    prXRight, prR] using terminal_A_t l (prE (d::ds))
          | true =>
              cases ps with
              | nil =>
                  simpa [prScanCost, prSource, prRight, prAcc, prJ,
                    prXRight, prR] using terminal_T_e l
              | cons d ds =>
                  simpa [prScanCost, prSource, prRight, prAcc, prJ,
                    prXRight, prR] using terminal_T_t l (prE (d::ds))
      | cons d ds =>
          have htail : d::ds ≠ [] := by simp
          cases c with
          | false =>
              change run (8 + prScanCost (d::ds))
                (other B
                  (pre [true,false,true,true,false,false]
                    (prSource (d::ds) l))
                  (prRight (prAcc ps))) =
                some
                  (other B (prJ l)
                    (prXRight
                      (prR ((false::d::ds).reverse ++ ps))))
              rw [run_add]
              rw [show run 8
                    (other B
                      (pre [true,false,true,true,false,false]
                        (prSource (d::ds) l))
                      (prRight (prAcc ps))) =
                    some
                      (other B (prSource (d::ds) l)
                        (prRight (prAcc (false::ps)))) by
                    simpa [prRight, prAcc_false] using
                      scan_AT (prSource (d::ds) l) (prAcc ps)]
              simp only [Option.bind_some]
              simpa [List.reverse_cons, List.append_assoc] using
                ih (ps := false::ps) htail
          | true =>
              change run (18 + prScanCost (d::ds))
                (other B
                  (pre [true,true,false,false,true,true,false,false]
                    (prSource (d::ds) l))
                  (prRight (prAcc ps))) =
                some
                  (other B (prJ l)
                    (prXRight
                      (prR ((true::d::ds).reverse ++ ps))))
              rw [run_add]
              rw [show run 18
                    (other B
                      (pre [true,true,false,false,true,true,false,false]
                        (prSource (d::ds) l))
                      (prRight (prAcc ps))) =
                    some
                      (other B (prSource (d::ds) l)
                        (prRight (prAcc (true::ps)))) by
                    simpa [prRight, prAcc_true] using
                      scan_TT (prSource (d::ds) l) (prAcc ps)]
              simp only [Option.bind_some]
              simpa [List.reverse_cons, List.append_assoc] using
                ih (ps := true::ps) htail

#print axioms pr_scan

end F197
