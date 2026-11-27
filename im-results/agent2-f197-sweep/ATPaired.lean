import ATPairedCore
import ATAlignedCore

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace F197
open Q

/-
Exact arbitrary-length complementary AT reset transducer.
Run notation: A=10, T=1100, P=AAT, J=100, C=110,
u=1111000, t=111000, s=11111000, e=1.
A Boolean list d=[c0,...,cq] encodes
  Z(d) = c0 (T c1) ... (T cq)
and the source is TAT Z(d) AA X.
The output is AAAT A H(c0)...H(cq) X,
H(A)=AT and H(T)=AAT.
Every source and intermediate data continuation is run-aligned (bit 0 = true).
-/

def atpJ (l : Tape) : Tape := pre [true,false,false] l

def atpE : List Bool → Tape
  | [] => blank
  | [false] =>
      pre [true,true,true,true,false,false,false,
           true,true,false,true] blank
  | [true] =>
      pre [true,false,true,true,true,true,false,false,false,
           true,true,false,true] blank
  | false::d::ds =>
      pre [true,true,true,false,false,false] (atpE (d::ds))
  | true::d::ds =>
      pre [true,false,true,true,true,false,false,false] (atpE (d::ds))

/-- Decoder R code, with the u C e carry attached to the terminal. -/
def atpR : List Bool → Tape
  | [] => blank
  | [false] =>
      pre [true,true,true,true,true,false,false,false,
           true,true,false,true] blank
  | [true] =>
      pre [true,true,false,true,true,true,true,false,false,false,
           true,true,false,true] blank
  | false::d::ds =>
      pre [true,true,true,true,false,false,false] (atpE (d::ds))
  | true::d::ds =>
      pre [true,true,false,true,true,true,false,false,false] (atpE (d::ds))

/-- Scanner accumulator: terminal carry if empty; otherwise t E(code). -/
def atpAcc : List Bool → Tape
  | [] => pre [true,true,true,true,false,false,false,true,true,false,true] blank
  | c::cs =>
      pre [true,true,true,false,false,false] (atpE (c::cs))

def atpRight (r : Tape) : Tape := pre [false,false] r
def atpXRight (r : Tape) : Tape := pre [false,false,true,false] r

/-- Z(d) A A X.  The terminal A A is part of the last code letter. -/
def atpSource : List Bool → Tape → Tape
  | [], l => l
  | [false], l => pre [true,false,true,false,true,false] l
  | [true], l => pre [true,true,false,false,true,false,true,false] l
  | false::d::ds, l =>
      pre [true,false,true,true,false,false] (atpSource (d::ds) l)
  | true::d::ds, l =>
      pre [true,true,false,false,true,true,false,false] (atpSource (d::ds) l)

def atpScanCost : List Bool → Nat
  | [] => 0
  | [false] => 47
  | [true] => 57
  | false::d::ds => 8 + atpScanCost (d::ds)
  | true::d::ds => 18 + atpScanCost (d::ds)

theorem atpAcc_false (ps : List Bool) :
    atpAcc (false::ps) =
      pre [true,true,true,false,false,false] (atpAcc ps) := by
  cases ps with
  | nil => rfl
  | cons d ds => cases d <;> rfl

theorem atpAcc_true (ps : List Bool) :
    atpAcc (true::ps) =
      pre [true,true,true,false,false,false,true,false] (atpAcc ps) := by
  cases ps with
  | nil => rfl
  | cons d ds => cases d <;> rfl

theorem atpSource_first (data : List Bool) (l : Tape) (hne : data ≠ []) :
    (atpSource data l) 0 = true := by
  cases data with
  | nil => exact (hne rfl).elim
  | cons c cs =>
      cases cs with
      | nil => cases c <;> rfl
      | cons d ds => cases c <;> rfl

theorem atpAcc_first (ps : List Bool) :
    (atpAcc ps) 0 = true := by
  cases ps with
  | nil => rfl
  | cons c cs => rfl

theorem atpE_first (ps : List Bool) (hne : ps ≠ []) :
    (atpE ps) 0 = true := by
  cases ps with
  | nil => exact (hne rfl).elim
  | cons c cs =>
      cases cs with
      | nil => cases c <;> rfl
      | cons d ds => cases c <;> rfl

/-- Scanner over arbitrarily many paired packets with the original uCe
    right carry.  ps is the already consumed prefix in reverse order. -/
theorem atp_scan (data ps : List Bool) (l : Tape) (hne : data ≠ [])
    (hl : l 0 = true) :
    run (atpScanCost data)
      (other B (atpSource data l) (atpRight (atpAcc ps))) =
    some
      (other B (atpJ l)
        (atpXRight (atpR (data.reverse ++ ps)))) := by
  induction data generalizing ps with
  | nil => exact (hne rfl).elim
  | cons c tail ih =>
      cases tail with
      | nil =>
          cases c with
          | false =>
              cases ps with
              | nil =>
                  simpa [atpScanCost,atpSource,atpRight,atpAcc,
                    atpJ,atpXRight,atpR] using at_term_A l hl
              | cons d ds =>
                  have hr : (atpE (d::ds)) 0 = true :=
                    atpE_first (d::ds) (by simp)
                  simpa [atpScanCost,atpSource,atpRight,atpAcc,
                    atpJ,atpXRight,atpR] using
                    term_A_t_aligned l (atpE (d::ds)) hl hr
          | true =>
              cases ps with
              | nil =>
                  simpa [atpScanCost,atpSource,atpRight,atpAcc,
                    atpJ,atpXRight,atpR] using at_term_T l hl
              | cons d ds =>
                  have hr : (atpE (d::ds)) 0 = true :=
                    atpE_first (d::ds) (by simp)
                  simpa [atpScanCost,atpSource,atpRight,atpAcc,
                    atpJ,atpXRight,atpR] using
                    term_T_t_aligned l (atpE (d::ds)) hl hr
      | cons d ds =>
          have htail : d::ds ≠ [] := by simp
          have hs : (atpSource (d::ds) l) 0 = true :=
            atpSource_first (d::ds) l htail
          have ha : (atpAcc ps) 0 = true := atpAcc_first ps
          cases c with
          | false =>
              change run (8 + atpScanCost (d::ds))
                (other B
                  (pre [true,false,true,true,false,false]
                    (atpSource (d::ds) l))
                  (atpRight (atpAcc ps))) =
                some
                  (other B (atpJ l)
                    (atpXRight (atpR ((false::d::ds).reverse ++ ps))))
              rw [run_add]
              rw [show run 8
                    (other B
                      (pre [true,false,true,true,false,false]
                        (atpSource (d::ds) l))
                      (atpRight (atpAcc ps))) =
                    some (other B (atpSource (d::ds) l)
                      (atpRight (atpAcc (false::ps)))) by
                    simpa [atpRight,atpAcc_false] using
                      scan_AT_aligned (atpSource (d::ds) l) (atpAcc ps) hs ha]
              simp only [Option.bind_some]
              simpa [List.reverse_cons,List.append_assoc] using
                ih (ps := false::ps) htail
          | true =>
              change run (18 + atpScanCost (d::ds))
                (other B
                  (pre [true,true,false,false,true,true,false,false]
                    (atpSource (d::ds) l))
                  (atpRight (atpAcc ps))) =
                some
                  (other B (atpJ l)
                    (atpXRight (atpR ((true::d::ds).reverse ++ ps))))
              rw [run_add]
              rw [show run 18
                    (other B
                      (pre [true,true,false,false,true,true,false,false]
                        (atpSource (d::ds) l))
                      (atpRight (atpAcc ps))) =
                    some (other B (atpSource (d::ds) l)
                      (atpRight (atpAcc (true::ps)))) by
                    simpa [atpRight,atpAcc_true] using
                      scan_TT_aligned (atpSource (d::ds) l) (atpAcc ps) hs ha]
              simp only [Option.bind_some]
              simpa [List.reverse_cons,List.append_assoc] using
                ih (ps := true::ps) htail

/-- Output builder: AAAT then the original A H(data) transform.
    data arrives in reverse order and the later letters are deposited on l. -/
def atpH : Bool → Tape → Tape
  | false, l => pre [true,false,true,true,false,false] l
  | true, l => pre [true,false,true,false,true,true,false,false] l

def atpOut : List Bool → Tape → Tape
  | [], l => l
  | [false], l =>
      pre [true,false,true,false,true,false,true,true,false,false,
           true,false,true,false,true,true,false,false] l
  | [true], l =>
      pre [true,false,true,false,true,false,true,true,false,false,
           true,false,true,false,true,false,true,true,false,false] l
  | false::d::ds, l => atpOut (d::ds) (atpH false l)
  | true::d::ds, l => atpOut (d::ds) (atpH true l)

def atpPeelCost : Bool → Nat
  | false => 60
  | true => 64

def atpDecCost : List Bool → Nat
  | [] => 0
  | [false] => 63
  | [true] => 67
  | false::d::ds => 60 + atpDecCost (d::ds)
  | true::d::ds => 64 + atpDecCost (d::ds)

/-- Correct full decoder peel; its terminal carry differs from the paired-AA
    decoder, so four new terminal peels are used, rather than a false
    blanket rewrite of generic arbitrary Tape tails. -/
theorem atp_peel (c d : Bool) (ds : List Bool) (l : Tape)
    (hl : l 0 = true) :
    run (atpPeelCost c)
      (other B (atpJ l) (atpXRight (atpR (c::d::ds)))) =
    some
      (other B (atpJ (atpH c l)) (atpXRight (atpR (d::ds)))) := by
  cases c with
  | false =>
      cases ds with
      | nil =>
          cases d with
          | false =>
              simpa [atpPeelCost,atpJ,atpH,atpXRight,atpR,atpE] using
                at_peel_AA l hl
          | true =>
              simpa [atpPeelCost,atpJ,atpH,atpXRight,atpR,atpE] using
                at_peel_AT l hl
      | cons e es =>
          have he : (atpE (e::es)) 0 = true :=
            atpE_first (e::es) (by simp)
          cases d with
          | false =>
              simpa [atpPeelCost,atpJ,atpH,atpXRight,atpR,atpE] using
                peel_A_t_aligned l (atpE (e::es)) hl he
          | true =>
              simpa [atpPeelCost,atpJ,atpH,atpXRight,atpR,atpE] using
                peel_A_At_aligned l (atpE (e::es)) hl he
  | true =>
      cases ds with
      | nil =>
          cases d with
          | false =>
              simpa [atpPeelCost,atpJ,atpH,atpXRight,atpR,atpE] using
                at_peel_TA l hl
          | true =>
              simpa [atpPeelCost,atpJ,atpH,atpXRight,atpR,atpE] using
                at_peel_TT l hl
      | cons e es =>
          have he : (atpE (e::es)) 0 = true :=
            atpE_first (e::es) (by simp)
          cases d with
          | false =>
              simpa [atpPeelCost,atpJ,atpH,atpXRight,atpR,atpE] using
                peel_T_t_aligned l (atpE (e::es)) hl he
          | true =>
              simpa [atpPeelCost,atpJ,atpH,atpXRight,atpR,atpE] using
                peel_T_At_aligned l (atpE (e::es)) hl he

/-- Decoder terminates at the carried boundary for any nonempty data. -/
theorem atp_decode (data : List Bool) (l : Tape)
    (hne : data ≠ []) (hl : l 0 = true) :
    run (atpDecCost data)
      (other B (atpJ l) (atpXRight (atpR data))) =
    some
      (other B (atpOut data l) (pre [false,false,true] blank)) := by
  induction data generalizing l with
  | nil => exact (hne rfl).elim
  | cons c tail ih =>
      cases tail with
      | nil =>
          cases c with
          | false =>
              simpa [atpDecCost,atpJ,atpXRight,atpR,atpOut] using
                at_base_A l hl
          | true =>
              simpa [atpDecCost,atpJ,atpXRight,atpR,atpOut] using
                at_base_T l hl
      | cons d ds =>
          have htail : d::ds ≠ [] := by simp
          change run (atpPeelCost c + atpDecCost (d::ds))
            (other B (atpJ l) (atpXRight (atpR (c::d::ds)))) =
            some
              (other B (atpOut (c::d::ds) l)
                (pre [false,false,true] blank))
          rw [run_add, atp_peel c d ds l hl]
          simp only [Option.bind_some]
          have hh : (atpH c l) 0 = true := by
            cases c <;> rfl
          simpa [atpOut] using ih (l := atpH c l) htail hh

/-- Unbounded F197 complementary AT family. For all nonempty Boolean data,
    source TAT Z(data) AA X reaches AAAT Phi(data) X with exactly
    46 + scanner + decoder primitive steps, no intermediate halt. -/
theorem atp_family (data : List Bool) (l : Tape)
    (hne : data ≠ []) (hl : l 0 = true) :
    run (46 + (atpScanCost data + atpDecCost data.reverse))
      (other B
        (pre [true,true,false,false,true,false,true,true,false,false]
          (atpSource data l))
        (pre [false,false,true] blank)) =
    some
      (other B (atpOut data.reverse l) (pre [false,false,true] blank)) := by
  have hr : data.reverse ≠ [] := by simpa using hne
  rw [run_add]
  rw [show run 46
        (other B
          (pre [true,true,false,false,true,false,true,true,false,false]
            (atpSource data l))
          (pre [false,false,true] blank)) =
        some
          (other B (atpSource data l)
            (atpRight (atpAcc []))) by
        simpa [atpRight,atpAcc] using
          at_preconsume (atpSource data l) (atpSource_first data l hne)]
  simp only [Option.bind_some]
  rw [show (atpRight (atpAcc [])) =
      (pre [false,false,true,true,true,true,false,false,false,
            true,true,false,true] blank : Tape) by rfl]
  rw [run_add]
  rw [show run (atpScanCost data)
        (other B (atpSource data l)
          (atpRight (atpAcc []))) =
        some (other B (atpJ l) (atpXRight (atpR data.reverse))) by
        simpa using atp_scan data [] l hne hl]
  simp only [Option.bind_some]
  exact atp_decode data.reverse l hr hl

#print axioms atp_scan
#print axioms atp_peel
#print axioms atp_decode
#print axioms atp_family

end F197
