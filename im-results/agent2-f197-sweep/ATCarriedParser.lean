import ATPaired
import ATCarryCore

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace F197
open Q

/-
Parametric scanner/decoder with an arbitrary run-aligned continuation R
in the right carry. The n=0 result ATPaired is the R=e specialization.
Symbol bits A=10,T=1100,J=100,C=110,t=111000,u=1111000,s=11111000.
-/

def atpEWith : List Bool → Tape → Tape
  | [], r => r
  | [false], r =>
      pre [true,true,true,true,false,false,false,true,true,false] r
  | [true], r =>
      pre [true,false,true,true,true,true,false,false,false,true,true,false] r
  | false::d::ds, r =>
      pre [true,true,true,false,false,false] (atpEWith (d::ds) r)
  | true::d::ds, r =>
      pre [true,false,true,true,true,false,false,false] (atpEWith (d::ds) r)

def atpRWith : List Bool → Tape → Tape
  | [], r => r
  | [false], r =>
      pre [true,true,true,true,true,false,false,false,true,true,false] r
  | [true], r =>
      pre [true,true,false,true,true,true,true,false,false,false,true,true,false] r
  | false::d::ds, r =>
      pre [true,true,true,true,false,false,false] (atpEWith (d::ds) r)
  | true::d::ds, r =>
      pre [true,true,false,true,true,true,false,false,false] (atpEWith (d::ds) r)

def atpAccWith : List Bool → Tape → Tape
  | [], r => pre [true,true,true,true,false,false,false,true,true,false] r
  | c::cs, r =>
      pre [true,true,true,false,false,false] (atpEWith (c::cs) r)

theorem atpAccWith_false (ps : List Bool) (r : Tape) :
    atpAccWith (false::ps) r =
      pre [true,true,true,false,false,false] (atpAccWith ps r) := by
  cases ps with
  | nil => rfl
  | cons d ds => cases d <;> rfl

theorem atpAccWith_true (ps : List Bool) (r : Tape) :
    atpAccWith (true::ps) r =
      pre [true,true,true,false,false,false,true,false] (atpAccWith ps r) := by
  cases ps with
  | nil => rfl
  | cons d ds => cases d <;> rfl

theorem atpAccWith_first (ps : List Bool) (r : Tape) :
    (atpAccWith ps r) 0 = true := by
  cases ps with
  | nil => rfl
  | cons d ds => rfl

theorem atpEWith_first (ps : List Bool) (r : Tape) (hne : ps ≠ []) :
    (atpEWith ps r) 0 = true := by
  cases ps with
  | nil => exact (hne rfl).elim
  | cons c cs =>
      cases cs with
      | nil => cases c <;> rfl
      | cons d ds => cases c <;> rfl

/-- Arbitrary-length scanner that preserves the unconsumed right carry r. -/
theorem atp_scan_with (data ps : List Bool) (l r : Tape)
    (hne : data ≠ []) (hl : l 0 = true) (hr : r 0 = true) :
    run (atpScanCost data)
      (other B (atpSource data l) (atpRight (atpAccWith ps r))) =
    some (other B (atpJ l)
      (atpXRight (atpRWith (data.reverse ++ ps) r))) := by
  induction data generalizing ps with
  | nil => exact (hne rfl).elim
  | cons c tail ih =>
      cases tail with
      | nil =>
          cases c with
          | false =>
              cases ps with
              | nil =>
                  simpa [atpScanCost,atpSource,atpRight,atpAccWith,
                    atpJ,atpXRight,atpRWith,pre] using
                    atc_term_A l r hl hr
              | cons d ds =>
                  have hE : (atpEWith (d::ds) r) 0 = true :=
                    atpEWith_first (d::ds) r (by simp)
                  simpa [atpScanCost,atpSource,atpRight,atpAccWith,
                    atpJ,atpXRight,atpRWith,pre] using
                    term_A_t_aligned l (atpEWith (d::ds) r) hl hE
          | true =>
              cases ps with
              | nil =>
                  simpa [atpScanCost,atpSource,atpRight,atpAccWith,
                    atpJ,atpXRight,atpRWith,pre] using
                    atc_term_T l r hl hr
              | cons d ds =>
                  have hE : (atpEWith (d::ds) r) 0 = true :=
                    atpEWith_first (d::ds) r (by simp)
                  simpa [atpScanCost,atpSource,atpRight,atpAccWith,
                    atpJ,atpXRight,atpRWith,pre] using
                    term_T_t_aligned l (atpEWith (d::ds) r) hl hE
      | cons d ds =>
          have htail : d::ds ≠ [] := by simp
          have hs : (atpSource (d::ds) l) 0 = true :=
            atpSource_first (d::ds) l htail
          have ha : (atpAccWith ps r) 0 = true := atpAccWith_first ps r
          cases c with
          | false =>
              change run (8 + atpScanCost (d::ds))
                (other B
                  (pre [true,false,true,true,false,false]
                    (atpSource (d::ds) l))
                  (atpRight (atpAccWith ps r))) =
                some (other B (atpJ l)
                  (atpXRight (atpRWith ((false::d::ds).reverse ++ ps) r)))
              rw [run_add]
              rw [show run 8
                    (other B
                      (pre [true,false,true,true,false,false]
                        (atpSource (d::ds) l))
                      (atpRight (atpAccWith ps r))) =
                    some (other B (atpSource (d::ds) l)
                      (atpRight (atpAccWith (false::ps) r))) by
                    simpa [atpRight,atpAccWith_false,pre] using
                      scan_AT_aligned
                        (atpSource (d::ds) l) (atpAccWith ps r) hs ha]
              simp only [Option.bind_some]
              simpa [List.reverse_cons,List.append_assoc] using
                ih (ps := false::ps) htail
          | true =>
              change run (18 + atpScanCost (d::ds))
                (other B
                  (pre [true,true,false,false,true,true,false,false]
                    (atpSource (d::ds) l))
                  (atpRight (atpAccWith ps r))) =
                some (other B (atpJ l)
                  (atpXRight (atpRWith ((true::d::ds).reverse ++ ps) r)))
              rw [run_add]
              rw [show run 18
                    (other B
                      (pre [true,true,false,false,true,true,false,false]
                        (atpSource (d::ds) l))
                      (atpRight (atpAccWith ps r))) =
                    some (other B (atpSource (d::ds) l)
                      (atpRight (atpAccWith (true::ps) r))) by
                    simpa [atpRight,atpAccWith_true,pre] using
                      scan_TT_aligned
                        (atpSource (d::ds) l) (atpAccWith ps r) hs ha]
              simp only [Option.bind_some]
              simpa [List.reverse_cons,List.append_assoc] using
                ih (ps := true::ps) htail

/-- Prefix Phi = A H(data) (data supplied in reverse order). -/
def atpPhi : List Bool → Tape → Tape
  | [], l => l
  | [false], l =>
      pre [true,false,true,false,true,true,false,false] l
  | [true], l =>
      pre [true,false,true,false,true,false,true,true,false,false] l
  | false::d::ds, l => atpPhi (d::ds) (atpH false l)
  | true::d::ds, l => atpPhi (d::ds) (atpH true l)

theorem atpPhi_first (data : List Bool) (l : Tape) (hne : data ≠ []) :
    (atpPhi data l) 0 = true := by
  induction data generalizing l with
  | nil => exact (hne rfl).elim
  | cons c cs ih =>
      cases cs with
      | nil => cases c <;> rfl
      | cons d ds =>
          cases c <;>
            simp only [atpPhi] <;>
            exact ih (l := atpH _ l) (by simp)

def atpCarryCost : List Bool → Nat
  | [] => 0
  | [false] => 32
  | [true] => 36
  | false::d::ds => 60 + atpCarryCost (d::ds)
  | true::d::ds => 64 + atpCarryCost (d::ds)

/-- The carried decoder peels, including the four guarded finite terminal
    carry cases; the final right-hand suffix r is never touched. -/
theorem atp_carry_peel (c d : Bool) (ds : List Bool) (l r : Tape)
    (hl : l 0 = true) (hr : r 0 = true) :
    run (atpPeelCost c)
      (other B (atpJ l) (atpXRight (atpRWith (c::d::ds) r))) =
    some
      (other B (atpJ (atpH c l))
        (atpXRight (atpRWith (d::ds) r))) := by
  cases c with
  | false =>
      cases ds with
      | nil =>
          cases d with
          | false =>
              simpa [atpPeelCost,atpJ,atpH,atpXRight,
                atpRWith,atpEWith,pre] using atc_peel_AA l r hl hr
          | true =>
              simpa [atpPeelCost,atpJ,atpH,atpXRight,
                atpRWith,atpEWith,pre] using atc_peel_AT l r hl hr
      | cons e es =>
          have hE : (atpEWith (e::es) r) 0 = true :=
            atpEWith_first (e::es) r (by simp)
          cases d with
          | false =>
              simpa [atpPeelCost,atpJ,atpH,atpXRight,
                atpRWith,atpEWith,pre] using
                peel_A_t_aligned l (atpEWith (e::es) r) hl hE
          | true =>
              simpa [atpPeelCost,atpJ,atpH,atpXRight,
                atpRWith,atpEWith,pre] using
                peel_A_At_aligned l (atpEWith (e::es) r) hl hE
  | true =>
      cases ds with
      | nil =>
          cases d with
          | false =>
              simpa [atpPeelCost,atpJ,atpH,atpXRight,
                atpRWith,atpEWith,pre] using atc_peel_TA l r hl hr
          | true =>
              simpa [atpPeelCost,atpJ,atpH,atpXRight,
                atpRWith,atpEWith,pre] using atc_peel_TT l r hl hr
      | cons e es =>
          have hE : (atpEWith (e::es) r) 0 = true :=
            atpEWith_first (e::es) r (by simp)
          cases d with
          | false =>
              simpa [atpPeelCost,atpJ,atpH,atpXRight,
                atpRWith,atpEWith,pre] using
                peel_T_t_aligned l (atpEWith (e::es) r) hl hE
          | true =>
              simpa [atpPeelCost,atpJ,atpH,atpXRight,
                atpRWith,atpEWith,pre] using
                peel_T_At_aligned l (atpEWith (e::es) r) hl hE

/-- Exact data decoder from the deposited scanner carry to a common
    J/Phi left stack with right x C r.  Unlike the n=0 decoder,
    this lemma does not consume the remaining right carry. -/
theorem atp_decode_with (data : List Bool) (l r : Tape)
    (hne : data ≠ []) (hl : l 0 = true) (hr : r 0 = true) :
    run (atpCarryCost data)
      (other B (atpJ l) (atpXRight (atpRWith data r))) =
    some
      (other B (atpJ (atpPhi data l))
        (atpXRight (pre [true,true,false] r))) := by
  induction data generalizing l with
  | nil => exact (hne rfl).elim
  | cons c cs ih =>
      cases cs with
      | nil =>
          cases c with
          | false =>
              simpa [atpCarryCost,atpJ,atpXRight,
                atpPhi,atpRWith,pre] using atc_junction_A l r hl hr
          | true =>
              simpa [atpCarryCost,atpJ,atpXRight,
                atpPhi,atpRWith,pre] using atc_junction_T l r hl hr
      | cons d ds =>
          have htail : d::ds ≠ [] := by simp
          have hcost :
              atpCarryCost (c::d::ds) =
                atpPeelCost c + atpCarryCost (d::ds) := by
            cases c <;> rfl
          rw [hcost,run_add,atp_carry_peel c d ds l r hl hr]
          simp only [Option.bind_some]
          cases c with
          | false =>
              simpa [atpPhi] using
                ih (l := atpH false l) htail (by rfl)
          | true =>
              simpa [atpPhi] using
                ih (l := atpH true l) htail (by rfl)

/-- Universal parametric front end: any aligned right carry r propagates
    through TAT + the unbounded paired scanner and decoder. -/
theorem atp_staged_with (data : List Bool) (l r : Tape)
    (hne : data ≠ []) (hl : l 0 = true) (hr : r 0 = true) :
    run (46 + (atpScanCost data + atpCarryCost data.reverse))
      (other B
        (pre [true,true,false,false,true,false,true,true,false,false]
          (atpSource data l))
        (atpRight r)) =
    some
      (other B (atpJ (atpPhi data.reverse l))
        (atpXRight (pre [true,true,false] r))) := by
  have hd : data.reverse ≠ [] := by simpa using hne
  rw [run_add]
  rw [show run 46
        (other B
          (pre [true,true,false,false,true,false,true,true,false,false]
            (atpSource data l))
          (atpRight r)) =
        some
          (other B (atpSource data l)
            (atpRight (atpAccWith [] r))) by
        simpa [atpRight,atpAccWith,pre] using
          atc_preconsume (atpSource data l) r
            (atpSource_first data l hne) hr]
  simp only [Option.bind_some]
  rw [run_add]
  rw [show run (atpScanCost data)
        (other B (atpSource data l)
          (atpRight (atpAccWith [] r))) =
        some
          (other B (atpJ l)
            (atpXRight (atpRWith data.reverse r))) by
        simpa [pre] using atp_scan_with data [] l r hne hl hr]
  simp only [Option.bind_some]
  exact atp_decode_with data.reverse l r hd hl hr

#print axioms atp_scan_with
#print axioms atp_carry_peel
#print axioms atp_decode_with
#print axioms atp_staged_with

end F197
