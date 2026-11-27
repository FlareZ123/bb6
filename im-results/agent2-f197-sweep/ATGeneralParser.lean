import ATCarriedParser

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace F197
open Q

/-
Generalized scanner/decoder for arbitrary run-aligned right continuation R
with a C-free u head carry. This extends the earlier u C R transducer.
Symbol bits A=10,T=1100,J=100,C=110,t=111000,u=1111000,s=11111000.
-/

def atgEWith : List Bool → Tape → Tape
  | [], r => r
  | [false], r =>
      pre [true,true,true,true,false,false,false] r
  | [true], r =>
      pre [true,false,true,true,true,true,false,false,false] r
  | false::d::ds, r =>
      pre [true,true,true,false,false,false] (atgEWith (d::ds) r)
  | true::d::ds, r =>
      pre [true,false,true,true,true,false,false,false] (atgEWith (d::ds) r)

def atgRWith : List Bool → Tape → Tape
  | [], r => r
  | [false], r =>
      pre [true,true,true,true,true,false,false,false] r
  | [true], r =>
      pre [true,true,false,true,true,true,true,false,false,false] r
  | false::d::ds, r =>
      pre [true,true,true,true,false,false,false] (atgEWith (d::ds) r)
  | true::d::ds, r =>
      pre [true,true,false,true,true,true,false,false,false] (atgEWith (d::ds) r)

def atgAccWith : List Bool → Tape → Tape
  | [], r => pre [true,true,true,true,false,false,false] r
  | c::cs, r =>
      pre [true,true,true,false,false,false] (atgEWith (c::cs) r)

theorem atgAccWith_false (ps : List Bool) (r : Tape) :
    atgAccWith (false::ps) r =
      pre [true,true,true,false,false,false] (atgAccWith ps r) := by
  cases ps with
  | nil => rfl
  | cons d ds => cases d <;> rfl

theorem atgAccWith_true (ps : List Bool) (r : Tape) :
    atgAccWith (true::ps) r =
      pre [true,true,true,false,false,false,true,false] (atgAccWith ps r) := by
  cases ps with
  | nil => rfl
  | cons d ds => cases d <;> rfl

theorem atgAccWith_first (ps : List Bool) (r : Tape) :
    (atgAccWith ps r) 0 = true := by
  cases ps with
  | nil => rfl
  | cons d ds => rfl

theorem atgEWith_first (ps : List Bool) (r : Tape) (hne : ps ≠ []) :
    (atgEWith ps r) 0 = true := by
  cases ps with
  | nil => exact (hne rfl).elim
  | cons c cs =>
      cases cs with
      | nil => cases c <;> rfl
      | cons d ds => cases c <;> rfl

/-- Arbitrary-length scanner that preserves the unconsumed right carry r. -/
theorem atg_scan_with (data ps : List Bool) (l r : Tape)
    (hne : data ≠ []) (hl : l 0 = true) (hr : r 0 = true) :
    run (atpScanCost data)
      (other B (atpSource data l) (atpRight (atgAccWith ps r))) =
    some (other B (atpJ l)
      (atpXRight (atgRWith (data.reverse ++ ps) r))) := by
  induction data generalizing ps with
  | nil => exact (hne rfl).elim
  | cons c tail ih =>
      cases tail with
      | nil =>
          cases c with
          | false =>
              cases ps with
              | nil =>
                  simpa [atpScanCost,atpSource,atpRight,atgAccWith,
                    atpJ,atpXRight,atgRWith,pre] using
                    atc_terminal_A_u l r hl hr
              | cons d ds =>
                  have hE : (atgEWith (d::ds) r) 0 = true :=
                    atgEWith_first (d::ds) r (by simp)
                  simpa [atpScanCost,atpSource,atpRight,atgAccWith,
                    atpJ,atpXRight,atgRWith,pre] using
                    term_A_t_aligned l (atgEWith (d::ds) r) hl hE
          | true =>
              cases ps with
              | nil =>
                  simpa [atpScanCost,atpSource,atpRight,atgAccWith,
                    atpJ,atpXRight,atgRWith,pre] using
                    atc_terminal_T_u l r hl hr
              | cons d ds =>
                  have hE : (atgEWith (d::ds) r) 0 = true :=
                    atgEWith_first (d::ds) r (by simp)
                  simpa [atpScanCost,atpSource,atpRight,atgAccWith,
                    atpJ,atpXRight,atgRWith,pre] using
                    term_T_t_aligned l (atgEWith (d::ds) r) hl hE
      | cons d ds =>
          have htail : d::ds ≠ [] := by simp
          have hs : (atpSource (d::ds) l) 0 = true :=
            atpSource_first (d::ds) l htail
          have ha : (atgAccWith ps r) 0 = true := atgAccWith_first ps r
          cases c with
          | false =>
              change run (8 + atpScanCost (d::ds))
                (other B
                  (pre [true,false,true,true,false,false]
                    (atpSource (d::ds) l))
                  (atpRight (atgAccWith ps r))) =
                some (other B (atpJ l)
                  (atpXRight (atgRWith ((false::d::ds).reverse ++ ps) r)))
              rw [run_add]
              rw [show run 8
                    (other B
                      (pre [true,false,true,true,false,false]
                        (atpSource (d::ds) l))
                      (atpRight (atgAccWith ps r))) =
                    some (other B (atpSource (d::ds) l)
                      (atpRight (atgAccWith (false::ps) r))) by
                    simpa [atpRight,atgAccWith_false,pre] using
                      scan_AT_aligned
                        (atpSource (d::ds) l) (atgAccWith ps r) hs ha]
              simp only [Option.bind_some]
              simpa [List.reverse_cons,List.append_assoc] using
                ih (ps := false::ps) htail
          | true =>
              change run (18 + atpScanCost (d::ds))
                (other B
                  (pre [true,true,false,false,true,true,false,false]
                    (atpSource (d::ds) l))
                  (atpRight (atgAccWith ps r))) =
                some (other B (atpJ l)
                  (atpXRight (atgRWith ((true::d::ds).reverse ++ ps) r)))
              rw [run_add]
              rw [show run 18
                    (other B
                      (pre [true,true,false,false,true,true,false,false]
                        (atpSource (d::ds) l))
                      (atpRight (atgAccWith ps r))) =
                    some (other B (atpSource (d::ds) l)
                      (atpRight (atgAccWith (true::ps) r))) by
                    simpa [atpRight,atgAccWith_true,pre] using
                      scan_TT_aligned
                        (atpSource (d::ds) l) (atgAccWith ps r) hs ha]
              simp only [Option.bind_some]
              simpa [List.reverse_cons,List.append_assoc] using
                ih (ps := true::ps) htail

/-- The carried decoder peels, including the four guarded finite terminal
    carry cases; the final right-hand suffix r is never touched. -/
theorem atg_carry_peel (c d : Bool) (ds : List Bool) (l r : Tape)
    (hl : l 0 = true) (hr : r 0 = true) :
    run (atpPeelCost c)
      (other B (atpJ l) (atpXRight (atgRWith (c::d::ds) r))) =
    some
      (other B (atpJ (atpH c l))
        (atpXRight (atgRWith (d::ds) r))) := by
  cases c with
  | false =>
      cases ds with
      | nil =>
          cases d with
          | false =>
              simpa [atpPeelCost,atpJ,atpH,atpXRight,
                atgRWith,atgEWith,pre] using atc_peel_AA_general l r hl hr
          | true =>
              simpa [atpPeelCost,atpJ,atpH,atpXRight,
                atgRWith,atgEWith,pre] using atc_peel_AT_general l r hl hr
      | cons e es =>
          have hE : (atgEWith (e::es) r) 0 = true :=
            atgEWith_first (e::es) r (by simp)
          cases d with
          | false =>
              simpa [atpPeelCost,atpJ,atpH,atpXRight,
                atgRWith,atgEWith,pre] using
                peel_A_t_aligned l (atgEWith (e::es) r) hl hE
          | true =>
              simpa [atpPeelCost,atpJ,atpH,atpXRight,
                atgRWith,atgEWith,pre] using
                peel_A_At_aligned l (atgEWith (e::es) r) hl hE
  | true =>
      cases ds with
      | nil =>
          cases d with
          | false =>
              simpa [atpPeelCost,atpJ,atpH,atpXRight,
                atgRWith,atgEWith,pre] using atc_peel_TA_general l r hl hr
          | true =>
              simpa [atpPeelCost,atpJ,atpH,atpXRight,
                atgRWith,atgEWith,pre] using atc_peel_TT_general l r hl hr
      | cons e es =>
          have hE : (atgEWith (e::es) r) 0 = true :=
            atgEWith_first (e::es) r (by simp)
          cases d with
          | false =>
              simpa [atpPeelCost,atpJ,atpH,atpXRight,
                atgRWith,atgEWith,pre] using
                peel_T_t_aligned l (atgEWith (e::es) r) hl hE
          | true =>
              simpa [atpPeelCost,atpJ,atpH,atpXRight,
                atgRWith,atgEWith,pre] using
                peel_T_At_aligned l (atgEWith (e::es) r) hl hE

/-- Exact data decoder from the deposited scanner carry to a common
    J/Phi left stack with right x C r.  Unlike the n=0 decoder,
    this lemma does not consume the remaining right carry. -/
theorem atg_decode_with (data : List Bool) (l r : Tape)
    (hne : data ≠ []) (hl : l 0 = true) (hr : r 0 = true) :
    run (atpCarryCost data)
      (other B (atpJ l) (atpXRight (atgRWith data r))) =
    some
      (other B (atpJ (atpPhi data l))
        (atpXRight r)) := by
  induction data generalizing l with
  | nil => exact (hne rfl).elim
  | cons c cs ih =>
      cases cs with
      | nil =>
          cases c with
          | false =>
              simpa [atpCarryCost,atpJ,atpXRight,
                atpPhi,atgRWith,pre] using atc_junction_A_general l r hl hr
          | true =>
              simpa [atpCarryCost,atpJ,atpXRight,
                atpPhi,atgRWith,pre] using atc_junction_T_general l r hl hr
      | cons d ds =>
          have htail : d::ds ≠ [] := by simp
          have hcost :
              atpCarryCost (c::d::ds) =
                atpPeelCost c + atpCarryCost (d::ds) := by
            cases c <;> rfl
          rw [hcost,run_add,atg_carry_peel c d ds l r hl hr]
          simp only [Option.bind_some]
          cases c with
          | false =>
              simpa [atpPhi] using
                ih (l := atpH false l) htail (by rfl)
          | true =>
              simpa [atpPhi] using
                ih (l := atpH true l) htail (by rfl)

/-- Generalized C-free paired transducer: starting right at u·R with
    arbitrary run-aligned R, the scanner and decoder leave right A·R
    and prepend the same Phi to the left.  No terminal C assumption. -/
theorem atg_staged (data : List Bool) (l r : Tape)
    (hne : data ≠ []) (hl : l 0 = true) (hr : r 0 = true) :
    run (atpScanCost data + atpCarryCost data.reverse)
      (other B (atpSource data l)
        (atpRight (atgAccWith [] r))) =
    some (other B
      (atpJ (atpPhi data.reverse l))
      (atpXRight r)) := by
  have hd : data.reverse ≠ [] := by simpa using hne
  rw [run_add]
  rw [show run (atpScanCost data)
        (other B (atpSource data l)
          (atpRight (atgAccWith [] r))) =
        some (other B (atpJ l)
          (atpXRight (atgRWith data.reverse r))) by
        simpa using atg_scan_with data [] l r hne hl hr]
  simp only [Option.bind_some]
  exact atg_decode_with data.reverse l r hd hl hr

#print axioms atg_scan_with
#print axioms atg_carry_peel
#print axioms atg_decode_with
#print axioms atg_staged

end F197
