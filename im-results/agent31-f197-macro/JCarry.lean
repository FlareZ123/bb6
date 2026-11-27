import Macro
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace F197.JCarry
def a : Tape → Tape := pre [true,false]
def j : Tape → Tape := pre [true,false,false]
def t : Tape → Tape := pre [true,true,false,false]
def p (l : Tape) := a (a (t l))
def h (c : Bool) (l : Tape) := if c then p l else a (t l)
def x : Tape → Tape := a
def tau : Tape → Tape := pre [true,true,true,false,false,false]
def u : Tape → Tape := pre [true,true,true,true,false,false,false]
def c : Tape → Tape := pre [true,true,false]
def e : Tape := pre [true] blank
def two : Tape := pre [true,true] blank
def b (l r : Tape) : Config := other Q.B l (pre [false,false] r)

theorem enter (l : Tape) (hl : l 0 = true) :
    run 71 (b (t (t (j l))) e) = some (b (t l) (tau two)) := by
  rw [← decompose_bit l true hl]
  rfl

theorem scanA (l r : Tape) :
    run 8 (b (a (t l)) r) = some (b l (tau r)) := by
  rw [← decompose l, ← decompose r]
  rfl

theorem scanT (l r : Tape) :
    run 18 (b (t (t l)) r) = some (b l (tau (a r))) := by
  rw [← decompose l, ← decompose r]
  rfl

theorem termA (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 47 (b (a (a (a l))) (tau r)) = some (b (j l) (x (u r))) := by
  rw [← decompose_bit l true hl, ← decompose_bit r true hr]
  rfl

theorem termT (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 57 (b (t (a (a l))) (tau r)) = some (b (j l) (x (c (tau r)))) := by
  rw [← decompose_bit l true hl, ← decompose_bit r true hr]
  rfl

theorem peelAA (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 60 (b (j l) (x (u (tau r)))) = some (b (j (h false l)) (x (u r))) := by
  rw [← decompose_bit l true hl, ← decompose_bit r true hr]
  rfl

theorem peelAT (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 60 (b (j l) (x (u (a (tau r))))) = some (b (j (h false l)) (x (c (tau r)))) := by
  rw [← decompose_bit l true hl, ← decompose_bit r true hr]
  rfl

theorem peelTA (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 64 (b (j l) (x (c (tau (tau r))))) = some (b (j (h true l)) (x (u r))) := by
  rw [← decompose_bit l true hl, ← decompose_bit r true hr]
  rfl

theorem peelTT (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 64 (b (j l) (x (c (tau (a (tau r)))))) = some (b (j (h true l)) (x (c (tau r)))) := by
  rw [← decompose_bit l true hl, ← decompose_bit r true hr]
  rfl

theorem base (l : Tape) (hl : l 0 = true) :
    run 95 (b (j l) (x (c (tau two)))) = some (b (t (p (p l))) e) := by
  rw [← decompose_bit l true hl]
  rfl
def enc : List Bool → Tape
  | [] => two
  | false::ds => tau (enc ds)
  | true::ds => a (tau (enc ds))
def dec : List Bool → Tape
  | [] => two
  | false::ds => u (enc ds)
  | true::ds => c (tau (enc ds))
theorem enc_first (ds : List Bool) : enc ds 0 = true := by
  cases ds with
  | nil => rfl
  | cons d ds => cases d <;> rfl
def letter (c : Bool) (l : Tape) : Tape := if c then t l else a l
def packets : List Bool → Tape → Tape
  | [], l => a (a l)
  | d::ds, l => t (letter d (packets ds l))
def src (c : Bool) (ds : List Bool) (l : Tape) := letter c (packets ds l)
def bit (c : Bool) : Nat := if c then 1 else 0
def scanCost (c : Bool) : List Bool → Nat
  | [] => 47 + 10 * bit c
  | d::ds => 8 + 10 * bit c + scanCost d ds
theorem scan (c : Bool) (ds ps : List Bool) (l : Tape) (hl : l 0 = true) :
    run (scanCost c ds) (b (src c ds l) (tau (enc ps))) =
    some (b (j l) (x (dec ((c::ds).reverse ++ ps)))) := by
  induction ds generalizing c ps with
  | nil =>
      cases c with
      | false =>
          simpa [scanCost, bit, src, letter, packets, dec] using
            termA l (enc ps) hl (enc_first ps)
      | true =>
          simpa [scanCost, bit, src, letter, packets, dec] using
            termT l (enc ps) hl (enc_first ps)
  | cons d ds ih =>
      cases c with
      | false =>
          change run (8 + scanCost d ds)
            (b (a (t (src d ds l))) (tau (enc ps))) = _
          rw [run_add, scanA]
          simp only [Option.bind_some]
          simpa [enc, List.reverse_cons, List.append_assoc] using
            ih d (false::ps)
      | true =>
          change run (18 + scanCost d ds)
            (b (t (t (src d ds l))) (tau (enc ps))) = _
          rw [run_add, scanT]
          simp only [Option.bind_some]
          simpa [enc, List.reverse_cons, List.append_assoc] using
            ih d (true::ps)
def peelCost (c : Bool) : Nat := 60 + 4 * bit c
theorem peel (c d : Bool) (ds : List Bool) (l : Tape) (hl : l 0 = true) :
    run (peelCost c) (b (j l) (x (dec (c::d::ds)))) =
    some (b (j (h c l)) (x (dec (d::ds)))) := by
  cases c <;> cases d
  · exact peelAA l (enc ds) hl (enc_first ds)
  · exact peelAT l (enc ds) hl (enc_first ds)
  · exact peelTA l (enc ds) hl (enc_first ds)
  · exact peelTT l (enc ds) hl (enc_first ds)
def decCost : List Bool → Nat
  | [] => 95
  | c::cs => peelCost c + decCost cs
def restore : List Bool → Tape → Tape
  | [], l => t (p (p l))
  | c::cs, l => restore cs (h c l)
theorem h_first (c : Bool) (l : Tape) : h c l 0 = true := by
  cases c <;> rfl
theorem decode (cs : List Bool) (l : Tape) (hl : l 0 = true) :
    run (decCost cs) (b (j l) (x (dec (cs ++ [true])))) =
    some (b (restore cs l) e) := by
  induction cs generalizing l with
  | nil => exact base l hl
  | cons c cs ih =>
      change run (peelCost c + decCost cs)
        (b (j l) (x (dec (c :: (cs ++ [true]))))) = _
      rw [run_add]
      have hp : run (peelCost c)
          (b (j l) (x (dec (c :: (cs ++ [true]))))) =
          some (b (j (h c l)) (x (dec (cs ++ [true])))) := by
        cases cs with
        | nil => exact peel c true [] l hl
        | cons d ds => exact peel c d (ds ++ [true]) l hl
      rw [hp]
      simp only [Option.bind_some]
      exact ih (h c l) (h_first c l)
def trueCount : List Bool → Nat
  | [] => 0
  | c::cs => bit c + trueCount cs
theorem trueCount_append (xs ys : List Bool) :
    trueCount (xs ++ ys) = trueCount xs + trueCount ys := by
  induction xs with
  | nil => simp [trueCount]
  | cons c cs ih => simp [trueCount, ih, Nat.add_assoc]
theorem trueCount_reverse (xs : List Bool) : trueCount xs.reverse = trueCount xs := by
  induction xs with
  | nil => rfl
  | cons c cs ih =>
      simp [List.reverse_cons, trueCount_append, trueCount, ih, Nat.add_comm]
theorem scanCost_formula (c : Bool) (ds : List Bool) :
    scanCost c ds = 47 + 8 * ds.length + 10 * (bit c + trueCount ds) := by
  induction ds generalizing c with
  | nil => simp [scanCost, trueCount]
  | cons d ds ih => simp [scanCost, ih, trueCount, Nat.mul_add]; omega
theorem decCost_formula (cs : List Bool) :
    decCost cs = 95 + 60 * cs.length + 4 * trueCount cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [decCost, peelCost, trueCount, ih, Nat.mul_add]; omega
def output (cs : List Bool) (l : Tape) : Tape := cs.foldr h l
theorem restore_append (xs ys : List Bool) (l : Tape) :
    restore (xs ++ ys) l = restore ys (xs.foldl (fun l c => h c l) l) := by
  induction xs generalizing l with
  | nil => rfl
  | cons c cs ih => exact ih (h c l)
theorem fold_reverse (cs : List Bool) (l : Tape) :
    cs.reverse.foldl (fun l c => h c l) l = output cs l := by
  induction cs generalizing l with
  | nil => rfl
  | cons c cs ih =>
      simp [List.reverse_cons, List.foldl_append, ih, output]
theorem restore_reverse (cs : List Bool) (l : Tape) :
    restore cs.reverse l = t (p (p (output cs l))) := by
  have he := restore_append cs.reverse [] l
  simpa [fold_reverse, restore, output] using he
theorem family (cs : List Bool) (l : Tape) (hl : l 0 = true) :
    run (223 + 68 * cs.length + 14 * trueCount cs)
      (b (t (t (j (packets cs l)))) e) =
    some (b (t (p (p (output cs l)))) e) := by
  have hp : packets cs l 0 = true := by cases cs <;> rfl
  have hcost : 223 + 68 * cs.length + 14 * trueCount cs =
      71 + scanCost true cs + decCost cs.reverse := by
    rw [scanCost_formula, decCost_formula, List.length_reverse, trueCount_reverse]
    simp [bit]; omega
  rw [hcost, run_add, run_add, enter _ hp]
  simp only [Option.bind_some]
  have hs := scan true cs [] l hl
  have hs' : run (scanCost true cs) (b (t (packets cs l)) (tau two)) =
      some (b (j l) (x (dec (cs.reverse ++ [true])))) := by
    simpa [src, letter, enc, List.reverse_cons] using hs
  rw [hs']
  simp only [Option.bind_some]
  simpa [restore_reverse] using decode cs.reverse l hl
#print axioms enter
#print axioms base
#print axioms family
end F197.JCarry
