import ATCounterStep

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

namespace F197
open Q

/-- A literal-source, length-unbounded P-counter transport. All work
    needed for a single 36-step phase is in the separately checked
    atPConsume_step source lemma.  This proof only composes those phases. -/
theorem atPConsume (n : Nat) (l : Tape) (hl : l 0 = true) :
    run (36*n)
      (other B (atPreP n l) (atpRight (atQ 0))) =
    some (other B l (atpRight (atQ n))) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
      let L : Tape := pre [true,false,true,false,true,true,false,false] l
      have hshift : atPreP (n+1) l = atPreP n L := by
        simpa [L] using atPreP_shift n l
      have htime : 36*(n+1) = 36*n + 36 := by omega
      calc
        run (36*(n+1))
          (other B (atPreP (n+1) l) (atpRight (atQ 0))) =
            run (36*n + 36)
              (other B (atPreP n L) (atpRight (atQ 0))) := by
                rw [htime, hshift]
        _ = (run (36*n)
              (other B (atPreP n L) (atpRight (atQ 0)))).bind (run 36) :=
            run_add (36*n) 36 _
        _ = (some (other B L (atpRight (atQ n)))).bind (run 36) := by
            rw [ih (l := L) (by rfl)]
        _ = some (other B l (atpRight (atQ (n+1)))) := by
            simp only [Option.bind_some]
            exact atPConsume_step n l hl

#print axioms atPConsume

end F197
