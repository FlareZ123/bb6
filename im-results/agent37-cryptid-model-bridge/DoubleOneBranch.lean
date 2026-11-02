import Lean.Elab.Tactic.Omega
import WordReturns
import BoundaryExtra

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace BB6.CryptidBridge

/-- A previously uncovered A-boundary prefix 1100 is consumed in a
    fixed 17-step scan, leaving an arbitrarily long standard D sweep.
    This is a raw-machine theorem over every m and every suffix. -/
theorem two_one_front (m : Nat) (ys : List Bool) :
    CryptidBoundary.run 17
      (CryptidBoundary.preA (m+2) ([true,true,false,false] ++ ys)) =
    CryptidBoundary.sweepD m
      ([true,true,false] ++ List.replicate 6 true ++ ys) := by
  simp [CryptidBoundary.run, CryptidBoundary.preA, CryptidBoundary.sweepD,
    CryptidBoundary.step, CryptidBoundary.goL, CryptidBoundary.goR,
    CryptidBoundary.pairs, List.append_assoc]

/-- A return that introduces a fixed 0 1^6 suffix packet, for all m,ys.
    The initial A left exponent m+2 is >= 2 by construction. -/
theorem two_one_return (m : Nat) (ys : List Bool) :
    CryptidBoundary.run (2*(m+2)+16)
      (CryptidBoundary.preA (m+2) ([true,true,false,false] ++ ys)) =
    ⟨[], false,
      List.replicate (2*(m+2)+1) true ++
        (false :: List.replicate 6 true ++ ys),5⟩ := by
  have ht : 2*(m+2)+16 = 17+(2*m+3) := by omega
  rw [ht, CryptidBoundary.run_add, two_one_front, CryptidBoundary.sweepD_run]
  have hrep :
      List.replicate (2*m+3) true ++
        ([true,true,false] ++ List.replicate 6 true ++ ys) =
      List.replicate (2*(m+2)+1) true ++
        (false :: List.replicate 6 true ++ ys) := by
    have he : List.replicate (2*m+3) true ++ [true,true] =
        List.replicate (2*m+5) true := by
      calc
        List.replicate (2*m+3) true ++ [true,true] =
            List.replicate (2*m+3) true ++ List.replicate 2 true := by rfl
        _ = List.replicate ((2*m+3)+2) true := List.replicate_append_replicate
        _ = List.replicate (2*m+5) true := by rw [show (2*m+3)+2=2*m+5 by omega]
    calc
      List.replicate (2*m+3) true ++
          ([true,true,false] ++ List.replicate 6 true ++ ys) =
        (List.replicate (2*m+3) true ++ [true,true]) ++
          (false :: List.replicate 6 true ++ ys) := by simp [List.append_assoc]
      _ = List.replicate (2*m+5) true ++
          (false :: List.replicate 6 true ++ ys) := by rw [he]
      _ = List.replicate (2*(m+2)+1) true ++
          (false :: List.replicate 6 true ++ ys) := by
            rw [show 2*(m+2)+1=2*m+5 by omega]
  exact congrArg (fun z : List Bool => CryptidBoundary.Cfg.mk [] false z 5) hrep

/-- A source-level complete F-to-F return after any interleaved token
    sequence followed by 1100. This covers a new productive suffix branch
    not contained in the delimiter-zero token-code closure. -/
theorem complete_A_word_two_one (k : Nat) (ws : List Bool) (ys : List Bool) :
    CryptidBoundary.run
      ((12*k*k+41*k+32) +
        (CryptidA.wordCost (4*k+3) ws +
          (2*((4*k+3)+CryptidA.wordInc ws)+16)))
      (CryptidBoundary.init
        (List.replicate (3*k+1) true ++
         false :: (CryptidA.wordCode ws ++
           ([true,true,false,false] ++ ys)))) =
    ⟨[],false,
      List.replicate
        (2*((4*k+3)+CryptidA.wordInc ws)+1) true ++
        (false :: List.replicate 6 true ++ ys),5⟩ := by
  rw [CryptidBoundary.run_add, CryptidBoundary.prefix_A]
  change CryptidBoundary.run
    (CryptidA.wordCost (4*k+3) ws +
      (2*((4*k+3)+CryptidA.wordInc ws)+16))
    (CryptidBoundary.preA (4*k+3)
      (CryptidA.wordCode ws ++ ([true,true,false,false] ++ ys))) = _
  rw [preA_embed_ab]
  rw [CryptidBoundary.run_add]
  -- Transport Agent25's universal arbitrary-word ingestion before the new branch.
  have hi : CryptidBoundary.run (CryptidA.wordCost (4*k+3) ws)
      (embed (CryptidA.ab (4*k+3)
        (CryptidA.wordCode ws ++ ([true,true,false,false] ++ ys)))) =
      embed (CryptidA.ab ((4*k+3)+CryptidA.wordInc ws)
        ([true,true,false,false] ++ ys)) := by
    apply transfer_nonF
    · simp [CryptidA.ab]
    · exact CryptidA.consume_code (4*k+3) ws ([true,true,false,false] ++ ys)
    · simp [CryptidA.ab]
  rw [hi]
  change CryptidBoundary.run
    (2*((4*k+3)+CryptidA.wordInc ws)+16)
    (CryptidBoundary.preA ((4*k+3)+CryptidA.wordInc ws)
      ([true,true,false,false] ++ ys)) = _
  have hparam : 2 ≤ ((4*k+3)+CryptidA.wordInc ws) := by omega
  obtain ⟨u, hu⟩ : ∃ u, ((4*k+3)+CryptidA.wordInc ws) = u+2 := by
    exact ⟨((4*k+3)+CryptidA.wordInc ws)-2,by omega⟩
  rw [hu]
  exact two_one_return u ys

#print axioms two_one_front
#print axioms two_one_return
#print axioms complete_A_word_two_one

end BB6.CryptidBridge
