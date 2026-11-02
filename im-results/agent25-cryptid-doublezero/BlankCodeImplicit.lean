import Lean.Elab.Tactic.Omega
import BlankNext
import ABridgeCode

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace BB6.Agent25
open CryptidBoundary

/-- Physical blank-tape version of the unmodified original-machine
    coded A return. It works for every finite token word and needs no
    fabricated explicitly stored terminal zero. -/
theorem full_A_code_implicit_blank (k : Nat) (ws : List Bool) :
    BB6.BoundaryPadding.ObsEq
      (run
        ((12*k*k+41*k+32) +
          (CryptidA.wordCost (4*k+3) ws +
            (2*((4*k+3)+CryptidA.wordInc ws)+6)))
        (init (List.replicate (3*k+1) true ++
          false :: CryptidA.wordCode ws)))
      (⟨[],false,
        List.replicate (2*((4*k+3)+CryptidA.wordInc ws)+5) true,5⟩ : Cfg) := by
  have hp := BB6.BoundaryPadding.source_init_pad
    ((12*k*k+41*k+32) +
      (CryptidA.wordCost (4*k+3) ws +
        (2*((4*k+3)+CryptidA.wordInc ws)+6)))
    1 (List.replicate (3*k+1) true ++ false :: CryptidA.wordCode ws)
  have hs :
      (List.replicate (3*k+1) true ++ false :: CryptidA.wordCode ws) ++ [false] =
        List.replicate (3*k+1) true ++
          false :: (CryptidA.wordCode ws ++ (false :: [])) := by
    simp [List.append_assoc]
  rw [List.replicate_one, hs] at hp
  have he := BB6.Agent35.full_A_code k ws ([] : List Bool)
  simp only [List.append_nil] at he
  rw [he] at hp
  simpa only using hp

/-- Formerly conditional section at 360,926,875,448,096,383,250,204 steps,
    now connected by a physical-tape proof to the genuine blank start. -/
theorem blank360926875448096383250204 :
    BB6.BoundaryPadding.ObsEq
      (run 360926875448096383250204 blank)
      (⟨[],false,List.replicate 1286175796359 true,5⟩ : Cfg) := by
  have h0 := CryptidBoundary.blank50755341858758075791267
  have hn : 482315923617 = 482315923615+2 := by decide
  rw [hn] at h0
  rw [finish_packet_init 482315923615
    (oppairs 2 ++ false :: List.replicate 15 true)] at h0
  have hs : oppairs 2 ++ false :: List.replicate 15 true =
    false :: CryptidA.wordCode ([false,false,true,true,true,true,true] : List Bool) := by
    decide
  rw [hs] at h0
  have hk : 482315923615 = 3*160771974538+1 := by decide
  rw [hk] at h0
  have ht : 360926875448096383250204 =
    50755341858758075791267 +
      ((12*160771974538*160771974538+41*160771974538+32) +
       (CryptidA.wordCost (4*160771974538+3)
          [false,false,true,true,true,true,true] +
         (2*((4*160771974538+3)+
           CryptidA.wordInc [false,false,true,true,true,true,true])+6))) := by
    decide
  rw [ht, run_add]
  have h := BB6.BoundaryPadding.source_congr
    ((12*160771974538*160771974538+41*160771974538+32) +
       (CryptidA.wordCost (4*160771974538+3)
          [false,false,true,true,true,true,true] +
         (2*((4*160771974538+3)+
           CryptidA.wordInc [false,false,true,true,true,true,true])+6))) h0
  have he := full_A_code_implicit_blank
    160771974538 ([false,false,true,true,true,true,true] : List Bool)
  have hh := BB6.Padding.cfgEq_trans h he
  change BB6.BoundaryPadding.ObsEq _ _ at hh
  simpa only [CryptidA.wordInc, Nat.reduceMul, Nat.reduceAdd] using hh

#print axioms full_A_code_implicit_blank
#print axioms blank360926875448096383250204
end BB6.Agent25
