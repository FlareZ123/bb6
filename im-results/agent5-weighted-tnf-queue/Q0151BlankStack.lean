import Q0151PhysicalStack

set_option maxHeartbeats 0
namespace BB6.Agent5Q0151BlankStack
open BB6.Agent5Q0151SourceMacro
open BB6.Agent5Q0151PhysicalStack
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent13PackedZipper
open BB6.Agent5PackedSweep

/-! Physical append of zero symbols is invisible to the packed Turing tape.
This resolves a genuine empty-saved-stack boundary case not handled by the
nonempty-stack pop lemmas. -/

theorem pack_trailing_false (L : List Bool) :
    pack (L ++ [false]) = pack L := by
  simp [pack_append,cat,pack]

theorem frame_trailing_false (q : Fin 6) (L R : List Bool) :
    frame q (L ++ [false]) R = frame q L R := by
  unfold frame encode0
  congr 1
  simpa only [List.cons_append] using
    (pack_trailing_false (R.headD false :: L))

theorem frame_trailing_marker (q : Fin 6) (L R : List Bool) :
    frame q (L ++ [false,false]) R = frame q L R := by
  have hh : L ++ [false,false] = (L++[false])++[false] := by
    simp [List.append_assoc]
  rw [hh,frame_trailing_false,frame_trailing_false]

theorem physical_empty_pop (s : List Bool) (hs : Scan s.reverse) :
    Goes (boundary 1 s [] [])
      (boundary 1 [true,true,true,true] [] s) := by
  have h := bEnd s.reverse [] hs
  have hsrc : boundary 1 s [] [] =
      frame 1 (s.reverse ++ [false,false]) [] := by
    simp [boundary,leftOf,savedLeft,marker]
  have hdst : boundary 1 [true,true,true,true] [] s =
      frame 1 [true,true,true,true] s := by
    simpa [boundary,leftOf,savedLeft,marker] using
      (frame_trailing_marker 1 [true,true,true,true] s)
  rw [hsrc,hdst]
  simpa [List.append_assoc] using h

#print axioms frame_trailing_false
#print axioms frame_trailing_marker
#print axioms physical_empty_pop
end BB6.Agent5Q0151BlankStack
