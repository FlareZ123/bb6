import Q0151Retreat

set_option maxHeartbeats 200000
set_option maxRecDepth 100000
namespace BB6.Agent5Q0151SourceMacro
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent13PackedZipper
open BB6.Agent5PackedSweep

theorem revAlt_reverse (n : Nat) : (revAlt n).reverse = alt n := by
  rw [← alt_reverse,List.reverse_reverse]

theorem go_of_run {a b : P} {k : Nat} (hk : 0 < k) (h : runP p k a = some b) : Goes a b := ⟨k,hk,h⟩

theorem bOdd1 (L R : List Bool) : Goes (frame 1 L (rr 1 R)) (frame 1 ([true,false]++L) R) :=
  go_of_run (by decide) (b10 L R)

theorem cOdd1 (L R : List Bool) : Goes (frame 2 L (rr 1 R)) (frame 1 ([true,true]++L) R) :=
  go_of_run (by decide) (c10 L R)

theorem bOddBig (n : Nat) (L R : List Bool) :
    Goes (frame 1 L (rr (4*n+5) R)) (frame 1 ([true,true]++revAlt (2*n+1)++[false,false]++L) R) := by
  exact go_of_run (by omega) (rightOdd true n L R)

theorem cOddBig (n : Nat) (L R : List Bool) :
    Goes (frame 2 L (rr (4*n+5) R)) (frame 1 ([true,true]++revAlt (2*n+2)++L) R) := by
  apply go_of_run (by omega : 0 < 2+4*n+4)
  have h := rightOdd false n L R
  rw [show 2*n+2=(2*n+1)+1 by omega,revAlt_snoc]
  change runP p _ _ = some (frame 1 ([true,true]++([false,true]++revAlt (2*n))++[false,true]++L) R)
  change runP p (2+4*n+4) (frame 2 L (rr (4*n+5) R)) = some (frame 1 ([true,true,false,true] ++ revAlt (2*n) ++ [false,true] ++ L) R) at h
  simpa only [List.append_assoc,List.cons_append,List.nil_append] using h

theorem bZero (n : Nat) (L R : List Bool) :
    Goes (frame 1 L (rr (4*n+4) R)) (frame 2 ([true,true,true]++revAlt (2*n)++[false,false]++L) R) :=
  go_of_run (by omega) (rightZero true n L R)

theorem cZero (n : Nat) (L R : List Bool) :
    Goes (frame 2 L (rr (4*n+4) R)) (frame 2 ([true,true,true]++revAlt (2*n+1)++L) R) := by
  apply go_of_run (by omega : 0 < 2+4*n+5)
  rw [revAlt_snoc]
  exact rightZero false n L R

theorem bEvenBig (n : Nat) (L R : List Bool) :
    Goes (frame 1 L (rr (4*(n+1)+2) R))
      (frame 1 ([true,true,true,true]++L) (alt (2*n+1)++true::R)) := by
  have h1 := go_of_run (by omega : 0 < 2+4*(n+1)) (rightTwo true (n+1) L R)
  have h2 := go_of_run (by decide : 0 < 3) (eTurn (revAlt (2*n+1)++[false,false]++L) R)
  have h12 := goes_join h1 h2
  have h3 := retreat (revAlt (2*n+1)) L (true::R) (scanAlt _)
  rw [revAlt_reverse] at h3
  exact goes_join h12 h3

theorem cEven (n : Nat) (S L R : List Bool) (hs : Scan S) :
    Goes (frame 2 (S++[false,false]++L) (rr (4*n+2) R))
      (frame 1 ([true,true,true,true]++L) (S.reverse++alt (2*n)++true::R)) := by
  have h1 := go_of_run (by omega : 0 < 2+4*n) (rightTwo false n (S++[false,false]++L) R)
  have h2 := go_of_run (by decide : 0 < 3) (eTurn (revAlt (2*n)++S++[false,false]++L) R)
  have h12 : Goes (frame 2 (S++[false,false]++L) (rr (4*n+2) R))
      (encode0 ⟨2,(revAlt (2*n)++S)++[false,false]++L,[true,false,true]++R⟩) := by
    apply goes_join h1
    rw [show (revAlt (2*n)++marker false) = revAlt (2*n+1) from (revAlt_snoc _).symm] <;> simp only [srcQ,marker,if_false,List.append_assoc] at *
    exact h2
  have h3 := retreat (revAlt (2*n)++S) L (true::R) ((scanAlt _).append hs)
  rw [List.reverse_append,revAlt_reverse] at h3
  exact goes_join h12 h3

theorem bEnd (S L : List Bool) (hs : Scan S) :
    Goes (frame 1 (S++[false,false]++L) []) (frame 1 ([true,true,true,true]++L) S.reverse) := by
  exact goes_join (go_of_run (by decide) (bBlank (S++[false,false]++L))) (by simpa only [List.append_nil] using retreat S L [] hs)

theorem cEnd (S L : List Bool) (hs : Scan S) :
    Goes (frame 2 (true::(S++[false,false]++L)) []) (frame 1 ([true,true,true,true]++L) S.reverse) := by
  exact goes_join (go_of_run (by decide) (cBlank (S++[false,false]++L))) (by simpa only [List.append_nil] using retreat S L [] hs)

theorem bTwoEnd (S L : List Bool) (hs : Scan S) :
    Goes (frame 1 (S++[false,false]++L) (rr 2 []))
      (frame 1 ([true,true,true,true]++L) (S.reverse++[true,true,true,true])) := by
  have h1 := go_of_run (by decide : 0 < 2) (rightTwo true 0 (S++[false,false]++L) [])
  have h2 := go_of_run (by decide : 0 < 6) (repairEmpty (S++[false,false]++L))
  have h3 := bEnd ([true,true,true,true]++S) L ((scanOnes 4).append hs)
  exact goes_join (goes_join h1 h2) (by simpa using h3)

theorem bTwoOdd1 (S L R : List Bool) (hs : Scan S) :
    Goes (frame 1 (S++[false,false]++L) (rr 2 (rr 1 R)))
      (frame 1 ([true,true,true,true]++L) (S.reverse++[true,true,true]++R)) := by
  have h1 := go_of_run (by decide : 0 < 2) (rightTwo true 0 (S++[false,false]++L) (rr 1 R))
  have h2 := go_of_run (by decide : 0 < 6) (repairOne (S++[false,false]++L) (false::R))
  have h3 := go_of_run (by decide : 0 < 3) (eTurn ([true,true]++S++[false,false]++L) R)
  have h4 := retreat ([true,true]++S) L (true::R) ((scanOnes 2).append hs)
  exact goes_join (goes_join (goes_join h1 h2) h3) (by simpa [List.append_assoc] using h4)

theorem bTwoOddBig (n : Nat) (S L R : List Bool) (hs : Scan S) :
    Goes (frame 1 (S++[false,false]++L) (rr 2 (rr (4*n+5) R)))
      (frame 1 ([true,true,true,true]++L) (S.reverse++[true,true,true,false]++alt (2*n+1)++true::R)) := by
  have h1 := go_of_run (by decide : 0 < 2) (rightTwo true 0 (S++[false,false]++L) (rr (4*n+5) R))
  have h2 := go_of_run (by decide : 0 < 6) (repairOne (S++[false,false]++L) (ones (4*(n+1))++false::R))
  have h12 : Goes (frame 1 (S++[false,false]++L) (rr 2 (rr (4*n+5) R)))
    (frame 4 ([false,true,true,true]++S++[false,false]++L) (ones (4*(n+1))++false::R)) := by
    apply goes_join h1
    change Goes (frame 4 ([false,false]++S++[false,false]++L) (false::rr (4*n+5) R)) _
    rw [rr,show 4*n+5=1+4*(n+1) by omega,ones_add]
    exact h2
  have h3 := eLoop (n+1) ([false,true,true,true]++S++[false,false]++L) (false::R)
  rw [repOnes4,repAlt4] at h3
  have h123 := goes_join h12 (go_of_run (by omega : 0 < 4*(n+1)) h3)
  have h4 := go_of_run (by decide : 0 < 3) (eTurn (revAlt (2*n+1)++[false,true,true,true]++S++[false,false]++L) R)
  rw [show 2*(n+1)=2*n+1+1 by omega] at h123
  have h123' : Goes (frame 1 (S++[false,false]++L) (rr 2 (rr (4*n+5) R)))
    (frame 4 ([false,true]++(revAlt (2*n+1)++[false,true,true,true]++S++[false,false]++L)) (false::R)) := by
    change Goes _ (frame 4 (([false,true]++revAlt (2*n+1))++([false,true,true,true]++S++[false,false]++L)) (false::R)) at h123
    simpa only [List.append_assoc] using h123
  have h1234 := goes_join h123' h4
  have hs5 : Scan (revAlt (2*n+1)++[false,true,true,true]++S) := by
    rw [List.append_assoc]
    apply Scan.append
    · exact scanAlt _
    · exact Scan.pair (Scan.one (Scan.one hs))
  have h5 := retreat (revAlt (2*n+1)++[false,true,true,true]++S) L (true::R) hs5
  rw [List.reverse_append,List.reverse_append,revAlt_reverse] at h5
  exact goes_join h1234 (by simpa [List.append_assoc] using h5)

theorem bTwoZero (n : Nat) (S L R : List Bool) :
    Goes (frame 1 (S++[false,false]++L) (rr 2 (rr (4*n+4) R)))
      (frame 1 ([true,true]++revAlt (2*n+1)++[false,true,true,true]++S++[false,false]++L) R) := by
  have h1 := go_of_run (by decide : 0 < 2) (rightTwo true 0 (S++[false,false]++L) (rr (4*n+4) R))
  have h2 := go_of_run (by decide : 0 < 6) (repairOne (S++[false,false]++L) (ones (4*n+3)++false::R))
  have h12 : Goes (frame 1 (S++[false,false]++L) (rr 2 (rr (4*n+4) R)))
    (frame 4 ([false,true,true,true]++S++[false,false]++L) (ones (4*n+3)++false::R)) := by
    apply goes_join h1
    change Goes (frame 4 ([false,false]++S++[false,false]++L) (false::rr (4*n+4) R)) _
    rw [rr,show 4*n+4=1+(4*n+3) by omega,ones_add]
    exact h2
  have h3 := eLoop n ([false,true,true,true]++S++[false,false]++L) ([true,true,true,false]++R)
  rw [repOnes4,repAlt4] at h3
  have h3' : runP p (4*n) (frame 4 ([false,true,true,true]++S++[false,false]++L) (ones (4*n+3)++false::R)) =
    some (frame 4 (revAlt (2*n)++[false,true,true,true]++S++[false,false]++L) ([true,true,true,false]++R)) := by
    rw [ones_add]
    change runP p _ (frame 4 _ (ones (4*n)++[true,true,true]++false::R)) = _
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using h3
  have h4 := e3 (revAlt (2*n)++[false,true,true,true]++S++[false,false]++L) R
  exact goes_join h12 (go_of_run (by omega : 0<4*n+4) (joinP h3' h4))

#print axioms bTwoOddBig
#print axioms bTwoZero
#print axioms bEvenBig
#print axioms cEven
#print axioms bTwoOdd1
end BB6.Agent5Q0151SourceMacro
