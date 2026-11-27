import Box28CarryPrefix

namespace BB6.Agent17.Box28CarryWildcard
open BB6Coverage BB6.Agent17.Box28CarryFamily BB6.Agent17.Box28CarryGateSource
open BB6.Agent13.Box33BinaryCounter (zeros zero_head zero_pop zero_push rep rep_add ones ones_succ)
open BB6.Agent17.Box28CarryPrefix
open C9Pair (left right)
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.constructorNameAsVariable false

/-- These prefixes run with B1 missing; thus every B1 completion is covered. -/
theorem gate20_12 (m : Machine) (hm : compatible (baseTable false) m)
    (he : m (4,false) = some ⟨true,true,2⟩) : NeverHalts m := by
  refine from3 m hm 8 (ones 1) ?_ Word3.endWord
  have hp := sourcePrefix false m (some ⟨true,true,2⟩) he 8 (⟨.E,[false],true,[false]⟩) (by decide)
  simpa [view,bits,Eroot,Froot,ones,rep,pair,triple] using hp

#print axioms gate20_12

theorem gate20_14 (m : Machine) (hm : compatible (baseTable false) m)
    (he : m (4,false) = some ⟨false,true,3⟩) : NeverHalts m := by
  refine from3 m hm 7 (ones 1) ?_ Word3.endWord
  have hp := sourcePrefix false m (some ⟨false,true,3⟩) he 7 (⟨.E,[false,false],true,[]⟩) (by decide)
  simpa [view,bits,Eroot,Froot,ones,rep,pair,triple] using hp

#print axioms gate20_14

theorem gate20_15 (m : Machine) (hm : compatible (baseTable false) m)
    (he : m (4,false) = some ⟨true,false,3⟩) : NeverHalts m := by
  refine from3 m hm 20 (triple true true true (ones 1)) ?_ (Word3.d111 Word3.endWord)
  have hp := sourcePrefix false m (some ⟨true,false,3⟩) he 20 (⟨.E,[false],true,[true,true,true]⟩) (by decide)
  simpa [view,bits,Eroot,Froot,ones,rep,pair,triple] using hp

#print axioms gate20_15

theorem gate20_18 (m : Machine) (hm : compatible (baseTable false) m)
    (he : m (4,false) = some ⟨false,true,4⟩) : NeverHalts m := by
  refine from3 m hm 5 (ones 1) ?_ Word3.endWord
  have hp := sourcePrefix false m (some ⟨false,true,4⟩) he 5 (⟨.E,[false,false],true,[]⟩) (by decide)
  simpa [view,bits,Eroot,Froot,ones,rep,pair,triple] using hp

#print axioms gate20_18

theorem gate20_24 (m : Machine) (hm : compatible (baseTable false) m)
    (he : m (4,false) = some ⟨true,true,5⟩) : NeverHalts m := by
  refine from3 m hm 24 (triple true true true (triple true true false (ones 1))) ?_ (Word3.d111 (Word3.d110 Word3.endWord))
  have hp := sourcePrefix false m (some ⟨true,true,5⟩) he 24 (⟨.E,[false],true,[true,true,true,true,false,true]⟩) (by decide)
  simpa [view,bits,Eroot,Froot,ones,rep,pair,triple] using hp

#print axioms gate20_24

theorem gate24_2 (m : Machine) (hm : compatible (baseTable true) m)
    (he : m (4,false) = some ⟨false,true,0⟩) : NeverHalts m := by
  refine from2 m hm 6 zeros ?_ Word2.endWord
  have hp := sourcePrefix true m (some ⟨false,true,0⟩) he 6 (⟨.F,[true,false,false],false,[]⟩) (by decide)
  simpa [view,bits,Eroot,Froot,ones,rep,pair,triple] using hp

#print axioms gate24_2

theorem gate24_4 (m : Machine) (hm : compatible (baseTable true) m)
    (he : m (4,false) = some ⟨true,true,0⟩) : NeverHalts m := by
  refine from2 m hm 15 (pair true true (pair false true zeros)) ?_ (Word2.d11 (Word2.d01 Word2.endWord))
  have hp := sourcePrefix true m (some ⟨true,true,0⟩) he 15 (⟨.F,[true,false],true,[true,false,true]⟩) (by decide)
  simpa [view,bits,Eroot,Froot,ones,rep,pair,triple] using hp

#print axioms gate24_4

theorem gate24_12 (m : Machine) (hm : compatible (baseTable true) m)
    (he : m (4,false) = some ⟨true,true,2⟩) : NeverHalts m := by
  refine from2 m hm 9 zeros ?_ Word2.endWord
  have hp := sourcePrefix true m (some ⟨true,true,2⟩) he 9 (⟨.F,[true,false],false,[]⟩) (by decide)
  simpa [view,bits,Eroot,Froot,ones,rep,pair,triple] using hp

#print axioms gate24_12

theorem gate24_14 (m : Machine) (hm : compatible (baseTable true) m)
    (he : m (4,false) = some ⟨false,true,3⟩) : NeverHalts m := by
  refine from2 m hm 8 zeros ?_ Word2.endWord
  have hp := sourcePrefix true m (some ⟨false,true,3⟩) he 8 (⟨.F,[true,false,false],false,[]⟩) (by decide)
  simpa [view,bits,Eroot,Froot,ones,rep,pair,triple] using hp

#print axioms gate24_14

theorem gate24_15 (m : Machine) (hm : compatible (baseTable true) m)
    (he : m (4,false) = some ⟨true,false,3⟩) : NeverHalts m := by
  refine from2 m hm 7 (pair true false zeros) ?_ (Word2.d10 Word2.endWord)
  have hp := sourcePrefix true m (some ⟨true,false,3⟩) he 7 (⟨.F,[true,false],true,[]⟩) (by decide)
  simpa [view,bits,Eroot,Froot,ones,rep,pair,triple] using hp

#print axioms gate24_15

theorem gate24_16 (m : Machine) (hm : compatible (baseTable true) m)
    (he : m (4,false) = some ⟨true,true,3⟩) : NeverHalts m := by
  refine from2 m hm 9 (pair true false zeros) ?_ (Word2.d10 Word2.endWord)
  have hp := sourcePrefix true m (some ⟨true,true,3⟩) he 9 (⟨.F,[true,false],true,[]⟩) (by decide)
  simpa [view,bits,Eroot,Froot,ones,rep,pair,triple] using hp

#print axioms gate24_16

theorem gate24_18 (m : Machine) (hm : compatible (baseTable true) m)
    (he : m (4,false) = some ⟨false,true,4⟩) : NeverHalts m := by
  refine from2 m hm 6 zeros ?_ Word2.endWord
  have hp := sourcePrefix true m (some ⟨false,true,4⟩) he 6 (⟨.F,[true,false,false],false,[]⟩) (by decide)
  simpa [view,bits,Eroot,Froot,ones,rep,pair,triple] using hp

#print axioms gate24_18

theorem gate24_20 (m : Machine) (hm : compatible (baseTable true) m)
    (he : m (4,false) = some ⟨true,true,4⟩) : NeverHalts m := by
  refine from2 m hm 15 (pair true true (pair false true zeros)) ?_ (Word2.d11 (Word2.d01 Word2.endWord))
  have hp := sourcePrefix true m (some ⟨true,true,4⟩) he 15 (⟨.F,[true,false],true,[true,false,true]⟩) (by decide)
  simpa [view,bits,Eroot,Froot,ones,rep,pair,triple] using hp

#print axioms gate24_20

theorem gate24_23 (m : Machine) (hm : compatible (baseTable true) m)
    (he : m (4,false) = some ⟨true,false,5⟩) : NeverHalts m := by
  refine from2 m hm 14 (pair true false (pair true false zeros)) ?_ (Word2.d10 (Word2.d10 Word2.endWord))
  have hp := sourcePrefix true m (some ⟨true,false,5⟩) he 14 (⟨.F,[true,false],true,[false,true]⟩) (by decide)
  simpa [view,bits,Eroot,Froot,ones,rep,pair,triple] using hp

#print axioms gate24_23

theorem gate24_24 (m : Machine) (hm : compatible (baseTable true) m)
    (he : m (4,false) = some ⟨true,true,5⟩) : NeverHalts m := by
  refine from2 m hm 5 (pair true false zeros) ?_ (Word2.d10 Word2.endWord)
  have hp := sourcePrefix true m (some ⟨true,true,5⟩) he 5 (⟨.F,[true,false],true,[]⟩) (by decide)
  simpa [view,bits,Eroot,Froot,ones,rep,pair,triple] using hp

#print axioms gate24_24

end BB6.Agent17.Box28CarryWildcard
