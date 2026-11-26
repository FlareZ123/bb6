import Box3C9Tree
import C9PairWeights

namespace BB6.Agent13.C9PairKnown
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent13.C9Bridge

def known (short : Bool) : BB6.Agent13.Box3C9.Known 11 :=
  ⟨partialTable short, by
    intro m _ hm
    rw [compatible_table short m hm]
    exact weight short⟩

def shortKnown := known true
def longKnown := known false
end BB6.Agent13.C9PairKnown
