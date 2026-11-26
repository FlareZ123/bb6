import Box33BranchTree
import Box33SourceBridge
namespace BB6.Agent13.Box33Branch
open BB6Coverage

def binary : Known 9 :=
  ⟨Box33Source.partialTable false false, good_never _ _ (Box33Source.compatible_never false false)⟩
def binaryFlip : Known 11 :=
  ⟨Box33Source.partialTable false true, good_never _ _ (Box33Source.compatible_never false true)⟩
def sweep : Known 8 :=
  ⟨Box33Source.partialTable true false, good_never _ _ (Box33Source.compatible_never true false)⟩
def sweepFlip : Known 10 :=
  ⟨Box33Source.partialTable true true, good_never _ _ (Box33Source.compatible_never true true)⟩
end BB6.Agent13.Box33Branch
