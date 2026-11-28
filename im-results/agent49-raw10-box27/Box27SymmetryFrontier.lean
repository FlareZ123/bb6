import Box27Partial6452
import Box27Symmetry

namespace BB6.Agent49.Box27SymmetryFrontier
open BB6.Agent49
/-- Source closure of the previous union under E/F renaming and early leaves. -/
def covered := Box27Symmetry.extend Box27Partial6452.covered

theorem bound255 : Box27Symmetry.Valid 255 covered :=
  Box27Symmetry.extend_valid _ Box27Partial6452.bound255

#print axioms bound255
end BB6.Agent49.Box27SymmetryFrontier
