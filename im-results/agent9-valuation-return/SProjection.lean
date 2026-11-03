import Std
namespace Agent9SProjection

def Sstep (q c : Nat) : Option (Nat × Nat) :=
  if q % 3 = 0 then
    if c = 0 then none else some (4*(q/3), c-1)
  else if q % 3 = 1 then
    some (4*(q/3)-3, c+4)
  else some (4*(q/3)+1, c+6)
end Agent9SProjection
