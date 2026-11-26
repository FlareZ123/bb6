import Q0HalfCounterexample

namespace BB429Q0Macro.HalfStep
open BB429Q0Macro
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

def w89 : List Bool := List.replicate 85 false ++ [true,true,true,false]
def v89 : List Bool := List.replicate 84 false ++ List.replicate 5 true
def z89 : List Bool := List.replicate 81 true ++ List.replicate 3 false ++ List.replicate 4 true ++ [false]

/-- The coefficient-one short binary barrier also fails, at scale 89. -/
theorem crossing89 : Cross2 1 0 89 := by
  let p : Nat := 383123885216472214589586756787577295904684780545900269
  let y : Nat := 20952087472775824235368025761820633369787448936103936
  let Y : Nat := 31428131209163736353052038642730950054681173404155904
  let P2 : Nat := 383123885216472214589586756787577295904684780545900829
  let Y2 : Nat := 127583246932438501147508871156800642483884287271632991
  let P3 : Nat := 383123885216472214589586756787577295904684780545901348
  let Y3 : Nat := 31804224297170222037336453539683273551739300045215128
  refine ⟨true,w89,v89,z89,p,y,Y,P2,Y2,P3,Y3,by decide,by decide,by decide,by decide,by decide,by unfold valid bit; decide,?_,?_,?_⟩
  all_goals apply run_sound; decide

#print axioms crossing89
end BB429Q0Macro.HalfStep
