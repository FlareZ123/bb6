import Raw140VariantTransfer

namespace Raw14037RootBridge
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140VariantTransfer
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def trip133 : Nat → List Sym
  | 0 => []
  | n+1 => trip133 n ++ [S 1,S 3,S 3]

def afterBank : BState :=
  ⟨4,true,
    S 1 :: (trip133 4 ++ S 1 :: (U 3 36)),
    [S 1,S 1,S 2,S 1]⟩

def transferIn : BState :=
  ⟨0,true,
    S 3 :: S 3 :: (U 3 74 ++ [S 2]),
    trip 1 ++ (trip 3 ++ [S 5,S 2,S 1,S 5])⟩

theorem macro_afterBank :
    execute M37 4574 afterBank = some (13730,transferIn) := by
  decide +kernel

theorem afterBank_run :
    run M37 13730 afterBank.prim = some transferIn.prim :=
  execute_sound M37 4574 13730 afterBank transferIn macro_afterBank

def transferOut : BState :=
  ⟨4,true,
    S 1 :: (bank 3 ++
      (S 2 :: S 2 :: S 6 :: S 7 :: (U 3 74 ++ [S 2]))),
    [S 5,S 2,S 1,S 5]⟩

theorem transfer_run :
    run M37 (83+45*3) transferIn.prim = some transferOut.prim := by
  simpa only [transferIn,transferOut,U,List.cons_append,List.append_assoc,
    List.append_nil,List.nil_append] using
    transferMany37 3 (U 3 74 ++ [S 2]) [S 5,S 2,S 1,S 5]

theorem afterBank_to_transferOut :
    run M37 (13730+(83+45*3)) afterBank.prim = some transferOut.prim :=
  join afterBank_run transfer_run

#print axioms macro_afterBank
#print axioms afterBank_run
#print axioms transfer_run
#print axioms afterBank_to_transferOut
end Raw14037RootBridge
