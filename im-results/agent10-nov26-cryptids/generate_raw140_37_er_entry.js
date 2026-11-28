const fs = require("fs"), path = require("path");
const { rule } = require("./generate_raw140_variant_transfer.js");

let out = `import Raw140VariantTransfer
import Raw140ERSuffix

namespace Raw14037EREntry
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140VariantTransfer
open Raw140ERSweep Raw140ERSuffix
set_option maxRecDepth 100000
set_option maxHeartbeats 0
attribute [local irreducible] run boundary

`;

out += rule(
  "front", 37,
  "1 1 1 3^p 5 X", "2 1 5", 1, 0,
  "3^p+1 5 X", "5 1 1 5 5", 4, 0,
  "BL1 CR2 DR1 EL6 ER1 EL2 BL5 DL1 AR2 EL3 EL1 DR1 EL7 ER1"
);

out += `
theorem toERBank (p : Nat) (X : List Sym) :
    run M37 (22*p+74)
      (boundary 1 false (S 1 :: S 1 :: S 1 :: (U 3 p ++ S 5 :: X))
        [S 2,S 1,S 5]) =
      some (boundary 4 true
        (S 1 :: S 1 :: (U 3 (p+1) ++ X))
        [S 1,S 1,S 5,S 5]) := by
  have h0 := front p X
  have h1 := sweepL M37 4 (S 3) (S 1) 3 (p+1)
    (S 5 :: X) [S 5,S 1,S 1,S 5,S 5] (by rfl)
  have h2 := stepL M37 4 4 true (S 5) (S 1) 1 X
    (U 1 (p+1) ++ [S 5,S 1,S 1,S 5,S 5]) (by rfl)
  have h3b := many (p+1) X [S 5,S 1,S 1,S 5,S 5]
  have h3 := run_ext M37 (fill_extends _ _) _ _ _ h3b
  have h4 := stepR M37 4 4 true (S 5) (S 1) 7
    (S 1 :: (U 3 (p+1) ++ X)) [S 1,S 1,S 5,S 5] (by rfl)
  have h := join (join (join (join h0 h1) h2) h3) h4
  simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc,
    List.append_nil, List.nil_append,
    show (1+7+1+1+7+3+3+3+3+3+3+1+1+7) + 3*(p+1) + 1 + 19*(p+1) + 7 =
      22*p+74 by omega] using h

def bankWord (p : Nat) : List Bool := false :: List.replicate (p+1) true

theorem oddword_bankWord (p : Nat) :
    oddword (bankWord p) = S 1 :: U 3 (p+1) := by
  simp [bankWord, oddword, U]

theorem drainBank (p n : Nat) (X : List Sym) :
    Reach M37
      (boundary 1 false
        (S 1 :: S 1 :: S 1 :: (U 3 p ++ U 5 (n+1) ++ X))
        [S 2,S 1,S 5])
      (boundary 4 true
        (S 1 :: (oddword (iterate n (bankWord p) .t1155).1 ++ X))
        (tailWord (iterate n (bankWord p) .t1155).2)) := by
  have h0 : Reach M37
      (boundary 1 false
        (S 1 :: S 1 :: S 1 :: (U 3 p ++ U 5 (n+1) ++ X))
        [S 2,S 1,S 5])
      (boundary 4 true
        (S 1 :: S 1 :: (U 3 (p+1) ++ U 5 n ++ X))
        [S 1,S 1,S 5,S 5]) := by
    refine ⟨22*p+74, ?_⟩
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc]
      using toERBank p (U 5 n ++ X)
  have hb := bank n (bankWord p) X Tail.t1155
  have hb' : Reach M37
      (boundary 4 true
        (S 1 :: (oddword (bankWord p) ++ U 5 n ++ X))
        (tailWord .t1155))
      (boundary 4 true
        (S 1 :: (oddword (iterate n (bankWord p) .t1155).1 ++ X))
        (tailWord (iterate n (bankWord p) .t1155).2)) :=
    Reach.lift (M := M37) (fill_extends _ _) hb
  have hw := oddword_bankWord p
  have hs : tailWord Tail.t1155 = [S 1,S 1,S 5,S 5] := rfl
  rw [hw, hs] at hb'
  exact Reach.trans h0 hb'

#print axioms front
#print axioms toERBank
#print axioms drainBank
end Raw14037EREntry
`;

fs.writeFileSync(path.join(__dirname, "Raw14037EREntry.lean"), out);
