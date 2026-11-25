import HardRootParents

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent19HardRoot
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47WeightedHalt BB6.Agent8TNFPath

def champion : Machine := literal [some ⟨true,true,1⟩, some ⟨true,true,0⟩, some ⟨true,true,2⟩, none, some ⟨true,false,3⟩, some ⟨false,true,5⟩, some ⟨true,true,0⟩, some ⟨false,false,4⟩, some ⟨false,false,3⟩, some ⟨true,true,2⟩, some ⟨true,true,0⟩, some ⟨false,true,4⟩]
def champion_schedule : List (Nat × Slot) := [(1,(1,false)), (2,(2,false)), (3,(3,true)), (4,(4,true)), (7,(4,false)), (8,(3,false)), (11,(2,true)), (12,(5,true)), (53,(5,false)), (213,(0,true))]
theorem champion_path : FirstHolePath (forgetHaltRows champion) 6 :=
  checked_from_root _ champion_schedule (by decide)
theorem champion_parent : compatible p139 champion :=
  (parentCheck_iff _ _).mp (by decide)
theorem champion_leaf_parent : ∀ m, compatible (forgetHaltRows champion) m → compatible p139 m :=
  leaf_extends_parent _ _ (ordinaryParentCheck_sound _ (by decide)) champion_parent
theorem champion_cover_iff (B : Nat) :
    Cover (WeightedBound B) (forgetHaltRows champion) ↔
      ∀ k, HaltsAfter champion k → k+1+0 ≤ B :=
  cover_iff_of_checks champion (1,true) [0] 0 B (by decide) (by decide)
    (by decide) (by simp)
#print axioms champion_path
#print axioms champion_parent
#print axioms champion_leaf_parent
#print axioms champion_cover_iff

def C : Machine := literal [some ⟨true,true,1⟩, some ⟨true,false,2⟩, some ⟨true,false,2⟩, some ⟨true,true,3⟩, some ⟨true,false,0⟩, some ⟨false,false,1⟩, some ⟨false,true,1⟩, some ⟨true,true,4⟩, some ⟨true,true,5⟩, some ⟨false,true,0⟩, none, some ⟨false,true,2⟩]
def C_schedule : List (Nat × Slot) := [(1,(1,false)), (2,(2,true)), (4,(2,false)), (6,(1,true)), (7,(3,true)), (8,(4,false)), (9,(5,true)), (13,(3,false)), (16,(0,true)), (22,(4,true))]
theorem C_path : FirstHolePath (forgetHaltRows C) 6 :=
  checked_from_root _ C_schedule (by decide)
theorem C_parent : compatible p10 C :=
  (parentCheck_iff _ _).mp (by decide)
theorem C_leaf_parent : ∀ m, compatible (forgetHaltRows C) m → compatible p10 m :=
  leaf_extends_parent _ _ (ordinaryParentCheck_sound _ (by decide)) C_parent
theorem C_cover_iff (B : Nat) :
    Cover (WeightedBound B) (forgetHaltRows C) ↔
      ∀ k, HaltsAfter C k → k+1+0 ≤ B :=
  cover_iff_of_checks C (5,false) [0] 0 B (by decide) (by decide)
    (by decide) (by simp)
#print axioms C_path
#print axioms C_parent
#print axioms C_leaf_parent
#print axioms C_cover_iff

def P1 : Machine := literal [some ⟨true,true,1⟩, some ⟨true,true,3⟩, some ⟨false,false,2⟩, some ⟨true,true,0⟩, some ⟨true,false,0⟩, some ⟨true,false,2⟩, some ⟨true,true,0⟩, some ⟨true,false,4⟩, some ⟨true,true,5⟩, some ⟨false,false,3⟩, none, some ⟨false,true,4⟩]
def P1_schedule : List (Nat × Slot) := [(1,(1,false)), (2,(2,true)), (3,(2,false)), (5,(1,true)), (6,(0,true)), (7,(3,false)), (19,(3,true)), (20,(4,true)), (36,(4,false)), (37,(5,true))]
theorem P1_path : FirstHolePath (forgetHaltRows P1) 6 :=
  checked_from_root _ P1_schedule (by decide)
theorem P1_parent : compatible p8 P1 :=
  (parentCheck_iff _ _).mp (by decide)
theorem P1_leaf_parent : ∀ m, compatible (forgetHaltRows P1) m → compatible p8 m :=
  leaf_extends_parent _ _ (ordinaryParentCheck_sound _ (by decide)) P1_parent
theorem P1_cover_iff (B : Nat) :
    Cover (WeightedBound B) (forgetHaltRows P1) ↔
      ∀ k, HaltsAfter P1 k → k+1+0 ≤ B :=
  cover_iff_of_checks P1 (5,false) [0] 0 B (by decide) (by decide)
    (by decide) (by simp)
#print axioms P1_path
#print axioms P1_parent
#print axioms P1_leaf_parent
#print axioms P1_cover_iff

def Sheep : Machine := literal [some ⟨true,true,1⟩, some ⟨true,false,0⟩, some ⟨false,false,2⟩, some ⟨false,true,2⟩, some ⟨true,false,4⟩, some ⟨true,true,3⟩, some ⟨true,true,4⟩, some ⟨true,true,2⟩, some ⟨true,false,5⟩, some ⟨false,false,0⟩, none, some ⟨true,false,4⟩]
def Sheep_schedule : List (Nat × Slot) := [(1,(1,false)), (2,(2,true)), (3,(3,false)), (4,(4,false)), (5,(5,true)), (6,(4,true)), (12,(0,true)), (15,(1,true)), (40,(3,true)), (100,(2,false))]
theorem Sheep_path : FirstHolePath (forgetHaltRows Sheep) 6 :=
  checked_from_root _ Sheep_schedule (by decide)
theorem Sheep_parent : compatible p8 Sheep :=
  (parentCheck_iff _ _).mp (by decide)
theorem Sheep_leaf_parent : ∀ m, compatible (forgetHaltRows Sheep) m → compatible p8 m :=
  leaf_extends_parent _ _ (ordinaryParentCheck_sound _ (by decide)) Sheep_parent
theorem Sheep_cover_iff (B : Nat) :
    Cover (WeightedBound B) (forgetHaltRows Sheep) ↔
      ∀ k, HaltsAfter Sheep k → k+1+0 ≤ B :=
  cover_iff_of_checks Sheep (5,false) [0] 0 B (by decide) (by decide)
    (by decide) (by simp)
#print axioms Sheep_path
#print axioms Sheep_parent
#print axioms Sheep_leaf_parent
#print axioms Sheep_cover_iff

def D0 : Machine := literal [some ⟨true,true,1⟩, some ⟨false,true,4⟩, some ⟨true,false,2⟩, some ⟨false,true,0⟩, some ⟨true,false,0⟩, some ⟨true,false,3⟩, some ⟨true,false,2⟩, some ⟨true,false,5⟩, some ⟨false,false,2⟩, some ⟨false,false,1⟩, some ⟨true,false,4⟩, none]
def D0_schedule : List (Nat × Slot) := [(1,(1,false)), (2,(2,true)), (3,(3,false)), (4,(2,false)), (6,(1,true)), (7,(0,true)), (8,(4,true)), (18,(4,false)), (35,(3,true)), (36,(5,false))]
theorem D0_path : FirstHolePath (forgetHaltRows D0) 6 :=
  checked_from_root _ D0_schedule (by decide)
theorem D0_parent : compatible p10 D0 :=
  (parentCheck_iff _ _).mp (by decide)
theorem D0_leaf_parent : ∀ m, compatible (forgetHaltRows D0) m → compatible p10 m :=
  leaf_extends_parent _ _ (ordinaryParentCheck_sound _ (by decide)) D0_parent
theorem D0_cover_iff (B : Nat) :
    Cover (WeightedBound B) (forgetHaltRows D0) ↔
      ∀ k, HaltsAfter D0 k → k+1+0 ≤ B :=
  cover_iff_of_checks D0 (5,true) [0] 0 B (by decide) (by decide)
    (by decide) (by simp)
#print axioms D0_path
#print axioms D0_parent
#print axioms D0_leaf_parent
#print axioms D0_cover_iff

def D1 : Machine := literal [some ⟨true,true,1⟩, none, some ⟨false,true,2⟩, some ⟨false,true,4⟩, some ⟨true,true,3⟩, some ⟨true,true,5⟩, some ⟨true,false,4⟩, some ⟨false,false,1⟩, some ⟨true,true,2⟩, some ⟨false,false,3⟩, some ⟨true,true,2⟩, some ⟨true,true,0⟩]
def D1_schedule : List (Nat × Slot) := [(1,(1,false)), (2,(2,false)), (3,(3,false)), (4,(4,true)), (8,(4,false)), (9,(2,true)), (10,(5,false)), (18,(3,true)), (19,(1,true)), (94,(5,true))]
theorem D1_path : FirstHolePath (forgetHaltRows D1) 6 :=
  checked_from_root _ D1_schedule (by decide)
theorem D1_parent : compatible p9 D1 :=
  (parentCheck_iff _ _).mp (by decide)
theorem D1_leaf_parent : ∀ m, compatible (forgetHaltRows D1) m → compatible p9 m :=
  leaf_extends_parent _ _ (ordinaryParentCheck_sound _ (by decide)) D1_parent
theorem D1_cover_iff (B : Nat) :
    Cover (WeightedBound B) (forgetHaltRows D1) ↔
      ∀ k, HaltsAfter D1 k → k+1+0 ≤ B :=
  cover_iff_of_checks D1 (0,true) [0] 0 B (by decide) (by decide)
    (by decide) (by simp)
#print axioms D1_path
#print axioms D1_parent
#print axioms D1_leaf_parent
#print axioms D1_cover_iff

def D2 : Machine := literal [some ⟨true,true,1⟩, some ⟨true,true,3⟩, some ⟨true,false,2⟩, some ⟨false,false,4⟩, some ⟨true,true,0⟩, some ⟨false,false,1⟩, some ⟨true,true,0⟩, some ⟨true,true,5⟩, some ⟨false,true,0⟩, some ⟨false,true,2⟩, some ⟨true,true,4⟩, none]
def D2_schedule : List (Nat × Slot) := [(1,(1,false)), (2,(2,true)), (4,(2,false)), (5,(0,true)), (6,(3,false)), (12,(1,true)), (13,(4,true)), (23,(4,false)), (91,(3,true)), (92,(5,false))]
theorem D2_path : FirstHolePath (forgetHaltRows D2) 6 :=
  checked_from_root _ D2_schedule (by decide)
theorem D2_parent : compatible p10 D2 :=
  (parentCheck_iff _ _).mp (by decide)
theorem D2_leaf_parent : ∀ m, compatible (forgetHaltRows D2) m → compatible p10 m :=
  leaf_extends_parent _ _ (ordinaryParentCheck_sound _ (by decide)) D2_parent
theorem D2_cover_iff (B : Nat) :
    Cover (WeightedBound B) (forgetHaltRows D2) ↔
      ∀ k, HaltsAfter D2 k → k+1+1 ≤ B :=
  cover_iff_of_checks D2 (5,true) [0, 1] 1 B (by decide) (by decide)
    (by decide) (by simp)
#print axioms D2_path
#print axioms D2_parent
#print axioms D2_leaf_parent
#print axioms D2_cover_iff

def D3 : Machine := literal [some ⟨true,true,1⟩, some ⟨false,false,2⟩, some ⟨true,true,2⟩, some ⟨true,true,4⟩, some ⟨true,false,0⟩, some ⟨false,false,3⟩, some ⟨false,true,1⟩, some ⟨false,true,0⟩, some ⟨true,true,1⟩, some ⟨true,true,5⟩, some ⟨true,true,3⟩, none]
def D3_schedule : List (Nat × Slot) := [(1,(1,false)), (2,(2,false)), (3,(0,true)), (4,(2,true)), (5,(3,false)), (11,(1,true)), (12,(4,false)), (14,(4,true)), (15,(5,false)), (23,(3,true))]
theorem D3_path : FirstHolePath (forgetHaltRows D3) 6 :=
  checked_from_root _ D3_schedule (by decide)
theorem D3_parent : compatible p13 D3 :=
  (parentCheck_iff _ _).mp (by decide)
theorem D3_leaf_parent : ∀ m, compatible (forgetHaltRows D3) m → compatible p13 m :=
  leaf_extends_parent _ _ (ordinaryParentCheck_sound _ (by decide)) D3_parent
theorem D3_cover_iff (B : Nat) :
    Cover (WeightedBound B) (forgetHaltRows D3) ↔
      ∀ k, HaltsAfter D3 k → k+1+0 ≤ B :=
  cover_iff_of_checks D3 (5,true) [0] 0 B (by decide) (by decide)
    (by decide) (by simp)
#print axioms D3_path
#print axioms D3_parent
#print axioms D3_leaf_parent
#print axioms D3_cover_iff

def A6 : Machine := literal [some ⟨true,true,1⟩, some ⟨false,false,5⟩, some ⟨true,true,2⟩, some ⟨false,true,0⟩, some ⟨true,false,3⟩, some ⟨false,true,1⟩, some ⟨false,false,4⟩, some ⟨false,false,2⟩, some ⟨false,false,0⟩, some ⟨false,false,2⟩, some ⟨false,false,1⟩, none]
def A6_schedule : List (Nat × Slot) := [(1,(1,false)), (2,(2,false)), (3,(3,true)), (4,(2,true)), (13,(3,false)), (14,(4,false)), (22,(1,true)), (41,(4,true)), (109,(0,true)), (110,(5,false))]
theorem A6_path : FirstHolePath (forgetHaltRows A6) 6 :=
  checked_from_root _ A6_schedule (by decide)
theorem A6_parent : compatible p139 A6 :=
  (parentCheck_iff _ _).mp (by decide)
theorem A6_leaf_parent : ∀ m, compatible (forgetHaltRows A6) m → compatible p139 m :=
  leaf_extends_parent _ _ (ordinaryParentCheck_sound _ (by decide)) A6_parent
theorem A6_cover_iff (B : Nat) :
    Cover (WeightedBound B) (forgetHaltRows A6) ↔
      ∀ k, HaltsAfter A6 k → k+1+2 ≤ B :=
  cover_iff_of_checks A6 (5,true) [0, 1, 2] 2 B (by decide) (by decide)
    (by decide) (by simp)
#print axioms A6_path
#print axioms A6_parent
#print axioms A6_leaf_parent
#print axioms A6_cover_iff

def r1 : Machine := literal [some ⟨true,true,1⟩, some ⟨false,false,2⟩, some ⟨true,false,2⟩, some ⟨false,true,1⟩, some ⟨false,false,4⟩, some ⟨false,false,3⟩, some ⟨true,false,2⟩, none, some ⟨false,true,0⟩, some ⟨true,false,5⟩, some ⟨true,false,0⟩, some ⟨true,false,5⟩]
def r1_schedule : List (Nat × Slot) := [(1,(1,false)), (2,(2,true)), (3,(3,false)), (4,(2,false)), (5,(4,false)), (7,(1,true)), (10,(4,true)), (11,(5,false)), (49,(0,true)), (52,(5,true))]
theorem r1_path : FirstHolePath (forgetHaltRows r1) 6 :=
  checked_from_root _ r1_schedule (by decide)
theorem r1_parent : compatible p10 r1 :=
  (parentCheck_iff _ _).mp (by decide)
theorem r1_leaf_parent : ∀ m, compatible (forgetHaltRows r1) m → compatible p10 m :=
  leaf_extends_parent _ _ (ordinaryParentCheck_sound _ (by decide)) r1_parent
theorem r1_cover_iff (B : Nat) :
    Cover (WeightedBound B) (forgetHaltRows r1) ↔
      ∀ k, HaltsAfter r1 k → k+1+2 ≤ B :=
  cover_iff_of_checks r1 (3,true) [0, 1, 2] 2 B (by decide) (by decide)
    (by decide) (by simp)
#print axioms r1_path
#print axioms r1_parent
#print axioms r1_leaf_parent
#print axioms r1_cover_iff

def r2 : Machine := literal [some ⟨true,true,1⟩, some ⟨false,true,0⟩, some ⟨false,true,2⟩, some ⟨false,false,3⟩, some ⟨true,false,0⟩, some ⟨true,true,5⟩, some ⟨true,false,4⟩, some ⟨true,false,3⟩, some ⟨true,false,1⟩, some ⟨true,true,4⟩, none, some ⟨true,true,0⟩]
def r2_schedule : List (Nat × Slot) := [(1,(1,false)), (2,(2,false)), (4,(1,true)), (5,(3,true)), (7,(3,false)), (8,(4,false)), (10,(2,true)), (11,(5,true)), (12,(0,true)), (35,(4,true))]
theorem r2_path : FirstHolePath (forgetHaltRows r2) 6 :=
  checked_from_root _ r2_schedule (by decide)
theorem r2_parent : compatible p9 r2 :=
  (parentCheck_iff _ _).mp (by decide)
theorem r2_leaf_parent : ∀ m, compatible (forgetHaltRows r2) m → compatible p9 m :=
  leaf_extends_parent _ _ (ordinaryParentCheck_sound _ (by decide)) r2_parent
theorem r2_cover_iff (B : Nat) :
    Cover (WeightedBound B) (forgetHaltRows r2) ↔
      ∀ k, HaltsAfter r2 k → k+1+0 ≤ B :=
  cover_iff_of_checks r2 (5,false) [0] 0 B (by decide) (by decide)
    (by decide) (by simp)
#print axioms r2_path
#print axioms r2_parent
#print axioms r2_leaf_parent
#print axioms r2_cover_iff

def r3 : Machine := literal [some ⟨true,true,1⟩, some ⟨false,true,0⟩, some ⟨false,true,2⟩, some ⟨false,false,4⟩, some ⟨true,false,3⟩, some ⟨true,true,5⟩, some ⟨true,false,1⟩, some ⟨true,true,3⟩, some ⟨true,false,3⟩, some ⟨true,false,4⟩, none, some ⟨true,true,0⟩]
def r3_schedule : List (Nat × Slot) := [(1,(1,false)), (2,(2,false)), (3,(3,false)), (4,(1,true)), (5,(4,false)), (8,(2,true)), (9,(5,true)), (12,(4,true)), (20,(0,true)), (38,(3,true))]
theorem r3_path : FirstHolePath (forgetHaltRows r3) 6 :=
  checked_from_root _ r3_schedule (by decide)
theorem r3_parent : compatible p9 r3 :=
  (parentCheck_iff _ _).mp (by decide)
theorem r3_leaf_parent : ∀ m, compatible (forgetHaltRows r3) m → compatible p9 m :=
  leaf_extends_parent _ _ (ordinaryParentCheck_sound _ (by decide)) r3_parent
theorem r3_cover_iff (B : Nat) :
    Cover (WeightedBound B) (forgetHaltRows r3) ↔
      ∀ k, HaltsAfter r3 k → k+1+0 ≤ B :=
  cover_iff_of_checks r3 (5,false) [0] 0 B (by decide) (by decide)
    (by decide) (by simp)
#print axioms r3_path
#print axioms r3_parent
#print axioms r3_leaf_parent
#print axioms r3_cover_iff

def r4 : Machine := literal [some ⟨true,true,1⟩, some ⟨false,true,0⟩, some ⟨true,true,2⟩, some ⟨false,false,2⟩, some ⟨false,false,3⟩, some ⟨true,true,5⟩, some ⟨true,true,0⟩, some ⟨true,false,4⟩, some ⟨true,false,3⟩, some ⟨false,false,1⟩, some ⟨false,true,4⟩, none]
def r4_schedule : List (Nat × Slot) := [(1,(1,false)), (2,(2,false)), (3,(3,true)), (4,(4,true)), (8,(4,false)), (9,(3,false)), (10,(0,true)), (13,(1,true)), (14,(2,true)), (15,(5,false))]
theorem r4_path : FirstHolePath (forgetHaltRows r4) 6 :=
  checked_from_root _ r4_schedule (by decide)
theorem r4_parent : compatible p23 r4 :=
  (parentCheck_iff _ _).mp (by decide)
theorem r4_leaf_parent : ∀ m, compatible (forgetHaltRows r4) m → compatible p23 m :=
  leaf_extends_parent _ _ (ordinaryParentCheck_sound _ (by decide)) r4_parent
theorem r4_cover_iff (B : Nat) :
    Cover (WeightedBound B) (forgetHaltRows r4) ↔
      ∀ k, HaltsAfter r4 k → k+1+0 ≤ B :=
  cover_iff_of_checks r4 (5,true) [0] 0 B (by decide) (by decide)
    (by decide) (by simp)
#print axioms r4_path
#print axioms r4_parent
#print axioms r4_leaf_parent
#print axioms r4_cover_iff

def r5 : Machine := literal [some ⟨true,true,1⟩, some ⟨true,true,0⟩, some ⟨false,false,2⟩, some ⟨false,true,0⟩, some ⟨true,true,2⟩, some ⟨true,false,3⟩, some ⟨false,false,1⟩, some ⟨true,false,4⟩, some ⟨true,false,5⟩, some ⟨false,true,2⟩, none, some ⟨false,false,3⟩]
def r5_schedule : List (Nat × Slot) := [(1,(1,false)), (2,(2,true)), (3,(3,false)), (5,(2,false)), (9,(3,true)), (10,(4,true)), (13,(1,true)), (16,(0,true)), (21,(4,false)), (22,(5,true))]
theorem r5_path : FirstHolePath (forgetHaltRows r5) 6 :=
  checked_from_root _ r5_schedule (by decide)
theorem r5_parent : compatible p8 r5 :=
  (parentCheck_iff _ _).mp (by decide)
theorem r5_leaf_parent : ∀ m, compatible (forgetHaltRows r5) m → compatible p8 m :=
  leaf_extends_parent _ _ (ordinaryParentCheck_sound _ (by decide)) r5_parent
theorem r5_cover_iff (B : Nat) :
    Cover (WeightedBound B) (forgetHaltRows r5) ↔
      ∀ k, HaltsAfter r5 k → k+1+0 ≤ B :=
  cover_iff_of_checks r5 (5,false) [0] 0 B (by decide) (by decide)
    (by decide) (by simp)
#print axioms r5_path
#print axioms r5_parent
#print axioms r5_leaf_parent
#print axioms r5_cover_iff

def r6 : Machine := literal [some ⟨true,true,1⟩, some ⟨true,true,0⟩, some ⟨true,true,2⟩, some ⟨true,false,1⟩, some ⟨false,false,3⟩, some ⟨false,true,0⟩, some ⟨true,true,5⟩, some ⟨true,false,4⟩, none, some ⟨true,false,5⟩, some ⟨true,false,2⟩, some ⟨false,false,5⟩]
def r6_schedule : List (Nat × Slot) := [(1,(1,false)), (2,(2,false)), (3,(3,true)), (4,(4,true)), (5,(5,false)), (7,(3,false)), (9,(2,true)), (10,(0,true)), (19,(5,true)), (62,(1,true))]
theorem r6_path : FirstHolePath (forgetHaltRows r6) 6 :=
  checked_from_root _ r6_schedule (by decide)
theorem r6_parent : compatible p23 r6 :=
  (parentCheck_iff _ _).mp (by decide)
theorem r6_leaf_parent : ∀ m, compatible (forgetHaltRows r6) m → compatible p23 m :=
  leaf_extends_parent _ _ (ordinaryParentCheck_sound _ (by decide)) r6_parent
theorem r6_cover_iff (B : Nat) :
    Cover (WeightedBound B) (forgetHaltRows r6) ↔
      ∀ k, HaltsAfter r6 k → k+1+0 ≤ B :=
  cover_iff_of_checks r6 (4,false) [0] 0 B (by decide) (by decide)
    (by decide) (by simp)
#print axioms r6_path
#print axioms r6_parent
#print axioms r6_leaf_parent
#print axioms r6_cover_iff

/-- A6 branches from raw139 before the champion's long path. -/
def a6Sibling : PartialMachine := refine p139 (3,true) (some ⟨false,false,2⟩)
theorem A6_sibling : ∀ m, compatible (forgetHaltRows A6) m → compatible a6Sibling m :=
  leaf_extends_parent _ _ (ordinaryParentCheck_sound _ (by decide))
    ((parentCheck_iff _ _).mp (by decide))

def A6_certificate (B : Nat) (h : NeverHalts A6) :
    WeightedTNFCertificate B (forgetHaltRows A6) 6 :=
  forgetHaltRows_nonhaltCertificate B A6 (by decide) h

theorem A6_cover (B : Nat) (h : NeverHalts A6) :
    Cover (WeightedBound B) (forgetHaltRows A6) := (A6_certificate B h).toCover

#print axioms A6_sibling
#print axioms A6_certificate
#print axioms A6_cover
end BB6.Agent19HardRoot
