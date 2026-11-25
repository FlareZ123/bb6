import Raw118M2869Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxSize 100000
namespace BB6Coverage.Agent1Raw118M2869

def before : Frame → Bool
  | .a | .s => false
  | .b | .d | .e => true
  | .c => false
def after : Frame → Bool
  | .a | .d | .e | .s => true
  | .b | .c => false

def LMeta (l : LI) (f : Frame) : Prop :=
  pushL l f ≠ 0 → phaseL l = before f ∧ phaseL (pushL l f) = after f ∧
    topL (pushL l f) = frameCode f + 1 ∧ pushL l f ≠ 1 ∧ (f = .d → topL l = 1)
instance (l : LI) (f : Frame) : Decidable (LMeta l f) := by unfold LMeta; infer_instance

theorem lmeta (l : LI) (f : Frame) : LMeta l f := by
  cases f <;> exact (by decide : ∀ l : LI, LMeta l _) l

def RMeta (r : RI) (t : Tok) : Prop :=
  pushR r t ≠ 0 → pushR r t ≠ 1 ∧ (t = .u ∨ t = .v → r = 1)
instance (r : RI) (t : Tok) : Decidable (RMeta r t) := by unfold RMeta; infer_instance

theorem rmeta (r : RI) (t : Tok) : RMeta r t := by
  cases t <;> exact (by decide : ∀ r : RI, RMeta r _) r

def Rules (l : LI) (r : RI) : Prop :=
  (phaseL l = false → Safe false l (pushR r .x) → Safe false (pushL l .a) r) ∧
  (phaseL l = true → Safe false l (pushR r .x) → Safe false (pushL l .b) r) ∧
  (phaseL l = false → Safe false l (pushR r .y) → Safe false (pushL l .c) r) ∧
  (phaseL l = true → Safe false l (pushR r .y) → Safe false (pushL l .d) r) ∧
  (phaseL l = false → Safe false l (pushR r .z) → Safe true l (pushR (pushR r .y) .x)) ∧
  (phaseL l = true → Safe false l (pushR r .z) → Safe false (pushL l .e) r) ∧
  (phaseL l = false → Safe false l 1 → Safe true l (pushR 1 .x)) ∧
  (phaseL l = true → Safe false l 1 → Safe true l (pushR 1 .v)) ∧
  (phaseL l = false → Safe false l (pushR 1 .v) → Safe true l (pushR (pushR 1 .u) .x)) ∧
  (phaseL l = true → Safe false l (pushR 1 .v) → Safe true l (pushR 1 .z)) ∧
  (Safe false (pushL l .a) (pushR 1 .u) → Safe false (pushL l .s) 1) ∧
  (Safe false l (pushR 1 .u) → topL l = 1) ∧
  (Safe true (pushL l .a) r → Safe true l (pushR r .x)) ∧
  (Safe true (pushL l .b) r → Safe true l (pushR r .x)) ∧
  (Safe true (pushL l .c) r → Safe true l (pushR r .y)) ∧
  (Safe true (pushL l .e) r → Safe true l (pushR r .z)) ∧
  (Safe true (pushL l .s) r → Safe true l (pushR r .z)) ∧
  (Safe true (pushL (pushL l .a) .d) r → Safe false (pushL l .s) r) ∧
  (Safe true 1 r → Safe false 1 (pushR r .x))
instance (l : LI) (r : RI) : Decidable (Rules l r) := by unfold Rules; infer_instance

-- Each row checks all right-tail summaries, with no trust in the discovery program.
def row (l : LI) : Bool := (List.finRange 94).all (fun r => decide (Rules l r))
theorem row0 : row 0 = true := by rfl
theorem row1 : row 1 = true := by rfl
theorem row2 : row 2 = true := by rfl
theorem row3 : row 3 = true := by rfl
theorem row4 : row 4 = true := by rfl
theorem row5 : row 5 = true := by rfl
theorem row6 : row 6 = true := by rfl
theorem row7 : row 7 = true := by rfl
theorem row8 : row 8 = true := by rfl
theorem row9 : row 9 = true := by rfl
theorem row10 : row 10 = true := by rfl
theorem row11 : row 11 = true := by rfl
theorem row12 : row 12 = true := by rfl
theorem row13 : row 13 = true := by rfl
theorem row14 : row 14 = true := by rfl
theorem row15 : row 15 = true := by rfl
theorem row16 : row 16 = true := by rfl
theorem row17 : row 17 = true := by rfl
theorem row18 : row 18 = true := by rfl
theorem row19 : row 19 = true := by rfl
theorem row20 : row 20 = true := by rfl
theorem row21 : row 21 = true := by rfl
theorem row22 : row 22 = true := by rfl
theorem row23 : row 23 = true := by rfl
theorem row24 : row 24 = true := by rfl
theorem row25 : row 25 = true := by rfl
theorem rows (l : LI) : row l = true := by
  have h := (by decide : ∀ l : LI, l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5 ∨ l = 6 ∨ l = 7 ∨ l = 8 ∨ l = 9 ∨ l = 10 ∨ l = 11 ∨ l = 12 ∨ l = 13 ∨ l = 14 ∨ l = 15 ∨ l = 16 ∨ l = 17 ∨ l = 18 ∨ l = 19 ∨ l = 20 ∨ l = 21 ∨ l = 22 ∨ l = 23 ∨ l = 24 ∨ l = 25) l
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row0
  · exact row1
  · exact row2
  · exact row3
  · exact row4
  · exact row5
  · exact row6
  · exact row7
  · exact row8
  · exact row9
  · exact row10
  · exact row11
  · exact row12
  · exact row13
  · exact row14
  · exact row15
  · exact row16
  · exact row17
  · exact row18
  · exact row19
  · exact row20
  · exact row21
  · exact row22
  · exact row23
  · exact row24
  · exact row25
theorem rulesOK (l : LI) (r : RI) : Rules l r := by
  have h := List.all_eq_true.mp (rows l) r (List.mem_finRange r)
  exact of_decide_eq_true h

structure Facts (l : LI) (r : RI) : Prop where
  fxP : phaseL l = false → Safe false l (pushR r .x) → Safe false (pushL l .a) r
  fxQ : phaseL l = true → Safe false l (pushR r .x) → Safe false (pushL l .b) r
  fyP : phaseL l = false → Safe false l (pushR r .y) → Safe false (pushL l .c) r
  fyQ : phaseL l = true → Safe false l (pushR r .y) → Safe false (pushL l .d) r
  fzP : phaseL l = false → Safe false l (pushR r .z) → Safe true l (pushR (pushR r .y) .x)
  fzQ : phaseL l = true → Safe false l (pushR r .z) → Safe false (pushL l .e) r
  feP : phaseL l = false → Safe false l 1 → Safe true l (pushR 1 .x)
  feQ : phaseL l = true → Safe false l 1 → Safe true l (pushR 1 .v)
  fvP : phaseL l = false → Safe false l (pushR 1 .v) → Safe true l (pushR (pushR 1 .u) .x)
  fvQ : phaseL l = true → Safe false l (pushR 1 .v) → Safe true l (pushR 1 .z)
  fu : Safe false (pushL l .a) (pushR 1 .u) → Safe false (pushL l .s) 1
  fuShape : Safe false l (pushR 1 .u) → topL l = 1
  ba : Safe true (pushL l .a) r → Safe true l (pushR r .x)
  bb : Safe true (pushL l .b) r → Safe true l (pushR r .x)
  bc : Safe true (pushL l .c) r → Safe true l (pushR r .y)
  be : Safe true (pushL l .e) r → Safe true l (pushR r .z)
  bs : Safe true (pushL l .s) r → Safe true l (pushR r .z)
  bd : Safe true (pushL (pushL l .a) .d) r → Safe false (pushL l .s) r
  base : Safe true 1 r → Safe false 1 (pushR r .x)
theorem facts (l : LI) (r : RI) : Facts l r := by
  rcases rulesOK l r with ⟨fxP, fxQ, fyP, fyQ, fzP, fzQ, feP, feQ, fvP, fvQ, fu, fuShape, ba, bb, bc, be, bs, bd, base⟩
  exact ⟨fxP, fxQ, fyP, fyQ, fzP, fzQ, feP, feQ, fvP, fvQ, fu, fuShape, ba, bb, bc, be, bs, bd, base⟩

#print axioms facts
end BB6Coverage.Agent1Raw118M2869
