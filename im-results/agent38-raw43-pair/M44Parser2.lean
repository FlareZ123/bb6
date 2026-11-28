import M44Actions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace BB6.Agent38M44
open BB6Coverage BB6Coverage.Agent31Pump

-- Finite check, with proof of access through the explicit bounded list.
def progressCheck (q b : Nat) : Bool :=
  match action q b with
  | none => true
  | some a => decide (a.q<14 ∧ (0 < a.cost ∨ rank a.q < rank q))

theorem progressChecked : (List.range 14).all (fun q => (List.range 18).all (progressCheck q)) = true := by decide

theorem action_progress (q b : Nat) (a : Act) (hq : q<14) (hb : b≤17)
    (h : action q b = some a) : a.q<14 ∧ (0 < a.cost ∨ rank a.q < rank q) := by
  have H := (List.all_eq_true.mp progressChecked) q (List.mem_range.mpr hq)
  have hb' : b < 18 := by omega
  have H2 := (List.all_eq_true.mp H) b (List.mem_range.mpr hb')
  simpa [progressCheck,h] using H2

-- The only exceptional padding operations consume implicit or explicit blank zeros.
theorem f3_padding (L : List Bool) (z : Nat) :
    run0 table 12 ⟨5,bits "11"++L,bits "10"++List.replicate z false⟩ =
      some ⟨0,bits "1110"++L,bits "101"++List.replicate (z-3) false⟩ := by
  cases z with
  | zero => rfl
  | succ z => cases z with
    | zero => rfl
    | succ z => cases z with
      | zero => rfl
      | succ z => exact f3 L (List.replicate z false)

theorem f14_padding (L : List Bool) (z : Nat) :
    run0 table 15 ⟨5,bits "11"++L,bits "1001"++List.replicate z false⟩ =
      some ⟨0,bits "1111110"++L,bits "101"++List.replicate (z-4) false⟩ := by
  cases z with
  | zero => rfl
  | succ z => cases z with
    | zero => rfl
    | succ z => cases z with
      | zero => rfl
      | succ z => cases z with
        | zero => rfl
        | succ z => exact f14 L (List.replicate z false)


theorem semantic0 (b : Nat) (a : Act) (hb : b≤17)
    (h : action 0 b = some a) (s d : List Nat) (j z : Nat)
    (he : endOK 0 b s d) (hw : well 0 (beforeL 0 b s)) :
    run0 table (cost a j) (interpret 0 (beforeL 0 b s) (beforeR 0 b d) j z) =
      some (interpret a.q (a.l++s) (a.r++d) (j+a.inc) (padNext a.pad z)) := by
  have hb' : b=0 ∨ b=1 ∨ b=2 ∨ b=3 ∨ b=4 ∨ b=5 ∨ b=6 ∨ b=7 ∨ b=8 ∨ b=9 ∨ b=10 ∨ b=11 ∨ b=12 ∨ b=13 ∨ b=14 ∨ b=15 ∨ b=16 ∨ b=17 := by omega
  rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  -- token 0
  · change some (⟨0,[0],[],7,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 1
  · change some (⟨1,[],[],0,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 2
  · change some (⟨2,[],[],0,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 3
  · change some (⟨10,[2],[0],12,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 4
  · change some (⟨10,[2],[1],12,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 5
  · change some (⟨10,[2],[2],12,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 6
  · change some (⟨10,[2],[3],12,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 7
  · change some (⟨10,[2],[4],12,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 8
  · change some (⟨10,[2],[5],12,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 9
  · change some (⟨10,[2],[6],12,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 10
  · change some (⟨10,[2],[7],12,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 11
  · change some (⟨10,[2],[8],12,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 12
  · change some (⟨10,[2],[9],12,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 13
  · change some (⟨10,[2],[10],12,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 14
  · change some (⟨10,[2],[11],12,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 15
  · change some (⟨10,[2],[12],12,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 16
  · change some (⟨10,[2],[13],12,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 17
  · change some (⟨10,[2],[],12,0,1,0⟩ : Act) = some a at h
    cases h
    have he' : d = [] := he rfl
    subst d
    simp only [cost,Nat.zero_mul,Nat.add_zero]
    exact f3_padding (stackL s ++ base j) z

theorem semantic1 (b : Nat) (a : Act) (hb : b≤17)
    (h : action 1 b = some a) (s d : List Nat) (j z : Nat)
    (he : endOK 1 b s d) (hw : well 1 (beforeL 1 b s)) :
    run0 table (cost a j) (interpret 1 (beforeL 1 b s) (beforeR 1 b d) j z) =
      some (interpret a.q (a.l++s) (a.r++d) (j+a.inc) (padNext a.pad z)) := by
  have hb' : b=0 ∨ b=1 ∨ b=2 ∨ b=3 ∨ b=4 ∨ b=5 ∨ b=6 ∨ b=7 ∨ b=8 ∨ b=9 ∨ b=10 ∨ b=11 ∨ b=12 ∨ b=13 ∨ b=14 ∨ b=15 ∨ b=16 ∨ b=17 := by omega
  rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  -- token 0
  · change some (⟨3,[],[],0,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 1
  · change some (⟨0,[3],[],10,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 2
  · change some (⟨4,[],[],0,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 3
  · change some (⟨5,[],[],0,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 4
  · change some (⟨10,[5],[0],15,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 5
  · change some (⟨10,[5],[1],15,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 6
  · change some (⟨10,[5],[2],15,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 7
  · change some (⟨10,[5],[3],15,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 8
  · change some (⟨10,[5],[4],15,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 9
  · change some (⟨10,[5],[5],15,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 10
  · change some (⟨10,[5],[6],15,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 11
  · change some (⟨10,[5],[7],15,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 12
  · change some (⟨10,[5],[8],15,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 13
  · change some (⟨10,[5],[9],15,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 14
  · change some (⟨10,[5],[10],15,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 15
  · change some (⟨10,[5],[11],15,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 16
  · change some (⟨10,[5],[12],15,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 17
  · change some (⟨10,[5],[],15,0,2,0⟩ : Act) = some a at h
    cases h
    have he' : d = [] := he rfl
    subst d
    simp only [cost,Nat.zero_mul,Nat.add_zero]
    exact f14_padding (stackL s ++ base j) z

theorem semantic2 (b : Nat) (a : Act) (hb : b≤17)
    (h : action 2 b = some a) (s d : List Nat) (j z : Nat)
    (he : endOK 2 b s d) (hw : well 2 (beforeL 2 b s)) :
    run0 table (cost a j) (interpret 2 (beforeL 2 b s) (beforeR 2 b d) j z) =
      some (interpret a.q (a.l++s) (a.r++d) (j+a.inc) (padNext a.pad z)) := by
  have hb' : b=0 ∨ b=1 ∨ b=2 ∨ b=3 ∨ b=4 ∨ b=5 ∨ b=6 ∨ b=7 ∨ b=8 ∨ b=9 ∨ b=10 ∨ b=11 ∨ b=12 ∨ b=13 ∨ b=14 ∨ b=15 ∨ b=16 ∨ b=17 := by omega
  rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  -- token 0
  · change none = some a at h
    cases h
  -- token 1
  · change some (⟨8,[],[],0,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 2
  · change none = some a at h
    cases h
  -- token 3
  · change none = some a at h
    cases h
  -- token 4
  · change none = some a at h
    cases h
  -- token 5
  · change none = some a at h
    cases h
  -- token 6
  · change none = some a at h
    cases h
  -- token 7
  · change none = some a at h
    cases h
  -- token 8
  · change none = some a at h
    cases h
  -- token 9
  · change none = some a at h
    cases h
  -- token 10
  · change none = some a at h
    cases h
  -- token 11
  · change none = some a at h
    cases h
  -- token 12
  · change none = some a at h
    cases h
  -- token 13
  · change none = some a at h
    cases h
  -- token 14
  · change none = some a at h
    cases h
  -- token 15
  · change none = some a at h
    cases h
  -- token 16
  · change none = some a at h
    cases h
  -- token 17
  · change none = some a at h
    cases h

theorem semantic3 (b : Nat) (a : Act) (hb : b≤17)
    (h : action 3 b = some a) (s d : List Nat) (j z : Nat)
    (he : endOK 3 b s d) (hw : well 3 (beforeL 3 b s)) :
    run0 table (cost a j) (interpret 3 (beforeL 3 b s) (beforeR 3 b d) j z) =
      some (interpret a.q (a.l++s) (a.r++d) (j+a.inc) (padNext a.pad z)) := by
  have hb' : b=0 ∨ b=1 ∨ b=2 ∨ b=3 ∨ b=4 ∨ b=5 ∨ b=6 ∨ b=7 ∨ b=8 ∨ b=9 ∨ b=10 ∨ b=11 ∨ b=12 ∨ b=13 ∨ b=14 ∨ b=15 ∨ b=16 ∨ b=17 := by omega
  rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  -- token 0
  · change some (⟨10,[],[3],21,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 1
  · change some (⟨10,[],[4],21,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 2
  · change some (⟨10,[],[5],21,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 3
  · change some (⟨10,[],[6],21,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 4
  · change some (⟨10,[],[7],21,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 5
  · change some (⟨10,[],[8],21,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 6
  · change some (⟨10,[],[9],21,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 7
  · change some (⟨10,[],[10],21,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 8
  · change some (⟨10,[],[11],21,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 9
  · change some (⟨10,[],[12],21,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 10
  · change some (⟨10,[],[13],21,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 11
  · change some (⟨10,[],[14],21,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 12
  · change some (⟨10,[],[15],21,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 13
  · change some (⟨10,[],[16],21,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 14
  · change none = some a at h
    cases h
  -- token 15
  · change none = some a at h
    cases h
  -- token 16
  · change none = some a at h
    cases h
  -- token 17
  · change some (⟨10,[],[],21,0,3,0⟩ : Act) = some a at h
    cases h
    have he' : d = [] := he rfl
    subst d
    simp only [cost,Nat.zero_mul,Nat.add_zero]
    exact f10 (stackL s++base j) (List.replicate z false)

theorem semantic4 (b : Nat) (a : Act) (hb : b≤17)
    (h : action 4 b = some a) (s d : List Nat) (j z : Nat)
    (he : endOK 4 b s d) (hw : well 4 (beforeL 4 b s)) :
    run0 table (cost a j) (interpret 4 (beforeL 4 b s) (beforeR 4 b d) j z) =
      some (interpret a.q (a.l++s) (a.r++d) (j+a.inc) (padNext a.pad z)) := by
  have hb' : b=0 ∨ b=1 ∨ b=2 ∨ b=3 ∨ b=4 ∨ b=5 ∨ b=6 ∨ b=7 ∨ b=8 ∨ b=9 ∨ b=10 ∨ b=11 ∨ b=12 ∨ b=13 ∨ b=14 ∨ b=15 ∨ b=16 ∨ b=17 := by omega
  rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  -- token 0
  · change none = some a at h
    cases h
  -- token 1
  · change some (⟨0,[6],[],13,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 2
  · change none = some a at h
    cases h
  -- token 3
  · change none = some a at h
    cases h
  -- token 4
  · change none = some a at h
    cases h
  -- token 5
  · change none = some a at h
    cases h
  -- token 6
  · change none = some a at h
    cases h
  -- token 7
  · change none = some a at h
    cases h
  -- token 8
  · change none = some a at h
    cases h
  -- token 9
  · change none = some a at h
    cases h
  -- token 10
  · change none = some a at h
    cases h
  -- token 11
  · change none = some a at h
    cases h
  -- token 12
  · change none = some a at h
    cases h
  -- token 13
  · change none = some a at h
    cases h
  -- token 14
  · change none = some a at h
    cases h
  -- token 15
  · change none = some a at h
    cases h
  -- token 16
  · change none = some a at h
    cases h
  -- token 17
  · change none = some a at h
    cases h

theorem semantic5 (b : Nat) (a : Act) (hb : b≤17)
    (h : action 5 b = some a) (s d : List Nat) (j z : Nat)
    (he : endOK 5 b s d) (hw : well 5 (beforeL 5 b s)) :
    run0 table (cost a j) (interpret 5 (beforeL 5 b s) (beforeR 5 b d) j z) =
      some (interpret a.q (a.l++s) (a.r++d) (j+a.inc) (padNext a.pad z)) := by
  have hb' : b=0 ∨ b=1 ∨ b=2 ∨ b=3 ∨ b=4 ∨ b=5 ∨ b=6 ∨ b=7 ∨ b=8 ∨ b=9 ∨ b=10 ∨ b=11 ∨ b=12 ∨ b=13 ∨ b=14 ∨ b=15 ∨ b=16 ∨ b=17 := by omega
  rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  -- token 0
  · change none = some a at h
    cases h
  -- token 1
  · change some (⟨6,[],[],0,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 2
  · change none = some a at h
    cases h
  -- token 3
  · change none = some a at h
    cases h
  -- token 4
  · change none = some a at h
    cases h
  -- token 5
  · change none = some a at h
    cases h
  -- token 6
  · change none = some a at h
    cases h
  -- token 7
  · change none = some a at h
    cases h
  -- token 8
  · change none = some a at h
    cases h
  -- token 9
  · change none = some a at h
    cases h
  -- token 10
  · change none = some a at h
    cases h
  -- token 11
  · change none = some a at h
    cases h
  -- token 12
  · change none = some a at h
    cases h
  -- token 13
  · change none = some a at h
    cases h
  -- token 14
  · change none = some a at h
    cases h
  -- token 15
  · change none = some a at h
    cases h
  -- token 16
  · change none = some a at h
    cases h
  -- token 17
  · change none = some a at h
    cases h

theorem semantic6 (b : Nat) (a : Act) (hb : b≤17)
    (h : action 6 b = some a) (s d : List Nat) (j z : Nat)
    (he : endOK 6 b s d) (hw : well 6 (beforeL 6 b s)) :
    run0 table (cost a j) (interpret 6 (beforeL 6 b s) (beforeR 6 b d) j z) =
      some (interpret a.q (a.l++s) (a.r++d) (j+a.inc) (padNext a.pad z)) := by
  have hb' : b=0 ∨ b=1 ∨ b=2 ∨ b=3 ∨ b=4 ∨ b=5 ∨ b=6 ∨ b=7 ∨ b=8 ∨ b=9 ∨ b=10 ∨ b=11 ∨ b=12 ∨ b=13 ∨ b=14 ∨ b=15 ∨ b=16 ∨ b=17 := by omega
  rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  -- token 0
  · change none = some a at h
    cases h
  -- token 1
  · change none = some a at h
    cases h
  -- token 2
  · change some (⟨7,[],[],0,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 3
  · change none = some a at h
    cases h
  -- token 4
  · change none = some a at h
    cases h
  -- token 5
  · change none = some a at h
    cases h
  -- token 6
  · change none = some a at h
    cases h
  -- token 7
  · change none = some a at h
    cases h
  -- token 8
  · change none = some a at h
    cases h
  -- token 9
  · change none = some a at h
    cases h
  -- token 10
  · change none = some a at h
    cases h
  -- token 11
  · change none = some a at h
    cases h
  -- token 12
  · change none = some a at h
    cases h
  -- token 13
  · change none = some a at h
    cases h
  -- token 14
  · change none = some a at h
    cases h
  -- token 15
  · change none = some a at h
    cases h
  -- token 16
  · change none = some a at h
    cases h
  -- token 17
  · change none = some a at h
    cases h

theorem semantic7 (b : Nat) (a : Act) (hb : b≤17)
    (h : action 7 b = some a) (s d : List Nat) (j z : Nat)
    (he : endOK 7 b s d) (hw : well 7 (beforeL 7 b s)) :
    run0 table (cost a j) (interpret 7 (beforeL 7 b s) (beforeR 7 b d) j z) =
      some (interpret a.q (a.l++s) (a.r++d) (j+a.inc) (padNext a.pad z)) := by
  have hb' : b=0 ∨ b=1 ∨ b=2 ∨ b=3 ∨ b=4 ∨ b=5 ∨ b=6 ∨ b=7 ∨ b=8 ∨ b=9 ∨ b=10 ∨ b=11 ∨ b=12 ∨ b=13 ∨ b=14 ∨ b=15 ∨ b=16 ∨ b=17 := by omega
  rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  -- token 0
  · change none = some a at h
    cases h
  -- token 1
  · change some (⟨0,[3,0,7],[],19,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 2
  · change none = some a at h
    cases h
  -- token 3
  · change none = some a at h
    cases h
  -- token 4
  · change none = some a at h
    cases h
  -- token 5
  · change none = some a at h
    cases h
  -- token 6
  · change none = some a at h
    cases h
  -- token 7
  · change none = some a at h
    cases h
  -- token 8
  · change none = some a at h
    cases h
  -- token 9
  · change none = some a at h
    cases h
  -- token 10
  · change none = some a at h
    cases h
  -- token 11
  · change none = some a at h
    cases h
  -- token 12
  · change none = some a at h
    cases h
  -- token 13
  · change none = some a at h
    cases h
  -- token 14
  · change none = some a at h
    cases h
  -- token 15
  · change none = some a at h
    cases h
  -- token 16
  · change none = some a at h
    cases h
  -- token 17
  · change none = some a at h
    cases h

theorem semantic8 (b : Nat) (a : Act) (hb : b≤17)
    (h : action 8 b = some a) (s d : List Nat) (j z : Nat)
    (he : endOK 8 b s d) (hw : well 8 (beforeL 8 b s)) :
    run0 table (cost a j) (interpret 8 (beforeL 8 b s) (beforeR 8 b d) j z) =
      some (interpret a.q (a.l++s) (a.r++d) (j+a.inc) (padNext a.pad z)) := by
  have hb' : b=0 ∨ b=1 ∨ b=2 ∨ b=3 ∨ b=4 ∨ b=5 ∨ b=6 ∨ b=7 ∨ b=8 ∨ b=9 ∨ b=10 ∨ b=11 ∨ b=12 ∨ b=13 ∨ b=14 ∨ b=15 ∨ b=16 ∨ b=17 := by omega
  rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  -- token 0
  · change some (⟨0,[5],[],28,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 1
  · change some (⟨0,[0,0,4],[],13,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 2
  · change some (⟨9,[],[],0,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 3
  · change none = some a at h
    cases h
  -- token 4
  · change none = some a at h
    cases h
  -- token 5
  · change none = some a at h
    cases h
  -- token 6
  · change none = some a at h
    cases h
  -- token 7
  · change none = some a at h
    cases h
  -- token 8
  · change none = some a at h
    cases h
  -- token 9
  · change none = some a at h
    cases h
  -- token 10
  · change none = some a at h
    cases h
  -- token 11
  · change none = some a at h
    cases h
  -- token 12
  · change none = some a at h
    cases h
  -- token 13
  · change none = some a at h
    cases h
  -- token 14
  · change none = some a at h
    cases h
  -- token 15
  · change none = some a at h
    cases h
  -- token 16
  · change none = some a at h
    cases h
  -- token 17
  · change none = some a at h
    cases h

theorem semantic9 (b : Nat) (a : Act) (hb : b≤17)
    (h : action 9 b = some a) (s d : List Nat) (j z : Nat)
    (he : endOK 9 b s d) (hw : well 9 (beforeL 9 b s)) :
    run0 table (cost a j) (interpret 9 (beforeL 9 b s) (beforeR 9 b d) j z) =
      some (interpret a.q (a.l++s) (a.r++d) (j+a.inc) (padNext a.pad z)) := by
  have hb' : b=0 ∨ b=1 ∨ b=2 ∨ b=3 ∨ b=4 ∨ b=5 ∨ b=6 ∨ b=7 ∨ b=8 ∨ b=9 ∨ b=10 ∨ b=11 ∨ b=12 ∨ b=13 ∨ b=14 ∨ b=15 ∨ b=16 ∨ b=17 := by omega
  rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  -- token 0
  · change none = some a at h
    cases h
  -- token 1
  · change some (⟨0,[3,0,4],[],16,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 2
  · change none = some a at h
    cases h
  -- token 3
  · change none = some a at h
    cases h
  -- token 4
  · change none = some a at h
    cases h
  -- token 5
  · change none = some a at h
    cases h
  -- token 6
  · change none = some a at h
    cases h
  -- token 7
  · change none = some a at h
    cases h
  -- token 8
  · change none = some a at h
    cases h
  -- token 9
  · change none = some a at h
    cases h
  -- token 10
  · change none = some a at h
    cases h
  -- token 11
  · change none = some a at h
    cases h
  -- token 12
  · change none = some a at h
    cases h
  -- token 13
  · change none = some a at h
    cases h
  -- token 14
  · change none = some a at h
    cases h
  -- token 15
  · change none = some a at h
    cases h
  -- token 16
  · change none = some a at h
    cases h
  -- token 17
  · change none = some a at h
    cases h

theorem semantic10 (b : Nat) (a : Act) (hb : b≤17)
    (h : action 10 b = some a) (s d : List Nat) (j z : Nat)
    (he : endOK 10 b s d) (hw : well 10 (beforeL 10 b s)) :
    run0 table (cost a j) (interpret 10 (beforeL 10 b s) (beforeR 10 b d) j z) =
      some (interpret a.q (a.l++s) (a.r++d) (j+a.inc) (padNext a.pad z)) := by
  have hb' : b=0 ∨ b=1 ∨ b=2 ∨ b=3 ∨ b=4 ∨ b=5 ∨ b=6 ∨ b=7 ∨ b=8 ∨ b=9 ∨ b=10 ∨ b=11 ∨ b=12 ∨ b=13 ∨ b=14 ∨ b=15 ∨ b=16 ∨ b=17 := by omega
  rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  -- token 0
  · change some (⟨11,[],[],0,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 1
  · change none = some a at h
    cases h
  -- token 2
  · change some (⟨10,[],[0,1],11,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 3
  · change some (⟨10,[],[1,1],12,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 4
  · change some (⟨10,[],[2,1],13,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 5
  · change some (⟨10,[],[3,1],14,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 6
  · change some (⟨10,[],[4,1],15,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 7
  · change some (⟨10,[],[5,1],16,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 8
  · change some (⟨10,[],[6,1],17,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 9
  · change some (⟨10,[],[7,1],18,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 10
  · change some (⟨10,[],[8,1],19,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 11
  · change some (⟨10,[],[9,1],20,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 12
  · change some (⟨10,[],[10,1],21,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 13
  · change some (⟨10,[],[11,1],22,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 14
  · change some (⟨10,[],[12,1],23,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 15
  · change some (⟨10,[],[13,1],24,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 16
  · change some (⟨10,[],[14,1],25,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 17
  · change some (⟨12,[],[],0,0,0,0⟩ : Act) = some a at h
    cases h
    have he' : s = [] := he rfl
    subst s
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl

theorem semantic11 (b : Nat) (a : Act) (hb : b≤17)
    (h : action 11 b = some a) (s d : List Nat) (j z : Nat)
    (he : endOK 11 b s d) (hw : well 11 (beforeL 11 b s)) :
    run0 table (cost a j) (interpret 11 (beforeL 11 b s) (beforeR 11 b d) j z) =
      some (interpret a.q (a.l++s) (a.r++d) (j+a.inc) (padNext a.pad z)) := by
  have hb' : b=0 ∨ b=1 ∨ b=2 ∨ b=3 ∨ b=4 ∨ b=5 ∨ b=6 ∨ b=7 ∨ b=8 ∨ b=9 ∨ b=10 ∨ b=11 ∨ b=12 ∨ b=13 ∨ b=14 ∨ b=15 ∨ b=16 ∨ b=17 := by omega
  rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  -- token 0
  · change some (⟨0,[1],[],7,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 1
  · change some (⟨0,[2],[],7,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 2
  · change some (⟨0,[3],[],7,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 3
  · change some (⟨0,[4],[],7,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 4
  · change some (⟨0,[5],[],7,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 5
  · change some (⟨0,[6],[],7,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 6
  · change some (⟨0,[7],[],7,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 7
  · change some (⟨0,[8],[],7,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 8
  · change some (⟨0,[9],[],7,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 9
  · change some (⟨0,[10],[],7,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 10
  · change some (⟨0,[11],[],7,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 11
  · change some (⟨0,[12],[],7,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 12
  · change some (⟨0,[13],[],7,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 13
  · change some (⟨0,[14],[],7,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 14
  · change some (⟨0,[15],[],7,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 15
  · change some (⟨0,[16],[],7,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 16
  · change none = some a at h
    cases h
  -- token 17
  · change none = some a at h
    cases h

theorem semantic12 (b : Nat) (a : Act) (hb : b≤17)
    (h : action 12 b = some a) (s d : List Nat) (j z : Nat)
    (he : endOK 12 b s d) (hw : well 12 (beforeL 12 b s)) :
    run0 table (cost a j) (interpret 12 (beforeL 12 b s) (beforeR 12 b d) j z) =
      some (interpret a.q (a.l++s) (a.r++d) (j+a.inc) (padNext a.pad z)) := by
  have hb' : b=0 ∨ b=1 ∨ b=2 ∨ b=3 ∨ b=4 ∨ b=5 ∨ b=6 ∨ b=7 ∨ b=8 ∨ b=9 ∨ b=10 ∨ b=11 ∨ b=12 ∨ b=13 ∨ b=14 ∨ b=15 ∨ b=16 ∨ b=17 := by omega
  rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  -- token 0
  · change none = some a at h
    cases h
  -- token 1
  · change none = some a at h
    cases h
  -- token 2
  · change none = some a at h
    cases h
  -- token 3
  · change none = some a at h
    cases h
  -- token 4
  · change none = some a at h
    cases h
  -- token 5
  · change none = some a at h
    cases h
  -- token 6
  · change some (⟨13,[],[],0,0,0,0⟩ : Act) = some a at h
    cases h
    simp only [cost,Nat.zero_mul,Nat.add_zero,interpret,beforeL,beforeR,isLeft,putBack,padNext,rawF,rawA,stackL_append,stackR_append,List.append_assoc,List.nil_append]
    try rfl
  -- token 7
  · change none = some a at h
    cases h
  -- token 8
  · change none = some a at h
    cases h
  -- token 9
  · change none = some a at h
    cases h
  -- token 10
  · change none = some a at h
    cases h
  -- token 11
  · change none = some a at h
    cases h
  -- token 12
  · change none = some a at h
    cases h
  -- token 13
  · change none = some a at h
    cases h
  -- token 14
  · change none = some a at h
    cases h
  -- token 15
  · change none = some a at h
    cases h
  -- token 16
  · change none = some a at h
    cases h
  -- token 17
  · change none = some a at h
    cases h

theorem semantic13 (b : Nat) (a : Act) (hb : b≤17)
    (h : action 13 b = some a) (s d : List Nat) (j z : Nat)
    (he : endOK 13 b s d) (hw : well 13 (beforeL 13 b s)) :
    run0 table (cost a j) (interpret 13 (beforeL 13 b s) (beforeR 13 b d) j z) =
      some (interpret a.q (a.l++s) (a.r++d) (j+a.inc) (padNext a.pad z)) := by
  have hb' : b=0 ∨ b=1 ∨ b=2 ∨ b=3 ∨ b=4 ∨ b=5 ∨ b=6 ∨ b=7 ∨ b=8 ∨ b=9 ∨ b=10 ∨ b=11 ∨ b=12 ∨ b=13 ∨ b=14 ∨ b=15 ∨ b=16 ∨ b=17 := by omega
  rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  -- token 0
  · change none = some a at h
    cases h
  -- token 1
  · change some (⟨0,[3,0,7],[],576,44,0,2⟩ : Act) = some a at h
    cases h
    have hs : s = [] := hw (Or.inr rfl)
    subst s
    have H := reset j (stackR d ++ List.replicate z false)
    have hc : 576+44*j = 12*j+21+(294+22*j)+(222+10*((j+1)+1))+19 := by omega
    change run0 table (576+44*j) _ = _
    rw [hc]
    exact H
  -- token 2
  · change none = some a at h
    cases h
  -- token 3
  · change none = some a at h
    cases h
  -- token 4
  · change none = some a at h
    cases h
  -- token 5
  · change none = some a at h
    cases h
  -- token 6
  · change none = some a at h
    cases h
  -- token 7
  · change none = some a at h
    cases h
  -- token 8
  · change none = some a at h
    cases h
  -- token 9
  · change none = some a at h
    cases h
  -- token 10
  · change none = some a at h
    cases h
  -- token 11
  · change none = some a at h
    cases h
  -- token 12
  · change none = some a at h
    cases h
  -- token 13
  · change none = some a at h
    cases h
  -- token 14
  · change none = some a at h
    cases h
  -- token 15
  · change none = some a at h
    cases h
  -- token 16
  · change none = some a at h
    cases h
  -- token 17
  · change none = some a at h
    cases h

theorem action_semantics (q b : Nat) (a : Act) (hq : q<14) (hb : b≤17)
    (h : action q b = some a) (s d : List Nat) (j z : Nat)
    (he : endOK q b s d) (hw : well q (beforeL q b s)) :
    run0 table (cost a j) (interpret q (beforeL q b s) (beforeR q b d) j z) =
      some (interpret a.q (a.l++s) (a.r++d) (j+a.inc) (padNext a.pad z)) := by
  have hq' : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 ∨ q=6 ∨ q=7 ∨ q=8 ∨ q=9 ∨ q=10 ∨ q=11 ∨ q=12 ∨ q=13 := by omega
  rcases hq' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact semantic0 b a hb h s d j z he hw
  · exact semantic1 b a hb h s d j z he hw
  · exact semantic2 b a hb h s d j z he hw
  · exact semantic3 b a hb h s d j z he hw
  · exact semantic4 b a hb h s d j z he hw
  · exact semantic5 b a hb h s d j z he hw
  · exact semantic6 b a hb h s d j z he hw
  · exact semantic7 b a hb h s d j z he hw
  · exact semantic8 b a hb h s d j z he hw
  · exact semantic9 b a hb h s d j z he hw
  · exact semantic10 b a hb h s d j z he hw
  · exact semantic11 b a hb h s d j z he hw
  · exact semantic12 b a hb h s d j z he hw
  · exact semantic13 b a hb h s d j z he hw

#print axioms action_semantics
#print axioms action_progress
end BB6.Agent38M44
