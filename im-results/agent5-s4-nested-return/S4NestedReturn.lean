import S4PrefixNinthCycle
import S4PrefixNinthBase
import S4PrefixReturn8Standalone
import S4Prefix5457
import S4BoundaryWord

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace S4NestedReturn

open S4Boundary

/-- One accelerated S4 return consists of these three source gates, in execution order. -/
def pBlock : List Nat := [509, 290, 219]

/-- Concatenation of n copies of a finite gate word. -/
def repeatWord (n : Nat) (w : List Nat) : List Nat :=
  (List.replicate n w).flatten

lemma repeatWord_succ (n : Nat) (w : List Nat) :
    repeatWord (n + 1) w = w ++ repeatWord n w := by
  simp [repeatWord, List.replicate_succ]

/-- Prefix action of a gate word. -/
def prefixRun (w : List Nat) : Nat → List Nat → List Nat
  | 0, xs => xs
  | n + 1, xs => prefixRun w n (S4Boundary.prefixWord w xs)

theorem prefixWord_append (cs ds : List Nat) (xs : List Nat) :
    S4Boundary.prefixWord (cs ++ ds) xs =
      S4Boundary.prefixWord ds (S4Boundary.prefixWord cs xs) := by
  induction cs generalizing xs with
  | nil => rfl
  | cons c cs ih =>
      simp [S4Boundary.prefixWord, ih]

theorem prefixWord_repeat (n : Nat) (w xs : List Nat) :
    S4Boundary.prefixWord (repeatWord n w) xs = prefixRun w n xs := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [repeatWord_succ, prefixWord_append, ih]
      rfl

theorem repeatWord_positive (n : Nat) (w : List Nat)
    (hw : ∀ c ∈ w, 0 < c) :
    ∀ c ∈ repeatWord n w, 0 < c := by
  induction n with
  | zero => simp [repeatWord]
  | succ n ih =>
      intro c hc
      rw [repeatWord_succ] at hc
      rcases List.mem_append.mp hc with h | h
      · exact hw c h
      · exact ih h

theorem pBlock_positive : ∀ c ∈ pBlock, 0 < c := by
  simp [pBlock]

def prefix9Start : List Nat := S4PrefixNinthBase.cycle9Start
def tail9Start : List Nat := S4PrefixNinthBase.tail5457

/-- The source-certified return-5457 state is exactly this 9+9 split. -/
theorem source_state_5457 :
    S4Prefix5457.s5457 = prefix9Start ++ tail9Start := by
  simpa [prefix9Start, tail9Start] using S4PrefixNinthBase.s5457_decomp

/-- The 81,920-return prefix period, expressed as a gate word. -/
def rootWord : List Nat := repeatWord 81920 pBlock

theorem prefixStep_eq_gp (c : Nat) (xs : List Nat) :
    S4Boundary.prefixStep c xs = S4PrefixReturn8Standalone.gp c xs := by
  cases xs with
  | nil => rfl
  | cons b tail =>
      simp [S4Boundary.prefixStep, S4PrefixReturn8Standalone.gp,
        S4Boundary.split, S4PrefixReturn8Standalone.hp]

theorem prefixWord_pBlock (xs : List Nat) :
    S4Boundary.prefixWord pBlock xs = S4PrefixReturn8Standalone.pp xs := by
  simp [pBlock, S4Boundary.prefixWord, prefixStep_eq_gp,
    S4PrefixReturn8Standalone.pp]

theorem prefixRun_pBlock_eq_fast (n : Nat) (xs : List Nat) :
    prefixRun pBlock n xs = S4PrefixNinthBase.prefixRunFast n xs := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
      simp [prefixRun, prefixWord_pBlock,
        S4PrefixNinthBase.prefixRunFast, ih]

theorem root_prefix_return :
    S4Boundary.prefixWord rootWord prefix9Start = prefix9Start := by
  rw [prefixWord_repeat, prefixRun_pBlock_eq_fast]
  exact S4PrefixNinth.cycle9_period81920

theorem rootWord_positive : ∀ c ∈ rootWord, 0 < c := by
  exact repeatWord_positive 81920 pBlock pBlock_positive

/-- An action on the suffix after the current prefix. -/
def actionFor (c : Nat) (P : List Nat) : S4Boundary.Action :=
  match P with
  | [] => .gate c
  | b :: T => (S4Boundary.split (b + c) T).2

/-- The sequence of suffix actions induced by a gate word and a prefix. -/
def actionWord : List Nat → List Nat → List S4Boundary.Action
  | [], _ => []
  | c :: cs, P =>
      actionFor c P :: actionWord cs (S4Boundary.prefixStep c P)

/-- Evaluate a sequence of suffix actions. -/
def evalWord : List S4Boundary.Action → List Nat → Option (List Nat)
  | [], S => some S
  | a :: as, S =>
      (S4Boundary.Action.eval a S).bind (evalWord as)

/-- Adds are folded into the next gate; a final run of adds remains pending. -/
def normalizeActions : List S4Boundary.Action → List Nat × Nat
  | [] => ([], 0)
  | .id :: as => normalizeActions as
  | .add d :: as =>
      let (gs, pending) := normalizeActions as
      match gs with
      | [] => ([], d + pending)
      | g :: gs' => (g + d :: gs', pending)
  | .gate d :: as =>
      let (gs, pending) := normalizeActions as
      (d :: gs, pending)

/-- A zero pending add is the identity, including on the empty list. -/
def applyPending (d : Nat) (S : List Nat) : List Nat :=
  if d = 0 then S else S4Boundary.bump d S

def actionPositive : S4Boundary.Action → Prop
  | .id => True
  | .add d => 0 < d
  | .gate d => 0 < d

theorem split_action_positive (a : Nat) (P : List Nat) (ha : 0 < a) :
    actionPositive (S4Boundary.split a P).2 := by
  induction P generalizing a with
  | nil =>
      by_cases h : a % 2 = 0
      · have hd : 0 < a / 2 := by omega
        simp [S4Boundary.split, actionPositive, h, hd]
      · have hd : 0 < a / 2 + 1 := by omega
        simp [S4Boundary.split, actionPositive, h, hd]
  | cons b T ih =>
      by_cases h : a % 2 = 0
      · simp [S4Boundary.split, actionPositive, h]
      · have ha' : 0 < b + a / 2 + 1 := by omega
        simpa [S4Boundary.split, actionPositive, h] using
          ih (b + a / 2 + 1) ha'

theorem actionFor_positive (c : Nat) (P : List Nat) (hc : 0 < c) :
    actionPositive (actionFor c P) := by
  cases P with
  | nil => simp [actionFor, actionPositive, hc]
  | cons b T =>
      exact split_action_positive (b + c) T (by omega)

theorem actionWord_positive (cs : List Nat) (P : List Nat)
    (hc : ∀ c ∈ cs, 0 < c) :
    ∀ a ∈ actionWord cs P, actionPositive a := by
  induction cs generalizing P with
  | nil => simp [actionWord]
  | cons c cs ih =>
      have hc0 : 0 < c := hc c (by simp)
      have hcs : ∀ d ∈ cs, 0 < d := by
        intro d hd
        exact hc d (by simp [hd])
      intro a ha
      simp [actionWord] at ha
      rcases ha with h | h
      · simpa [h] using actionFor_positive c P hc0
      · exact ih (S4Boundary.prefixStep c P) hcs a h

lemma applyPending_pos (d : Nat) (S : List Nat) (hd : 0 < d) :
    applyPending d S = S4Boundary.bump d S := by
  simp [applyPending, Nat.ne_of_gt hd]

lemma applyPending_add (d e : Nat) (S : List Nat) :
    applyPending d (applyPending e S) = applyPending (d + e) S := by
  by_cases hd : d = 0
  · subst d
    simp [applyPending]
  · by_cases he : e = 0
    · subst e
      simp [applyPending]
    · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
      have hepos : 0 < e := Nat.pos_of_ne_zero he
      simp [applyPending, hd, he, Nat.ne_of_gt (Nat.add_pos hdpos hepos),
        S4Boundary.bump_bump d e S hdpos hepos]

lemma applyPending_bump (p d : Nat) (S : List Nat) (hd : 0 < d) :
    applyPending p (S4Boundary.bump d S) = applyPending (d + p) S := by
  rw [← applyPending_pos d S hd, applyPending_add]
  simp [Nat.add_comm]

lemma wholeWord_bump (g d : Nat) (gs : List Nat) (S : List Nat) (hd : 0 < d) :
    S4Boundary.wholeWord (g :: gs) (S4Boundary.bump d S) =
      S4Boundary.wholeWord ((g + d) :: gs) S := by
  simp [S4Boundary.wholeWord, S4Boundary.G_bump g d S hd]

theorem evalWord_normalize (acts : List S4Boundary.Action) (S : List Nat)
    (hpos : ∀ a ∈ acts, actionPositive a) :
    evalWord acts S =
      (S4Boundary.wholeWord (normalizeActions acts).1 S).map
        (applyPending (normalizeActions acts).2) := by
  induction acts generalizing S with
  | nil =>
      simp [evalWord, normalizeActions, applyPending, S4Boundary.wholeWord]
  | cons a as ih =>
      have htail : ∀ b ∈ as, actionPositive b := by
        intro b hb
        exact hpos b (by simp [hb])
      cases a with
      | id =>
          simpa [evalWord, normalizeActions] using ih htail
      | add d =>
          have hd : 0 < d := hpos (.add d) (by simp)
          cases hnorm : normalizeActions as with
          | mk gs pending =>
              cases gs with
              | nil =>
                  calc
                    evalWord (.add d :: as) S =
                        evalWord as (S4Boundary.bump d S) := by
                          simp [evalWord, S4Boundary.Action.eval]
                    _ =
                        (S4Boundary.wholeWord [] (S4Boundary.bump d S)).map
                          (applyPending pending) := by
                            simpa [hnorm] using ih htail (S := S4Boundary.bump d S)
                    _ =
                        (S4Boundary.wholeWord [] S).map
                          (applyPending (d + pending)) := by
                            simp [S4Boundary.wholeWord, applyPending_bump,
                              hd, Nat.add_comm]
                    _ =
                        (S4Boundary.wholeWord (normalizeActions (.add d :: as)).1 S).map
                          (applyPending (normalizeActions (.add d :: as)).2) := by
                            simp [normalizeActions, hnorm]
              | cons g gs =>
                  calc
                    evalWord (.add d :: as) S =
                        evalWord as (S4Boundary.bump d S) := by
                          simp [evalWord, S4Boundary.Action.eval]
                    _ =
                        (S4Boundary.wholeWord (g :: gs) (S4Boundary.bump d S)).map
                          (applyPending pending) := by
                            simpa [hnorm] using ih htail (S := S4Boundary.bump d S)
                    _ =
                        (S4Boundary.wholeWord ((g + d) :: gs) S).map
                          (applyPending pending) := by
                            rw [wholeWord_bump g d gs S hd]
                    _ =
                        (S4Boundary.wholeWord (normalizeActions (.add d :: as)).1 S).map
                          (applyPending (normalizeActions (.add d :: as)).2) := by
                            simp [normalizeActions, hnorm]
      | gate d =>
          cases hnorm : normalizeActions as with
          | mk gs pending =>
              simpa [evalWord, normalizeActions, hnorm,
                S4Boundary.wholeWord] using
                (ih htail (S := S4Octet.G d S))

theorem suffixWord_eq_evalWord (cs : List Nat) (P S : List Nat) :
    S4Boundary.suffixWord cs P S = evalWord (actionWord cs P) S := by
  induction cs generalizing P S with
  | nil => rfl
  | cons c cs ih =>
      cases P with
      | nil =>
          simp [S4Boundary.suffixWord, S4Boundary.suffixStep,
            actionWord, actionFor, evalWord, S4Boundary.Action.eval, ih]
      | cons b T =>
          simp [S4Boundary.suffixWord, S4Boundary.suffixStep,
            actionWord, actionFor, evalWord, S4Boundary.Action.eval, ih]

theorem suffixWord_compact (cs : List Nat) (P S : List Nat)
    (hc : ∀ c ∈ cs, 0 < c) :
    S4Boundary.suffixWord cs P S =
      (S4Boundary.wholeWord (normalizeActions (actionWord cs P)).1 S).map
        (applyPending (normalizeActions (actionWord cs P)).2) := by
  rw [suffixWord_eq_evalWord]
  exact evalWord_normalize (actionWord cs P) S
    (actionWord_positive cs P hc)

theorem returnWhole (cs P S : List Nat)
    (hc : ∀ c ∈ cs, 0 < c)
    (hprefix : S4Boundary.prefixWord cs P = P)
    (hpending : (normalizeActions (actionWord cs P)).2 = 0) :
    S4Boundary.wholeWord cs (P ++ S) =
      (S4Boundary.wholeWord (normalizeActions (actionWord cs P)).1 S).map
        (P ++ ·) := by
  rw [S4Boundary.wholeWord_split cs P S hc]
  rw [suffixWord_compact cs P S hc]
  simp [hprefix, hpending, applyPending]

def firstNorm : List Nat × Nat :=
  normalizeActions (actionWord rootWord prefix9Start)

def firstReturnWord : List Nat := firstNorm.1
def firstPending : Nat := firstNorm.2

theorem firstPending_zero : firstPending = 0 := by
  native_decide

theorem firstReturnWord_length : firstReturnWord.length = 703 := by
  native_decide

theorem firstReturnWord_mass :
    (firstReturnWord.foldl (fun s c => s + c + 2) 0) = 83886080 := by
  native_decide

theorem firstReturnWord_positive : ∀ c ∈ firstReturnWord, 0 < c := by
  native_decide

theorem firstReturnWhole (S : List Nat) :
    S4Boundary.wholeWord rootWord (prefix9Start ++ S) =
      (S4Boundary.wholeWord firstReturnWord S).map (prefix9Start ++ ·) := by
  have hc : ∀ c ∈ rootWord, 0 < c := rootWord_positive
  have hp : S4Boundary.prefixWord rootWord prefix9Start = prefix9Start :=
    root_prefix_return
  simpa [firstReturnWord, firstPending, firstNorm, firstPending_zero] using
    returnWhole rootWord prefix9Start S hc hp firstPending_zero

def tailAfter16 : List Nat :=
  [366446, 435438, 366335, 527037, 2639156, 3037351, 3252483, 6310511,
   24221543, 24423525, 56750562, 67602890, 162126013, 335820941, 659578070]

def blockTail : List Nat := tailAfter16.take 9
def tailRest : List Nat := tailAfter16.drop 9

theorem tailAfter16_exact :
    S4Boundary.wholeWord (repeatWord 16 firstReturnWord) tail9Start =
      some tailAfter16 := by
  native_decide

theorem blockTail_prefixProjection :
    blockTail = prefixRun firstReturnWord 16 tail9Start := by
  native_decide

theorem blockTail_period256 :
    prefixRun firstReturnWord 256 blockTail = blockTail := by
  native_decide

def qRootWord : List Nat := repeatWord 256 firstReturnWord
def qNorm : List Nat × Nat :=
  normalizeActions (actionWord qRootWord blockTail)
def qReturnWord : List Nat := qNorm.1
def qPending : Nat := qNorm.2

theorem qPending_zero : qPending = 0 := by
  native_decide

theorem qReturnWord_length : qReturnWord.length = 386 := by
  native_decide

theorem qReturnWord_mass :
    (qReturnWord.foldl (fun s c => s + c + 2) 0) = 21474836480 := by
  native_decide

theorem qReturnWord_positive : ∀ c ∈ qReturnWord, 0 < c := by
  native_decide

theorem qRootWord_positive : ∀ c ∈ qRootWord, 0 < c := by
  exact repeatWord_positive 256 firstReturnWord firstReturnWord_positive

theorem qPrefixReturn :
    S4Boundary.prefixWord qRootWord blockTail = blockTail := by
  rw [prefixWord_repeat]
  exact blockTail_period256

theorem qReturnWhole (S : List Nat) :
    S4Boundary.wholeWord qRootWord (blockTail ++ S) =
      (S4Boundary.wholeWord qReturnWord S).map (blockTail ++ ·) := by
  have hc : ∀ c ∈ qRootWord, 0 < c := qRootWord_positive
  have hp : S4Boundary.prefixWord qRootWord blockTail = blockTail :=
    qPrefixReturn
  simpa [qReturnWord, qPending, qNorm, qPending_zero] using
    returnWhole qRootWord blockTail S hc hp qPending_zero

theorem root18_return :
    S4Boundary.wholeWord (repeatWord 256 rootWord)
      (prefix9Start ++ tailAfter16) =
      (S4Boundary.wholeWord qReturnWord tailRest).map
        (fun U => prefix9Start ++ blockTail ++ U) := by
  have hfirst := wholeWord_repeat_return
    rootWord firstReturnWord prefix9Start firstReturnWhole 256 tailAfter16
  have hsplit : tailAfter16 = blockTail ++ tailRest := by
    simp [blockTail, tailRest, List.take_append_drop]
  rw [hfirst, hsplit, qReturnWhole]
  simp [List.append_assoc]

end S4NestedReturn
