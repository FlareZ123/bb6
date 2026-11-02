import DSectionTransfer
import Generic
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19.Physical
open BB6.Padding (Config bitAt goLeft goRight)
open BB6.Portfolio (Cfg State)

def tape (c : Config) (i : Int) : Bool :=
  if i = 0 then c.bit else if i < 0 then bitAt c.left ((-i-1).toNat)
  else bitAt c.right ((i-1).toNat)

def encode (c : Config) (hs : c.state < 6) : Cfg :=
  ⟨⟨c.state,hs⟩, 0, tape c⟩

private theorem bitAt_drop_one (xs : List Bool) (n : Nat) :
  bitAt (xs.drop 1) n = bitAt xs (n+1) := by
  cases xs <;> rfl

private theorem left_shift (c : Config) (w : Bool) (s : Nat) :
  ∀ i : Int, BB6.Portfolio.updateTape (tape c) 0 w i =
    tape (goLeft c w s) (i+1) := by
  intro i
  by_cases h : i = 0
  · subst i
    simp [BB6.Portfolio.updateTape, tape, goLeft]
  · by_cases hi : i < 0
    · have hin : i+1 ≤ 0 := by omega
      by_cases hei : i+1=0
      · have heqi : i=-1 := by omega
        subst i
        simp [BB6.Portfolio.updateTape, tape, goLeft, bitAt]
      · have his : i+1 < 0 := by omega
        simp only [BB6.Portfolio.updateTape, if_neg h]
        simp only [tape, if_neg h, if_pos hi]
        simp only [tape, if_neg hei, if_pos his, goLeft]
        rw [bitAt_drop_one]
        congr 1
        omega
    · have hip : 0 < i := by omega
      have hplus : 0 < i+1 := by omega
      simp only [BB6.Portfolio.updateTape, if_neg h]
      simp only [tape, if_neg h, if_neg (show ¬i<0 by omega)]
      simp only [tape, if_neg (show i+1≠0 by omega), if_neg (show ¬i+1<0 by omega),goLeft]
      have hidx : (i + 1 - 1).toNat = (i-1).toNat + 1 := by omega
      rw [hidx, BB6.Padding.bitAt_cons_succ]

private theorem right_shift (c : Config) (w : Bool) (s : Nat) :
  ∀ i : Int, BB6.Portfolio.updateTape (tape c) 0 w i =
    tape (goRight c w s) (i-1) := by
  intro i
  by_cases h : i = 0
  · subst i
    simp [BB6.Portfolio.updateTape, tape, goRight]
  · by_cases hi : i < 0
    · have hminus : i-1 < 0 := by omega
      simp only [BB6.Portfolio.updateTape, if_neg h]
      simp only [tape, if_neg h, if_pos hi]
      simp only [tape, if_neg (show i-1≠0 by omega), if_pos hminus,goRight]
      have hidx : (- (i-1) - 1).toNat = (-i-1).toNat + 1 := by omega
      rw [hidx, BB6.Padding.bitAt_cons_succ]
    · have hip : 0 < i := by omega
      by_cases hei : i-1=0
      · have heqi : i=1 := by omega
        subst i
        simp [BB6.Portfolio.updateTape, tape, goRight, bitAt]
      · have hminus : 0 < i-1 := by omega
        simp only [BB6.Portfolio.updateTape, if_neg h]
        simp only [tape, if_neg h, if_neg (show ¬i<0 by omega)]
        simp only [tape, if_neg hei, if_neg (show ¬i-1<0 by omega),goRight]
        rw [bitAt_drop_one]
        congr 1
        omega

theorem step_left (c : Config) (hc : c.state < 6) (w : Bool) (s : State)
    (hi : BB6.Portfolio.D0 ⟨c.state,hc⟩ c.bit = some (w,.L,s)) :
    BB6.Portfolio.step BB6.Portfolio.D0 (encode c hc) =
      some (BB6.Portfolio.translateCfg (-1) (encode (goLeft c w s.val) s.isLt)) := by
  have hhead : (encode c hc).tape 0 = c.bit := by rfl
  have hstep : BB6.Portfolio.step BB6.Portfolio.D0 (encode c hc) =
      some ⟨s,-1,BB6.Portfolio.updateTape (tape c) 0 w⟩ := by
    simp [BB6.Portfolio.step, encode, BB6.Portfolio.Dir.dx, hi, tape]
  rw [hstep]
  congr 1
  change (⟨s,-1,BB6.Portfolio.updateTape (tape c) 0 w⟩ : Cfg) =
    ⟨s,-1,fun i => tape (goLeft c w s.val) (i+1)⟩
  congr 1
  funext i
  change BB6.Portfolio.updateTape (tape c) 0 w i = tape (goLeft c w s.val) (i+1)
  exact left_shift c w s.val i

theorem step_right (c : Config) (hc : c.state < 6) (w : Bool) (s : State)
    (hi : BB6.Portfolio.D0 ⟨c.state,hc⟩ c.bit = some (w,.R,s)) :
    BB6.Portfolio.step BB6.Portfolio.D0 (encode c hc) =
      some (BB6.Portfolio.translateCfg 1 (encode (goRight c w s.val) s.isLt)) := by
  have hstep : BB6.Portfolio.step BB6.Portfolio.D0 (encode c hc) =
      some ⟨s,1,BB6.Portfolio.updateTape (tape c) 0 w⟩ := by
    simp [BB6.Portfolio.step, encode, BB6.Portfolio.Dir.dx, hi, tape]
  rw [hstep]
  congr 1
  change (⟨s,1,BB6.Portfolio.updateTape (tape c) 0 w⟩ : Cfg) =
    ⟨s,1,fun i => tape (goRight c w s.val) (i-1)⟩
  congr 1
  funext i
  change BB6.Portfolio.updateTape (tape c) 0 w i = tape (goRight c w s.val) (i-1)
  exact right_shift c w s.val i

/-- Shift offsets compose under the physical tape/head representation. -/
theorem translate_compose (a b : Int) (c : Cfg) :
    BB6.Portfolio.translateCfg a (BB6.Portfolio.translateCfg b c) =
      BB6.Portfolio.translateCfg (a+b) c := by
  cases c with
  | mk st head t =>
    change (⟨st,head+b+a,fun i => t (i-a-b)⟩ : Cfg) =
      ⟨st,head+(a+b),fun i => t (i-(a+b))⟩
    congr 1
    · omega
    · funext i
      have h : i-a-b=i-(a+b) := by omega
      rw [h]

/-- An exact finite left/right tape equipped with a physical head offset.
    The state is a genuine running state; a halt is represented by `none`. -/
structure SafeCfg where
  data : Config
  offset : Int
  running : data.state < 6

def realize (c : SafeCfg) : Cfg :=
  BB6.Portfolio.translateCfg c.offset (encode c.data c.running)

def stepFinite (c : SafeCfg) : Option SafeCfg :=
  match BB6.Portfolio.D0 ⟨c.data.state,c.running⟩ c.data.bit with
  | none => none
  | some (w,.L,s) => some ⟨goLeft c.data w s.val,c.offset-1,s.isLt⟩
  | some (w,.R,s) => some ⟨goRight c.data w s.val,c.offset+1,s.isLt⟩

def runFinite : Nat → Option SafeCfg → Option SafeCfg
  | 0,c => c
  | n+1,c => (runFinite n c).bind stepFinite

/-- Each real primitive D0 transition is exactly one finite half-tape
    transition, including the true undefined halt event. -/
theorem step_semiconjugacy (c : SafeCfg) :
    BB6.Portfolio.step BB6.Portfolio.D0 (realize c) =
      (stepFinite c).map realize := by
  have he := BB6.Portfolio.translate_step BB6.Portfolio.D0 c.offset
    (encode c.data c.running)
  rw [realize, he]
  cases h : BB6.Portfolio.D0 ⟨c.data.state,c.running⟩ c.data.bit with
  | none =>
    simp [stepFinite, BB6.Portfolio.step,encode,tape,h]
  | some instr =>
    rcases instr with ⟨w,d,s⟩
    cases d with
    | L =>
      rw [step_left c.data c.running w s h]
      simp only [stepFinite, h, Option.map_some, realize, translate_compose]
      congr 1
    | R =>
      rw [step_right c.data c.running w s h]
      simp only [stepFinite, h, Option.map_some, realize, translate_compose]

/-- Full primitive-time trace transport for any finite run duration.
    No horizon, simulation assumption or finite tape cutoff is involved. -/
theorem run_semiconjugacy (n : Nat) (c : Option SafeCfg) :
    BB6.Portfolio.run BB6.Portfolio.D0 n (c.map realize) =
      (runFinite n c).map realize := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [BB6.Portfolio.run,runFinite,ih]
    cases h : runFinite n c with
    | none => simp
    | some cfg => simpa [step_semiconjugacy]

#print axioms translate_compose
#print axioms step_semiconjugacy
#print axioms run_semiconjugacy
#print axioms step_left
#print axioms step_right
end BB6.Agent19.Physical
