import Frontier
namespace BB6.Agent32FiniteSource
open BB6Coverage
/-- The finite blank-padded tape used by BusyCoq Individual62.cconfig.
The first list stores the nearest left cell first, the second the nearest right. -/
structure FiniteCfg where
  left : List Bool
  right : List Bool
  cur : Bool
  state : Fin 6
  deriving DecidableEq, Repr

def query (c : FiniteCfg) : Slot := (c.state,c.cur)
def finiteBlank : FiniteCfg := ⟨[],[],false,0⟩
def move (c : FiniteCfg) (mv : Move) : FiniteCfg :=
  if mv.right then ⟨mv.write::c.left,c.right.tail,c.right.headD false,mv.next⟩
  else ⟨c.left.tail,mv.write::c.right,c.left.headD false,mv.next⟩
def step (m : Machine) (c : FiniteCfg) : Option FiniteCfg := (m (query c)).map (move c)
/-- Same recursion order as BusyCoq multistep_c. -/
def finiteRun (m : Machine) : Nat → FiniteCfg → Option FiniteCfg
  | 0,c => some c
  | n+1,c => (step m c).bind (finiteRun m n)

def symbol (c : FiniteCfg) : Int → Bool
  | .ofNat 0 => c.cur
  | .ofNat (n+1) => c.right[n]?.getD false
  | .negSucc n => c.left[n]?.getD false

abbrev absolute (c : FiniteCfg) (h : Int) : Config := ⟨c.state,h,fun i => symbol c (i-h)⟩
def dx (mv : Move) : Int := if mv.right then 1 else -1

theorem get_tail (xs : List Bool) (n : Nat) : xs.tail[n]?.getD false = xs[n+1]?.getD false := by
  cases xs <;> rfl

theorem get_head (xs : List Bool) : xs.headD false = xs[0]?.getD false := by cases xs <;> rfl

theorem symbol_move_right (c : FiniteCfg) (mv : Move) (hr : mv.right = true) (i : Int) :
    symbol (move c mv) i = if i = -1 then mv.write else symbol c (i+1) := by
  cases i with
  | ofNat n =>
    cases n with
    | zero =>
      change (move c mv).cur = c.right[0]?.getD false
      simp only [move,hr,ite_true]
      exact get_head _
    | succ n =>
      change (move c mv).right[n]?.getD false = c.right[n+1]?.getD false
      simp only [move,hr,ite_true]
      exact get_tail _ _
  | negSucc n =>
    cases n with
    | zero => simp [symbol,move,hr]
    | succ n =>
      have hneq : (Int.negSucc (n+1) : Int) ≠ -1 := by omega
      have hshift : (Int.negSucc (n+1) : Int) + 1 = Int.negSucc n := by omega
      simp [symbol,move,hr,hneq,hshift]

theorem symbol_move_left (c : FiniteCfg) (mv : Move) (hr : mv.right = false) (i : Int) :
    symbol (move c mv) i = if i = 1 then mv.write else symbol c (i-1) := by
  cases i with
  | ofNat n =>
    cases n with
    | zero =>
      change (move c mv).cur = c.left[0]?.getD false
      simp only [move,hr,Bool.false_eq_true,ite_false]
      exact get_head _
    | succ n =>
      cases n with
      | zero => simp [symbol,move,hr]
      | succ n =>
        have hneq : (Int.ofNat (n+2) : Int) ≠ 1 := by
          simp only [Int.ofNat_eq_natCast,Int.natCast_add]
          omega
        have hshift : (Int.ofNat (n+2) : Int) - 1 = Int.ofNat (n+1) := by
          simp only [Int.ofNat_eq_natCast,Int.natCast_add]
          omega
        change (move c mv).right[n+1]?.getD false = if (Int.ofNat (n+2) : Int) = 1 then mv.write else symbol c ((Int.ofNat (n+2) : Int)-1)
        rw [if_neg hneq,hshift]
        simp [move,hr,symbol]
  | negSucc n => simp [symbol,move,hr]

theorem read_absolute (c : FiniteCfg) (h : Int) : readSlot (absolute c h) = query c := by
  simp [absolute,query,symbol]

theorem move_absolute (c : FiniteCfg) (h : Int) (mv : Move) :
    applyMove (absolute c h) mv = absolute (move c mv) (h+dx mv) := by
  cases hr : mv.right
  · simp only [applyMove,absolute,move,hr,Bool.false_eq_true,ite_false,dx]
    congr 1
    funext i
    have a := symbol_move_left c mv hr (i-(h + -1))
    have hshift : i-(h + -1)-1 = i-h := by omega
    have hiff : (i-(h + -1) = 1) ↔ i=h := by omega
    by_cases he : i=h
    · rw [if_pos he]
      rw [if_pos (hiff.mpr he)] at a
      simpa only [move,hr,Bool.false_eq_true,ite_false,ite_true] using a.symm
    · rw [if_neg he]
      rw [if_neg (fun hx => he (hiff.mp hx)),hshift] at a
      simpa only [move,hr,Bool.false_eq_true,ite_false,ite_true] using a.symm
  · simp only [applyMove,absolute,move,hr,ite_true,dx]
    congr 1
    funext i
    have a := symbol_move_right c mv hr (i-(h+1))
    have hshift : i-(h+1)+1 = i-h := by omega
    have hiff : (i-(h+1) = -1) ↔ i=h := by omega
    by_cases he : i=h
    · rw [if_pos he]
      rw [if_pos (hiff.mpr he)] at a
      simpa only [move,hr,Bool.false_eq_true,ite_false,ite_true] using a.symm
    · rw [if_neg he]
      rw [if_neg (fun hx => he (hiff.mp hx)),hshift] at a
      simpa only [move,hr,Bool.false_eq_true,ite_false,ite_true] using a.symm

theorem absolute_blank : absolute finiteBlank 0 = blank := by
  unfold absolute finiteBlank blank
  congr 1
  funext i
  simp only [Int.sub_zero]
  cases i with
  | ofNat n => cases n <;> rfl
  | negSucc n => rfl

theorem run_succ_first (m : Machine) (n : Nat) (c : Config) :
    run m (n+1) c = (rawStep m c).bind (run m n) := by
  induction n generalizing c with
  | zero => simp [run]
  | succ n ih =>
    rw [run,ih]
    cases hs : rawStep m c <;> simp [hs,run]

/-- Preserve the actual read slot at a finite endpoint, without adding an
absolute head coordinate to the upstream Coq finite state. -/
theorem run_transport (m : Machine) (n : Nat) (c : FiniteCfg) (h : Int) :
    match finiteRun m n c with
    | none => run m n (absolute c h) = none
    | some d => ∃ h', run m n (absolute c h) = some (absolute d h') := by
  induction n generalizing c h with
  | zero => exact ⟨h,rfl⟩
  | succ n ih =>
    rw [finiteRun,run_succ_first,rawStep,read_absolute]
    cases hm : m (query c) with
    | none => simp [step,hm]
    | some mv =>
      simp only [step,hm,Option.map_some,Option.bind_some,move_absolute]
      exact ih (move c mv) (h+dx mv)

theorem finite_halt_sound (m : Machine) (n : Nat) (c : FiniteCfg) (s : Slot)
    (hr : finiteRun m n finiteBlank = some c) (hs : query c = s) (hh : m s = none) :
    ∃ d, run m n blank = some d ∧ readSlot d = s ∧ m s = none := by
  have ht := run_transport m n finiteBlank 0
  rw [hr,absolute_blank] at ht
  obtain ⟨h,hd⟩ := ht
  exact ⟨absolute c h,hd,(read_absolute c h).trans hs,hh⟩

theorem finite_never_iff (m : Machine) :
    (∀ n, ∃ c, finiteRun m n finiteBlank = some c) ↔ NeverHalts m := by
  constructor
  · intro hf n
    obtain ⟨c,hc⟩ := hf n
    have ht := run_transport m n finiteBlank 0
    rw [hc,absolute_blank] at ht
    obtain ⟨h,hh⟩ := ht
    have : (run m n blank).isSome = true := by rw [hh]; rfl
    exact this
  · intro hn n
    have ht := run_transport m n finiteBlank 0
    cases hf : finiteRun m n finiteBlank with
    | none =>
      rw [hf,absolute_blank] at ht
      have hh : (run m n blank).isSome = true := hn n
      rw [ht] at hh
      contradiction
    | some c => exact ⟨c,rfl⟩

#print axioms finite_halt_sound
#print axioms finite_never_iff
end BB6.Agent32FiniteSource
