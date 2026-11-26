import Lean
import SparseZipper
import FastThreeHoleAudit

namespace BB6Coverage.Agent3E0LFExcursion
open BB6Coverage BB6Coverage.Agent50Zipper

/-- Common transitions of residuals 3862 and 3863, differing only at B1. -/
def table (alt : Bool) : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => if alt then some (some ⟨false,true,5⟩) else some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨true,false,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => none
  | 3, true => some (some ⟨false,false,4⟩)
  | 4, false => some (some ⟨false,false,5⟩)
  | 4, true => some (some ⟨true,true,2⟩)
  | 5, false => some (some ⟨true,true,0⟩)
  | 5, true => some (some ⟨false,false,0⟩)
  | _, _ => none

/-- True means the first terminal configuration of the excursion reads A0;
false means it reads the unique hole D0. All intermediate states avoid both. -/
inductive Exit (p : PartialMachine) : Z → Bool → Prop
  | a0 (z : Z) : z.q = 0 → z.l.headD false = false → Exit p z true
  | d0 (z : Z) : z.q = 3 → z.l.headD false = false → Exit p z false
  | next {z z' : Z} {b : Bool} :
      (z.q ≠ 0 ∨ z.l.headD false = true) →
      (z.q ≠ 3 ∨ z.l.headD false = true) →
      step p z = some z' → Exit p z' b → Exit p z b

mutual
  def W : List Bool → Bool
    | true :: true :: true :: l => W l
    | true :: _ => true
    | false :: true :: l => S l
    | _ => false
  def S : List Bool → Bool
    | true :: l => S l
    | false :: true :: true :: l => W l
    | _ => true
end

/-- A1 at the head, two blank cells to its right. Left and right tails arbitrary. -/
def A (h : Int) (l r : List Bool) : Z := ⟨0,h,true::l,false::false::r⟩
/-- E with a blank cell immediately to the right. -/
def E (h : Int) (l r : List Bool) : Z := ⟨4,h,l,false::r⟩

-- Basic local transition proof. A terminal guard is solved before the next step.
macro "advance" : tactic => `(tactic| refine Exit.next (of_decide_eq_true rfl) (of_decide_eq_true rfl) rfl ?_)
macro "endA" : tactic => `(tactic| exact Exit.a0 _ rfl rfl)
macro "endD" : tactic => `(tactic| exact Exit.d0 _ rfl rfl)

-- Each local chain is symbolic in the untouched tails and head coordinate.
theorem aEmpty (alt : Bool) (h : Int) (r : List Bool) : Exit (table alt) (A h [] r) false := by
  unfold A
  advance
  advance
  endD

theorem aZero (alt : Bool) (h : Int) (r : List Bool) : Exit (table alt) (A h [false] r) false := by
  unfold A
  advance
  advance
  endD

theorem aZeros (alt : Bool) (h : Int) (l r : List Bool) : Exit (table alt) (A h (false::false::l) r) false := by
  unfold A
  advance
  advance
  endD

theorem aOne (alt : Bool) (h : Int) (r : List Bool) : Exit (table alt) (A h [true] r) true := by
  unfold A
  advance
  advance
  advance
  advance
  advance
  advance
  advance
  endA

theorem aOneZero (alt : Bool) (h : Int) (l r : List Bool) : Exit (table alt) (A h (true::false::l) r) true := by
  unfold A
  advance
  advance
  advance
  advance
  advance
  advance
  advance
  endA

theorem aTwo (alt : Bool) (h : Int) (r : List Bool) : Exit (table alt) (A h [true,true] r) true := by
  unfold A
  advance
  advance
  advance
  advance
  advance
  advance
  advance
  endA

theorem aTwoZero (alt : Bool) (h : Int) (l r : List Bool) : Exit (table alt) (A h (true::true::false::l) r) true := by
  unfold A
  advance
  advance
  advance
  advance
  advance
  advance
  advance
  endA

-- We obtain the exact remaining configuration by unifying the symbolic successor.
theorem aThree (alt : Bool) (h : Int) (l r : List Bool) (b : Bool)
    (ih : ∀ h' r', Exit (table alt) (A h' l r') b) :
    Exit (table alt) (A h (true::true::true::l) r) b := by
  unfold A
  advance
  advance
  advance
  advance
  advance
  advance
  advance
  apply ih

theorem aZeroOne (alt : Bool) (h : Int) (l r : List Bool) (b : Bool)
    (ih : ∀ h' r', Exit (table alt) (E h' l r') b) :
    Exit (table alt) (A h (false::true::l) r) b := by
  unfold A
  advance
  advance
  advance
  apply ih

theorem eOne (alt : Bool) (h : Int) (l r : List Bool) (b : Bool)
    (ih : ∀ h' r', Exit (table alt) (E h' l r') b) :
    Exit (table alt) (E h (true::l) r) b := by
  unfold E
  advance
  advance
  advance
  apply ih

theorem eEmpty (alt : Bool) (h : Int) (r : List Bool) : Exit (table alt) (E h [] r) true := by
  unfold E
  advance
  advance
  endA

theorem eZero (alt : Bool) (h : Int) (r : List Bool) : Exit (table alt) (E h [false] r) true := by
  unfold E
  advance
  advance
  endA

theorem eZeros (alt : Bool) (h : Int) (l r : List Bool) : Exit (table alt) (E h (false::false::l) r) true := by
  unfold E
  advance
  advance
  endA

theorem eZeroOne (alt : Bool) (h : Int) (r : List Bool) : Exit (table alt) (E h [false,true] r) true := by
  unfold E
  advance
  advance
  endA

theorem eZeroOneZero (alt : Bool) (h : Int) (l r : List Bool) : Exit (table alt) (E h (false::true::false::l) r) true := by
  unfold E
  advance
  advance
  endA

theorem eZeroTwo (alt : Bool) (h : Int) (l r : List Bool) (b : Bool)
    (ih : ∀ h' r', Exit (table alt) (A h' l r') b) :
    Exit (table alt) (E h (false::true::true::l) r) b := by
  unfold E
  advance
  advance
  apply ih

mutual
  theorem a_correct (alt : Bool) (l : List Bool) (h : Int) (r : List Bool) :
      Exit (table alt) (A h l r) (W l) := by
    match l with
    | [] => exact aEmpty alt h r
    | [false] => exact aZero alt h r
    | false::false::l => exact aZeros alt h l r
    | false::true::l => exact aZeroOne alt h l r (S l) (fun h' r' => e_correct alt l h' r')
    | [true] => exact aOne alt h r
    | [true,true] => exact aTwo alt h r
    | true::false::l => exact aOneZero alt h l r
    | true::true::false::l => exact aTwoZero alt h l r
    | true::true::true::l => exact aThree alt h l r (W l) (fun h' r' => a_correct alt l h' r')
  termination_by l.length
  theorem e_correct (alt : Bool) (l : List Bool) (h : Int) (r : List Bool) :
      Exit (table alt) (E h l r) (S l) := by
    match l with
    | [] => exact eEmpty alt h r
    | [false] => exact eZero alt h r
    | false::false::l => exact eZeros alt h l r
    | [false,true] => exact eZeroOne alt h r
    | false::true::false::l => exact eZeroOneZero alt h l r
    | false::true::true::l => exact eZeroTwo alt h l r (W l) (fun h' r' => a_correct alt l h' r')
    | true::l => exact eOne alt h l r (S l) (fun h' r' => e_correct alt l h' r')
  termination_by l.length
end

/-- Nine-state deterministic automaton, reading left tape nearest-cell first. -/
inductive Q where
  | w | w1 | w11 | w0 | s | s0 | s01 | yes | no
  deriving DecidableEq

def trans : Q → Bool → Q
  | .w, true => .w1
  | .w, false => .w0
  | .w1, true => .w11
  | .w1, false => .yes
  | .w11, true => .w
  | .w11, false => .yes
  | .w0, true => .s
  | .w0, false => .no
  | .s, true => .s
  | .s, false => .s0
  | .s0, true => .s01
  | .s0, false => .yes
  | .s01, true => .w
  | .s01, false => .yes
  | .yes, _ => .yes
  | .no, _ => .no

def accept : Q → Bool
  | .w | .w0 | .no => false
  | _ => true

def scan (q : Q) : List Bool → Bool
  | [] => accept q
  | a::l => scan (trans q a) l

def meaning : Q → List Bool → Bool
  | .w, l => W l
  | .w1, l => W (true::l)
  | .w11, l => W (true::true::l)
  | .w0, l => W (false::l)
  | .s, l => S l
  | .s0, l => S (false::l)
  | .s01, l => S (false::true::l)
  | .yes, _ => true
  | .no, _ => false

theorem meaning_trans (q : Q) (a : Bool) (l : List Bool) :
    meaning q (a::l) = meaning (trans q a) l := by
  cases q <;> cases a <;> rfl

theorem scan_correct (q : Q) (l : List Bool) : scan q l = meaning q l := by
  induction l generalizing q with
  | nil => cases q <;> rfl
  | cons a l ih => rw [scan, ih, meaning_trans]

theorem table_binding (alt : Bool) :
    table alt = FAR.fromCodes [7,10,11,(if alt then 21 else 19),14,17,24,16,20,11,3,0] := by
  cases alt <;> apply BB6.Agent31ThreeHole.tableOK_sound <;> decide +kernel

/-- A concrete trace gives exactly one first-exit answer. -/
theorem exit_unique {p : PartialMachine} {z : Z} {a b : Bool}
    (ha : Exit p z a) (hb : Exit p z b) : a = b := by
  induction ha generalizing b with
  | a0 z hq hs =>
    cases hb with
    | a0 => rfl
    | d0 _ hq' _ => rw [hq] at hq'; contradiction
    | next h _ _ _ =>
      rcases h with h | h
      · exact False.elim (h hq)
      · rw [hs] at h; contradiction
  | d0 z hq hs =>
    cases hb with
    | a0 _ hq' _ => rw [hq] at hq'; contradiction
    | d0 => rfl
    | next _ h _ _ =>
      rcases h with h | h
      · exact False.elim (h hq)
      · rw [hs] at h; contradiction
  | next hgA hgD ht ha ih =>
    cases hb with
    | a0 _ hq hs =>
      rcases hgA with h | h
      · exact False.elim (h hq)
      · rw [hs] at h; contradiction
    | d0 _ hq hs =>
      rcases hgD with h | h
      · exact False.elim (h hq)
      · rw [hs] at h; contradiction
    | next _ _ ht' hb =>
      rw [ht] at ht'
      cases Option.some.inj ht'
      exact ih hb

theorem exit_run {p : PartialMachine} {z : Z} {b : Bool} (hx : Exit p z b) :
    ∃ n z', zrun p n z = some z' ∧ z'.q = (if b then 0 else 3) ∧ z'.l.headD false = false := by
  induction hx with
  | a0 z hq hs => exact ⟨0,z,rfl,hq,hs⟩
  | d0 z hq hs => exact ⟨0,z,rfl,hq,hs⟩
  | next _ _ ht _ ih =>
    obtain ⟨n,z',hr,hq,hs⟩ := ih
    exact ⟨n+1,z',by simp [zrun,ht,hr],hq,hs⟩

/-- Exact first-exit test, for each actual residual table, every head position,
all left words and every untouched right suffix. -/
theorem residual_first_exit (alt : Bool) (h : Int) (l r : List Bool) (b : Bool) :
    Exit (FAR.fromCodes [7,10,11,(if alt then 21 else 19),14,17,24,16,20,11,3,0]) (A h l r) b ↔
      scan .w l = b := by
  rw [← table_binding, scan_correct]
  change Exit (table alt) (A h l r) b ↔ W l = b
  constructor
  · intro hb; exact exit_unique (a_correct alt l h r) hb
  · intro hb; rw [← hb]; exact a_correct alt l h r

#print axioms residual_first_exit
#print axioms exit_run
#print axioms a_correct
#print axioms e_correct

end BB6Coverage.Agent3E0LFExcursion
