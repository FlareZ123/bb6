import Box12Core

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent48PackedFinite
open BB6Coverage BB6.Agent32FiniteSource BB6.Agent13BlankDelay
open BB6.Agent50TranslatedCycler

def pack : List Bool → Nat
  | [] => 0
  | b::bs => b.toNat + 2 * pack bs

theorem pack_head (xs : List Bool) : pack xs % 2 = (xs.headD false).toNat := by
  cases xs with
  | nil => rfl
  | cons b bs => cases b <;> simp [pack, Bool.toNat] <;> omega

theorem pack_tail (xs : List Bool) : pack xs / 2 = pack xs.tail := by
  cases xs with
  | nil => rfl
  | cons b bs => cases b <;> simp [pack, Bool.toNat] <;> omega

theorem pack_bit (xs : List Bool) (i : Nat) : (pack xs).testBit i = xs[i]?.getD false := by
  induction i generalizing xs with
  | zero =>
    rw [Nat.testBit_zero,pack_head,← get_head]
    cases xs.headD false <;> rfl
  | succ i ih => rw [Nat.testBit_succ,pack_tail,ih,get_tail]

structure PCfg where
  left : Nat
  right : Nat
  cur : Bool
  state : Fin 6
  deriving DecidableEq

def encode (c : FiniteCfg) : PCfg := ⟨pack c.left,pack c.right,c.cur,c.state⟩
def pblank : PCfg := ⟨0,0,false,0⟩
def pquery (c : PCfg) : Slot := (c.state,c.cur)
def pmove (c : PCfg) (mv : Move) : PCfg :=
  if mv.right then ⟨mv.write.toNat+2*c.left,c.right/2,c.right%2==1,mv.next⟩
  else ⟨c.left/2,mv.write.toNat+2*c.right,c.left%2==1,mv.next⟩

theorem encode_move (c : FiniteCfg) (mv : Move) : encode (move c mv) = pmove (encode c) mv := by
  cases h : mv.right <;> simp [move,pmove,h,encode,pack,pack_head,pack_tail]
  · cases c.left.head?.getD false <;> rfl
  · cases c.right.head?.getD false <;> rfl


def pstep (m : Machine) (c : PCfg) : Option PCfg := (m (pquery c)).map (pmove c)
def prun (m : Machine) : Nat → PCfg → Option PCfg
  | 0,c => some c
  | n+1,c => (pstep m c).bind (prun m n)

theorem encode_step (m : Machine) (c : FiniteCfg) : (step m c).map encode = pstep m (encode c) := by
  unfold step pstep pquery query encode
  cases h : m (c.state,c.cur) <;> simp
  exact encode_move c _

theorem encode_run (m : Machine) (n : Nat) (c : FiniteCfg) : (finiteRun m n c).map encode = prun m n (encode c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [finiteRun,prun,← encode_step]
    cases step m c with
    | none => rfl
    | some d => exact ih d

def pboundedStep (m : Machine) (k : Nat) (c : PCfg) : Option (Nat × PCfg) :=
  match m (pquery c) with
  | none => none
  | some mv => if mv.right then some (k+1,pmove c mv) else
      match k with | 0 => none | k+1 => some (k,pmove c mv)

def pboundedRun (m : Machine) : Nat → Nat → PCfg → Option (Nat × PCfg)
  | 0,k,c => some (k,c)
  | n+1,k,c => (pboundedStep m k c).bind fun (k',c') => pboundedRun m n k' c'

def encodePair (x : Nat × FiniteCfg) : Nat × PCfg := (x.1, encode x.2)

theorem encode_bstep (m : Machine) (k : Nat) (c : FiniteCfg) :
    (boundedStep m k c).map encodePair = pboundedStep m k (encode c) := by
  unfold boundedStep pboundedStep
  have he : pquery (encode c) = query c := rfl
  rw [he]
  cases h : m (query c) with
  | none => rfl
  | some mv => cases hr : mv.right <;> cases k <;> simp [hr,encodePair,encode_move]

theorem encode_brun (m : Machine) (n k : Nat) (c : FiniteCfg) :
    (boundedRun m n k c).map encodePair = pboundedRun m n k (encode c) := by
  induction n generalizing k c with
  | zero => rfl
  | succ n ih =>
    simp only [boundedRun,pboundedRun,← encode_bstep]
    cases boundedStep m k c with
    | none => rfl
    | some x => exact ih x.1 x.2

def eqPacked (k : Nat) (c d : PCfg) : Bool :=
  decide (c.state=d.state) && decide (c.left%2^k=d.left%2^k) && decide (c.cur=d.cur) && decide (c.right=d.right)

theorem eqPacked_sound (k : Nat) (c d : FiniteCfg) (h : eqPacked k (encode c) (encode d)=true) : EqLimit k c d := by
  simp only [eqPacked,encode,Bool.and_eq_true] at h
  refine ⟨of_decide_eq_true h.1.1.1,?_,of_decide_eq_true h.1.2,?_⟩
  · intro i hi
    have H := congrArg (fun n : Nat => n.testBit i) (of_decide_eq_true h.1.1.2)
    simpa [Nat.testBit_mod_two_pow,hi,pack_bit] using H
  · intro i
    exact (pack_bit c.right i).symm.trans ((congrArg (fun n : Nat => n.testBit i) (of_decide_eq_true h.2)).trans (pack_bit d.right i))

def pcycleRight (m : Machine) (entry period budget : Nat) : Bool :=
  match prun m entry pblank with
  | none => false
  | some c => match pboundedRun m period budget c with
    | none => false
    | some (endBudget,d) => decide (0<period) && decide (budget≤endBudget) && eqPacked budget c d

def pcycle (m : Machine) (right : Bool) (entry period budget : Nat) : Bool :=
  pcycleRight (if right then m else reflectTable m) entry period budget

theorem pcycleRight_sound {m : Machine} {entry period budget : Nat} (h : pcycleRight m entry period budget = true) : NeverHalts m := by
  unfold pcycleRight at h
  rw [show pblank = encode finiteBlank from rfl,← encode_run] at h
  cases he : finiteRun m entry finiteBlank with
  | none => simp [he] at h
  | some c =>
    simp only [he,Option.map_some,← encode_brun] at h
    cases hb : boundedRun m period budget c with
    | none => simp [hb] at h
    | some x =>
      rcases x with ⟨k,d⟩
      simp only [hb,Option.map_some,encodePair,Bool.and_eq_true,decide_eq_true_eq] at h
      exact TranslatedCycle.neverBlank he h.1.1 ⟨k,d,boundedRun_sound hb,h.1.2,eqPacked_sound _ _ _ h.2⟩

theorem pcycle_sound {m : Machine} {right : Bool} {entry period budget : Nat} (h : pcycle m right entry period budget=true) : NeverHalts m := by
  cases right with
  | true => exact pcycleRight_sound h
  | false => exact (reflect_never_iff m).mp (pcycleRight_sound h)

open BB6.Agent48Box12 BB6.Agent49BoxBridge
open BB6.Agent49Box6 (fromCodes decode code index code_ok)
open BB6.Agent49Box (Box Fits)

def phalt (B : Nat) (p : PartialMachine) (n : Nat) : Bool :=
  match prun (weightedTNFDefaultCompletion p) n pblank with
  | none => false
  | some c => decide (n+1≤B) && decide (p (pquery c) = some none)

theorem phalt_eq (B : Nat) (p : PartialMachine) (n : Nat) : phalt B p n = haltCheck B p n := by
  unfold phalt haltCheck
  rw [show pblank = encode finiteBlank from rfl,← encode_run]
  cases finiteRun (weightedTNFDefaultCompletion p) n finiteBlank <;> rfl

def plast (B : Nat) (p : PartialMachine) (n : Nat) : Bool :=
  match prun (weightedTNFDefaultCompletion p) n pblank with
  | none => false
  | some c => decide (n+1≤B) && slots.all (fun s => if s = pquery c then true else ((p s).getD none).isSome)

theorem plast_eq (B : Nat) (p : PartialMachine) (n : Nat) : plast B p n = lastCheck B p n := by
  unfold plast lastCheck
  rw [show pblank = encode finiteBlank from rfl,← encode_run]
  cases finiteRun (weightedTNFDefaultCompletion p) n finiteBlank <;> rfl

def pleaf (B : Nat) (ext : PartialMachine → Bool) (p : PartialMachine) : Witness → Bool
  | .halt n => phalt B p n
  | .last n => plast B p n
  | .ray r e n k => pcycle (weightedTNFDefaultCompletion p) r e n k
  | w => leafCheck B ext p w

theorem pleaf_sound (B : Nat) (ext : PartialMachine → Bool)
    (hExt : ∀ p, ext p = true → ∀ m, compatible p m → DecidedBelow B m)
    (p : PartialMachine) (w : Witness) (h : pleaf B ext p w = true)
    (m : Machine) (hm : compatible p m) : DecidedBelow B m := by
  cases w with
  | halt n => exact haltCheck_sound B p n (by simpa only [pleaf,phalt_eq] using h) m hm
  | last n => exact lastCheck_sound B p n (by simpa only [pleaf,plast_eq] using h) m hm
  | ray r e n k => exact Or.inl (BB6.Agent49Box6.default_never_sound p (pcycle_sound h) m hm)
  | total => exact leafCheck_sound B ext hExt p .total h m hm
  | ngram c => exact leafCheck_sound B ext hExt p (.ngram c) h m hm
  | far r d c => exact leafCheck_sound B ext hExt p (.far r d c) h m hm
  | external => exact leafCheck_sound B ext hExt p .external h m hm

theorem index_lt (s : Slot) : index s < 12 := by
  rcases s with ⟨q,b⟩
  have h := q.isLt
  cases b <;> simp [index, Bool.toNat] <;> omega

theorem index_inj {s t : Slot} (h : index s = index t) : s=t := by
  rcases s with ⟨q,b⟩; rcases t with ⟨r,c⟩
  cases b <;> cases c <;> simp [index,Bool.toNat] at h ⊢ <;> omega

def setCode (cs : Array Nat) (s : Slot) (t : Transition) : Array Nat := cs.setIfInBounds (index s) (code t)

theorem fromCodes_set (cs : Array Nat) (h : cs.size=12) (s : Slot) (t : Transition) :
    fromCodes (setCode cs s t) = refine (fromCodes cs) s t := by
  funext u
  unfold fromCodes setCode refine
  by_cases he : u=s
  · subst u
    have hi : index s < cs.size := by rw [h]; exact index_lt s
    rw [Array.getElem?_setIfInBounds_self_of_lt hi]
    simp [(code_ok t).2,show code t ≠ 25 by have := (code_ok t).1; omega]
  · have hn : index s ≠ index u := fun hh => he (index_inj hh.symm)
    rw [Array.getElem?_setIfInBounds_ne hn]
    simp [he]

def fastTree (B : Nat) (ext : PartialMachine → Bool) (domain : Box Slot Transition) :
    Nat → Array Nat → Tree → Bool
  | 0,_,_ => false
  | _fuel+1,cs,.leaf w => pleaf B ext (fromCodes cs) w
  | fuel+1,cs,.split s kids => (domain s).all fun t =>
      match kids[code t]? with
      | none => false
      | some child => fastTree B ext domain fuel (setCode cs s t) child

theorem fastTree_sound (B : Nat) (ext : PartialMachine → Bool)
    (hExt : ∀ p, ext p = true → ∀ m, compatible p m → DecidedBelow B m)
    (domain : Box Slot Transition) (fuel : Nat) (cs : Array Nat) (tree : Tree)
    (hs : cs.size=12) (h : fastTree B ext domain fuel cs tree = true)
    (m : Machine) (hm : Fits domain m) (hp : compatible (fromCodes cs) m) : DecidedBelow B m := by
  induction fuel generalizing cs tree with
  | zero => simp [fastTree] at h
  | succ fuel ih =>
    cases tree with
    | leaf w => exact pleaf_sound B ext hExt _ w h m hp
    | split s kids =>
      have hh := List.all_eq_true.mp h (m s) (hm s)
      cases hk : kids[code (m s)]? with
      | none => simp [hk] at hh
      | some child =>
        rw [hk] at hh
        apply ih (setCode cs s (m s)) child (by simpa [setCode] using hs) hh
        rw [fromCodes_set cs hs]
        exact compatible_refine _ m s hp

#print axioms pcycle_sound
#print axioms fastTree_sound
end BB6.Agent48PackedFinite
