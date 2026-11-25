import Raw110WordSweep
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Raw110Run
open BB6BlockFAR BB6Raw110Word
open BB6Carry hiding render
abbrev Runs := List (Bool × Nat)

def expand : Runs → List Bool
  | [] => []
  | (b,n)::xs => List.replicate n b ++ expand xs

def push (b : Bool) (n : Nat) (xs : Runs) : Runs :=
  if n = 0 then xs else
  match xs with
  | (c,k)::ys => if b = c then (b,n+k)::ys else (b,n)::xs
  | [] => [(b,n)]

theorem expand_push (b : Bool) (n : Nat) (xs : Runs) :
    expand (push b n xs) = List.replicate n b ++ expand xs := by
  by_cases hn : n = 0
  · subst n; simp [push]
  · cases xs with
    | nil => simp [push,hn,expand]
    | cons x xs =>
      rcases x with ⟨c,k⟩
      by_cases h : b = c
      · subst c; simp [push,hn,expand,← List.replicate_append_replicate,List.append_assoc]
      · simp [push,hn,h,expand]

/-- Remove a maximal prefix of equal bits, ignoring empty runs. -/
def take (b : Bool) : Runs → Nat × Runs
  | [] => (0,[])
  | (c,n)::xs =>
    if n=0 then take b xs
    else if b=c then let t := take b xs; (n+t.1,t.2)
    else (0,(c,n)::xs)

theorem take_spec (b : Bool) (xs : Runs) :
    let t := take b xs
    expand xs = List.replicate t.1 b ++ expand t.2 ∧
      (t.2 = [] ∨ ∃ r, expand t.2 = (!b)::r) := by
  induction xs with
  | nil => exact ⟨rfl,Or.inl rfl⟩
  | cons x xs ih =>
    rcases x with ⟨c,n⟩
    by_cases hn : n=0
    · subst n; simpa [take,expand] using ih
    · by_cases hc : b=c
      · subst c
        simp only [take,hn,if_false,if_true]
        refine ⟨?_,ih.2⟩
        simp only [expand,← List.replicate_append_replicate,List.append_assoc]
        rw [← ih.1]
      · simp only [take,hn,if_false,hc]
        refine ⟨rfl,Or.inr ?_⟩
        have hb : c = !b := by cases b <;> cases c <;> simp_all
        subst c
        cases n with
        | zero => contradiction
        | succ n => exact ⟨_,rfl⟩

def dropOne : Runs → Runs
  | [] => []
  | (b,0)::xs => dropOne xs
  | (b,1)::xs => xs
  | (b,n+2)::xs => (b,n+1)::xs

theorem expand_dropOne (xs : Runs) : expand (dropOne xs) = (expand xs).tail := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨b,n⟩
    cases n with
    | zero => exact ih
    | succ n => cases n <;> rfl

def aWord (n : Nat) : List Pair := List.replicate n .A
def aBits (n : Nat) : List Bool := flatten (aWord n)

theorem flatten_append (u v : List Pair) : flatten (u++v) = flatten u ++ flatten v := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append,flatten,ih,List.append_assoc]

theorem aBits_succ (n : Nat) : aBits (n+1) = true::false::aBits n := rfl

theorem aBits_add (m n : Nat) : aBits (m+n) = aBits m ++ aBits n := by
  simp only [aBits,aWord,← List.replicate_append_replicate,flatten_append]

theorem pairs_aBits (n : Nat) (r : List Bool) :
    pairs (aBits n ++ r) = aWord n ++ pairs r := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Pair.A :: pairs (aBits n ++ r) = Pair.A :: (aWord n ++ pairs r)
    rw [ih]

theorem pairs_false_aBits (n : Nat) (r : List Bool) :
    pairs (false::(aBits n ++ r)) = List.replicate n Pair.B ++ pairs (false::r) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Pair.B :: pairs (false::(aBits n ++ r)) = Pair.B :: (List.replicate n Pair.B ++ pairs (false::r))
    rw [ih]

/-- The expensive linear scans are exact affine-cost identities. -/
theorem cw_ones (n : Nat) (l r : List Bool) :
    cw (List.replicate n true ++ l) r =
      let t := cw l (aBits n ++ r); (2*n+t.1,t.2) := by
  induction n generalizing r with
  | zero => simp [cw,aBits,aWord,flatten]
  | succ n ih =>
    simp only [List.replicate_succ,List.cons_append,cw,ih,aBits_succ]
    have h : aBits n ++ true::false::r = true::false::(aBits n ++ r) := by
      rw [show true::false::r = aBits 1 ++ r by rfl, ← List.append_assoc, ← aBits_add, aBits_succ]
      rfl
    rw [h]
    congr 1 <;> omega

theorem fw_zeros (slow : Bool) (n : Nat) (l r : List Bool) :
    fw slow (List.replicate n false ++ l) r =
      let t := fw slow l (aBits n ++ r); (2*n+t.1,t.2) := by
  induction n generalizing r with
  | zero => simp [fw,aBits,aWord,flatten]
  | succ n ih =>
    simp only [List.replicate_succ,List.cons_append,fw,ih]
    have h : aBits n ++ true::false::r = aBits (n+1) ++ r := by
      rw [aBits_add n 1,List.append_assoc]; rfl
    rw [h]
    congr 1 <;> omega

def takeA : List Pair → Nat × List Pair
  | .A::xs => let t := takeA xs; (t.1+1,t.2)
  | xs => (0,xs)

theorem takeA_spec (xs : List Pair) : aWord (takeA xs).1 ++ (takeA xs).2 = xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases a with
    | A => change Pair.A :: (aWord (takeA xs).1 ++ (takeA xs).2) = _; rw [ih]
    | B => rfl
    | C => rfl
    | D => rfl

structure State where
  l : Runs
  a : Nat
  r : List Pair
  deriving DecidableEq, Repr

def State.expand (s : State) : BB6Raw110Word.State := ⟨BB6Raw110Run.expand s.l,aWord s.a ++ s.r⟩

def State.render (s : State) : Prim := s.expand.render

inductive Result where
  | halt (n : Nat)
  | next (n : Nat) (s : State)
  deriving DecidableEq, Repr

def Result.expand : Result → Outcome
  | .halt n => .halt n
  | .next n s => .next n s.expand

def Result.prepend (k : Nat) : Result → Result
  | .halt n => .halt (k+n)
  | .next n s => .next (k+n) s

theorem prepend_expand (k : Nat) (t : Result) :
    (t.prepend k).expand = t.expand.prepend k := by cases t <;> rfl

def out (k : Nat) (l : Runs) (a : Nat) (r : List Pair) : Result :=
  let t := takeA r
  .next k ⟨l,a+t.1,t.2⟩

theorem out_expand (k : Nat) (l : Runs) (a : Nat) (r : List Pair) :
    (out k l a r).expand = .next k ⟨expand l,aWord a ++ r⟩ := by
  simp only [out,Result.expand,State.expand,aWord,← List.replicate_append_replicate,List.append_assoc]
  change Outcome.next k ⟨expand l,aWord a ++ (aWord (takeA r).1 ++ (takeA r).2)⟩ = _
  rw [takeA_spec]
  rfl

/-- Scan the leading zeros (F) and ones (C) as whole runs.
    Shifting the odd prefix maps A^z to B^z without expanding the bits. -/
def fs (slow : Bool) (k : Nat) (l : Runs) (r : List Bool) : Result :=
  let (z,xs) := take false l
  if xs.isEmpty then out (k+2*z+4) [(false,1)] z (pairs r)
  else
    let (o,ys) := take true (dropOne xs)
    let newL := if ys.isEmpty then [(false,1)] else push false 1 ys
    out (k+2*z+(if slow then 6 else 2)+2*o+3) newL o
      (List.replicate z Pair.B ++ pairs (false::r))

theorem fs_expand (slow : Bool) (k : Nat) (l : Runs) (r : List Bool) :
    (fs slow k l r).expand = finish k (fw slow (expand l) r) := by
  have H := take_spec false l
  cases h : take false l with
  | mk z xs =>
    rw [h] at H
    obtain ⟨hl,hxs⟩ := H
    simp only [Prod.fst,Prod.snd] at hl hxs
    unfold fs
    rw [h,hl,fw_zeros]
    rcases hxs with he | ⟨w,hw⟩
    · subst xs
      simp only [List.isEmpty,ite_true,out_expand,expand,List.replicate_succ,List.replicate_zero,List.nil_append,List.append_nil,fw,finish,pairs_aBits]
      congr 1 <;> omega
    · have hne : xs.isEmpty = false := by
        cases xs <;> simp_all [expand]
      simp only [hne, Bool.false_eq_true, ite_false, hw, Bool.not_false, fw]
      have H2 := take_spec true (dropOne xs)
      cases h2 : take true (dropOne xs) with
      | mk o ys =>
        rw [h2] at H2
        obtain ⟨hl2,hys⟩ := H2
        simp only [Prod.fst,Prod.snd] at hl2 hys
        have ht : expand (dropOne xs) = w := by rw [expand_dropOne,hw]; rfl
        rw [ht] at hl2
        rw [hl2,cw_ones]
        rcases hys with he | ⟨v,hv⟩
        · subst ys
          simp only [List.isEmpty,ite_true,out_expand,expand,List.replicate_succ,List.replicate_zero,List.nil_append,List.append_nil,cw,finish,pairs_aBits,pairs_false_aBits]
          congr 1 <;> omega
        · have hne2 : ys.isEmpty = false := by cases ys <;> simp_all [expand]
          simp only [hne2,Bool.false_eq_true,ite_false,Bool.not_true,out_expand,expand_push,List.replicate_succ,List.replicate_zero,List.nil_append, hv,cw,finish,pairs_aBits,pairs_false_aBits,List.cons_append]
          congr 1 <;> omega

def bs (slow : Bool) : List Pair → Runs → Result
  | [],l => fs slow 7 l [false,true]
  | .A::r,l => (bs slow r (push true 1 l)).prepend 2
  | .B::r,l => fs slow (if slow then 7 else 3) l (false::flatten r)
  | .C::[],l => fs slow 7 l [false,true]
  | .C::.A::r,l => (bs slow r (push false 2 l)).prepend 4
  | .C::.B::r,l => fs slow 7 l (false::true::true::flatten r)
  | .C::.C::r,l => fs slow 7 l (false::true::false::flatten r)
  | .C::.D::r,l => fs slow 7 l (true::false::false::flatten r)
  | .D::_,_ => .halt 1

theorem bs_expand (slow : Bool) (w : List Pair) (l : Runs) :
    (bs slow w l).expand = bw slow w (expand l) := by
  match w with
  | [] => exact fs_expand slow 7 l _
  | .A::r =>
    simp only [bs,bw,prepend_expand,bs_expand slow r,expand_push]
    rfl
  | .B::r => exact fs_expand slow _ l _
  | .C::[] => exact fs_expand slow 7 l _
  | .C::.A::r =>
    simp only [bs,bw,prepend_expand,bs_expand slow r,expand_push]
    rfl
  | .C::.B::r => exact fs_expand slow 7 l _
  | .C::.C::r => exact fs_expand slow 7 l _
  | .C::.D::r => exact fs_expand slow 7 l _
  | .D::r => rfl

theorem bw_As (slow : Bool) (n : Nat) (w : List Pair) (l : List Bool) :
    bw slow (aWord n ++ w) l = (bw slow w (List.replicate n true ++ l)).prepend (2*n) := by
  induction n generalizing l with
  | zero =>
    change bw slow w l = (bw slow w l).prepend 0
    cases bw slow w l <;> simp [Outcome.prepend]
  | succ n ih =>
    change (bw slow (aWord n ++ w) (true::l)).prepend 2 = _
    rw [ih]
    have he : List.replicate n true ++ true::l = List.replicate (n+1) true ++ l := by
      rw [show true::l = List.replicate 1 true ++ l by rfl,← List.append_assoc,List.replicate_append_replicate]
    rw [he]
    cases bw slow w (List.replicate (n+1) true ++ l) <;> simp only [Outcome.prepend] <;> congr 1 <;> omega

def sweep (slow : Bool) (s : State) : Result :=
  (bs slow s.r (push true s.a s.l)).prepend (2*s.a)

theorem sweep_expand (slow : Bool) (s : State) :
    (sweep slow s).expand = bw slow s.expand.r s.expand.l := by
  simp only [sweep,prepend_expand,bs_expand,expand_push,State.expand,bw_As]

theorem sweep_sound (slow : Bool) (s : State) :
    (sweep slow s).expand.sound slow s.render := by
  rw [sweep_expand]
  exact bw_sound slow s.expand.r s.expand.l

def replay (slow : Bool) : Nat → State → Result
  | 0,s => .next 0 s
  | n+1,s => match sweep slow s with
    | .halt k => .halt k
    | .next k t => (replay slow n t).prepend k

theorem replay_sound (slow : Bool) (n : Nat) (s : State) :
    (replay slow n s).expand.sound slow s.render := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have h := sweep_sound slow s
    unfold replay
    cases e : sweep slow s with
    | halt k => rw [e] at h; exact h
    | next k t => rw [e] at h; rw [prepend_expand]; exact prepend_sound slow h (ih t)

def first : State := ⟨[(true,1)],0,[]⟩

theorem first_sound (slow : Bool) : run (machine slow) 1 primBlank = some first.render := BB6Raw110Word.first_sound slow

theorem checked_next (slow : Bool) (n k : Nat) (s t : State)
    (h : replay slow n s = .next k t) :
    run (machine slow) k s.render = some t.render := by
  have hs := replay_sound slow n s
  rw [h] at hs
  exact hs

theorem checked_halt (slow : Bool) (n k : Nat) (s : State)
    (h : replay slow n s = .halt k) :
    (Outcome.halt k).sound slow s.render := by
  have hs := replay_sound slow n s
  rw [h] at hs
  exact hs

#print axioms sweep_sound
#print axioms replay_sound
#print axioms checked_next
#print axioms checked_halt
end BB6Raw110Run
