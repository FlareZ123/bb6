import Raw13Coupled6OneRAReplay
namespace BB6Coverage.Agent31Pump.Raw13Coupled6OneRAReplay
open BB6Coverage Agent31Pump Raw13Coupled6OneRAHierarchy Raw13Coupled6OneRACost Raw13Coupled6OneRABatch
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def takeOnes (R : List Bool) : Nat := (R.takeWhile id).length
def digitHead : List Bool → Option (Bool × List Bool)
 | false::true::false::true::r => some (false,r)
 | false::true::true::false::r => some (true,r)
 | _ => none
def parseWord : Nat → List Bool → Word
 | 0,R => .lit R
 | fuel+1,R =>
   match digitHead R with
   | none => .lit R
   | some (b,r) =>
     if r==V then .term b true
     else if r==U then .term b false
     else let k:=takeOnes r
          if k>0 && k%3==0 && (digitHead (r.drop k)).isSome then
             .bit b (k/3) (parseWord fuel (r.drop k))
          else .bit b 0 (parseWord fuel r)

theorem start_eq (z : Z0) (R : List Bool) (hq : z.q=0) (hl : z.l.headD false=false) (hr : z.r=R) :
  ZEq z (A (false::z.l.tail) R) := by
  refine ⟨hq,?_,?_⟩
  · cases h : z.l with
    | nil => exact tape_symm tape_zero_nil
    | cons b t => simp [h] at hl; subst b; exact tape_refl _
  · rw [hr]; exact tape_refl _

def fastFill (z : Z0) (j : Nat) (w : Word) : Option (Nat × Z0) :=
  if z.q=0 ∧ z.l.headD false=false ∧ z.r=rep one (3*j) ++ w.encode then do
    let (u,c) ← w.advance (2^j)
    if z.l.isEmpty then
      return (c+fillOver j+3,norm (A [] ([true,true,true]++rep one (3*j)++u.encode)))
    else return (c+fillOver j,norm (A (true::z.l.tail) (rep one (3*j)++u.encode)))
  else none

theorem fastFill_sound {z : Z0} {j : Nat} {w : Word} {n : Nat} {out : Z0}
  (h : fastFill z j w = some (n,out)) : MacroOK z n out := by
  unfold fastFill at h
  split at h
  · rename_i hz
    cases ha : w.advance (2^j) with
    | none => simp [ha] at h
    | some a =>
      obtain ⟨u,c⟩ := a
      have hs := Word.advance_sound ha
      have hf := fillC_all j z.l.tail hs
      have he := start_eq z _ hz.1 hz.2.1 hz.2.2
      simp only [ha,Option.bind_some] at h
      split at h
      · rename_i hl
        have ht : z.l.tail=[] := by cases hL : z.l <;> simp_all
        rw [ht] at hf he
        have h3 : run0 p 3 (A [true] (rep one (3*j)++u.encode)) = some (A [] ([true,true,true]++rep one (3*j)++u.encode)) := by rfl
        cases h
        exact macro_transport he (macro_of_run (join0 hf h3))
      · cases h
        exact macro_transport he (macro_of_run hf)
  · contradiction

def fastOne (z : Z0) (k : Nat) (w : Word) : Option (Nat × Z0) :=
  if z.q=0 ∧ z.l.headD false=false ∧ z.r=rep one k ++ w.encode then do
    let (u,c) ← w.advance 1
    return (k+c,norm (A (rep zero k ++ true::z.l.tail) u.encode))
  else none

theorem one_good {c : Nat} {r s : List Bool} (h : StepsC 1 c r s) : GoodC c r s := by
  cases h with
  | cons h g => cases g; simpa using h

theorem fastOne_sound {z : Z0} {k : Nat} {w : Word} {n : Nat} {out : Z0}
  (h : fastOne z k w = some (n,out)) : MacroOK z n out := by
  unfold fastOne at h
  split at h
  · rename_i hz
    cases ha : w.advance 1 with
    | none => simp [ha] at h
    | some a =>
      obtain ⟨u,c⟩ := a
      have hg := one_good (Word.advance_sound ha) k z.l.tail
      have he := start_eq z _ hz.1 hz.2.1 hz.2.2
      simp only [ha,Option.bind_some] at h
      cases h
      exact macro_transport he (macro_of_run hg)
  · contradiction

def rawTime (z : Z0) : Nat :=
  if z.l.headD false then
    if z.l.getD 1 false then 2 else if z.l.getD 2 false then 4 else 3
  else
    let k:=takeOnes z.r
    let s:=z.r.drop k
    if !s.getD 1 false then k+3 else if s.getD 2 false then k+4 else if s.getD 3 false then k+6 else k+4

def rawStep (z : Z0) : Option (Nat × Z0) := do
  let t:=rawTime z
  let u ← run0 p t z
  return (t,norm u)

theorem rawStep_sound {z : Z0} {n : Nat} {out : Z0} (h : rawStep z=some (n,out)) : MacroOK z n out := by
  unfold rawStep at h
  cases hr : run0 p (rawTime z) z with
  | none => simp [hr] at h
  | some u =>
    simp only [hr,Option.bind_some] at h
    cases h
    exact macro_of_run hr

def macroStep (z : Z0) : Option (Nat × Z0) :=
  if z.q != 0 then none else
  let k:=takeOnes z.r
  let w:=parseWord z.r.length (z.r.drop k)
  let f:=if k%3==0 && w.cap>=2^(k/3) then fastFill z (k/3) w else fastOne z k w
  match f with
  | some a => some a
  | none => rawStep z

theorem macroStep_sound {z : Z0} {n : Nat} {out : Z0} (h : macroStep z=some (n,out)) : MacroOK z n out := by
  unfold macroStep at h
  split at h
  · contradiction
  · dsimp only at h
    split at h
    · rename_i a ha
      cases h
      split at ha
      · exact fastFill_sound ha
      · exact fastOne_sound ha
    · exact rawStep_sound h

def replay : Nat → Z0 → Option (Nat × Z0)
 | 0,z => some (0,z)
 | n+1,z => do
   let (a,u) ← macroStep z
   let (b,v) ← replay n u
   return (a+b,v)

theorem replay_sound {k : Nat} {z : Z0} {n : Nat} {out : Z0} (h : replay k z=some (n,out)) : MacroOK z n out := by
  induction k generalizing z n out with
  | zero => cases h; exact ⟨z,rfl,zrefl z⟩
  | succ k ih =>
    cases hm : macroStep z with
    | none => simp [replay,hm] at h
    | some a =>
      obtain ⟨t,u⟩ := a
      cases hr : replay k u with
      | none => simp [replay,hm,hr] at h
      | some b =>
        obtain ⟨s,v⟩ := b
        simp [replay,hm,hr] at h
        obtain ⟨rfl,rfl⟩ := h
        exact macro_join (macroStep_sound hm) (ih hr)

#print axioms replay_sound
end BB6Coverage.Agent31Pump.Raw13Coupled6OneRAReplay
