import WordNat
set_option maxHeartbeats 0
namespace BB6.Agent6RuleCompose
open BB6Coverage BB6.Agent6NatTape BB6.Agent6WordNat

/-- Numeric suffix candidate. All uses check the exact concatenation. -/
def WordSuffix (a b : Word) : Word := ⟨a.len-b.len,a.val/2^b.len⟩

def side (a b c d : Word) : Option (Word × Word) :=
  if b.len ≤ c.len then
    let e := WordSuffix c b
    if b.cat e = c then some (a.cat e,d) else none
  else
    let e := WordSuffix b c
    if c.cat e = b then some (a,d.cat e) else none

theorem side_sound {a b c d i o : Word} (h : side a b c d = some (i,o)) (t : Nat) :
    ∃ u v, i.apply t = a.apply u ∧ b.apply u = c.apply v ∧ d.apply v = o.apply t := by
  unfold side at h
  split at h
  · dsimp only at h
    split at h
    · rename_i he
      simp only [Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨hi,ho⟩; subst i; subst o
      refine ⟨(WordSuffix c b).apply t,t,Word.cat_apply _ _ _,?_,rfl⟩
      rw [←Word.cat_apply,he]
    · contradiction
  · dsimp only at h
    split at h
    · rename_i he
      simp only [Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨hi,ho⟩; subst i; subst o
      refine ⟨t,(WordSuffix b c).apply t,rfl,?_,(Word.cat_apply _ _ _).symm⟩
      rw [←Word.cat_apply,he]
    · contradiction

def compose (a b : Rule) : Option Rule := do
  let (li,lo) ← side a.leftIn a.leftOut b.leftIn b.leftOut
  let (ri,ro) ← side a.rightIn a.rightOut b.rightIn b.rightOut
  return ⟨li,ri,lo,ro,a.cost+b.cost⟩

theorem compose_sound {p : PartialMachine} {a b c : Rule} (ha : a.Valid p) (hb : b.Valid p)
    (h : compose a b = some c) : c.Valid p := by
  unfold compose at h
  cases hl : side a.leftIn a.leftOut b.leftIn b.leftOut with
  | none => simp [hl] at h
  | some l =>
    cases hr : side a.rightIn a.rightOut b.rightIn b.rightOut with
    | none => simp [hl,hr] at h
    | some r =>
      rcases l with ⟨li,lo⟩; rcases r with ⟨ri,ro⟩
      rw [hl,hr] at h
      have he : (⟨li,ri,lo,ro,a.cost+b.cost⟩ : Rule) = c := Option.some.inj h
      subst c
      intro L R
      obtain ⟨u,v,h1,h2,h3⟩ := side_sound hl L
      obtain ⟨U,V,H1,H2,H3⟩ := side_sound hr R
      change runN p (a.cost+b.cost) ⟨4,li.apply L,ri.apply R⟩ = some ⟨4,lo.apply L,ro.apply R⟩
      rw [h1,H1,←h3,←H3]
      have H := ha u U
      rw [h2,H2] at H
      exact runN_join H (hb v V)

def fixedRule (s : Sweep) (n : Nat) : Rule :=
  if s.leftwards then ⟨s.A.cat (s.W.rep n),s.C,s.A,s.C.cat (s.V.rep n),s.cost*n⟩
  else ⟨s.C,s.A.cat (s.W.rep n),s.C.cat (s.V.rep n),s.A,s.cost*n⟩
theorem fixedRule_sound (p : PartialMachine) (s : Sweep) (h : s.Valid p) (n : Nat) : (fixedRule s n).Valid p := by
  intro L R
  cases hd : s.leftwards
  · simpa only [fixedRule,hd,Bool.false_eq_true,ite_false,Word.cat_apply] using s.right p h hd n L R
  · simpa only [fixedRule,hd,ite_true,Word.cat_apply] using s.left p h hd n L R

structure CR (p : PartialMachine) where
  data : Rule
  sound : data.Valid p
structure CS (p : PartialMachine) where
  data : Sweep
  sound : data.Valid p

def CR.checked (p : PartialMachine) (r : Rule) (h : r.check p = true) : CR p := ⟨r,r.sound p h⟩
def CS.checked (p : PartialMachine) (s : Sweep) (h : s.rule.check p = true) : CS p := ⟨s,s.rule.sound p h⟩
def CS.fixed {p} (s : CS p) (n : Nat) : CR p := ⟨fixedRule s.data n,fixedRule_sound p s.data s.sound n⟩

def identity : Rule := ⟨.empty,.empty,.empty,.empty,0⟩
theorem identity_sound (p : PartialMachine) : identity.Valid p := by intro L R; rfl

def combine {p : PartialMachine} : List (CR p) → Option Rule
  | [] => some identity
  | r::rs => (combine rs).bind (compose r.data)
theorem combine_sound {p : PartialMachine} (rs : List (CR p)) {r : Rule} (h : combine rs = some r) : r.Valid p := by
  induction rs generalizing r with
  | nil => have he : identity = r := Option.some.inj h; subst r; exact identity_sound p
  | cons a rs ih =>
    rw [combine] at h
    cases hs : combine rs with
    | none => simp [hs] at h
    | some b => exact compose_sound a.sound (ih hs) (by simpa only [hs,Option.bind_some] using h)

#print axioms compose_sound
#print axioms combine_sound
end BB6.Agent6RuleCompose
