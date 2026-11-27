import Lean.Elab.Tactic.Omega

namespace BB6.Agent19Raw40.Leaf66Drain

-- Two framed primitive operations suffice. This file proves the abstract
-- normalized recurrence; its original-table soundness is a separate target.
abbrev Token := Nat × Nat
structure C where
  k : Nat
  b : Nat
  u : List Nat
  v : List Token
  deriving DecidableEq, Repr

def zero (b : Nat) (u : List Nat) (v : List Token) : C := ⟨0,b,u,v⟩
def pop (b : Nat) (u : List Nat) (v : List Token) : C :=
  ⟨u.headD 0,b,u.tail,v⟩
def inc : List Nat → List Nat
  | [] => [1]
  | x::u => (x+1)::u
def tok (j : Nat) : Token := (5*j+3,3)
def E (n : Nat) : List Nat := List.replicate n 1

inductive Step : C → C → Prop where
  | join (k b c : Nat) (u : List Nat) (v : List Token)
      (hb : 4 ≤ b) (hc : 0 < c) :
      Step ⟨k,b,u,(3,c)::v⟩ (zero (b+c+1) ((k+1)::u) v)
  | split (k b g c : Nat) (u : List Nat) (v : List Token)
      (hb : 4 ≤ b) (hg : 5 < g) :
      Step ⟨k,b,u,(g,c)::v⟩ (pop (k+6) u ((b-3,3)::(g-5,c)::v))
  | five (k b c : Nat) (u : List Nat) (v : List Token) (hb : 4 ≤ b) :
      Step ⟨k,b,u,(5,c)::v⟩ (pop (k+6) u ((b-3,c+3)::v))
  | blank (k b : Nat) (u : List Nat) (hb : 4 ≤ b) :
      Step ⟨k,b,u,[]⟩ (pop (k+6) u [(b-3,3)])

-- Positive transitive closure, so the final recurrence cannot be empty.
inductive Reach : C → C → Prop where
  | one {a b : C} : Step a b → Reach a b
  | trans {a b c : C} : Reach a b → Reach b c → Reach a c

theorem joinPop (b : Nat) (u : List Nat) (v : List Token) (hb : 4 ≤ b) :
    Reach (pop b u (tok 0::v)) (zero (b+4) (inc u) v) := by
  cases u with
  | nil =>
    simpa [pop,inc,tok] using Reach.one (Step.join 0 b 3 [] v hb (by decide))
  | cons x u =>
    simpa [pop,inc,tok] using Reach.one (Step.join x b 3 u v hb (by decide))

theorem joinZero (b : Nat) (u : List Nat) (v : List Token) (hb : 4 ≤ b) :
    Reach (zero b u (tok 0::v)) (zero (b+4) (1::u) v) := by
  simpa [zero,tok] using Reach.one (Step.join 0 b 3 u v hb (by decide))

theorem startPair (k r : Nat) (u : List Nat) (v : List Token) :
    Reach ⟨k,6,u,tok (r+1)::v⟩ (zero (k+10) (inc u) (tok r::v)) := by
  have h := Reach.one (Step.split k 6 (5*(r+1)+3) 3 u v (by decide) (by omega))
  have e : 5*(r+1)+3-5 = 5*r+3 := by omega
  have h1 : Reach ⟨k,6,u,tok (r+1)::v⟩ (pop (k+6) u (tok 0::tok r::v)) := by
    simpa [tok,e] using h
  exact Reach.trans h1 (joinPop (k+6) u (tok r::v) (by omega))

theorem splitStage (a r : Nat) (u : List Nat) (v : List Token) :
    Reach (zero (6+5*(a+1)) u (tok (r+1)::v))
      (pop 6 u (tok (a+1)::tok r::v)) := by
  have h := Reach.one (Step.split 0 (6+5*(a+1)) (5*(r+1)+3) 3 u v (by omega) (by omega))
  have e : 6+5*(a+1)-3 = 5*(a+1)+3 := by omega
  have f : 5*(r+1)+3-5 = 5*r+3 := by omega
  simpa [zero,tok,e,f] using h

-- n indexes T_(n+1). Using pop on a nonempty list unifies T_1
-- with the longer drains instead of introducing a separate recursive rule.
def Standard (n : Nat) : Prop :=
  ∀ (x : Nat) (u : List Nat) (v : List Token),
    Reach (pop 6 (E n ++ x::u) (tok (n+1)::v))
      (zero (x+5*n+14) (E (n+1) ++ inc u) v)

/-- The stage invariant uses inc on the still-unprocessed suffix.
    Induction on r consumes one residual token at a time. -/
theorem stdLoop (r a x : Nat) (u : List Nat) (v : List Token)
    (earlier : ∀ t, t ≤ a+r → Standard t) :
    Reach (zero (6+5*(a+1)) (E a ++ inc (E r ++ x::u)) (tok (r+1)::v))
      (zero (x+5*(a+r+1)+14) (E (a+r+2) ++ inc u) v) := by
  induction r generalizing a with
  | zero =>
    have hs := splitStage a 0 (E a ++ (x+1)::u) v
    have hd := earlier a (by omega) (x+1) u (tok 0::v)
    have hj := joinZero (x+1+5*a+14) (E (a+1) ++ inc u) v (by omega)
    have H := Reach.trans (Reach.trans hs hd) hj
    have e : x+1+5*a+14+4 = x+5*(a+0+1)+14 := by omega
    simpa [E,inc,List.replicate_succ,e] using H
  | succ r ih =>
    have hs := splitStage a (r+1) (E a ++ 2::(E r ++ x::u)) v
    have hd := earlier a (by omega) 2 (E r ++ x::u) (tok (r+1)::v)
    have e : 2+5*a+14 = 6+5*(a+1+1) := by omega
    rw [e] at hd
    have hn := ih (a+1) (fun t ht => earlier t (by omega))
    have H := Reach.trans hs (Reach.trans hd hn)
    have f : a+1+r+1 = a+(r+1)+1 := by omega
    have g : a+1+r+2 = a+(r+1)+2 := by omega
    simpa [E,inc,List.replicate_succ,List.append_assoc,f,g] using H

theorem standardAll (n : Nat) : Standard n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro x u v
    cases n with
    | zero =>
      have h1 := startPair x 0 u v
      have h2 := joinZero (x+10) (inc u) v (by omega)
      simpa [pop,E,inc,zero] using Reach.trans h1 h2
    | succ n =>
      have h1 := startPair 1 (n+1) (E n ++ x::u) v
      have h2 := stdLoop n 0 x u v (fun t ht => ih t (by omega))
      have H := Reach.trans h1 h2
      simpa [pop,E,List.replicate_succ,List.append_assoc] using H

theorem gapSplit (a m r c : Nat) (u : List Nat) (v : List Token) (hr : 1 ≤ r) :
    Reach (zero (6+5*(a+1)) u ((5*(m+1)+r,c)::v))
      (pop 6 u (tok (a+1)::(5*m+r,c)::v)) := by
  have h := Reach.one (Step.split 0 (6+5*(a+1)) (5*(m+1)+r) c u v (by omega) (by omega))
  have e : 6+5*(a+1)-3 = 5*(a+1)+3 := by omega
  have f : 5*(m+1)+r-5 = 5*m+r := by omega
  simpa [zero,tok,e,f] using h

theorem gapStart (m r c : Nat) (u : List Nat) (v : List Token) (hr : 1 ≤ r) :
    Reach ⟨1,6,u,(5*(m+1)+r,c)::v⟩
      (zero 11 (inc u) ((5*m+r,c)::v)) := by
  have h := Reach.one (Step.split 1 6 (5*(m+1)+r) c u v (by decide) (by omega))
  have e : 5*(m+1)+r-5 = 5*m+r := by omega
  have h1 : Reach ⟨1,6,u,(5*(m+1)+r,c)::v⟩
      (pop 7 u (tok 0::(5*m+r,c)::v)) := by
    simpa [tok,e] using h
  exact Reach.trans h1 (joinPop 7 u ((5*m+r,c)::v) (by decide))

theorem gapLoop (m a r c : Nat) (v : List Token) (hr : 1 ≤ r) :
    Reach (zero (6+5*(a+1)) (E a ++ inc (E (m+1))) ((5*(m+1)+r,c)::v))
      (zero (6+5*(a+m+2)) (E (a+m+2)) ((r,c)::v)) := by
  induction m generalizing a with
  | zero =>
    have hs := gapSplit a 0 r c (E a ++ [2]) v hr
    simp only [Nat.mul_zero,Nat.zero_add] at hs
    have hd := standardAll a 2 [] ((r,c)::v)
    have e : 2+5*a+14 = 6+5*(a+0+2) := by omega
    have H := Reach.trans hs hd
    have he : E (a+1) ++ [1] = E (a+2) := by
      simp only [E,List.replicate_succ']
    simpa [E,inc,List.replicate_succ,e,he,List.append_assoc] using H
  | succ m ih =>
    have hs := gapSplit a (m+1) r c (E a ++ 2::E (m+1)) v hr
    have hd := standardAll a 2 (E (m+1)) ((5*(m+1)+r,c)::v)
    have e : 2+5*a+14 = 6+5*(a+1+1) := by omega
    rw [e] at hd
    have H := Reach.trans hs (Reach.trans hd (ih (a+1)))
    have f : a+1+m+2 = a+(m+1)+2 := by omega
    simpa [E,inc,List.replicate_succ,List.append_assoc,f] using H

/-- n indexes a general gap of size 5(n+1)+r. -/
theorem gapAll (n r c : Nat) (v : List Token) (hr : 1 ≤ r) :
    Reach ⟨1,6,E n,(5*(n+1)+r,c)::v⟩
      (zero (6+5*(n+1)) (E (n+1)) ((r,c)::v)) := by
  cases n with
  | zero => simpa [E,inc] using gapStart 0 r c [] v hr
  | succ n =>
    have h1 := gapStart (n+1) r c (E (n+1)) v hr
    have h2 := gapLoop n 0 r c v hr
    simpa [E,inc,List.replicate_succ,List.append_assoc] using Reach.trans h1 h2

def X (n : Nat) : C := zero (5*n+8) (E n) []

theorem growth (n : Nat) : Reach (X (n+1)) (X (n+2)) := by
  let b := 5*(n+1)+8
  have h1 := Reach.one (Step.blank 0 b (E (n+1)) (by dsimp [b]; omega))
  have e1 : b-3 = 5*(n+1)+5 := by dsimp [b]; omega
  have h1' : Reach (X (n+1)) ⟨1,6,E n,[(5*(n+1)+5,3)]⟩ := by
    simpa [X,zero,pop,E,List.replicate_succ,b,e1] using h1
  have h2 := gapAll n 5 3 [] (by decide)
  let d := 6+5*(n+1)
  have h3 := Reach.one (Step.five 0 d 3 (E (n+1)) [] (by dsimp [d]; omega))
  have e3 : d-3 = 5*(n+1)+3 := by dsimp [d]; omega
  have h3' : Reach (zero d (E (n+1)) [(5,3)])
      ⟨1,6,E n,[(5*(n+1)+3,6)]⟩ := by
    simpa [zero,pop,E,List.replicate_succ,d,e3] using h3
  have h4 := gapAll n 3 6 [] (by decide)
  have h5 := Reach.one (Step.join 0 d 6 (E (n+1)) [] (by dsimp [d]; omega) (by decide))
  have e5 : d+6+1 = 5*(n+2)+8 := by dsimp [d]; omega
  have h5' : Reach (zero d (E (n+1)) [(3,6)]) (X (n+2)) := by
    simpa [X,zero,E,List.replicate_succ,e5] using h5
  exact Reach.trans h1' (Reach.trans h2 (Reach.trans h3' (Reach.trans h4 h5')))

#print axioms standardAll
#print axioms gapAll
#print axioms growth
end BB6.Agent19Raw40.Leaf66Drain
