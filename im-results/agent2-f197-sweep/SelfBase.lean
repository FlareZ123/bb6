import CounterCore
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace F197.Agent2Self
open Agent2EpochMarker (b pre_append zeros_blank)
open Agent2Counter
open PrefixCheck
abbrev Reach (a b : Config) : Prop := ∃ t : Nat, run t a = some b
abbrev ReachPos (a b : Config) : Prop := ∃ t : Nat, 0 < t ∧ run t a = some b

theorem reach_refl (a : Config) : Reach a a := ⟨0,rfl⟩
theorem reach_trans {a b c : Config} (h1 : Reach a b) (h2 : Reach b c) : Reach a c := by
  obtain ⟨t,h1⟩ := h1; obtain ⟨u,h2⟩ := h2
  exact ⟨t+u,Agent2EpochMarker.compose h1 h2⟩
theorem reach_pos_trans {a b c : Config} (h1 : ReachPos a b) (h2 : Reach b c) : ReachPos a c := by
  obtain ⟨t,ht,h1⟩ := h1; obtain ⟨u,h2⟩ := h2
  exact ⟨t+u,by omega,Agent2EpochMarker.compose h1 h2⟩

theorem reach_trans_pos {a b c : Config} (h1 : Reach a b) (h2 : ReachPos b c) : ReachPos a c := by
  obtain ⟨t,h1⟩ := h1; obtain ⟨u,hu,h2⟩ := h2
  exact ⟨t+u,by omega,Agent2EpochMarker.compose h1 h2⟩

theorem reach_of_pos {a b : Config} (h : ReachPos a b) : Reach a b := by
  obtain ⟨t,_,h⟩ := h; exact ⟨t,h⟩

def okHead (w : Word) : Bool := w.isEmpty || w.head? == some true

theorem pre_first (w : Word) (l : Tape) (hw : okHead w = true) (hl : l 0 = true) : pre w l 0 = true := by
  cases w with
  | nil => exact hl
  | cons h t => cases h <;> simp [okHead] at hw ⊢ <;> rfl

def flat (w : Word) (n : Nat) : Word := List.flatten (List.replicate n w)
theorem flat_pre (w : Word) (n : Nat) (l : Tape) : pre (flat w n) l = rep w n l := by
  induction n with
  | zero => rfl
  | succ n ih => rw [flat,List.replicate_succ]; simp only [List.flatten_cons,pre_append,rep]; change pre w (pre (flat w n) l) = pre w (rep w n l); rw [ih]

def state (n : Nat) (w : Word) (l : Tape) := b (rep P n (pre w l)) e

theorem core_lift (W Y S : Word) (k j add extra steps cost : Nat) (l : Tape) (hl : l 0 = true)
    (hs : okHead S = true) (hw : W.head? = some true) (hy : (flat P add ++ Y).head? = some true)
    (cert : exec steps (guard W (u ++ flat s k)) = some (cost, guard (J ++ (flat P add ++ Y)) (x ++ flat s j))) :
    ReachPos (state (k+extra+1) (W++S) l) (state (j+extra+1+add) (Y++S) l) := by
  have h := core k j extra steps cost W (flat P add ++ Y) (pre S l) (pre_first S l hs hl) hw hy cert
  rw [pre_append (flat P add) Y,flat_pre,← rep_add,← pre_append W S,← pre_append Y S] at h
  exact ⟨_,by omega,h⟩

theorem direct_lift (W Y S : Word) (n n' pad steps cost : Nat) (l : Tape) (hl : l 0 = true)
    (hs : okHead S = true) (hcost : cost > 0)
    (cert : exec steps (guardBlank (flat P n ++ W) ([true] ++ List.replicate pad false)) =
      some (cost, guardBlank (flat P n' ++ Y) [true])) :
    ReachPos (state n (W++S) l) (state n' (Y++S) l) := by
  have h := guardBlank_sound (flat P n ++ W) ([true] ++ List.replicate pad false)
    (flat P n' ++ Y) [true] steps cost (pre S l) (pre_first S l hs hl) cert
  rw [pre_append,pre_append,pre_append,zeros_blank,flat_pre,flat_pre,← pre_append,← pre_append] at h
  exact ⟨cost,hcost,h⟩

inductive Rule where
  | core (src dst : Word) (k j add steps cost : Nat)
  | direct (src dst : Word) (n n' pad steps cost : Nat)
  deriving Repr

def ruleOK : Rule → Bool
  | .core W Y k j add steps cost => W.head? == some true && (flat P add ++ Y).head? == some true &&
      (exec steps (guard W (u ++ flat s k)) == some (cost,guard (J ++ (flat P add ++ Y)) (x ++ flat s j)))
  | .direct W Y n n' pad steps cost => (cost > 0) &&
      (exec steps (guardBlank (flat P n ++ W) ([true] ++ List.replicate pad false)) ==
        some (cost,guardBlank (flat P n' ++ Y) [true]))

def ruleSrc : Rule → Word | .core W .. | .direct W .. => W

def applyRule (r : Rule) (n : Nat) (w : Word) : Option (Nat × Word) := do
  let W := ruleSrc r
  let S := w.drop W.length
  if w.take W.length != W || !okHead S then none else
    match r with
    | .core _ Y k j add _ _ => if k+1 ≤ n then some (n-k+j+add,Y++S) else none
    | .direct _ Y N N' _ _ _ => if n == N then some (N',Y++S) else none

theorem apply_sound (r : Rule) (n n' : Nat) (w w' : Word) (l : Tape) (hl : l 0 = true)
    (hok : ruleOK r = true) (ha : applyRule r n w = some (n',w')) : ReachPos (state n w l) (state n' w' l) := by
  cases r with
  | core W Y k j add steps cost =>
    simp only [ruleOK,Bool.and_eq_true,beq_iff_eq] at hok
    simp [applyRule,ruleSrc] at ha
    obtain ⟨⟨hp,hs⟩,hn,he1,he2⟩ := ha
    let S := w.drop W.length
    have hS : w = W ++ S := by
      dsimp [S]
      conv => lhs; rw [← List.take_append_drop W.length w]
      rw [hp]
    have h := core_lift W Y S k j add (n-k-1) steps cost l hl hs hok.1.1 hok.1.2 hok.2
    have h1 : k+(n-k-1)+1 = n := by omega
    have h2 : j+(n-k-1)+1+add = n-k+j+add := by omega
    rw [h1,h2,← hS,he1,he2] at h
    exact h
  | direct W Y N N' pad steps cost =>
    simp only [ruleOK,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at hok
    simp [applyRule,ruleSrc] at ha
    obtain ⟨⟨hp,hs⟩,hn,he1,he2⟩ := ha
    let S := w.drop W.length
    have hS : w = W ++ S := by
      dsimp [S]
      conv => lhs; rw [← List.take_append_drop W.length w]
      rw [hp]
    have h := direct_lift W Y S N N' pad steps cost l hl hs hok.1 hok.2
    rw [← hS,← hn,he1,he2] at h
    exact h

def applyRules (rs : List Rule) (n : Nat) (w : Word) : Option (Nat × Word) :=
  match rs with
  | [] => some (n,w)
  | r::rs => do
    let (n',w') ← applyRule r n w
    applyRules rs n' w'

theorem applyRules_sound (rs : List Rule) (n n' : Nat) (w w' : Word) (l : Tape) (hl : l 0 = true)
    (hok : rs.all ruleOK = true) (ha : applyRules rs n w = some (n',w')) : Reach (state n w l) (state n' w' l) := by
  induction rs generalizing n w with
  | nil => simp [applyRules] at ha; obtain ⟨rfl,rfl⟩ := ha; exact reach_refl _
  | cons r rs ih =>
    simp only [List.all_cons,Bool.and_eq_true] at hok
    simp only [applyRules] at ha
    cases h : applyRule r n w with
    | none => simp [h] at ha
    | some v =>
      rcases v with ⟨m,z⟩
      simp [h] at ha
      obtain ⟨t,_,ht⟩ := apply_sound r n m w z l hl hok.1 h
      exact reach_trans ⟨t,ht⟩ (ih m z hok.2 ha)

def coreOnly : Rule → Bool | .core .. => true | _ => false

theorem apply_shift (r : Rule) (n m a : Nat) (w z : Word) (hc : coreOnly r = true)
    (h : applyRule r n w = some (m,z)) : applyRule r (n+a) w = some (m+a,z) := by
  cases r with
  | direct W Y N N' pad steps cost => simp [coreOnly] at hc
  | core W Y k j add steps cost =>
    simp [applyRule,ruleSrc] at h ⊢
    obtain ⟨hp,hn,h1,h2⟩ := h
    exact ⟨hp,by omega,by omega,h2⟩

theorem applyRules_shift (rs : List Rule) (n m a : Nat) (w z : Word) (hc : rs.all coreOnly = true)
    (h : applyRules rs n w = some (m,z)) : applyRules rs (n+a) w = some (m+a,z) := by
  induction rs generalizing n w with
  | nil => simp [applyRules] at h ⊢; obtain ⟨rfl,rfl⟩ := h; simp
  | cons r rs ih =>
    simp only [List.all_cons,Bool.and_eq_true] at hc
    simp only [applyRules] at h ⊢
    cases hh : applyRule r n w with
    | none => simp [hh] at h
    | some v =>
      rcases v with ⟨p,q⟩
      simp [hh] at h
      simp [apply_shift r n p a w q hc.1 hh]
      exact ih p q hc.2 h

#print axioms applyRules_sound
#print axioms applyRules_shift
end F197.Agent2Self
