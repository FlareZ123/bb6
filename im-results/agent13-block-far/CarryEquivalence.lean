import CarryMacro

namespace BB6Carry
open BB6BlockFAR

structure MacroCfg where
  phase : Phase
  left : List Bool
  right : Ray

def MacroCfg.render (c : MacroCfg) : Prim := BB6Carry.render c.phase c.left c.right

def MacroCfg.good (c : MacroCfg) : Prop :=
  match c.phase with
  | .B => True
  | .F => c.right 0 = false
  | .C => c.right 0 = true ∧ c.right 1 = false

def initial : MacroCfg := ⟨.B,[true],blankRay⟩

def drop (n : Nat) (r : Ray) : Ray := fun i => r (n+i)

theorem split1 (r : Ray) : cons (r 0) (drop 1 r) = r := by
  funext i
  cases i with
  | zero => rfl
  | succ i => simp [cons,drop,Nat.add_comm]

theorem split2 (r : Ray) : bits [r 0,r 1] (drop 2 r) = r := by
  funext i
  rcases i with _|_|i
  · rfl
  · rfl
  · simp [bits,cons,drop]; congr 1; omega

theorem split3 (r : Ray) : bits [r 0,r 1,r 2] (drop 3 r) = r := by
  funext i
  rcases i with _|_|_|i
  · rfl
  · rfl
  · rfl
  · simp [bits,cons,drop]; congr 1; omega

theorem split4 (r : Ray) : bits [r 0,r 1,r 2,r 3] (drop 4 r) = r := by
  funext i
  rcases i with _|_|_|_|i
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [bits,cons,drop]; congr 1; omega

/-- Next macro configuration, with both exact primitive costs. -/
structure MacroExit where
  next : MacroCfg
  fast : Nat
  slow : Nat

def MacroExit.cost (e : MacroExit) (slow : Bool) := if slow then e.slow else e.fast

def advance (c : MacroCfg) : Option MacroExit :=
  let l := c.left
  let r := c.right
  match c.phase with
  | .B =>
    match r 0,r 1,r 2,r 3 with
    | true,true,_,_ => none
    | true,false,_,_ => some ⟨⟨.B,true::l,drop 2 r⟩,2,2⟩
    | false,true,_,_ => some ⟨⟨.F,l,bits [false,false] (drop 2 r)⟩,3,7⟩
    | false,false,false,_ => some ⟨⟨.F,l,bits [false,false,true] (drop 3 r)⟩,7,7⟩
    | false,false,true,false => some ⟨⟨.B,false::false::l,drop 4 r⟩,4,4⟩
    | false,false,true,true => some ⟨⟨.F,l,bits [false,true,false,false] (drop 4 r)⟩,7,7⟩
  | .F =>
    match l with
    | [] => some ⟨⟨.B,[false],drop 1 r⟩,4,4⟩
    | false::l => some ⟨⟨.F,l,bits [false,true] r⟩,2,2⟩
    | true::l => some ⟨⟨.C,l,bits [true,false,false] (drop 1 r)⟩,2,6⟩
  | .C =>
    match l with
    | [] => some ⟨⟨.B,[false],drop 2 r⟩,3,3⟩
    | false::l => some ⟨⟨.B,false::false::l,drop 2 r⟩,3,3⟩
    | true::l => some ⟨⟨.C,l,bits [true,false] r⟩,2,2⟩

theorem initial_good : initial.good := trivial

theorem advance_sound (c : MacroCfg) (hc : c.good) (e : MacroExit) (he : advance c = some e) (slow : Bool) :
    e.next.good ∧ 0 < e.cost slow ∧ run (machine slow) (e.cost slow) c.render = some e.next.render := by
  rcases c with ⟨p,l,r⟩
  cases p with
  | B =>
    cases h0 : r 0 <;> cases h1 : r 1 <;> cases h2 : r 2 <;> cases h3 : r 3 <;>
      simp [advance,h0,h1,h2,h3] at he
    all_goals subst e
    all_goals refine ⟨by first | trivial | rfl, by cases slow <;> simp [MacroExit.cost], ?_⟩
    all_goals simp only [MacroExit.cost,MacroCfg.render,ite_self]
    all_goals first
      | have H := split2 r; rw [h0,h1] at H; rw [show BB6Carry.render .B l r = BB6Carry.render .B l (bits [false,true] (drop 2 r)) from congrArg (BB6Carry.render .B l) H.symm]; exact B01 slow l (drop 2 r)
      | have H := split2 r; rw [h0,h1] at H; rw [show BB6Carry.render .B l r = BB6Carry.render .B l (bits [true,false] (drop 2 r)) from congrArg (BB6Carry.render .B l) H.symm]; exact B10 slow l (drop 2 r)
      | have H := split3 r; rw [h0,h1,h2] at H; rw [show BB6Carry.render .B l r = BB6Carry.render .B l (bits [false,false,false] (drop 3 r)) from congrArg (BB6Carry.render .B l) H.symm]; exact B000 slow l (drop 3 r)
      | have H := split4 r; rw [h0,h1,h2,h3] at H; rw [show BB6Carry.render .B l r = BB6Carry.render .B l (bits [false,false,true,false] (drop 4 r)) from congrArg (BB6Carry.render .B l) H.symm]; exact B0010 slow l (drop 4 r)
      | have H := split4 r; rw [h0,h1,h2,h3] at H; rw [show BB6Carry.render .B l r = BB6Carry.render .B l (bits [false,false,true,true] (drop 4 r)) from congrArg (BB6Carry.render .B l) H.symm]; exact B0011 slow l (drop 4 r)
  | F =>
    change r 0 = false at hc
    cases l with
    | nil =>
      simp [advance] at he; subst e
      refine ⟨trivial,by cases slow <;> simp [MacroExit.cost],?_⟩
      have H := split1 r; rw [hc] at H
      simp only [MacroExit.cost,MacroCfg.render,ite_self]
      conv => lhs; rw [← H]
      exact Fnil slow (drop 1 r)
    | cons a l =>
      cases a <;> simp [advance] at he <;> subst e
      · refine ⟨rfl,by cases slow <;> simp [MacroExit.cost],?_⟩
        simpa [MacroExit.cost,MacroCfg.render] using F01 slow l r
      · refine ⟨⟨rfl,rfl⟩,by cases slow <;> simp [MacroExit.cost],?_⟩
        have H := split1 r; rw [hc] at H
        simp only [MacroExit.cost,MacroCfg.render]
        conv => lhs; rw [← H]
        exact F10 slow l (drop 1 r)
  | C =>
    change r 0 = true ∧ r 1 = false at hc
    cases l with
    | nil =>
      simp [advance] at he; subst e
      refine ⟨trivial,by cases slow <;> simp [MacroExit.cost],?_⟩
      have H := split2 r; rw [hc.1,hc.2] at H
      simp only [MacroExit.cost,MacroCfg.render,ite_self]
      conv => lhs; rw [← H]
      exact Cnil slow (drop 2 r)
    | cons a l =>
      cases a <;> simp [advance] at he <;> subst e
      · refine ⟨trivial,by cases slow <;> simp [MacroExit.cost],?_⟩
        have H := split2 r; rw [hc.1,hc.2] at H
        simp only [MacroExit.cost,MacroCfg.render,ite_self]
        conv => lhs; rw [← H]
        exact C01 slow l (drop 2 r)
      · refine ⟨⟨rfl,rfl⟩,by cases slow <;> simp [MacroExit.cost],?_⟩
        simpa [MacroExit.cost,MacroCfg.render] using C10 slow l r

theorem advance_halt (c : MacroCfg) (h : advance c = none) (slow : Bool) :
    run (machine slow) 2 c.render = none := by
  rcases c with ⟨p,l,r⟩
  cases p with
  | B =>
    cases h0 : r 0 <;> cases h1 : r 1 <;> cases h2 : r 2 <;> cases h3 : r 3 <;>
      simp [advance,h0,h1,h2,h3] at h
    all_goals have H := split2 r; rw [h0,h1] at H
    all_goals simp only [MacroCfg.render]
    all_goals rw [← H]
    all_goals cases slow <;> rfl
  | F => cases l with
    | nil => simp [advance] at h
    | cons a l => cases a <;> simp [advance] at h
  | C => cases l with
    | nil => simp [advance] at h
    | cons a l => cases a <;> simp [advance] at h

def mrun : Nat → MacroCfg → Option MacroCfg
  | 0,c => some c
  | n+1,c => (advance c).bind (fun e => mrun n e.next)

def PrimSafe (slow : Bool) (c : MacroCfg) : Prop :=
  ∀ n, ∃ d, run (machine slow) n c.render = some d

def MacroSafe (c : MacroCfg) : Prop := ∀ n, ∃ d, mrun n c = some d

theorem prim_safe_next (slow : Bool) (c : MacroCfg) (e : MacroExit)
    (hc : c.good) (he : advance c = some e) (hsafe : PrimSafe slow c) : PrimSafe slow e.next := by
  intro n
  obtain ⟨d,hd⟩ := hsafe (e.cost slow+n)
  rw [run_add,(advance_sound c hc e he slow).2.2] at hd
  exact ⟨d,hd⟩

theorem prim_safe_macro_safe (slow : Bool) (c : MacroCfg) (hc : c.good)
    (h : PrimSafe slow c) : MacroSafe c := by
  intro n
  induction n generalizing c with
  | zero => exact ⟨c,rfl⟩
  | succ n ih =>
    cases he : advance c with
    | none => obtain ⟨d,hd⟩ := h 2; rw [advance_halt c he slow] at hd; contradiction
    | some e =>
      obtain ⟨d,hd⟩ := ih e.next (advance_sound c hc e he slow).1 (prim_safe_next slow c e hc he h)
      exact ⟨d,by simp [mrun,he,hd]⟩

theorem macro_safe_prim_safe (slow : Bool) (c : MacroCfg) (hc : c.good)
    (h : MacroSafe c) : PrimSafe slow c := by
  intro n
  induction n using Nat.strongRecOn generalizing c with
  | ind n ih =>
    obtain ⟨d,hd⟩ := h 1
    cases he : advance c with
    | none => simp [mrun,he] at hd
    | some e =>
      have H := advance_sound c hc e he slow
      have hnext : MacroSafe e.next := by
        intro k
        obtain ⟨x,hx⟩ := h (k+1)
        exact ⟨x,by simpa [mrun,he] using hx⟩
      by_cases hle : e.cost slow ≤ n
      · obtain ⟨x,hx⟩ := ih (n-e.cost slow) (by omega) e.next H.1 hnext
        exact ⟨x,by rw [show n=e.cost slow+(n-e.cost slow) by omega,run_add,H.2.2]; exact hx⟩
      · have hr := H.2.2
        rw [show e.cost slow=n+(e.cost slow-n) by omega,run_add] at hr
        cases hn : run (machine slow) n c.render with
        | none => simp [hn] at hr
        | some x => exact ⟨x,rfl⟩

theorem blank_safe_iff (slow : Bool) :
    (∀ n, ∃ d, run (machine slow) n primBlank = some d) ↔ MacroSafe initial := by
  have H : run (machine slow) 1 primBlank = some initial.render := start slow
  constructor
  · intro h
    apply prim_safe_macro_safe slow initial initial_good
    intro n
    obtain ⟨d,hd⟩ := h (1+n)
    rw [run_add,H] at hd
    exact ⟨d,hd⟩
  · intro h n
    cases n with
    | zero => exact ⟨primBlank,rfl⟩
    | succ n =>
      obtain ⟨d,hd⟩ := macro_safe_prim_safe slow initial initial_good h n
      exact ⟨d,by rw [show n+1=1+n by omega,run_add,H]; exact hd⟩

theorem equivalence :
    (∀ n, ∃ d, run (machine false) n primBlank = some d) ↔
    (∀ n, ∃ d, run (machine true) n primBlank = some d) :=
  (blank_safe_iff false).trans (blank_safe_iff true).symm

#print axioms advance_sound
#print axioms advance_halt
#print axioms equivalence
end BB6Carry
