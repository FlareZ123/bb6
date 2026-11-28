import TraceLogic
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
namespace F197.PackedCheck
open PrefixCheck

def pack : List Bool → Nat
  | [] => 1
  | b::xs => 2*pack xs + (if b then 1 else 0)

theorem pack_pos (xs : List Bool) : 0 < pack xs := by
  induction xs with
  | nil => decide
  | cons b xs ih => cases b <;> simp [pack] <;> omega

def pop (n : Nat) : Option (Bool × Nat) :=
  if n ≤ 1 then none else some (n%2 == 1,n/2)

@[simp] theorem pop_nil : pop (pack []) = none := rfl
@[simp] theorem pop_cons (b : Bool) (xs : List Bool) : pop (pack (b::xs)) = some (b,pack xs) := by
  have h := pack_pos xs
  cases b <;> simp [pop,pack,show ¬ 2*pack xs ≤ 1 by omega,show ¬ 2*pack xs+1 ≤ 1 by omega] <;> omega

theorem pack_inj (xs ys : List Bool) (h : pack xs = pack ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => have h' := congrArg pop h; simp at h'
  | cons x xs ih =>
    cases ys with
    | nil => have h' := congrArg pop h; simp at h'
    | cons y ys =>
      have h' := congrArg pop h
      simp only [pop_cons,Option.some.injEq,Prod.mk.injEq] at h'
      rw [h'.1,ih ys h'.2]

def push (b : Bool) (n : Nat) : Nat := 2*n+(if b then 1 else 0)
def pushs (w : List Bool) (n : Nat) := w.foldr push n
@[simp] theorem push_pack (b : Bool) (w : List Bool) : push b (pack w) = pack (b::w) := rfl
@[simp] theorem pushs_pack (w xs : List Bool) : pushs w (pack xs) = pack (w++xs) := by
  induction w with
  | nil => rfl
  | cons a w ih => change push a (pushs w (pack xs)) = pack (a::(w++xs)); rw [ih,push_pack]

structure PC where
  p : Phase
  l : Nat
  r : Nat
  deriving DecidableEq

def packC (c : C) : PC := ⟨c.p,pack c.l,pack c.r⟩

def pnext : PC → Option (Nat × PC)
  | ⟨.D,l,r⟩ => do
    let (a,l') ← pop l
    if a then none else do
      let (b,r') ← pop r
      let (c,r'') ← pop r'
      if !b then
        if c then some (4,⟨.D,pushs [false,true] l,r''⟩)
        else some (6,⟨.B,l',pushs [false,false,true] r''⟩)
      else do
        let (d,r''') ← pop r''
        if c then
          if d then some (5,⟨.D,pushs [false,true,false] l,r'''⟩)
          else some (9,⟨.D,pushs [false,true] l',pushs [false,true] r'''⟩)
        else if d then some (6,⟨.D,pushs [false,true] l,push false r'''⟩)
        else do
          let (e,r'''') ← pop r'''
          if e then none else some (4,⟨.D,pushs [false,true,true,false] l,r''''⟩)
  | ⟨.B,l,r⟩ => do
    let (a,r') ← pop r
    if a then none else do
      let (b,l') ← pop l
      if !b then some (2,⟨.D,pushs [false,true] l',r'⟩)
      else do
        let (c,l'') ← pop l'
        if c then some (2,⟨.B,l'',pushs [false,false,false] r'⟩)
        else some (2,⟨.F,l'',pushs [true,false,false] r'⟩)
  | ⟨.F,l,r⟩ => do
    let (a,l') ← pop l
    some (1,⟨if a then .F else .A,l',push true r⟩)
  | ⟨.A,l,r⟩ => do
    let (a,r') ← pop r
    if !a then none else do
      let (b,l') ← pop l
      if b then some (4,⟨.D,pushs [false,true] l',r'⟩)
      else some (3,⟨.B,l',pushs [false,false] r'⟩)

theorem pnext_sound (c : C) : pnext (packC c) = (next c).map (fun (n,c') => (n,packC c')) := by
  rcases c with ⟨p,l,r⟩
  cases p with
  | D =>
    cases l with
    | nil => simp [pnext,packC,next]
    | cons a l =>
      cases a with
      | true => simp [pnext,packC,next]
      | false =>
        cases r with
        | nil => simp [pnext,packC,next]
        | cons b r =>
          cases r with
          | nil => cases b <;> simp [pnext,packC,next]
          | cons c r =>
            cases b <;> cases c
            · simp [pnext,packC,next]
            · simp [pnext,packC,next]
            · cases r with
              | nil => simp [pnext,packC,next]
              | cons d r =>
                cases d with
                | false => cases r with
                  | nil => simp [pnext,packC,next]
                  | cons e r => cases e <;> simp [pnext,packC,next]
                | true => simp [pnext,packC,next]
            · cases r with
              | nil => simp [pnext,packC,next]
              | cons d r => cases d <;> simp [pnext,packC,next]
  | B =>
    cases r with
    | nil => cases l <;> simp [pnext,packC,next]
    | cons a r =>
      cases a with
      | true => cases l <;> simp [pnext,packC,next]
      | false =>
        cases l with
        | nil => simp [pnext,packC,next]
        | cons b l =>
          cases b with
          | false => simp [pnext,packC,next]
          | true => cases l with
            | nil => simp [pnext,packC,next]
            | cons c l => cases c <;> simp [pnext,packC,next]
  | F => cases l with
    | nil => simp [pnext,packC,next]
    | cons a l => cases a <;> simp [pnext,packC,next]
  | A =>
    cases r with
    | nil => cases l <;> simp [pnext,packC,next]
    | cons a r => cases a with
      | false => cases l <;> simp [pnext,packC,next]
      | true => cases l with
        | nil => simp [pnext,packC,next]
        | cons b l => cases b <;> simp [pnext,packC,next]

def pexec : Nat → PC → Option (Nat × PC)
  | 0,c => some (0,c)
  | n+1,c => do
    let (t,c') ← pnext c
    let (u,c'') ← pexec n c'
    return (t+u,c'')

theorem pexec_eq (k : Nat) (c : C) : pexec k (packC c) = (exec k c).map (fun (n,c') => (n,packC c')) := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    simp only [pexec,exec,pnext_sound]
    cases h : next c with
    | none => rfl
    | some v =>
      rcases v with ⟨t,c'⟩
      change (pexec k (packC c')).bind (fun (u,d) => some (t+u,d)) =
        ((exec k c').bind (fun (u,d) => some (t+u,d))).map (fun (n,d) => (n,packC d))
      rw [ih]
      cases h' : exec k c' with
      | none => rfl
      | some v => rcases v with ⟨u,c''⟩; rfl

def pexecAcc : Nat → PC → Nat → Option (Nat × PC)
  | 0,c,a => some (a,c)
  | n+1,c,a => match pnext c with
    | none => none
    | some (t,c') => pexecAcc n c' (a+t)

theorem pexecAcc_eq (k : Nat) (c : PC) (a : Nat) :
    pexecAcc k c a = (pexec k c).map (fun (t,c') => (a+t,c')) := by
  induction k generalizing c a with
  | zero => simp [pexecAcc,pexec]
  | succ k ih =>
    simp only [pexecAcc,pexec]
    cases h : pnext c with
    | none => rfl
    | some v =>
      rcases v with ⟨t,c'⟩
      change pexecAcc k c' (a+t) = ((pexec k c').bind (fun (u,d) => some (t+u,d))).map (fun (n,d) => (a+n,d))
      rw [ih]
      change (pexec k c').map (fun (u,d) => (a+t+u,d)) =
        ((pexec k c').bind (fun (u,d) => some (t+u,d))).map (fun (n,d) => (a+n,d))
      cases h' : pexec k c' with
      | none => rfl
      | some v => rcases v with ⟨u,d⟩; simp [Nat.add_assoc]

def pexecFast (k : Nat) (c : PC) := pexecAcc k c 0

theorem pexecFast_eq (k : Nat) (c : PC) : pexecFast k c = pexec k c := by
  rw [pexecFast,pexecAcc_eq]
  cases h : pexec k c with
  | none => rfl
  | some v => rcases v with ⟨t,c'⟩; simp

theorem pexecAcc_add (n m : Nat) (c : PC) (a : Nat) :
    pexecAcc (n+m) c a = (pexecAcc n c a).bind (fun (t,d) => pexecAcc m d t) := by
  induction n generalizing c a with
  | zero => simp [pexecAcc]
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [pexecAcc]
    cases h : pnext c with
    | none => rfl
    | some v => rcases v with ⟨t,d⟩; exact ih d (a+t)

theorem pexecFast_compose (n m t u : Nat) (a b c : PC)
    (h1 : pexecFast n a = some (t,b)) (h2 : pexecFast m b = some (u,c)) :
    pexecFast (n+m) a = some (t+u,c) := by
  unfold pexecFast at h1 ⊢
  rw [pexecAcc_add,h1]
  change pexecAcc m b t = some (t+u,c)
  rw [pexecAcc_eq,← pexecFast_eq,h2]
  rfl

theorem packC_inj (c d : C) (h : packC c = packC d) : c = d := by
  rcases c with ⟨p,l,r⟩; rcases d with ⟨q,a,b⟩
  simp only [packC,PC.mk.injEq] at h
  rw [h.1,pack_inj l a h.2.1,pack_inj r b h.2.2]

theorem pexec_check (k t : Nat) (c c' : C)
    (h : pexecFast k (packC c) = some (t,packC c')) : exec k c = some (t,c') := by
  rw [pexecFast_eq,pexec_eq] at h
  cases he : exec k c with
  | none => simp [he] at h
  | some v =>
    rcases v with ⟨u,d⟩
    simp only [he,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
    rw [h.1,packC_inj d c' h.2]

open Agent2Self Agent2Counter

def fastRuleOK : Rule → Bool
  | .core W Y k j add steps cost => W.head? == some true && (flat P add ++ Y).head? == some true &&
      (pexecFast steps (packC (guard W (u ++ flat s k))) == some (cost,packC (guard (J ++ (flat P add ++ Y)) (x ++ flat s j))))
  | .direct W Y n n' pad steps cost => (cost > 0) &&
      (pexecFast steps (packC (guardBlank (flat P n ++ W) ([true] ++ List.replicate pad false))) ==
        some (cost,packC (guardBlank (flat P n' ++ Y) [true])))

theorem fastRuleOK_sound (r : Rule) (h : fastRuleOK r = true) : ruleOK r = true := by
  cases r with
  | core W Y k j add steps cost =>
    simp only [fastRuleOK,Bool.and_eq_true,beq_iff_eq] at h
    simp only [ruleOK,Bool.and_eq_true,beq_iff_eq]
    exact ⟨h.1,pexec_check steps cost _ _ h.2⟩
  | direct W Y n n' pad steps cost =>
    simp only [fastRuleOK,Bool.and_eq_true,beq_iff_eq] at h
    simp only [ruleOK,Bool.and_eq_true,beq_iff_eq]
    exact ⟨h.1,pexec_check steps cost _ _ h.2⟩

def fastTerminalOK (t : Terminal) : Bool :=
  okHead t.src && okHead t.dst &&
    (pexecFast t.steps (packC (guard t.src [])) == some (t.cost,packC (guard (J++t.dst) XC)))

theorem fastTerminalOK_sound (t : Terminal) (h : fastTerminalOK t = true) : epochOK t = true := by
  simp only [fastTerminalOK,Bool.and_eq_true,beq_iff_eq] at h
  simp only [epochOK,terminalOK,Bool.and_eq_true,beq_iff_eq]
  exact ⟨h.1,pexec_check t.steps t.cost _ _ h.2⟩

def fastOpOK : Op → Bool | .loc r => fastRuleOK r | .epoch t => fastTerminalOK t

theorem fastOpOK_sound (o : Op) (h : fastOpOK o = true) : opOK o = true := by
  cases o with
  | loc r => exact fastRuleOK_sound r h
  | epoch t => exact fastTerminalOK_sound t h

#print axioms fastOpOK_sound
#print axioms pnext_sound
end F197.PackedCheck
