import Raw54E1RF47Runs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.RF47
open BB6Coverage BB6Coverage.Agent31Pump

-- Finite quotient of Nat: exact below four, modulo seven above it.
def cls (n : Nat) : Nat := if n < 4 then n else 4+(n-4)%7

theorem cls_lt (n : Nat) : cls n < 11 := by unfold cls; split <;> omega
theorem cls_add (a b : Nat) : cls (a+b) = cls (cls a+cls b) := by
  unfold cls
  split <;> split <;> split <;> (try split) <;> omega

theorem cls_small (n k : Nat) (hk : k<4) : cls n=k ↔ n=k := by unfold cls; split <;> omega
theorem cls_ge (n k : Nat) (hk : k≤4) : k≤cls n ↔ k≤n := by unfold cls; split <;> omega

def addA (a b : Nat) : Nat := cls (a+b)
def classR (p : Nat × Nat) : Nat × Nat := (cls p.1,cls p.2)

abbrev State (α : Type) := List α
abbrev Edges (α : Type) := List (State α × State α)
def stkPush (a : α) (s : State α) : State α := (a::s).take 4

-- Each concrete stack carries a complete suffix derivation in the finite graph.
inductive Rep (E : Edges α) : List α → State α → Prop where
  | nil : Rep E [] []
  | cons {a : α} {xs : List α} {s : State α} : Rep E xs s →
      (stkPush a s,s) ∈ E → Rep E (a::xs) (stkPush a s)

abbrev ML := State Nat
abbrev MR := State (Nat × Nat)
abbrev EL := Edges Nat
abbrev ER := Edges (Nat × Nat)
def LRep (E : EL) (l : LWord) (s : ML) : Prop := Rep E (l.map cls) s
def RRep (E : ER) (r : RWord) (s : MR) : Prop := Rep E (r.map classR) s

abbrev M (α : Type) := List (Option α)
def pureM (a : α) : M α := [some a]
def bindM (m : M α) (f : α → M β) : M β := m.flatMap (fun o => match o with | none => [none] | some a => f a)
def badM : M α := [none]
instance : Monad M where
  pure := pureM
  bind := bindM

def Good (m : M α) (P : α → Prop) : Prop := ∀ o ∈ m, match o with | none => False | some a => P a

theorem good_pure {a : α} {P : α → Prop} (h : Good (pureM a) P) : P a := h (some a) (by simp [pureM,M])
theorem good_bad {P : α → Prop} (h : Good badM P) : False := h none (by simp [badM,M])
theorem good_bind {m : M α} {f : α → M β} {P : β → Prop} (h : Good (bindM m f) P) : Good m (fun a => Good (f a) P) := by
  intro o ho
  cases o with
  | none =>
    exact h none (List.mem_flatMap.mpr ⟨none,ho,by simp⟩)
  | some a =>
    intro v hv
    exact h v (List.mem_flatMap.mpr ⟨some a,ho,hv⟩)

def popA [DecidableEq α] (E : Edges α) (s : State α) : M (Option (α × State α)) :=
  match s with
  | [] => pureM none
  | a::_ => (E.filter (fun e => e.1 == s)).map (fun e => some (some (a,e.2)))

def pushA [DecidableEq α] (E : Edges α) (a : α) (s : State α) : M (State α) :=
  if E.contains (stkPush a s,s) then pureM (stkPush a s) else badM

theorem pop_nil [DecidableEq α] {E : Edges α} {s : State α} {P : Option (α × State α) → Prop}
    (h : Rep E [] s) (g : Good (popA E s) P) : P none := by
  cases h; exact good_pure g

theorem pop_cons [DecidableEq α] {E : Edges α} {a : α} {xs : List α} {s : State α}
    {P : Option (α × State α) → Prop} (h : Rep E (a::xs) s) (g : Good (popA E s) P) :
    ∃ t, Rep E xs t ∧ P (some (a,t)) := by
  cases h with
  | @cons _ _ t ht he =>
    refine ⟨t,ht,g (some (some (a,t))) ?_⟩
    change some (some (a,t)) ∈ (E.filter (fun e => e.1 == stkPush a t)).map (fun e => some (some (a,e.2)))
    apply List.mem_map.mpr
    exact ⟨(stkPush a t,t),List.mem_filter.mpr ⟨he,by simp⟩,rfl⟩

theorem push_sound [DecidableEq α] {E : Edges α} {a : α} {xs : List α} {s : State α}
    {P : State α → Prop} (h : Rep E xs s) (g : Good (pushA E a s) P) :
    Rep E (a::xs) (stkPush a s) ∧ P (stkPush a s) := by
  unfold pushA at g
  split at g
  · rename_i he; exact ⟨Rep.cons h (List.contains_iff_mem.mp he),good_pure g⟩
  · exact False.elim (good_bad g)

def subA (a d : Nat) : M Nat := ((List.range 11).filter (fun x => addA x d == a)).map some

theorem sub_sound {n d : Nat} {P : Nat → Prop} (hd : d≤n) (hs : d<4) (h : Good (subA (cls n) d) P) : P (cls (n-d)) := by
  apply h (some (cls (n-d)))
  apply List.mem_map.mpr
  refine ⟨cls (n-d),List.mem_filter.mpr ⟨List.mem_range.mpr (cls_lt _),?_⟩,rfl⟩
  apply beq_iff_eq.mpr
  change cls (cls (n-d)+d) = cls n
  have hh := cls_add (n-d) d
  rw [(cls_small d d hs).mpr rfl] at hh
  rw [← hh]
  congr 1; omega

-- Leading left class, including the empty-stack convention.
theorem left_head {E : EL} {l : LWord} {s : ML} (h : LRep E l s) : s.headD 1 = cls (l.headD 1) := by
  cases l with
  | nil => cases h; rfl
  | cons a xs => cases h; rfl

def prependZA (E : ER) (s : MR) : M MR := do
  let t ← popA E s
  match t with
  | none => pure []
  | some ((g,b),rs) => pushA E (addA g 1,b) rs

def prependRunA (E : ER) (n : Nat) (s : MR) : M MR := do
  let t ← prependZA E s
  pushA E (0,n) t

def decLA (E : EL) (s : ML) : M ML := do
  let t ← popA E s
  match t with
  | none => pure []
  | some (g,ls) =>
    if g < 2 then badM else do
      let d ← subA g 1
      pushA E d ls

def stripRunA (E : ER) (s : MR) : M (Nat × MR) := do
  let t ← popA E s
  match t with
  | some ((g,b),rs) => if g=0 then pure (b,rs) else pure (0,s)
  | none => pure (0,s)

def a0A (ELs : EL) (ERs : ER) (l : ML) (r : MR) : M (ML × MR) := do
  let ld ← decLA ELs l
  let (b,rs) ← stripRunA ERs r
  let t ← popA ERs rs
  match t with
  | none => do
    let ll ← pushA ELs 0 ld
    let rr ← pushA ERs (0,addA b 2) []
    pure (ll,rr)
  | some ((g,c),rest) =>
    if g=0 ∨ c=0 then badM else
    if g=1 then do
      let cc ← subA c 1
      let rprog : M MR := if cc=0 then pureM rest else pushA ERs (0,cc) rest
      let rr ← rprog
      let ll ← pushA ELs 1 ld
      let ll ← pushA ELs b ll
      pure (ll,rr)
    else do
      let gg ← subA g 2
      let rprog : M MR := if gg=0 then pushA ERs (0,addA (addA b 2) c) rest else do
        let r2 ← pushA ERs (gg,c) rest
        pushA ERs (0,addA b 2) r2
      let rr ← rprog
      let ll ← pushA ELs 0 ld
      pure (ll,rr)

def a1A (ELs : EL) (ERs : ER) (l : ML) (r : MR) : M (ML × MR) := do
  let t ← popA ELs l
  match t with
  | none => badM
  | some (a,ls) => if a≠0 then badM else do
    let t ← popA ELs ls
    match t with
    | none => do
      let rr ← prependRunA ERs 3 r
      pure ([],rr)
    | some (g,rest) => if g=0 then badM else
      if g=1 then do
        let t ← popA ELs rest
        let lprog : M ML := match t with
          | none => pure []
          | some (h,tail) => pushA ELs (addA h 1) tail
        let ll ← lprog
        let ll ← pushA ELs 0 ll
        let rr ← prependZA ERs r
        pure (ll,rr)
      else if g=2 then
        if rest.headD 1 = 0 then badM else do
          let ll ← pushA ELs 0 rest
          let rr ← prependRunA ERs 2 r
          pure (ll,rr)
      else do
        let gg ← subA g 3
        let ll ← pushA ELs gg rest
        let rr ← prependRunA ERs 3 r
        pure (ll,rr)

def advanceA (ELs : EL) (ERs : ER) (l : ML) (r : MR) : M (ML × MR) :=
  if l.headD 1=0 then a1A ELs ERs l r else a0A ELs ERs l r

end BB6.Agent8Raw54.RF47
