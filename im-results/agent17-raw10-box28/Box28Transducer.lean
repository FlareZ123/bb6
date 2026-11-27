import Box28CarryFamily

namespace BB6.Agent17.Box28Transducer
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

abbrev S := Fin 3
abbrev Code := Fin 6
def dst (c : Code) : S := ⟨c.val/2, by have h := c.isLt; omega⟩
def wr (c : Code) : Bool := decide (c.val%2=1)
structure OneParams where
  a : Code
  e : Code
  f : Code
  deriving DecidableEq
structure Params where
  o : OneParams
  ze : Code
  zf : Code
  deriving DecidableEq
def one (p : OneParams) (s : S) : Code := if s=0 then p.a else if s=1 then p.e else p.f
def zero (p : Params) (s : S) : Code := if s=1 then p.ze else p.zf
def inc (c : Code) (r : Nat) : Nat := if wr c then r+1 else 0

/-- Rightward scan over a known unary prefix, tracking only the trailing
    run of written ones. The left tape beyond the most recent zero is free. -/
def scan (p : OneParams) : Nat → S → Nat → S × Nat
  | 0,s,r => (s,r)
  | n+1,s,r => scan p n (dst (one p s)) (inc (one p s) r)
def allOne (p : OneParams) : Nat → S → Bool
  | 0,_ => true
  | n+1,s => wr (one p s) && allOne p n (dst (one p s))

theorem scan_add (p : OneParams) (n m : Nat) (s : S) (r : Nat) :
    scan p (n+m) s r = scan p m (scan p n s r).1 (scan p n s r).2 := by
  induction n generalizing s r with
  | zero => rfl
  | succ n ih => rw [Nat.succ_add,scan,scan,ih]

theorem scan_shift (p : OneParams) (n : Nat) (s : S) (r d : Nat) :
    scan p n s (r+d) =
      ((scan p n s r).1, (scan p n s r).2 + if allOne p n s then d else 0) := by
  induction n generalizing s r with
  | zero => rfl
  | succ n ih =>
    simp only [scan,allOne]
    cases hw : wr (one p s)
    · simp [inc,hw]
    · simp only [inc,hw,if_true,Bool.true_and]
      rw [show r+d+1=r+1+d by omega,ih]

/-- The finite check is over just the 216 one-transition triples and six
    residues, not over all machines or unbounded lengths. At length at
    least eight the six-step block is in its eventual cycle. -/
theorem loop_check : ∀ (a e f : Code) (r : Fin 6),
    let p : OneParams := ⟨a,e,f⟩
    let n := 8+r.val
    let h := scan p n 1 0
    let l := scan p 6 h.1 h.2
    l.1=h.1 ∧ (if allOne p 6 h.1 then l.2=h.2+6 ∧ n≤h.2+2 else l.2=h.2) := by decide

theorem loop_fact (p : OneParams) (r : Fin 6) :
    let n := 8+r.val
    let h := scan p n 1 0
    let l := scan p 6 h.1 h.2
    l.1=h.1 ∧ (if allOne p 6 h.1 then l.2=h.2+6 ∧ n≤h.2+2 else l.2=h.2) := by
  rcases p with ⟨a,e,f⟩
  exact loop_check a e f r

theorem scan_period (p : OneParams) (r : Fin 6) (k : Nat) :
    scan p (8+r.val+6*k) 1 0 =
      let h := scan p (8+r.val) 1 0
      (h.1,h.2 + if allOne p 6 h.1 then 6*k else 0) := by
  let n := 8+r.val
  let h := scan p n 1 0
  change scan p (n+6*k) 1 0 = (h.1,h.2+ if allOne p 6 h.1 then 6*k else 0)
  have hf := loop_fact p r
  change (scan p 6 h.1 h.2).1=h.1 ∧
    (if allOne p 6 h.1 then (scan p 6 h.1 h.2).2=h.2+6 ∧ n≤h.2+2
     else (scan p 6 h.1 h.2).2=h.2) at hf
  induction k with
  | zero => simp [h]
  | succ k ih =>
    rw [show n+6*(k+1)=n+6*k+6 by omega,scan_add,ih]
    change scan p 6 h.1 (h.2+ if allOne p 6 h.1 then 6*k else 0) = _
    rw [scan_shift]
    cases hb : allOne p 6 h.1
    · simp only [hb,if_false,Nat.add_zero] at hf ⊢
      exact Prod.ext hf.1 hf.2
    · simp only [hb,if_true] at hf ⊢
      exact Prod.ext hf.1 (by rw [hf.2.1]; omega)

/-- The two gap/marker moves and at most two subsequent zero moves.
    None means the zero orbit never reaches A. -/
def tailCodes (p : Params) (s : S) : Option (List Code) :=
  let c := zero p s
  let d := one p.o (dst c)
  let q := dst d
  if q=0 then some [c,d] else
    let e := zero p q
    if dst e=0 then some [c,d,e] else
      let f := zero p (dst e)
      if dst f=0 then some [c,d,e,f] else none

def countList : List Code → Nat → Nat
  | [],r => r
  | c::cs,r => countList cs (inc c r)

theorem count_shift (l : List Code) (r d : Nat) :
    countList l (r+d) = countList l r + if l.all wr then d else 0 := by
  induction l generalizing r with
  | nil => rfl
  | cons c cs ih =>
    simp only [countList,List.all_cons]
    cases hw : wr c
    · simp [inc,hw]
    · simp only [inc,hw,if_true,Bool.true_and]
      rw [show r+d+1=r+1+d by omega,ih]

theorem count_all (l : List Code) (r : Nat) (h : l.all wr = true) :
    countList l r = r+l.length := by
  induction l generalizing r with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.all_cons,Bool.and_eq_true] at h
    rw [countList,inc,if_pos h.1,ih _ h.2,List.length_cons]
    omega

theorem tail_length (p : Params) (s : S) (l : List Code) (h : tailCodes p s = some l) :
    2≤l.length := by
  unfold tailCodes at h
  split at h
  · cases h; decide
  · split at h
    · cases h; decide
    · split at h
      · cases h; decide
      · contradiction

inductive Outcome where
  | halt
  | drift
  | next (n : Nat)
  deriving DecidableEq, Repr

def concreteStep (p : Params) (n : Nat) : Outcome :=
  let h := scan p.o n 1 0
  if h.1=0 then .halt else
    match tailCodes p h.1 with
    | none => .drift
    | some l => .next (countList l h.2)

def classOf (n : Nat) : Nat := if n<8 then n else 8+(n-8)%6
def abstractStep (p : Params) (n : Nat) : Outcome :=
  match concreteStep p n with
  | .halt => .halt
  | .drift => .drift
  | .next m => .next (classOf m)

theorem class_add (n k : Nat) (h : 8≤n) :
    classOf (n+6*k) = classOf n := by
  unfold classOf
  rw [if_neg (by omega),if_neg (by omega)]
  omega

/-- Exact quotient congruence for every representative plus an arbitrary
    number of six-step blocks. No bound on the real tape length is assumed. -/
theorem step_period (p : Params) (r : Fin 6) (k : Nat) :
    abstractStep p (8+r.val+6*k) = abstractStep p (8+r.val) := by
  let n := 8+r.val
  let h := scan p.o n 1 0
  have hs := scan_period p.o r k
  change scan p.o (n+6*k) 1 0 = (h.1,h.2+ if allOne p.o 6 h.1 then 6*k else 0) at hs
  change abstractStep p (n+6*k) = abstractStep p n
  unfold abstractStep concreteStep
  rw [hs]
  change (match (if h.1=0 then Outcome.halt else
      match tailCodes p h.1 with
      | none => Outcome.drift
      | some l => Outcome.next (countList l (h.2+ if allOne p.o 6 h.1 then 6*k else 0))) with
    | .halt => .halt | .drift => .drift | .next m => .next (classOf m)) =
    (match (if h.1=0 then Outcome.halt else
      match tailCodes p h.1 with
      | none => Outcome.drift
      | some l => Outcome.next (countList l h.2)) with
    | .halt => .halt | .drift => .drift | .next m => .next (classOf m))
  by_cases ha : h.1=0
  · simp [ha]
  · simp only [ha,if_false]
    cases ht : tailCodes p h.1 with
    | none => rfl
    | some l =>
      simp only [Outcome.next.injEq]
      rw [count_shift]
      cases hb : allOne p.o 6 h.1
      · simp [hb]
      · simp only [hb,if_true]
        cases hl : l.all wr
        · simp [hl]
        · simp only [hl,if_true]
          have hf := loop_fact p.o r
          change (scan p.o 6 h.1 h.2).1=h.1 ∧
            (if allOne p.o 6 h.1 then (scan p.o 6 h.1 h.2).2=h.2+6 ∧ n≤h.2+2
             else (scan p.o 6 h.1 h.2).2=h.2) at hf
          rw [hb,if_true] at hf
          have hc := count_all l h.2 hl
          have hlen := tail_length p h.1 l ht
          have h8 : 8≤countList l h.2 := by dsimp [n] at hf; omega
          rw [class_add _ k h8]

theorem step_class (p : Params) (n : Nat) :
    abstractStep p n = abstractStep p (classOf n) := by
  by_cases h : n<8
  · simp [classOf,h]
  · let r : Fin 6 := ⟨(n-8)%6, Nat.mod_lt _ (by decide)⟩
    let k := (n-8)/6
    have hn : n=8+r.val+6*k := by dsimp [r,k]; omega
    have hc : classOf n=8+r.val := by simp [classOf,h,r]
    rw [hc,hn]
    exact step_period p r k

def orbit (p : Params) : Nat → Nat → List Nat
  | 0,_ => []
  | k+1,n => n :: match abstractStep p n with
    | .next m => orbit p k m
    | _ => []
def bank (p : Params) : List Nat := orbit p 15 0
def closedAt (p : Params) (l : List Nat) (n : Nat) : Bool :=
  match abstractStep p n with
  | .halt => false
  | .drift => true
  | .next m => l.contains m
def safeCert (p : Params) : Bool := (bank p).all (closedAt p (bank p))

theorem bank_zero (p : Params) : 0 ∈ bank p := by simp [bank,orbit]
theorem safe_member (p : Params) (h : safeCert p = true) (n : Nat)
    (hn : n ∈ bank p) : closedAt p (bank p) n = true := by
  exact (List.all_eq_true.mp h) n hn

/-- Exact live cost, when the orbit reaches the unique possible halt B1.
    Fifteen quotient vertices suffice for the finite classification. -/
def haltCost (p : Params) : Nat → Nat → Option Nat
  | 0,_ => none
  | k+1,n =>
    let h := scan p.o n 1 0
    if h.1=0 then some (n+1) else
      match tailCodes p h.1 with
      | none => none
      | some l =>
        let m := countList l h.2
        (haltCost p k m).map (fun t => n+l.length+m+4+t)
def blankCost (p : Params) : Option Nat := (haltCost p 15 0).map (4+·)

#print axioms step_class
#print axioms safe_member
end BB6.Agent17.Box28Transducer
