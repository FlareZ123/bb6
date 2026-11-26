import Std

namespace Root53
abbrev Side := Nat → Bool
def z : Side := fun _ => false
def push (b : Bool) (s : Side) : Side
  | 0 => b
  | n+1 => s n
infixr:67 " ::: " => push
def hd (s : Side) := s 0
def tl (s : Side) : Side := fun n => s (n+1)
@[simp] theorem hd_push (b : Bool) (s : Side) : hd (b ::: s) = b := rfl
@[simp] theorem tl_push (b : Bool) (s : Side) : tl (b ::: s) = s := rfl
@[simp] theorem hd_z : hd z = false := rfl
@[simp] theorem tl_z : tl z = z := rfl
@[simp] theorem zero_push : false ::: z = z := by funext n; cases n <;> rfl

def pre : List Bool → Side → Side
  | [], s => s
  | b::bs, s => b ::: pre bs s
@[simp] theorem pre_append (a b : List Bool) (s : Side) : pre (a++b) s = pre a (pre b s) := by
  induction a with
  | nil => rfl
  | cons a as ih => simp [pre, ih]

def ones : Nat → Side → Side
  | 0, s => s
  | n+1, s => true ::: ones n s
@[simp] theorem ones_add (a b : Nat) (s : Side) : ones (a+b) s = ones a (ones b s) := by
  induction a with
  | zero => simp [ones]
  | succ a ih => simp [Nat.succ_add,ones,ih]

def alt : Nat → Side → Side
  | 0, s => s
  | n+1, s => false ::: true ::: alt n s

def Config := Nat × Side × Bool × Side
def c (q : Nat) (l : Side) (b : Bool) (r : Side) : Config := (q,l,b,r)
def right (q : Nat) (l : Side) (w : Bool) (r : Side) : Config := c q (w ::: l) (hd r) (tl r)
def left (q : Nat) (l : Side) (w : Bool) (r : Side) : Config := c q (tl l) (hd l) (w ::: r)
def step : Config → Option Config
  | (0,l,false,r) => some (right 1 l true r)
  | (0,l,true,r) => some (right 3 l true r)
  | (1,l,false,r) => some (right 2 l true r)
  | (1,l,true,r) => some (right 4 l true r)
  | (2,l,false,r) => some (left 0 l false r)
  | (2,l,true,r) => some (right 2 l false r)
  | (3,l,false,r) => some (left 0 l true r)
  | (3,l,true,r) => some (left 3 l true r)
  | (4,l,true,r) => some (left 5 l true r)
  | (5,l,false,r) => some (left 2 l true r)
  | (5,l,true,r) => some (left 4 l false r)
  | _ => none

def run : Nat → Config → Option Config
  | 0, s => some s
  | n+1, s => (step s).bind (run n)

theorem run_add (n m : Nat) (s : Config) : run (n+m) s = (run n s).bind (run m) := by
  induction n generalizing s with
  | zero => simp [run]
  | succ n ih =>
    rw [Nat.succ_add]; simp only [run]
    cases h : step s with
    | none => rfl
    | some t => exact ih t

def Reach (a b : Config) : Prop := ∃ n, run n a = some b
def Progress (a b : Config) : Prop := ∃ n, 0<n ∧ run n a = some b

theorem Reach.refl (a : Config) : Reach a a := ⟨0,rfl⟩
theorem Reach.trans {a b d : Config} (h : Reach a b) (h' : Reach b d) : Reach a d := by
  obtain ⟨n,hn⟩ := h; obtain ⟨m,hm⟩ := h'
  exact ⟨n+m, by rw [run_add,hn]; exact hm⟩
theorem Progress.trans {a b d : Config} (h : Progress a b) (h' : Reach b d) : Progress a d := by
  obtain ⟨n,hp,hn⟩ := h; obtain ⟨m,hm⟩ := h'
  exact ⟨n+m, by omega, by rw [run_add,hn]; exact hm⟩
theorem Progress.reach {a b : Config} (h : Progress a b) : Reach a b := by
  obtain ⟨n,_,hn⟩ := h; exact ⟨n,hn⟩

def alt10 : Nat → Side → Side
  | 0, s => s
  | n+1, s => true ::: false ::: alt10 n s

theorem alt10_push (n : Nat) (s : Side) : alt10 n (true ::: false ::: s) = alt10 (n+1) s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change true ::: false ::: alt10 n (true ::: false ::: s) = true ::: false ::: alt10 (n+1) s
    rw [ih]

theorem alt10_shift (n : Nat) (s : Side) : alt10 n (true ::: s) = true ::: alt n s := by
  induction n with
  | zero => rfl
  | succ n ih => simp [alt10, alt, ih]

-- Sweep E/F over an odd block, with the next zero explicitly present.
theorem fSweep (n : Nat) (p r : Side) :
    Reach (c 5 (ones (2*n+1) (false ::: p)) true r)
      (c 2 (tl p) (hd p) (true ::: alt10 (n+1) r)) := by
  induction n generalizing r with
  | zero => exact ⟨3,rfl⟩
  | succ n ih =>
    have h : Reach (c 5 (ones (2*(n+1)+1) (false ::: p)) true r)
      (c 5 (ones (2*n+1) (false ::: p)) true (true ::: false ::: r)) := by
      refine ⟨2, ?_⟩
      rw [show 2*(n+1)+1 = 2+(2*n+1) by omega,ones_add]
      rfl
    apply h.trans
    rw [← alt10_push (n+1) r]
    exact ih (true ::: false ::: r)

theorem sweep (n : Nat) (p r : Side) :
    Progress (c 1 (ones (2*n+1) (false ::: p)) true (true ::: r))
      (c 2 (tl p) (hd p) (true ::: true ::: alt (n+1) r)) := by
  have h : Progress (c 1 (ones (2*n+1) (false ::: p)) true (true ::: r))
      (c 5 (ones (2*n+1) (false ::: p)) true (true ::: r)) := ⟨2,by decide,rfl⟩
  apply h.trans
  rw [← alt10_shift]
  exact fSweep n p (true ::: r)

def zeros : Nat → Side → Side
  | 0, s => s
  | n+1, s => false ::: zeros n s

theorem zeros_push (n : Nat) (s : Side) : zeros n (false ::: s) = zeros (n+1) s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change false ::: zeros n (false ::: s) = false ::: zeros (n+1) s
    rw [ih]

theorem cRun (k : Nat) (l r : Side) :
    Reach (c 2 l true (ones k (false ::: r)))
      (c 2 (true ::: true ::: zeros k l) (hd r) (tl r)) := by
  induction k generalizing l with
  | zero => exact ⟨4,rfl⟩
  | succ k ih =>
    have h : Reach (c 2 l true (ones (k+1) (false ::: r)))
      (c 2 (false ::: l) true (ones k (false ::: r))) := ⟨1,rfl⟩
    apply h.trans
    rw [← zeros_push k l]
    exact ih (false ::: l)

theorem finish (n : Nat) (l : Side) :
    Reach (c 2 l true (alt n (true ::: true ::: z)))
      (c 1 (ones (2*n+1) l) true (true ::: true ::: true ::: z)) := by
  induction n generalizing l with
  | zero =>
    have h := cRun 2 l z
    change Reach (c 2 l true (true ::: true ::: false ::: z))
      (c 2 (true ::: true ::: false ::: false ::: l) false z) at h
    rw [zero_push] at h
    apply h.trans
    exact ⟨9,rfl⟩
  | succ n ih =>
    have h := cRun 0 l (true ::: alt n (true ::: true ::: z))
    change Reach (c 2 l true (alt (n+1) (true ::: true ::: z)))
      (c 2 (true ::: true ::: l) true (alt n (true ::: true ::: z))) at h
    apply h.trans
    rw [show 2*(n+1)+1 = (2*n+1)+2 by omega,ones_add]
    exact ih (true ::: true ::: l)

def main (p : Side) (n : Nat) : Config :=
  c 1 (ones (2*n+1) p) true (true ::: true ::: true ::: z)

theorem ordinary10 (u : Side) (n : Nat) :
    Progress (main (false ::: true ::: u) n) (main (false ::: false ::: u) (n+1)) := by
  have h := sweep n (true ::: u) (true ::: true ::: z)
  change Progress (main (false ::: true ::: u) n)
    (c 2 u true (true ::: true ::: false ::: true ::: alt n (true ::: true ::: z))) at h
  apply h.trans
  have h' := cRun 2 u (true ::: alt n (true ::: true ::: z))
  apply h'.trans
  unfold main
  rw [show 2*(n+1)+1 = (2*n+1)+2 by omega,ones_add]
  exact finish n (true ::: true ::: false ::: false ::: u)

theorem ordinary000 (u : Side) (n : Nat) :
    Progress (main (false ::: false ::: false ::: u) n) (main (false ::: true ::: true ::: u) (n+1)) := by
  have h := sweep n (false ::: false ::: u) (true ::: true ::: z)
  change Progress (main (false ::: false ::: false ::: u) n)
    (c 2 (false ::: u) false (true ::: true ::: false ::: true ::: alt n (true ::: true ::: z))) at h
  apply h.trans
  have h' : Reach (c 2 (false ::: u) false (true ::: true ::: false ::: true ::: alt n (true ::: true ::: z)))
      (c 2 (true ::: true ::: u) true (true ::: false ::: true ::: alt n (true ::: true ::: z))) := ⟨3,rfl⟩
  apply h'.trans
  have h'' := cRun 1 (true ::: true ::: u) (true ::: alt n (true ::: true ::: z))
  apply h''.trans
  unfold main
  rw [show 2*(n+1)+1 = (2*n+1)+2 by omega,ones_add]
  exact finish n (true ::: true ::: false ::: true ::: true ::: u)

theorem ones_push (n : Nat) (s : Side) : ones n (true ::: s) = ones (n+1) s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change true ::: ones n (true ::: s) = true ::: ones (n+1) s
    rw [ih]

inductive SafeTail : List Bool → Prop
  | nil : SafeTail []
  | one {xs} : SafeTail xs → SafeTail (true::xs)
  | zeroOne {xs} : SafeTail xs → SafeTail (false::true::xs)

theorem dSweep (xs : List Bool) (hxs : SafeTail xs) (u r : Side) :
    Reach (c 3 (pre xs (false ::: false ::: u)) true r)
      (c 1 (true ::: u) true (ones (xs.length+1) r)) := by
  induction hxs generalizing r with
  | nil => exact ⟨3,rfl⟩
  | @one xs h ih =>
    have h' : Reach (c 3 (pre (true::xs) (false ::: false ::: u)) true r)
        (c 3 (pre xs (false ::: false ::: u)) true (true ::: r)) := ⟨1,rfl⟩
    apply h'.trans
    simp only [List.length_cons]
    rw [← ones_push (xs.length+1) r]
    exact ih (true ::: r)
  | @zeroOne xs h ih =>
    have h' : Reach (c 3 (pre (false::true::xs) (false ::: false ::: u)) true r)
        (c 3 (pre xs (false ::: false ::: u)) true (true ::: true ::: r)) := ⟨4,rfl⟩
    apply h'.trans
    simp only [List.length_cons]
    rw [← ones_push (xs.length+2) r, ← ones_push (xs.length+1) (true ::: r)]
    exact ih (true ::: true ::: r)

theorem carryFirst (xs : List Bool) (hxs : SafeTail xs) (u : Side) (n : Nat) :
    Progress (main (false ::: false ::: true ::: pre xs (false ::: false ::: u)) n)
      (c 1 (true ::: u) true (ones (xs.length+4) (alt (n+1) (true ::: true ::: z)))) := by
  have h := sweep n (false ::: true ::: pre xs (false ::: false ::: u)) (true ::: true ::: z)
  change Progress (main (false ::: false ::: true ::: pre xs (false ::: false ::: u)) n)
    (c 2 (true ::: pre xs (false ::: false ::: u)) false (true ::: true ::: alt (n+1) (true ::: true ::: z))) at h
  apply h.trans
  have h' : Reach (c 2 (true ::: pre xs (false ::: false ::: u)) false (true ::: true ::: alt (n+1) (true ::: true ::: z)))
      (c 3 (pre xs (false ::: false ::: u)) true (true ::: true ::: true ::: alt (n+1) (true ::: true ::: z))) := ⟨5,rfl⟩
  apply h'.trans
  rw [show xs.length+4 = (xs.length+1)+3 by omega,ones_add]
  exact dSweep xs hxs u _

theorem carryFinish (k n : Nat) (g : Side) :
    Reach (c 2 (true ::: true ::: g) true (ones k (alt (n+1) (true ::: true ::: z))))
      (main (zeros k (true ::: true ::: g)) (n+1)) := by
  have h := cRun k (true ::: true ::: g) (true ::: alt n (true ::: true ::: z))
  apply h.trans
  unfold main
  rw [show 2*(n+1)+1 = (2*n+1)+2 by omega,ones_add]
  exact finish n _

theorem carry10 (k n : Nat) (u : Side) :
    Reach (c 1 (true ::: false ::: true ::: u) true (ones (k+1) (alt (n+1) (true ::: true ::: z))))
      (main (zeros k (true ::: true ::: false ::: false ::: u)) (n+1)) := by
  have h := sweep 0 (true ::: u) (ones k (alt (n+1) (true ::: true ::: z)))
  apply h.reach.trans
  have h' := cRun 2 u (true ::: ones k (alt (n+1) (true ::: true ::: z)))
  apply h'.trans
  exact carryFinish k n _

theorem carry000 (k n : Nat) (u : Side) :
    Reach (c 1 (true ::: false ::: false ::: false ::: u) true (ones (k+1) (alt (n+1) (true ::: true ::: z))))
      (main (zeros k (true ::: true ::: false ::: true ::: true ::: u)) (n+1)) := by
  have h := sweep 0 (false ::: false ::: u) (ones k (alt (n+1) (true ::: true ::: z)))
  apply h.reach.trans
  have h' : Reach (c 2 (false ::: u) false (true ::: true ::: false ::: true ::: ones k (alt (n+1) (true ::: true ::: z))))
      (c 2 (true ::: true ::: u) true (true ::: false ::: true ::: ones k (alt (n+1) (true ::: true ::: z)))) := ⟨3,rfl⟩
  apply h'.trans
  have h'' := cRun 1 (true ::: true ::: u) (true ::: ones k (alt (n+1) (true ::: true ::: z)))
  apply h''.trans
  exact carryFinish k n _

def block (b d : Bool) : List Bool := [false,d,d,b,b] -- reversed f(b,d), except for d=false below
-- f(0,0)=00000; f(0,1)=00110; f(1,0)=11000; f(1,1)=11110
-- reverse order: 0,d,d,b,b, so the third bit is d.
inductive Core : Bool → Side → Prop
  | header : Core true (false ::: true ::: true ::: z)
  | next {b d : Bool} {u : Side} : Core b u → Core d (pre (block b d) u)

def phase2 (b : Bool) (u : Side) : Side := false ::: false ::: true ::: b ::: b ::: u

inductive Valid : Side → Prop
  | empty : Valid z
  | core {b u} : Core b u → Valid u
  | carryHeader : Valid (false ::: false ::: true ::: z)
  | carry {b u} : Core b u → Valid (phase2 b u)

theorem coreFalseFlip {u : Side} (h : Core false u) :
    ∃ v, u = false ::: false ::: false ::: v ∧ Core true (false ::: true ::: true ::: v) := by
  cases h with
  | @next b d s h =>
    exact ⟨b ::: b ::: s,rfl,Core.next (d:=true) h⟩

def tailWord : Nat → List Bool
  | 0 => [false,true,true]
  | k+1 => false::true::true::true::true::tailWord k

theorem tailWord_safe (k : Nat) : SafeTail (tailWord k) := by
  induction k with
  | zero => exact .zeroOne (.one .nil)
  | succ k ih => exact .zeroOne (.one (.one (.one ih)))

theorem tailWord_len (k : Nat) : (tailWord k).length = 5*k+3 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [tailWord,List.length_cons,ih]; omega

theorem coreTrueSplit {u : Side} (h : Core true u) :
    ∃ k v, u = pre (tailWord k) (false ::: false ::: v) ∧ (v=z ∨ Core false v) := by
  -- inductive decomposition of the suffix of consecutive 1-bits
  have aux : ∀ b s, Core b s → b=true → ∃ k v, s = pre (tailWord k) (false ::: false ::: v) ∧ (v=z ∨ Core false v) := by
    intro b s hs
    induction hs with
    | header =>
      intro _
      refine ⟨0,z,?_,Or.inl rfl⟩
      simp [tailWord,pre]
    | @next b d u hu ih =>
      intro hd
      subst d
      cases b with
      | false => exact ⟨0,u,rfl,Or.inr hu⟩
      | true =>
        obtain ⟨k,v,hv,hc⟩ := ih rfl
        exact ⟨k+1,v,by rw [hv]; rfl,hc⟩
  exact aux true u h rfl

theorem zeros_add (a b : Nat) (s : Side) : zeros (a+b) s = zeros a (zeros b s) := by
  induction a with
  | zero => simp [zeros]
  | succ a ih => simp [Nat.succ_add,zeros,ih]

theorem coreZeros (k : Nat) {u : Side} (h : Core false u) : Core false (zeros (5*k) u) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [show 5*(k+1)=5+5*k by omega,zeros_add]
    exact Core.next (b:=false) (d:=false) ih

theorem carryBarrier (xs : List Bool) (hs : SafeTail xs) (u : Side) (n : Nat)
    (hu : u=z ∨ Core false u) :
    ∃ g, Core true g ∧ Progress (main (false ::: false ::: true ::: pre xs (false ::: false ::: u)) n)
      (main (zeros (xs.length+3) (true ::: true ::: g)) (n+1)) := by
  have h := carryFirst xs hs u n
  cases hu with
  | inl hu =>
    subst u
    refine ⟨false ::: true ::: true ::: z,Core.header,?_⟩
    apply h.trans
    have e : false ::: false ::: false ::: z = z := by simp
    have h' := carry000 (xs.length+3) n z
    rw [e] at h'
    exact h'
  | inr hu =>
    obtain ⟨v,hv,hg⟩ := coreFalseFlip hu
    refine ⟨false ::: true ::: true ::: v,hg,?_⟩
    rw [hv] at h ⊢
    exact h.trans (carry000 (xs.length+3) n v)

theorem validProgress {p : Side} (hp : Valid p) (n : Nat) :
    ∃ p', Valid p' ∧ Progress (main p n) (main p' (n+1)) := by
  cases hp with
  | empty =>
    refine ⟨_,Valid.core Core.header,?_⟩
    simpa only [zero_push] using ordinary000 z n
  | @core d p hc =>
    cases hc with
    | header =>
      exact ⟨_,Valid.carryHeader,ordinary10 (true ::: z) n⟩
    | @next b _ u hc =>
      cases d with
      | false => exact ⟨_,Valid.core (Core.next (d:=true) hc),ordinary000 (b ::: b ::: u) n⟩
      | true => exact ⟨_,Valid.carry hc,ordinary10 (true ::: b ::: b ::: u) n⟩
  | carryHeader =>
    obtain ⟨g,hg,h⟩ := carryBarrier [] .nil z n (Or.inl rfl)
    refine ⟨_,Valid.core (Core.next (d:=false) hg),?_⟩
    change Progress (main (false ::: false ::: true ::: false ::: false ::: z) n) (main (pre (block true false) g) (n+1)) at h
    simpa only [zero_push] using h
  | @carry b u hu =>
    cases b with
    | false =>
      obtain ⟨g,hg,h⟩ := carryBarrier [] .nil u n (Or.inr hu)
      exact ⟨_,Valid.core (Core.next (d:=false) hg),h⟩
    | true =>
      obtain ⟨k,v,hv,hc⟩ := coreTrueSplit hu
      let xs := true::true::tailWord k
      have hs : SafeTail xs := .one (.one (tailWord_safe k))
      obtain ⟨g,hg,h⟩ := carryBarrier xs hs v n hc
      have hx : xs.length+3 = 5*(k+1)+3 := by
        simp only [xs,List.length_cons,tailWord_len]; omega
      rw [hx,zeros_add] at h
      refine ⟨_,Valid.core (coreZeros (k+1) (Core.next (d:=false) hg)),?_⟩
      rw [hv]
      exact h

def blank : Config := c 0 z false z

theorem seed : Progress blank (main z 0) := by
  refine ⟨11,by decide,?_⟩
  -- the only discrepancy is explicit zero prefixes on the blank stream
  rfl

theorem longRuns (n : Nat) : ∃ k p, n ≤ k ∧ Valid p ∧ run k blank = some (main p n) := by
  induction n with
  | zero =>
    obtain ⟨k,_,hk⟩ := seed
    exact ⟨k,z,by omega,Valid.empty,hk⟩
  | succ n ih =>
    obtain ⟨k,p,hk,hp,hr⟩ := ih
    obtain ⟨p',hp',m,hm,hr'⟩ := validProgress hp n
    exact ⟨k+m,p',by omega,hp',by rw [run_add,hr]; exact hr'⟩

theorem never (n : Nat) : run n blank ≠ none := by
  intro h
  obtain ⟨k,p,hk,_,hr⟩ := longRuns n
  rw [show k=n+(k-n) by omega,run_add,h] at hr
  contradiction

#print axioms validProgress
#print axioms never

end Root53
