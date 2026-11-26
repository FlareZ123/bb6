import Lean

/-! Exact right-counter arithmetic for Raw13 coupled counters. -/
namespace BB6.Agent46Raw13RightCounter

structure Triple where
  a : Bool
  b : Bool
  c : Bool
  deriving DecidableEq, Repr

def value : List Triple → Nat
  | [] => 0
  | t :: ts => t.c.toNat + 2 * value ts

def add : List Triple → Nat → Option (List Triple)
  | ts, 0 => some ts
  | [], _+1 => none
  | t::ts, d+1 => (add ts ((t.c.toNat+d+1)/2)).map
      (fun us => ⟨false,false, (t.c.toNat+d+1)%2 == 1⟩::us)

def inc : List Triple → Option (List Triple)
  | [] => none
  | t::ts => if t.c then (inc ts).map (fun us => ⟨false,false,false⟩::us)
             else some (⟨false,false,true⟩::ts)

theorem add_zero (ts : List Triple) : add ts 0 = some ts := by cases ts <;> rfl

theorem value_lt (ts : List Triple) : value ts < 2^ts.length := by
  induction ts with
  | nil => decide
  | cons t ts ih =>
    have hb : t.c.toNat ≤ 1 := by cases t.c <;> decide
    simp only [value,List.length_cons,Nat.pow_succ]
    omega

theorem add_one (ts : List Triple) : add ts 1 = inc ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | mk a b c => cases c <;> simp [add, inc, add_zero, ih]

theorem add_spec (ts : List Triple) (d : Nat) :
    (add ts d).isSome = (value ts+d < 2^ts.length) := by
  induction ts generalizing d with
  | nil => cases d <;> simp [add,value]
  | cons t ts ih =>
    cases d with
    | zero => simpa [add_zero] using value_lt (t::ts)
    | succ d =>
      simp only [add, Option.isSome_map, ih, value, List.length_cons, Nat.pow_succ]
      apply propext
      omega

theorem add_value (ts us : List Triple) (d : Nat) (h : add ts d = some us) :
    value us = value ts+d ∧ us.length = ts.length := by
  induction ts generalizing us d with
  | nil => cases d <;> simp [add] at h
           subst us; simp [value]
  | cons t ts ih =>
    cases d with
    | zero => simp [add] at h; subst us; simp
    | succ d =>
      simp only [add] at h
      cases e : add ts ((t.c.toNat+d+1)/2) with
      | none => simp [e] at h
      | some vs =>
        simp [e] at h
        subst us
        obtain ⟨hv,hl⟩ := ih vs _ e
        simp only [value,List.length_cons,hl,and_true]
        have hb : ((t.c.toNat+d+1)%2 == 1).toNat = (t.c.toNat+d+1)%2 := by
          have hh : (t.c.toNat+d+1)%2 = 0 ∨ (t.c.toNat+d+1)%2 = 1 := by omega
          rcases hh with hh|hh <;> simp [hh]
        rw [hb,hv]
        omega

def cell (n : Nat) : Triple := ⟨false,false,n%2 == 1⟩

theorem cell_bit (n : Nat) : (cell n).c.toNat = n%2 := by
  unfold cell
  have h : n%2 = 0 ∨ n%2 = 1 := by omega
  rcases h with h|h <;> simp [h]

theorem add_cons_pos (t : Triple) (ts : List Triple) (d : Nat) (h : 0<d) :
    add (t::ts) d = (add ts ((t.c.toNat+d)/2)).map (cell (t.c.toNat+d)::·) := by
  cases d with
  | zero => omega
  | succ d => rfl

theorem cell_mod (n m : Nat) (h : n%2 = m%2) : cell n = cell m := by simp [cell,h]

theorem add_add (ts : List Triple) (d e : Nat) :
    (add ts d).bind (fun us => add us e) = add ts (d+e) := by
  induction ts generalizing d e with
  | nil => cases d <;> cases e <;> rfl
  | cons t ts ih =>
    by_cases hd : d=0
    · subst d; simp [add_zero]
    by_cases he : e=0
    · subst e; cases add (t::ts) d <;> simp [add_zero]
    have hd' : 0<d := by omega
    have he' : 0<e := by omega
    rw [add_cons_pos t ts d hd', add_cons_pos t ts (d+e) (by omega)]
    rw [← Nat.add_assoc]
    let n := t.c.toNat+d
    have hcarry : n/2 + (n%2+e)/2 = (n+e)/2 := by omega
    have hcell : cell (n%2+e) = cell (n+e) := by apply cell_mod; omega
    change ((add ts (n/2)).map (cell n :: ·)).bind (fun us => add us e) =
      (add ts ((n+e)/2)).map (cell (n+e)::·)
    rw [← hcarry, ← ih, ← hcell]
    cases h : add ts (n/2) with
    | none => rfl
    | some us =>
      simp only [Option.map_some,Option.bind_some]
      rw [add_cons_pos _ _ e he',cell_bit]

def iterate : List Triple → Nat → Option (List Triple)
  | ts, 0 => some ts
  | ts, d+1 => (iterate ts d).bind inc

theorem iterate_eq_add (ts : List Triple) (d : Nat) : iterate ts d = add ts d := by
  induction d with
  | zero => exact (add_zero ts).symm
  | succ d ih =>
    rw [iterate,ih,← add_add]
    simp only [add_one]

/-- Serialize complete triples, leaving an arbitrary physical suffix untouched. -/
def word : List Triple → List Bool → List Bool
  | [], R => R
  | t::ts, R => t.a::t.b::t.c::word ts R

/-- The pure scan function of Raw13Frames, copied verbatim for this arithmetic lemma. -/
def scan : List Bool → Nat × List Bool
  | [] => (0,[])
  | false::W => (0,W)
  | [true] => (3,[])
  | [true,_] => (3,[])
  | true::_::_::W => let s := scan W; (6+s.1,s.2)

def zeros (n : Nat) : List Bool := List.replicate n false

theorem zeros_add (n m : Nat) : zeros (n+m) = zeros n ++ zeros m := by
  induction n with
  | zero => simp [zeros]
  | succ n ih =>
    rw [show n+1+m=n+m+1 by omega]
    simp only [zeros,List.replicate_succ,List.cons_append] at ih ⊢
    rw [ih]

theorem scan_inc (ts us : List Triple) (R : List Bool) (h : inc ts = some us) :
    ∃ j V, scan (true::word ts R) = (6*(j+1),V) ∧
      word us R = zeros (3*j+2) ++ true::V := by
  induction ts generalizing us with
  | nil => simp [inc] at h
  | cons t ts ih =>
    obtain ⟨a,b,c⟩ := t
    cases c with
    | false =>
      simp [inc] at h; subst us
      exact ⟨0,word ts R,by rfl,by rfl⟩
    | true =>
      simp only [inc,ite_true] at h
      cases ht : inc ts with
      | none => simp [ht] at h
      | some vs =>
        simp [ht] at h; subst us
        obtain ⟨j,V,hs,hv⟩ := ih vs ht
        refine ⟨j+1,V,?_,?_⟩
        · simp only [word,scan,hs]
          congr 1 <;> omega
        · change false::false::false::word vs R = _
          rw [hv,show 3*(j+1)+2=3+(3*j+2) by omega,zeros_add 3 (3*j+2)]
          rfl

/-- If a prefix addition does not overflow, it commutes with appending any complete-triple suffix. -/
theorem add_append (ts us tail : List Triple) (d : Nat) (h : add ts d = some us) :
    add (ts++tail) d = some (us++tail) := by
  induction ts generalizing d us with
  | nil => cases d <;> simp [add] at h
           subst us; simp [add_zero]
  | cons t ts ih =>
    cases d with
    | zero => simp [add] at h; subst us; exact add_zero _
    | succ d =>
      simp only [add] at h
      cases e : add ts ((t.c.toNat+d+1)/2) with
      | none => simp [e] at h
      | some vs =>
        simp [e] at h; subst us
        simp [add,ih vs _ e]

/-- Fixed-width, low-bit-first left counter. Trailing blank padding is explicit. -/
def encode : Nat → Nat → List Bool
  | 0, _ => []
  | m+1, x => (x%2 == 1)::false::false::false::encode m (x/2)

def oneBlocks : Nat → List Bool
  | 0 => []
  | n+1 => true::false::false::false::oneBlocks n

theorem encode_even (m x : Nat) (h : x%2=0) :
    encode (m+1) x = false::false::false::false::encode m (x/2) := by simp [encode,h]
theorem encode_odd (m x : Nat) (h : x%2=1) :
    encode (m+1) x = true::false::false::false::encode m (x/2) := by simp [encode,h]

/-- Both sides have the identical arbitrary suffix after the first zero digit. -/
theorem left_carry (m x : Nat) (U : List Bool) (h : x+1 < 2^m) :
    ∃ n L, encode m x ++ U = oneBlocks n ++ false::L ∧
      encode m (x+1) ++ U = zeros (4*n) ++ true::L := by
  induction m generalizing x with
  | zero => simp at h
  | succ m ih =>
    by_cases hb : x%2=0
    · have h1 : (x+1)%2=1 := by omega
      have h2 : (x+1)/2=x/2 := by omega
      refine ⟨0,false::false::false::(encode m (x/2)++U),?_,?_⟩
      · simp [encode_even m x hb,oneBlocks]
      · simp [encode_odd m (x+1) h1,h2,zeros]
    · have h1 : x%2=1 := by omega
      have h2 : (x+1)%2=0 := by omega
      have h3 : (x+1)/2=x/2+1 := by omega
      have h4 : x/2+1 < 2^m := by rw [Nat.pow_succ] at h; omega
      obtain ⟨n,L,hs,ht⟩ := ih (x/2) h4
      refine ⟨n+1,L,?_,?_⟩
      · simp only [encode_odd m x h1,List.cons_append,oneBlocks,hs]
      · rw [encode_even m (x+1) h2,h3]
        simp only [List.cons_append,ht]
        rw [show 4*(n+1)=4+4*n by omega,zeros_add 4 (4*n)]
        rfl

def ones (n : Nat) : List Bool := List.replicate n true

section Frames
variable {C : Type} (F : List Bool → List Bool → C) (Path : C → C → Prop)
variable (trans : ∀ {a b c}, Path a b → Path b c → Path a c)
variable (firstRule : ∀ n L W,
    Path (F (oneBlocks n ++ false::L) W)
      (F (ones (scan (true::W)).1 ++ zeros (4*n) ++ true::L) (scan (true::W)).2))
variable (secondRule : ∀ k n L W,
    Path (F (ones (2*(k+1)) ++ oneBlocks n ++ false::L) W)
      (F (zeros (4*n) ++ true::L) (zeros k ++ true::W)))

include trans firstRule secondRule
/-- One ordinary double increment from the two exact frame rules. -/
theorem double_step (m x : Nat) (U R : List Bool) (ts us : List Triple)
    (hx : x+2 < 2^m) (hi : inc ts = some us) :
    Path (F (encode m x++U) (word ts R)) (F (encode m (x+2)++U) (word us R)) := by
  obtain ⟨n,L,h1,h2⟩ := left_carry m x U (by omega)
  obtain ⟨n',L',h3,h4⟩ := left_carry m (x+1) U (by omega)
  obtain ⟨j,V,hs,hv⟩ := scan_inc ts us R hi
  have a := firstRule n L (word ts R)
  rw [← h1,hs,List.append_assoc,← h2] at a
  have b := secondRule (3*j+2) n' L' V
  rw [List.append_assoc,← h3,← h4,← hv] at b
  have hlen : 2*(3*j+2+1)=6*(j+1) := by omega
  rw [hlen] at b
  exact trans a b

/-- Arbitrarily many double increments with no overflow of either counter.
    The certificate uses `add`, whose recursion is on digit count, not on d. -/
theorem double_jump (m x d : Nat) (U R : List Bool) (ts us : List Triple)
    (hd : 0<d) (hx : x+2*d < 2^m) (ha : add ts d = some us) :
    Path (F (encode m x++U) (word ts R)) (F (encode m (x+2*d)++U) (word us R)) := by
  induction d generalizing us with
  | zero => omega
  | succ d ih =>
    rw [← add_add] at ha
    simp only [add_one] at ha
    cases he : add ts d with
    | none => simp [he] at ha
    | some vs =>
      simp only [he,Option.bind_some] at ha
      have hlast := double_step F Path trans firstRule secondRule m (x+2*d) U R vs us (by omega) ha
      rw [show x+2*d+2=x+2*(d+1) by omega] at hlast
      by_cases hz : d=0
      · subst d
        simp [add_zero] at he
        subst vs
        simpa using hlast
      · exact trans (ih vs (by omega) (by omega) he) hlast
end Frames

#print axioms add_spec
#print axioms add_value
#print axioms iterate_eq_add
#print axioms scan_inc
#print axioms add_append
#print axioms left_carry
#print axioms double_jump
end BB6.Agent46Raw13RightCounter
