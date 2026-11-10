import Lean

namespace ChampionBubble

def write (t : Int → Bool) (h : Int) (b : Bool) : Int → Bool :=
  fun i => if i = h then b else t i

structure Config where
  state : Nat
  head : Int
  tape : Int → Bool

instance : Inhabited Config := ⟨0,0,fun _ => false⟩

def action : Nat → Bool → Option (Bool × Int × Nat)
  | 0, false => some (true, 1, 1)
  | 0, true  => none
  | 1, false => some (true, -1, 2)
  | 1, true  => some (false, 1, 5)
  | 2, false => some (true, 1, 4)
  | 2, true  => some (false, -1, 3)
  | 3, false => some (false, -1, 2)
  | 3, true  => some (true, 1, 1)
  | 4, false => some (true, 1, 0)
  | 4, true  => some (true, 1, 4)
  | 5, false => some (true, 1, 4)
  | 5, true  => some (false, 1, 3)
  | _, _     => none

def step (c : Config) : Option Config := do
  let (ink, direction, next) ← action c.state (c.tape c.head)
  return ⟨next, c.head + direction, write c.tape c.head ink⟩

def run : Nat → Config → Option Config
  | 0, c => some c
  | n+1, c => do
    let d ← step c
    run n d

@[simp] theorem write_same (t : Int → Bool) (h : Int) (b : Bool) :
    write t h b h = b := by simp [write]

@[simp] theorem write_other (t : Int → Bool) (h i : Int) (b : Bool)
    (hne : i ≠ h) : write t h b i = t i := by simp [write, hne]

/-- Three exact source TM63 actions exchange a `10` pair into `01`
    and move the D-state head one cell left. -/
theorem bubble3 (t : Int → Bool) (h : Int)
  (h1 : t h = true) (h0 : t (h+1) = false) :
  run 3 ⟨3,h,t⟩ =
    some ⟨3,h-1,write (write t (h+1) true) h false⟩ := by
  have hneq : h+1 ≠ h := by omega
  have hv : write t h true (h+1) = false := by simp [write_other, hneq, h0]
  have hmid : h+1+(-1:Int) = h := by omega
  have hread : write (write t h true) (h+1) true (h+1+(-1:Int)) = true := by
    rw [hmid]
    simp [write, hneq]
  have hh : write (write t h true) (h+1) true h = true := by
    simp [write]
  simp [run, step, action, h1, h0, hv, hmid, hh]
  constructor
  · omega
  · funext i
    simp [write]
    by_cases hi : i = h
    · subst i
      simp
    · by_cases hj : i = h+1
      · subst i
        simp [hi]
      · simp [hi, hj]

theorem run_add (a b : Nat) (c : Config) :
    run (a+b) c = (run a c).bind (run b) := by
  induction a generalizing c with
  | zero => simp [run]
  | succ a ih =>
    simp only [Nat.succ_add, run]
    cases hs : step c with
    | none => simp [hs]
    | some d => simpa [hs, ih] using (rfl : (run a d).bind (run b) = (run a d).bind (run b))

def sweptTape : Nat → (Int → Bool) → Int → (Int → Bool)
  | 0, t, _ => t
  | n+1, t, h => sweptTape n (write (write t (h+1) true) h false) (h-1)

theorem bubble_run (n : Nat) (t : Int → Bool) (h : Int)
    (hzero : t (h+1) = false)
    (hones : ∀ i : Nat, i < n → t (h-(i:Int)) = true) :
    run (3*n) ⟨3,h,t⟩ =
      some ⟨3,h-(n:Int),sweptTape n t h⟩ := by
  induction n generalizing t h with
  | zero => simp [run, sweptTape]
  | succ n ih =>
    let t1 := write (write t (h+1) true) h false
    have hh : t h = true := by
      have hh := hones 0 (by omega)
      simpa using hh
    have hfirst := bubble3 t h hh hzero
    have hzero1 : t1 (h-1+1) = false := by
      dsimp [t1]
      have heq : h-1+1 = h := by omega
      rw [heq]
      simp
    have hones1 : ∀ i : Nat, i<n → t1 ((h-1)-(i:Int))=true := by
      intro i hi
      have hj : i+1<n+1 := by omega
      have hx : h-1-(i:Int) ≠ h := by omega
      have hy : h-1-(i:Int) ≠ h+1 := by omega
      have heq : h-1-(i:Int) = h-((i+1:Nat):Int) := by push_cast; omega
      dsimp [t1, write]
      rw [if_neg hx, if_neg hy, heq]
      exact hones (i+1) hj
    have hrest := ih t1 (h-1) hzero1 hones1
    have hlen : 3*(n+1)=3+3*n := by omega
    rw [hlen, run_add, hfirst]
    simp only [Option.bind_some]
    rw [hrest]
    have heq : h-1-(n:Int) = h-((n+1:Nat):Int) := by push_cast; omega
    simp [sweptTape, t1, heq]

@[simp] theorem write_twice (t : Int → Bool) (h : Int) (b c : Bool) :
    write (write t h b) h c = write t h c := by
  funext i
  by_cases hi : i = h <;> simp [write, hi]

@[simp] theorem write_unchanged (t : Int → Bool) (h : Int) :
    write t h (t h) = t := by
  funext i
  by_cases hi : i = h <;> simp [write, hi]

theorem sweptTape_closed (n : Nat) (t : Int → Bool) (h : Int)
    (hones : ∀ i : Nat, i < n+1 → t (h-(i:Int)) = true) :
    sweptTape (n+1) t h =
      write (write t (h+1) true) (h-(n:Int)) false := by
  induction n generalizing t h with
  | zero => simp [sweptTape]
  | succ n ih =>
    let t1 := write (write t (h+1) true) h false
    have hones1 : ∀ i : Nat, i<n+1 → t1 ((h-1)-(i:Int))=true := by
      intro i hi
      have hj : i+1 < n+1+1 := by omega
      have hx : h-1-(i:Int) ≠ h := by omega
      have hy : h-1-(i:Int) ≠ h+1 := by omega
      have heq : h-1-(i:Int) = h-((i+1:Nat):Int) := by push_cast; omega
      dsimp [t1, write]
      rw [if_neg hx, if_neg hy, heq]
      exact hones (i+1) hj
    have hhead : t h = true := by
      have := hones 0 (by omega)
      simpa using this
    have hpos : h ≠ h+1 := by omega
    have hrestore : write t1 h true = write t (h+1) true := by
      dsimp [t1]
      rw [write_twice]
      have hx : write t (h+1) true h = true := by
        simp [write, hpos, hhead]
      simpa [hx] using (write_unchanged (write t (h+1) true) h)
    have hh := ih t1 (h-1) hones1
    change sweptTape (n+1) t1 (h-1) =
      write (write t (h+1) true) (h-((n+1:Nat):Int)) false
    rw [hh]
    have hpos' : h-1+1=h := by omega
    rw [hpos', hrestore]
    congr 1
    push_cast
    omega

theorem bubble_run_closed (n : Nat) (t : Int → Bool) (h : Int)
    (hzero : t (h+1) = false)
    (hones : ∀ i : Nat, i < n+1 → t (h-(i:Int)) = true) :
    run (3*(n+1)) ⟨3,h,t⟩ =
      some ⟨3,h-((n+1:Nat):Int),
        write (write t (h+1) true) (h-(n:Int)) false⟩ := by
  rw [bubble_run (n+1) t h hzero hones]
  rw [sweptTape_closed n t h hones]

#print axioms ChampionBubble.bubble3
#print axioms ChampionBubble.bubble_run
#print axioms ChampionBubble.sweptTape_closed
#print axioms ChampionBubble.bubble_run_closed

/-- Exact physical TM63 three-step rightward block conversion 111 → 100. -/
theorem triple3 (t : Int → Bool) (h : Int)
    (h0 : t h = true) (h1 : t (h+1) = true) (h2 : t (h+2) = true) :
    run 3 ⟨3,h,t⟩ =
      some ⟨3,h+3,write (write t (h+1) false) (h+2) false⟩ := by
  have hn1 : h+1 ≠ h := by omega
  have hn2 : h+2 ≠ h := by omega
  have hn3 : h+2 ≠ h+1 := by omega
  have hv1 : write t h true (h+1) = true := by simp [write, hn1, h1]
  have hv2 : write (write t h true) (h+1) false (h+2) = true := by
    simp [write, hn2, hn3, h2]
  have hm : h+1+1=h+2 := by omega
  have hvF : write t h true (h+2) = true := by simp [write, hn2, h2]
  simp [run, step, action, h0, hv1, hm, hvF]
  constructor
  · omega
  · funext i
    simp [write]
    by_cases hi : i = h+1
    · subst i
      simp
    · by_cases hj : i = h+2
      · subst i
        simp [hi]
      · by_cases hk : i = h
        · subst i
          simp [hi, hj, h0]
        · simp [hi, hj, hk]

def tripleTape : Nat → (Int → Bool) → Int → (Int → Bool)
  | 0, t, _ => t
  | n+1, t, h => tripleTape n (write (write t (h+1) false) (h+2) false) (h+3)

/-- Complete exact source table path across n consecutive 111 triples. -/
theorem triple_run (n : Nat) (t : Int → Bool) (h : Int)
    (hones : ∀ i : Nat, i < 3*n → t (h+(i:Int)) = true) :
    run (3*n) ⟨3,h,t⟩ =
      some ⟨3,h+3*(n:Int),tripleTape n t h⟩ := by
  induction n generalizing t h with
  | zero => simp [run, tripleTape]
  | succ n ih =>
    let t1 := write (write t (h+1) false) (h+2) false
    have hh (j : Nat) (hj : j<3) : t (h+(j:Int))=true := by
      apply hones j
      omega
    have hhead : t h=true := by simpa using hh 0 (by omega)
    have hfirst : t (h+1)=true := by simpa using hh 1 (by omega)
    have hsecond : t (h+2)=true := by simpa using hh 2 (by omega)
    have hstep := triple3 t h hhead hfirst hsecond
    have hones1 : ∀ i : Nat, i<3*n → t1 ((h+3)+(i:Int))=true := by
      intro i hi
      have hj : i+3 < 3*(n+1) := by omega
      have hx : (h+3)+(i:Int) ≠ h+2 := by omega
      have hy : (h+3)+(i:Int) ≠ h+1 := by omega
      have heq : h+3+(i:Int) = h+((i+3:Nat):Int) := by push_cast; omega
      dsimp [t1,write]
      rw [if_neg hx, if_neg hy, heq]
      exact hones (i+3) hj
    have hrest := ih t1 (h+3) hones1
    have hlen : 3*(n+1)=3+3*n := by omega
    rw [hlen,run_add,hstep]
    simp only [Option.bind_some]
    rw [hrest]
    have heq : h+3+3*(n:Int) = h+3*((n+1:Nat):Int) := by push_cast; omega
    simp [tripleTape,t1,heq]

#print axioms ChampionBubble.triple3
#print axioms ChampionBubble.triple_run
end ChampionBubble
