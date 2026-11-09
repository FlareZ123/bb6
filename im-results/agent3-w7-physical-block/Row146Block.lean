import Row146Conjugacy
import Lean.Elab.Tactic.Omega

open BB6Row146Conjugacy
namespace BB6.Agent3W7

/-- Physical four-cell replacement on an arbitrary two-way infinite tape. -/
def set4 (t : Int → Bool) (h : Int)
    (b0 b1 b2 b3 : Bool) : Int → Bool :=
  fun x => if x = h then b0
    else if x = h+1 then b1
    else if x = h+2 then b2
    else if x = h+3 then b3
    else t x

theorem four_b_0100_1011 (t : Int → Bool) :
  run row146 4 {state:=.B,head:=0,tape:=set4 t 0 false true false false} =
    some {state:=.B,head:=4,tape:=set4 t 0 true false true true} := by
  simp [run, step, row146, delta, set4]
  congr 1
  funext x
  by_cases h0 : x = 0 <;> by_cases h1 : x = 1 <;>
    by_cases h2 : x = 2 <;> by_cases h3 : x = 3 <;>
    simp [set4,h0,h1,h2,h3]

theorem four_c_1000_0111 (t : Int → Bool) :
  run row146 4 {state:=.C,head:=0,tape:=set4 t 0 true false false false} =
    some {state:=.C,head:=4,tape:=set4 t 0 false true true true} := by
  simp [run, step, row146, delta, set4]
  congr 1
  funext x
  by_cases h0 : x = 0 <;> by_cases h1 : x = 1 <;>
    by_cases h2 : x = 2 <;> by_cases h3 : x = 3 <;>
    simp [set4,h0,h1,h2,h3]

theorem four_e_0001_1110 (t : Int → Bool) :
  run row146 4 {state:=.E,head:=0,tape:=set4 t 0 false false false true} =
    some {state:=.E,head:=4,tape:=set4 t 0 true true true false} := by
  simp [run, step, row146, delta, set4]
  congr 1
  funext x
  by_cases h0 : x = 0 <;> by_cases h1 : x = 1 <;>
    by_cases h2 : x = 2 <;> by_cases h3 : x = 3 <;>
    simp [set4,h0,h1,h2,h3]

theorem four_f_0010_1101 (t : Int → Bool) :
  run row146 4 {state:=.F,head:=0,tape:=set4 t 0 false false true false} =
    some {state:=.F,head:=4,tape:=set4 t 0 true true false true} := by
  simp [run, step, row146, delta, set4]
  congr 1
  funext x
  by_cases h0 : x = 0 <;> by_cases h1 : x = 1 <;>
    by_cases h2 : x = 2 <;> by_cases h3 : x = 3 <;>
    simp [set4,h0,h1,h2,h3]

theorem four_a_0111_0100 (t : Int → Bool) :
  run row146 14 {state:=.A,head:=3,tape:=set4 t 0 false true true true} =
    some {state:=.A,head:=-1,tape:=set4 t 0 false true false false} := by
  simp [run, step, row146, delta, set4]
  congr 1
  funext x
  by_cases h0 : x = 0 <;> by_cases h1 : x = 1 <;>
    by_cases h2 : x = 2 <;> by_cases h3 : x = 3 <;>
    simp [set4,h0,h1,h2,h3]

theorem four_a_1111_0101 (t : Int → Bool) :
  run row146 4 {state:=.A,head:=3,tape:=set4 t 0 true true true true} =
    some {state:=.A,head:=-1,tape:=set4 t 0 false true false true} := by
  simp [run, step, row146, delta, set4]
  congr 1
  funext x
  by_cases h0 : x = 0 <;> by_cases h1 : x = 1 <;>
    by_cases h2 : x = 2 <;> by_cases h3 : x = 3 <;>
    simp [set4,h0,h1,h2,h3]

theorem four_b_1111_1010 (t : Int → Bool) :
  run row146 4 {state:=.B,head:=3,tape:=set4 t 0 true true true true} =
    some {state:=.B,head:=-1,tape:=set4 t 0 true false true false} := by
  simp [run, step, row146, delta, set4]
  congr 1
  funext x
  by_cases h0 : x = 0 <;> by_cases h1 : x = 1 <;>
    by_cases h2 : x = 2 <;> by_cases h3 : x = 3 <;>
    simp [set4,h0,h1,h2,h3]


/-- Full translation of both head and infinite tape. -/
def translate (z : Int) (c : Config) : Config :=
  {state := c.state, head := c.head + z, tape := fun x => c.tape (x-z)}

theorem step_translate (M : Machine) (z : Int) (c : Config) :
    step M (translate z c) = (step M c).map (translate z) := by
  have ht : c.head + z - z = c.head := by omega
  simp only [step, translate, ht]
  cases hm : M c.state (c.tape c.head) with
  | none => simp
  | some r =>
      simp only [Option.map_some]
      simp only [translate]
      congr 1
      simp only [Config.mk.injEq, true_and]
      constructor
      · omega
      · funext x
        by_cases hx : x = c.head+z
        · have hh : x-z = c.head := by omega
          simp [hx]
        · have hh : x-z ≠ c.head := by omega
          simp [hx,hh]

theorem run_translate (M : Machine) (z : Int) (n : Nat) (c : Config) :
    run M n (translate z c) = (run M n c).map (translate z) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      simp only [run]
      rw [step_translate]
      cases hs : step M c with
      | none => simp
      | some c' => simpa using ih c'

theorem translate_set4 (t : Int → Bool) (h : Int)
    (b0 b1 b2 b3 : Bool) :
    (fun x => set4 (fun i => t (i+h)) 0 b0 b1 b2 b3 (x-h)) =
      set4 t h b0 b1 b2 b3 := by
  funext x
  have he0 : (x-h=0) = (x=h) := propext (by omega)
  have he1 : (x-h=1) = (x=h+1) := propext (by omega)
  have he2 : (x-h=2) = (x=h+2) := propext (by omega)
  have he3 : (x-h=3) = (x=h+3) := propext (by omega)
  simp [set4, he0, he1, he2, he3, show x-h+h=x by omega]

/-- A source-checked rule at the origin transports to any head coordinate. -/
theorem shift_local_rule
    (n : Nat) (s : State) (startPos finishPos : Int)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Bool)
    (hbase : ∀ t : Int → Bool,
      run row146 n {state := s, head := startPos, tape := set4 t 0 a0 a1 a2 a3} =
        some {state := s, head := finishPos, tape := set4 t 0 b0 b1 b2 b3})
    (t : Int → Bool) (h : Int) :
    run row146 n {state := s, head := startPos+h, tape := set4 t h a0 a1 a2 a3} =
      some {state := s, head := finishPos+h, tape := set4 t h b0 b1 b2 b3} := by
  let t0 : Int → Bool := fun i => t (i+h)
  have hinput : translate h {state := s, head := startPos, tape := set4 t0 0 a0 a1 a2 a3} =
      {state := s, head := startPos+h, tape := set4 t h a0 a1 a2 a3} := by
    simp only [translate, Config.mk.injEq, true_and]
    exact translate_set4 t h a0 a1 a2 a3
  have houtput : translate h {state := s, head := finishPos, tape := set4 t0 0 b0 b1 b2 b3} =
      {state := s, head := finishPos+h, tape := set4 t h b0 b1 b2 b3} := by
    simp only [translate, Config.mk.injEq, true_and]
    exact translate_set4 t h b0 b1 b2 b3
  rw [←hinput, run_translate, hbase, Option.map_some, houtput]

/-- Disjoint four-cell replacements commute for arbitrary ambient tape. -/
theorem set4_commute_far (t : Int → Bool) (p q : Int)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Bool) (hpq : p+4 ≤ q) :
    set4 (set4 t p a0 a1 a2 a3) q b0 b1 b2 b3 =
    set4 (set4 t q b0 b1 b2 b3) p a0 a1 a2 a3 := by
  funext x
  by_cases hp0 : x=p <;> by_cases hp1 : x=p+1 <;>
    by_cases hp2 : x=p+2 <;> by_cases hp3 : x=p+3 <;>
    by_cases hq0 : x=q <;> by_cases hq1 : x=q+1 <;>
    by_cases hq2 : x=q+2 <;> by_cases hq3 : x=q+3
  all_goals
    first
    | omega
    | (simp [set4,hp0,hp1,hp2,hp3,hq0,hq1,hq2,hq3]
       all_goals (repeat (first | rfl | omega | split)))

/-- Arbitrarily long right-hand strings of contiguous four-cell words. -/
def putR (t : Int → Bool) (h : Int)
    (a0 a1 a2 a3 : Bool) : Nat → Int → Bool
  | 0 => t
  | n+1 => set4 (putR t (h+4) a0 a1 a2 a3 n) h a0 a1 a2 a3

theorem set4_putR_far (t : Int → Bool) (p q : Int)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Bool) (hpq : p+4 ≤ q)
    (n : Nat) :
    set4 (putR t q a0 a1 a2 a3 n) p b0 b1 b2 b3 =
    putR (set4 t p b0 b1 b2 b3) q a0 a1 a2 a3 n := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
      change set4 (set4 (putR t (q+4) a0 a1 a2 a3 n) q a0 a1 a2 a3)
        p b0 b1 b2 b3 =
        set4 (putR (set4 t p b0 b1 b2 b3) (q+4) a0 a1 a2 a3 n)
          q a0 a1 a2 a3
      rw [← set4_commute_far (putR t (q+4) a0 a1 a2 a3 n)
        p q b0 b1 b2 b3 a0 a1 a2 a3 hpq]
      rw [ih (q+4) (by omega)]

theorem raw_run_add (M : Machine) (m n : Nat) (c : Config) :
    run M (m+n) c = (run M m c).bind (run M n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih =>
      simp only [Nat.succ_add, run]
      cases hs : step M c with
      | none => simp
      | some d => simpa using ih d

/-- All-length physical rightward sweep with exact primitive step count. -/
theorem sweepR (s : State) (a0 a1 a2 a3 b0 b1 b2 b3 : Bool)
    (hr : ∀ t : Int → Bool,
       run row146 4 {state := s, head := 0, tape := set4 t 0 a0 a1 a2 a3} =
         some {state := s, head := 4, tape := set4 t 0 b0 b1 b2 b3})
    (t : Int → Bool) (h : Int) (n : Nat) :
    run row146 (4*n) {state := s, head := h, tape := putR t h a0 a1 a2 a3 n} =
    some {state := s, head := h+4*n, tape := putR t h b0 b1 b2 b3 n} := by
  induction n generalizing t h with
  | zero => simp [run, putR]
  | succ n ih =>
      have ht : 4*(n+1) = 4 + 4*n := by omega
      have hfirst := shift_local_rule 4 s 0 4
        a0 a1 a2 a3 b0 b1 b2 b3 hr
        (putR t (h+4) a0 a1 a2 a3 n) h
      have hcommute := set4_putR_far t h (h+4)
        a0 a1 a2 a3 b0 b1 b2 b3 (by omega) n
      have hswap := set4_putR_far t h (h+4)
        b0 b1 b2 b3 b0 b1 b2 b3 (by omega) n
      change run row146 (4*(n+1))
        {state := s, head := h, tape := set4 (putR t (h+4) a0 a1 a2 a3 n) h a0 a1 a2 a3} =
        some {state := s, head := h+4*(n+1), tape := set4 (putR t (h+4) b0 b1 b2 b3 n) h b0 b1 b2 b3}
      have hfirst' : run row146 4
          {state := s, head := h, tape := set4 (putR t (h+4) a0 a1 a2 a3 n) h a0 a1 a2 a3} =
          some {state := s, head := h+4, tape := set4 (putR t (h+4) a0 a1 a2 a3 n) h b0 b1 b2 b3} := by
        simpa only [Int.zero_add, show (4:Int)+h = h+4 by omega] using hfirst
      rw [ht, raw_run_add, hfirst', Option.bind_some, hcommute]
      rw [ih (set4 t h b0 b1 b2 b3) (h+4)]
      rw [← hswap]
      have hpos : h+4+4*(n:Int) = h+4*((n:Int)+1) := by omega
      simp only [hpos]

/-- Contiguous four-cell words to the left of a block-boundary head. -/
def putL (t : Int → Bool) (h : Int)
    (a0 a1 a2 a3 : Bool) : Nat → Int → Bool
  | 0 => t
  | n+1 => set4 (putL t (h-4) a0 a1 a2 a3 n) (h-4) a0 a1 a2 a3

theorem set4_putL_far (t : Int → Bool) (p q : Int)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Bool) (hpq : q ≤ p)
    (n : Nat) :
    set4 (putL t q a0 a1 a2 a3 n) p b0 b1 b2 b3 =
    putL (set4 t p b0 b1 b2 b3) q a0 a1 a2 a3 n := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
      change set4 (set4 (putL t (q-4) a0 a1 a2 a3 n) (q-4) a0 a1 a2 a3)
        p b0 b1 b2 b3 =
        set4 (putL (set4 t p b0 b1 b2 b3) (q-4) a0 a1 a2 a3 n)
          (q-4) a0 a1 a2 a3
      rw [set4_commute_far (putL t (q-4) a0 a1 a2 a3 n)
        (q-4) p a0 a1 a2 a3 b0 b1 b2 b3 (by omega)]
      rw [ih (q-4) (by omega)]

/-- All-length physical leftward sweep with exact primitive step count. -/
theorem sweepL (s : State) (steps : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Bool)
    (hr : ∀ t : Int → Bool,
       run row146 steps {state := s, head := 3, tape := set4 t 0 a0 a1 a2 a3} =
         some {state := s, head := -1, tape := set4 t 0 b0 b1 b2 b3})
    (t : Int → Bool) (h : Int) (n : Nat) :
    run row146 (steps*n) {state := s, head := h-1, tape := putL t h a0 a1 a2 a3 n} =
    some {state := s, head := h-4*n-1, tape := putL t h b0 b1 b2 b3 n} := by
  induction n generalizing t h with
  | zero => simp [run, putL]
  | succ n ih =>
      have ht : steps*(n+1) = steps + steps*n := by
        simp only [Nat.mul_succ]; omega
      have hfirst := shift_local_rule steps s 3 (-1)
        a0 a1 a2 a3 b0 b1 b2 b3 hr
        (putL t (h-4) a0 a1 a2 a3 n) (h-4)
      have hcommute := set4_putL_far t (h-4) (h-4)
        a0 a1 a2 a3 b0 b1 b2 b3 (by omega) n
      have hswap := set4_putL_far t (h-4) (h-4)
        b0 b1 b2 b3 b0 b1 b2 b3 (by omega) n
      change run row146 (steps*(n+1))
        {state := s, head := h-1, tape := set4 (putL t (h-4) a0 a1 a2 a3 n) (h-4) a0 a1 a2 a3} =
        some {state := s, head := h-4*(n+1)-1, tape := set4 (putL t (h-4) b0 b1 b2 b3 n) (h-4) b0 b1 b2 b3}
      have hfirst' : run row146 steps
          {state := s, head := h-1, tape := set4 (putL t (h-4) a0 a1 a2 a3 n) (h-4) a0 a1 a2 a3} =
          some {state := s, head := h-5, tape := set4 (putL t (h-4) a0 a1 a2 a3 n) (h-4) b0 b1 b2 b3} := by
        have hs : 3 + (h-4) = h-1 := by omega
        have he : (-1:Int) + (h-4) = h-5 := by omega
        simpa only [hs, he] using hfirst
      rw [ht, raw_run_add, hfirst', Option.bind_some, hcommute]
      have hs : h-5 = (h-4)-1 := by omega
      rw [hs, ih (set4 t (h-4) b0 b1 b2 b3) (h-4)]
      rw [← hswap]
      have hpos : h-4-4*(n:Int)-1 = h-4*((n:Int)+1)-1 := by omega
      simp only [hpos]

theorem physical_b_0100_1011 (t : Int → Bool) (h : Int) (n : Nat) :
    run row146 (4*n) {state:=.B, head:=h, tape:=putR t h false true false false n} =
      some {state:=.B, head:=h+4*n, tape:=putR t h true false true true n} :=
  sweepR .B false true false false true false true true four_b_0100_1011 t h n

theorem physical_c_1000_0111 (t : Int → Bool) (h : Int) (n : Nat) :
    run row146 (4*n) {state:=.C, head:=h, tape:=putR t h true false false false n} =
      some {state:=.C, head:=h+4*n, tape:=putR t h false true true true n} :=
  sweepR .C true false false false false true true true four_c_1000_0111 t h n

theorem physical_e_0001_1110 (t : Int → Bool) (h : Int) (n : Nat) :
    run row146 (4*n) {state:=.E, head:=h, tape:=putR t h false false false true n} =
      some {state:=.E, head:=h+4*n, tape:=putR t h true true true false n} :=
  sweepR .E false false false true true true true false four_e_0001_1110 t h n

theorem physical_f_0010_1101 (t : Int → Bool) (h : Int) (n : Nat) :
    run row146 (4*n) {state:=.F, head:=h, tape:=putR t h false false true false n} =
      some {state:=.F, head:=h+4*n, tape:=putR t h true true false true n} :=
  sweepR .F false false true false true true false true four_f_0010_1101 t h n

theorem physical_a_0111_0100 (t : Int → Bool) (h : Int) (n : Nat) :
    run row146 (14*n) {state:=.A, head:=h-1, tape:=putL t h false true true true n} =
      some {state:=.A, head:=h-4*n-1, tape:=putL t h false true false false n} :=
  sweepL .A 14 false true true true false true false false four_a_0111_0100 t h n

theorem physical_a_1111_0101 (t : Int → Bool) (h : Int) (n : Nat) :
    run row146 (4*n) {state:=.A, head:=h-1, tape:=putL t h true true true true n} =
      some {state:=.A, head:=h-4*n-1, tape:=putL t h false true false true n} :=
  sweepL .A 4 true true true true false true false true four_a_1111_0101 t h n

theorem physical_b_1111_1010 (t : Int → Bool) (h : Int) (n : Nat) :
    run row146 (4*n) {state:=.B, head:=h-1, tape:=putL t h true true true true n} =
      some {state:=.B, head:=h-4*n-1, tape:=putL t h true false true false n} :=
  sweepL .B 4 true true true true true false true false four_b_1111_1010 t h n

#print axioms physical_b_0100_1011
#print axioms physical_c_1000_0111
#print axioms physical_e_0001_1110
#print axioms physical_f_0010_1101
#print axioms physical_a_0111_0100
#print axioms physical_a_1111_0101
#print axioms physical_b_1111_1010

end BB6.Agent3W7
