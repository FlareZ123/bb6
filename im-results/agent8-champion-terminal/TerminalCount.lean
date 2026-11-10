import Lean.Elab.Tactic.Omega

/-!
A counted terminal macro for the literal TM63 transition table
1RB---_1LC0RF_1RE0LD_0LC1RB_1RA1RE_1RE0RD.
Finite lists represent a two-sided infinite tape with implicit zero padding.
The current symbol is the one under the head, and left/right lists are
ordered from nearest to farthest cell.
-/
namespace BB6.ChampionTerminal

inductive Q where | A | B | C | D | E | F
  deriving DecidableEq, Repr

structure Z where
  state : Q
  left : List Bool
  cur : Bool
  right : List Bool
  deriving DecidableEq, Repr

def cfg (q : Q) (l : List Bool) (c : Bool) (r : List Bool) : Z :=
  ⟨q,l,c,r⟩

def moveL (q : Q) (v : Bool) (z : Z) : Z :=
  cfg q z.left.tail (z.left.headD false) (v::z.right)

def moveR (q : Q) (v : Bool) (z : Z) : Z :=
  cfg q (v::z.left) (z.right.headD false) z.right.tail

def step (z : Z) : Option Z :=
  match z.state, z.cur with
  | .A, false => some (moveR .B true z)
  | .A, true => none
  | .B, false => some (moveL .C true z)
  | .B, true => some (moveR .F false z)
  | .C, false => some (moveR .E true z)
  | .C, true => some (moveL .D false z)
  | .D, false => some (moveL .C false z)
  | .D, true => some (moveR .B true z)
  | .E, false => some (moveR .A true z)
  | .E, true => some (moveR .E true z)
  | .F, false => some (moveR .E true z)
  | .F, true => some (moveR .D false z)

def run : Nat → Z → Option Z
  | 0,z => some z
  | n+1,z => (run n z).bind step

theorem run_add (n m : Nat) (z : Z) :
    run (n+m) z = (run n z).bind (run m) := by
  induction m with
  | zero => simp [run]
  | succ m ih =>
    rw [Nat.add_succ,run,ih]
    cases h : run n z with
    | none => simp
    | some y => simp [run]

private def ones (n : Nat) : List Bool := List.replicate n true
private def o3 (n : Nat) : List Bool := ones (3*n)
private def tail3 : Nat → List Bool
  | 0 => []
  | n+1 => [false,true,false] ++ tail3 n

private theorem ones_add (n m : Nat) : ones (n+m)=ones n ++ ones m := by
  induction n with
  | zero => simp [ones]
  | succ n ih =>
    simpa [ones, Nat.succ_add, List.replicate_succ] using
      congrArg (List.cons true) ih

private theorem ones_succ (n : Nat) : ones (n+1)=true::ones n := by
  simp [ones, List.replicate_succ]

private theorem ones_push (n : Nat) (r : List Bool) :
  ones n ++ true::r = ones (n+1) ++ r := by
  change ones n ++ ([true] ++ r) = ones (n+1) ++ r
  rw [← List.append_assoc]
  change (ones n ++ ones 1) ++ r = ones (n+1) ++ r
  rw [← ones_add]

-- Six symbolic machine identities, independent of all unvisited tape cells.
private theorem d3 (b : Bool) (l r : List Bool) :
  run 3 (cfg .D (b::l) true (false::r)) =
     some (cfg .D l b (false::true::r)) := by
  rfl

private theorem b3 (l r : List Bool) :
  run 3 (cfg .B (true::true::l) false r) =
    some (cfg .B (true::l) false (true::r)) := by
  rfl

private theorem f3 (l r : List Bool) :
  run 3 (cfg .F l true (true::true::true::true::r)) =
    some (cfg .F (false::true::false::l) true (true::r)) := by
  rfl

private theorem bridgeD (l r : List Bool) :
  run 6 (cfg .D (true::false::false::true::l) false (false::r)) =
    some (cfg .B (true::true::true::true::l) false (false::r)) := by
  rfl

private theorem turnB (r : List Bool) :
  run 15 (cfg .B [true,false,true,true,true] false r) =
    some (cfg .F [false,true,true,true] true (false::false::true::r)) := by
  rfl

private theorem bridgeF6 (l r : List Bool) :
  run 6 (cfg .F (false::true::true::true::l) true (false::false::true::true::r)) =
    some (cfg .F (false::true::true::true::false::true::true::true::l) true r) := by
  rfl

private theorem bridgeF12 (l r : List Bool) :
  run 12 (cfg .F l true (true::true::true::true::false::true::r)) =
    some (cfg .F (false::true::true::true::true::false::l) true r) := by
  rfl

private theorem finalF5 (l r : List Bool) :
  run 5 (cfg .F l true (true::true::false::false::true::r)) =
    some (cfg .A (true::true::false::true::false::l) true r) := by
  rfl

private theorem d_scan (n : Nat) (l r : List Bool) :
  run (3*(n+1)) (cfg .D (ones n ++ false::l) true (false::r)) =
    some (cfg .D l false (false::ones (n+1) ++ r)) := by
  induction n generalizing r with
  | zero => simp [ones,run,d3,step,moveL,moveR,cfg]
  | succ n ih =>
    have heq : 3*(n+1+1) = 3 + 3*(n+1) := by omega
    rw [heq,run_add]
    have hfirst : run 3 (cfg .D (ones (n+1) ++ false::l) true (false::r)) =
      some (cfg .D (ones n ++ false::l) true (false::true::r)) := by
      simpa only [ones_succ, List.cons_append] using d3 true (ones n ++ false::l) r
    rw [hfirst]
    simp only [Option.bind_some]
    rw [ih (true::r)]
    simp only [List.cons_append, ones_push]

private theorem b_scan (n : Nat) (r : List Bool) :
  run (3*n) (cfg .B (ones (n+1) ++ [false,true,true,true]) false r) =
    some (cfg .B [true,false,true,true,true] false (ones n ++ r)) := by
  induction n generalizing r with
  | zero => simp [ones,run,cfg]
  | succ n ih =>
    have heq : 3*(n+1) = 3 + 3*n := by omega
    rw [heq,run_add]
    have hfirst : run 3
      (cfg .B (ones (n+1+1) ++ [false,true,true,true]) false r) =
      some (cfg .B (ones (n+1) ++ [false,true,true,true]) false (true::r)) := by
      simpa only [ones_succ, List.cons_append] using b3 (ones n ++ [false,true,true,true]) r
    rw [hfirst]
    simp only [Option.bind_some]
    rw [ih (true::r)]
    simp only [ones_push]

private theorem tail3_comm (n : Nat) :
  tail3 n ++ [false,true,false] = [false,true,false] ++ tail3 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [tail3, List.append_assoc]
    rw [ih]

private theorem f_scan (n : Nat) (l r : List Bool) :
  run (3*n) (cfg .F l true (ones (3*n+1) ++ r)) =
    some (cfg .F (tail3 n ++ l) true (true::r)) := by
  induction n generalizing l r with
  | zero => simp [ones,tail3,run,cfg]
  | succ n ih =>
    have heq : 3*(n+1) = 3 + 3*n := by omega
    conv => lhs; arg 1; rw [heq]
    rw [run_add]
    have hfirst : run 3 (cfg .F l true (ones (3*(n+1)+1) ++ r)) =
      some (cfg .F ([false,true,false] ++ l) true (ones (3*n+1) ++ r)) := by
      have hi : 3*(n+1)+1 = 4+3*n := by omega
      rw [hi, ones_add, ones_succ]
      rw [ones_succ (3*n)]
      simpa [ones] using f3 l (ones (3*n) ++ r)
    rw [hfirst]
    simp only [Option.bind_some]
    rw [ih ([false,true,false] ++ l) r]
    have hleft : tail3 n ++ ([false,true,false] ++ l) =
      [false,true,false] ++ (tail3 n ++ l) := by
      calc
        tail3 n ++ ([false,true,false] ++ l) =
            (tail3 n ++ [false,true,false]) ++ l := by rw [List.append_assoc]
        _ = ([false,true,false] ++ tail3 n) ++ l := by rw [tail3_comm]
        _ = [false,true,false] ++ (tail3 n ++ l) := by rw [List.append_assoc]
    simpa only [tail3, List.append_assoc] using congrArg
      (fun xs : List Bool => some (cfg .F xs true (true::r))) hleft


private theorem chain (n m : Nat) (x y z : Z)
    (h1 : run n x = some y) (h2 : run m y = some z) :
    run (n+m) x = some z := by
  rw [run_add, h1]
  exact h2

private def lb (L : Nat) : List Bool :=
  [true,false,false,true] ++ o3 L ++ [true,true,false,true,true,true]
private def rb (b : Nat) : List Bool :=
  [true,true,true,false,false] ++ o3 (b+1)
private def startD (L a b : Nat) : Z :=
  cfg .D (lb L) false (false::o3 a ++ rb b)

private theorem d_to_b (L a b : Nat) :
  run (6 + 3*(5+3*L)) (startD L a b) =
  some (cfg .B [true,false,true,true,true] false
    (ones (5+3*L) ++ false::o3 a ++ rb b)) := by
  have hd : run 6 (startD L a b) =
    some (cfg .B (ones (6+3*L) ++ [false,true,true,true]) false
      (false::o3 a ++ rb b)) := by
    have h0 := bridgeD (o3 L ++ [true,true,false,true,true,true]) (o3 a ++ rb b)
    have heq : 6+3*L = 4+(3*L+2) := by omega
    have hshape : ones (6+3*L) ++ [false,true,true,true] =
      [true,true,true,true] ++ o3 L ++ [true,true,false,true,true,true] := by
      rw [heq,ones_add,ones_add]
      simp [ones, o3, List.append_assoc]
    simpa only [startD, lb, List.append_assoc, List.cons_append, List.nil_append,
      hshape] using h0
  have hb : run (3*(5+3*L))
      (cfg .B (ones (6+3*L) ++ [false,true,true,true]) false (false::o3 a ++ rb b)) =
      some (cfg .B [true,false,true,true,true] false
        (ones (5+3*L) ++ false::o3 a ++ rb b)) := by
    have h := b_scan (5+3*L) (false::o3 a ++ rb b)
    have hn : 5+3*L+1 = 6+3*L := by omega
    simpa only [hn, List.append_assoc] using h
  exact chain 6 (3*(5+3*L)) _ _ _ hd hb


private def lF1 : List Bool := [false,true,true,true,false,true,true,true]
private def lF2 (L : Nat) := tail3 L ++ lF1
private def lF3 (L : Nat) := [false,true,true,true,true,false] ++ lF2 L
private def lF4 (L a : Nat) := tail3 a ++ lF3 L
private def lF5 (L a : Nat) := [true,true,false,true,false] ++ lF4 L a

private def rB (L a b : Nat) : List Bool :=
  ones (5+3*L) ++ false::o3 a ++ rb b
private def rF0 (L a b : Nat) : List Bool := [false,false,true] ++ rB L a b
private def rF1 (L a b : Nat) : List Bool := ones (4+3*L) ++ false::o3 a ++ rb b
private def rF2 (a b : Nat) : List Bool := ones 4 ++ false::o3 a ++ rb b
private def rF3 (a b : Nat) : List Bool := ones (3*a+2) ++ [false,false] ++ o3 (b+1)
private def rF4 (b : Nat) : List Bool := [true,true,false,false] ++ o3 (b+1)
private def rF5 (b : Nat) : List Bool := ones (3*b+2)

private def sB (L a b : Nat) : Z := cfg .B [true,false,true,true,true] false (rB L a b)
private def sF0 (L a b : Nat) : Z := cfg .F [false,true,true,true] true (rF0 L a b)
private def sF1 (L a b : Nat) : Z := cfg .F lF1 true (rF1 L a b)
private def sF2 (L a b : Nat) : Z := cfg .F (lF2 L) true (rF2 a b)
private def sF3 (L a b : Nat) : Z := cfg .F (lF3 L) true (rF3 a b)
private def sF4 (L a b : Nat) : Z := cfg .F (lF4 L a) true (rF4 b)
def sF5 (L a b : Nat) : Z := cfg .A (lF5 L a) true (rF5 b)

private theorem bturn (L a b : Nat) :
    run 15 (sB L a b) = some (sF0 L a b) := by
  exact turnB (rB L a b)

private theorem fbridge6 (L a b : Nat) :
    run 6 (sF0 L a b) = some (sF1 L a b) := by
  have hlen : 5+3*L = 1+(4+3*L) := by omega
  have heq : rF0 L a b = false::false::true::true::rF1 L a b := by
    have hones : ones (5+3*L) = true :: ones (4+3*L) := by
      rw [hlen, show 1+(4+3*L) = (4+3*L)+1 by omega, ones_succ]
    simp [rF0, rB, rF1, hones, List.append_assoc]
  rw [show sF0 L a b =
    cfg .F [false,true,true,true] true (false::false::true::true::rF1 L a b)
      from congrArg (cfg .F [false,true,true,true] true) heq]
  exact bridgeF6 [] (rF1 L a b)

private theorem fscanL (L a b : Nat) :
    run (3*L) (sF1 L a b) = some (sF2 L a b) := by
  have heq : 4+3*L = (3*L+1)+3 := by omega
  have hr : rF1 L a b = ones (3*L+1) ++ (ones 3 ++ false::o3 a ++ rb b) := by
    simp only [rF1, heq, ones_add, List.append_assoc]
  have h := f_scan L lF1 (ones 3 ++ false::o3 a ++ rb b)
  have hout : true::(ones 3 ++ false::o3 a ++ rb b) = rF2 a b := by
    simp [rF2, ones, List.append_assoc]
  simpa only [sF1,sF2,lF2,hr,hout] using h

private theorem fbridge12 (L a b : Nat) :
    run 12 (sF2 L a b) = some (sF3 L a b) := by
  have hm : o3 a ++ [true,true,true] = true::ones (3*a+2) := by
    change ones (3*a) ++ ones 3 = _
    rw [← ones_add]
    have hn : 3*a+3=(3*a+2)+1 := by omega
    rw [hn, ones_succ (3*a+2)]
  have hmid : o3 a ++ rb b = true::rF3 a b := by
    simpa [rb, rF3, List.append_assoc] using
      congrArg (fun x : List Bool => x ++ [false,false] ++ o3 (b+1)) hm
  have hr : rF2 a b = true::true::true::true::false::true::rF3 a b := by
    simp [rF2, hmid, ones, List.append_assoc]
  have h := bridgeF12 (lF2 L) (rF3 a b)
  simpa [sF2,sF3,lF3,hr] using h

private theorem fscanA (L a b : Nat) :
    run (3*a) (sF3 L a b) = some (sF4 L a b) := by
  have hr : rF3 a b = ones (3*a+1) ++ ([true,false,false] ++ o3 (b+1)) := by
    simp only [rF3]
    have hn : 3*a+2=3*a+1+1 := by omega
    rw [hn,ones_add]
    simp [ones,List.append_assoc]
  have h := f_scan a (lF3 L) ([true,false,false] ++ o3 (b+1))
  simpa only [sF3,sF4,lF4,hr,rF4,List.cons_append,List.nil_append] using h

private theorem flast5 (L a b : Nat) :
    run 5 (sF4 L a b) = some (sF5 L a b) := by
  have hr : rF4 b = true::true::false::false::true::rF5 b := by
    simp only [rF4,rF5,o3]
    have hn : 3*(b+1) = 1+(3*b+2) := by omega
    rw [hn, show 1+(3*b+2) = (3*b+2)+1 by omega, ones_succ (3*b+2)]
    rfl
  have h := finalF5 (lF4 L a) (rF5 b)
  simpa [sF4,sF5,lF5,hr] using h



/-- Published S1(L,0,m0,a,0,b) as a finite-support, two-sided tape.
The current symbol is the LAST bit of the physical left word
`111011 ++ (111)^L ++ 100 ++ 10 ++ (111)^a`; the physical right word
is `0 ++ 11100 ++ (111)^(b+1)`. -/
def prepared (L a b : Nat) : Z :=
  match a with
  | 0 => startD L 0 b
  | k+1 => cfg .D (ones (3*k+2) ++ false::lb L) true (false::rb b)

private theorem prepared_to_d (L a b : Nat) :
    run (9*a) (prepared L a b) = some (startD L a b) := by
  cases a with
  | zero => rfl
  | succ k =>
    have hlen : 9*(k+1) = 3*((3*k+2)+1) := by omega
    rw [hlen]
    have hs := d_scan (3*k+2) (lb L) (rb b)
    have hn : 3*k+2+1 = 3*(k+1) := by omega
    simpa only [prepared, startD, o3, hn] using hs

private theorem b_to_a (L a b : Nat) :
    run ((((15+6)+3*L)+12)+3*a+5) (sB L a b) =
      some (sF5 L a b) := by
  have h01 := chain 15 6 (sB L a b) (sF0 L a b) (sF1 L a b)
    (bturn L a b) (fbridge6 L a b)
  have h02 := chain (15+6) (3*L) (sB L a b) (sF1 L a b) (sF2 L a b)
    h01 (fscanL L a b)
  have h03 := chain ((15+6)+3*L) 12 (sB L a b) (sF2 L a b) (sF3 L a b)
    h02 (fbridge12 L a b)
  have h04 := chain (((15+6)+3*L)+12) (3*a) (sB L a b) (sF3 L a b)
    (sF4 L a b) h03 (fscanA L a b)
  exact chain ((((15+6)+3*L)+12)+3*a) 5 (sB L a b)
    (sF4 L a b) (sF5 L a b) h04 (flast5 L a b)

/-- All-parameter counted terminal macro from the S1 intermediate state.
The time is primitive successful transitions before the first undefined
A/1 query. In particular, the b counter has no effect on this cost. -/
theorem terminal_macro_count (L a b : Nat) :
    run (59+12*(L+a)) (prepared L a b) = some (sF5 L a b) := by
  have hb : run (6+3*(5+3*L)) (startD L a b) = some (sB L a b) := by
    simpa only [sB, rB] using d_to_b L a b
  have hda := chain (6+3*(5+3*L)) ((((15+6)+3*L)+12)+3*a+5)
    (startD L a b) (sB L a b) (sF5 L a b) hb (b_to_a L a b)
  have hwhole := chain (9*a)
    ((6+3*(5+3*L)) + ((((15+6)+3*L)+12)+3*a+5))
    (prepared L a b) (startD L a b) (sF5 L a b)
    (prepared_to_d L a b) hda
  have hcount : 9*a + ((6+3*(5+3*L)) + ((((15+6)+3*L)+12)+3*a+5)) =
    59+12*(L+a) := by omega
  simpa only [hcount] using hwhole

/-- The terminal configuration truly consults the absent A/1 row. -/
theorem terminal_macro_halts (L a b : Nat) :
    (run (59+12*(L+a)) (prepared L a b)).bind step = none := by
  rw [terminal_macro_count]
  rfl


private theorem run_none_extended (n m : Nat) (z : Z) (h : run n z = none) :
    run (n+m) z = none := by
  rw [run_add, h]
  rfl

/-- Exact earliest undefined-query time, with no earlier premature halt.
Here `run t = none` means that the requested t successful moves cannot be
completed; the halt query is encountered after exactly N moves. -/
theorem terminal_first_halt (L a b t : Nat) :
    run t (prepared L a b) = none ↔ 59+12*(L+a) < t := by
  constructor
  · intro ht
    by_cases hlt : 59+12*(L+a) < t
    · exact hlt
    · have hle : t ≤ 59+12*(L+a) := by omega
      have hnone := run_none_extended t (59+12*(L+a)-t) (prepared L a b) ht
      have heq : t + (59+12*(L+a)-t) = 59+12*(L+a) := by omega
      rw [heq, terminal_macro_count] at hnone
      contradiction
  · intro hgt
    have heq : t = (59+12*(L+a)+1) + (t-(59+12*(L+a)+1)) := by omega
    rw [heq]
    have hfirst : run (59+12*(L+a)+1) (prepared L a b) = none := by
      change (run (59+12*(L+a)) (prepared L a b)).bind step = none
      exact terminal_macro_halts L a b
    exact run_none_extended (59+12*(L+a)+1)
      (t-(59+12*(L+a)+1)) (prepared L a b) hfirst

#print axioms terminal_first_halt

#print axioms terminal_macro_count
#print axioms terminal_macro_halts

end BB6.ChampionTerminal
