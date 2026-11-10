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


/-- Full physical words of the original published S1 marker-m0 section.
The head is on the last bit of the left physical word. -/
def originalLeftWord (L a : Nat) : List Bool :=
  [true,true,true,false,true,true] ++ o3 L ++
  [true,false,false,true,false] ++ o3 a

def originalRightWord (b : Nat) : List Bool :=
  [false,true,true,true,false,false] ++ o3 (b+1)

def fromPhysicalWords (physicalLeft physicalRight : List Bool) : Z :=
  match physicalLeft.reverse with
  | [] => cfg .D [] false physicalRight
  | head :: nearestLeft => cfg .D nearestLeft head physicalRight

private theorem originalLeftWord_reverse (L a : Nat) :
    (originalLeftWord L a).reverse =
    o3 a ++ [false,true,false,false,true] ++ o3 L ++
      [true,true,false,true,true,true] := by
  simp [originalLeftWord, o3, ones, List.reverse_append, List.append_assoc]

/-- Source-word fidelity for EVERY three-parameter prepared tape. -/
theorem original_words_eq_prepared (L a b : Nat) :
    fromPhysicalWords (originalLeftWord L a) (originalRightWord b) =
      prepared L a b := by
  rw [fromPhysicalWords, originalLeftWord_reverse]
  cases a with
  | zero =>
    simp [prepared,startD,lb,originalRightWord,rb,o3,ones,List.append_assoc]
  | succ k =>
    have hn : o3 (k+1) = true::ones (3*k+2) := by
      change ones (3*(k+1)) = _
      have heq : 3*(k+1)=3*k+2+1 := by omega
      rw [heq,ones_succ]
    rw [hn]
    simp [prepared,startD,lb,originalRightWord,rb,o3,ones,List.append_assoc]

#print axioms original_words_eq_prepared


/-- Read the nth tape symbol, with implicit zero padding. -/
def sideBit : List Bool → Nat → Bool
 | [], _ => false
 | h::_, 0 => h
 | _::t, n+1 => sideBit t n

/-- The physical tape relative to the current head. -/
def relativeTape (z : Z) : Int → Bool
 | .ofNat 0 => z.cur
 | .ofNat (n+1) => sideBit z.right n
 | .negSucc n => sideBit z.left n

private theorem sideBit_tail (l : List Bool) (n : Nat) :
  sideBit l.tail n = sideBit l (n+1) := by
  cases l <;> rfl

private theorem sideBit_zero (l : List Bool) :
    sideBit l 0 = l.headD false := by
  cases l <;> rfl

private theorem tape_moveR (q : Q) (v : Bool) (z : Z) (d : Int) :
    relativeTape (moveR q v z) (d-1) =
      if d=0 then v else relativeTape z d := by
  cases d with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero =>
        simp [relativeTape,moveR,cfg,sideBit_zero]
      | succ n =>
        have hd : (Int.ofNat (n+1+1))-1 = Int.ofNat (n+1) := by simp
        have hp : (n:Int)+1+1≠0 := by
          have hn := Int.natCast_nonneg n
          omega
        rw [hd]
        simp [relativeTape,moveR,cfg,sideBit_tail,hp]
  | negSucc n =>
    have hd : (Int.negSucc n)-1 = Int.negSucc (n+1) := by omega
    rw [hd]
    simp [relativeTape,moveR,cfg,sideBit]

private theorem tape_moveL (q : Q) (v : Bool) (z : Z) (d : Int) :
    relativeTape (moveL q v z) (d+1) =
      if d=0 then v else relativeTape z d := by
  cases d with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ n =>
      have hd : (Int.ofNat (n+1))+1 = Int.ofNat (n+1+1) := by simp
      have hp : (n:Int)+1≠0 := by
        have hn := Int.natCast_nonneg n
        omega
      rw [hd]
      simp [relativeTape,moveL,cfg,sideBit,hp]
  | negSucc n =>
    cases n with
    | zero =>
      have hd : (Int.negSucc 0)+1 = 0 := by omega
      rw [hd]
      simp [relativeTape,moveL,cfg,sideBit_zero]
    | succ n =>
      have hd : (Int.negSucc (n+1))+1 = Int.negSucc n := by omega
      rw [hd]
      simp [relativeTape,moveL,cfg,sideBit_tail]

#print axioms tape_moveR
#print axioms tape_moveL


/-- Explicit bi-infinite physical tape, for comparison with the canonical
    research coverage-machine semantics. -/
structure Full where
  state : Q
  head : Int
  tape : Int → Bool

def embedFull (z : Z) (position : Int) : Full :=
  ⟨z.state, position, fun x => relativeTape z (x-position)⟩

def fullR (q : Q) (v : Bool) (z : Full) : Full :=
  ⟨q,z.head+1,fun x => if x=z.head then v else z.tape x⟩

def fullL (q : Q) (v : Bool) (z : Full) : Full :=
  ⟨q,z.head-1,fun x => if x=z.head then v else z.tape x⟩

theorem embed_moveR (q : Q) (v : Bool) (z : Z) (p : Int) :
    embedFull (moveR q v z) (p+1) = fullR q v (embedFull z p) := by
  have htape : (fun x : Int => relativeTape (moveR q v z) (x-(p+1))) =
      (fun x : Int => if x=p then v else relativeTape z (x-p)) := by
    funext x
    have heq : x-(p+1)=(x-p)-1 := by omega
    rw [heq,tape_moveR]
    by_cases hx : x=p
    · simp [hx]
    · have hne : x-p≠0 := by omega
      simp [hx,hne]
  exact congrArg (fun tape : Int→Bool => Full.mk q (p+1) tape) htape

theorem embed_moveL (q : Q) (v : Bool) (z : Z) (p : Int) :
    embedFull (moveL q v z) (p-1) = fullL q v (embedFull z p) := by
  have htape : (fun x : Int => relativeTape (moveL q v z) (x-(p-1))) =
      (fun x : Int => if x=p then v else relativeTape z (x-p)) := by
    funext x
    have heq : x-(p-1)=(x-p)+1 := by omega
    rw [heq,tape_moveL]
    by_cases hx : x=p
    · simp [hx]
    · have hne : x-p≠0 := by omega
      simp [hx,hne]
  exact congrArg (fun tape : Int→Bool => Full.mk q (p-1) tape) htape

#print axioms embed_moveR
#print axioms embed_moveL


def fullStep (z : Full) : Option Full :=
  match z.state, z.tape z.head with
  | .A, false => some (fullR .B true z)
  | .A, true => none
  | .B, false => some (fullL .C true z)
  | .B, true => some (fullR .F false z)
  | .C, false => some (fullR .E true z)
  | .C, true => some (fullL .D false z)
  | .D, false => some (fullL .C false z)
  | .D, true => some (fullR .B true z)
  | .E, false => some (fullR .A true z)
  | .E, true => some (fullR .E true z)
  | .F, false => some (fullR .E true z)
  | .F, true => some (fullR .D false z)

def delta (z : Z) : Int :=
  match z.state,z.cur with
  | .A,false => 1
  | .A,true => 0
  | .B,false => -1
  | .B,true => 1
  | .C,false => 1
  | .C,true => -1
  | .D,false => -1
  | .D,true => 1
  | .E,false => 1
  | .E,true => 1
  | .F,false => 1
  | .F,true => 1

def locatedStep (zp : Z × Int) : Option (Z × Int) :=
  (step zp.1).map (fun newZ => (newZ,zp.2+delta zp.1))

@[simp] theorem embed_read_current (z : Z) (p : Int) :
  (embedFull z p).tape (embedFull z p).head = z.cur := by
  simp [embedFull,relativeTape]

@[simp] theorem embed_state (z : Z) (p : Int) :
  (embedFull z p).state = z.state := rfl

private theorem embed_moveL_add (q : Q) (v : Bool) (z : Z) (p : Int) :
    embedFull (moveL q v z) (p+(-1)) = fullL q v (embedFull z p) := by
  have hp : p+(-1:Int) = p-1 := by omega
  rw [hp]
  exact embed_moveL q v z p

theorem step_semiconjugacy (z : Z) (p : Int) :
  fullStep (embedFull z p) =
    (locatedStep (z,p)).map (fun x => embedFull x.1 x.2) := by
  cases z with
  | mk q l c r =>
    cases q <;> cases c <;>
      simp [fullStep,locatedStep,delta,step,embed_read_current,embed_state,
        embed_moveR,embed_moveL_add]

#print axioms step_semiconjugacy


def locatedRun : Nat → Z × Int → Option (Z × Int)
 | 0,z => some z
 | n+1,z => (locatedRun n z).bind locatedStep

def fullRun : Nat → Full → Option Full
 | 0,z => some z
 | n+1,z => (fullRun n z).bind fullStep

private theorem locatedStep_fst (zp : Z × Int) :
    (locatedStep zp).map Prod.fst = step zp.1 := by
  unfold locatedStep
  cases h : step zp.1 <;> simp [h]

/-- Machine-independent all-fuel simulation embedding, preserving absolute
head coordinates and the entire infinite tape at each successful step. -/
theorem run_semiconjugacy (n : Nat) (z : Z) (p : Int) :
    (locatedRun n (z,p)).map (fun w => embedFull w.1 w.2) =
      fullRun n (embedFull z p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [locatedRun,fullRun]
    rw [← ih]
    cases h : locatedRun n (z,p) with
    | none => simp [h]
    | some w =>
      simp only [h,Option.bind_some,Option.map_some]
      exact (step_semiconjugacy w.1 w.2).symm

private theorem run_located_fst (n : Nat) (z : Z) (p : Int) :
    (locatedRun n (z,p)).map Prod.fst = run n z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [locatedRun,run]
    rw [← ih]
    cases h : locatedRun n (z,p) with
    | none => simp [h]
    | some w =>
      simp only [h,Option.bind_some,Option.map_some]
      exact locatedStep_fst w

/-- Original table in an absolute-head, full-biinfinite tape: exactly the
same fuel-to-halt predicate as the local zipper, for every initial tape. -/
theorem full_run_none_iff (n : Nat) (z : Z) (p : Int) :
    fullRun n (embedFull z p) = none ↔ run n z = none := by
  rw [← run_semiconjugacy, ← run_located_fst]
  cases h : locatedRun n (z,p) <;> simp [h]

/-- Fully infinite-tape exact terminal cost for all L,a,b. -/
theorem full_terminal_first_halt (L a b t : Nat) :
    fullRun t (embedFull (prepared L a b) 0) = none ↔
      59+12*(L+a)<t := by
  rw [full_run_none_iff]
  exact terminal_first_halt L a b t

#print axioms run_semiconjugacy
#print axioms full_run_none_iff
#print axioms full_terminal_first_halt


/-- Original BB6Coverage's successful-moves counting shape in this
physical, infinite-tape machine. -/
def FullHaltsAfter (z : Full) (n : Nat) : Prop :=
  (fullRun n z).isSome = true ∧ fullRun (n+1) z = none

/-- Uniform exact scored stopping time for the full infinite-tape model. -/
theorem full_halting_score_iff (L a b t : Nat) :
  FullHaltsAfter (embedFull (prepared L a b) 0) t ↔
    t = 59+12*(L+a) := by
  constructor
  · intro h
    obtain ⟨hlive, hnstop⟩ := h
    have hnext : 59+12*(L+a) < t+1 :=
      (full_terminal_first_halt L a b (t+1)).mp hnstop
    by_cases hbig : 59+12*(L+a) < t
    · have hbad : fullRun t (embedFull (prepared L a b) 0) = none :=
        (full_terminal_first_halt L a b t).mpr hbig
      rw [hbad] at hlive
      contradiction
    · omega
  · intro ht
    subst t
    constructor
    · cases h : fullRun (59+12*(L+a)) (embedFull (prepared L a b) 0) with
      | none =>
        have hn := (full_terminal_first_halt L a b (59+12*(L+a))).mp h
        omega
      | some z => rfl
    · exact (full_terminal_first_halt L a b (59+12*(L+a)+1)).mpr (by omega)

#print axioms full_halting_score_iff

end BB6.ChampionTerminal
