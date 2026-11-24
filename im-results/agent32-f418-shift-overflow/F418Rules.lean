import SourceFiniteSemantics
namespace BB6.Agent32F418
open BB6Coverage BB6.Agent32FiniteSource

def machine : Machine := fun (q,b) =>
  match q.val,b with
  | 0,false => some ⟨true,true,1⟩
  | 0,true => some ⟨true,false,3⟩
  | 1,false => some ⟨true,true,2⟩
  | 1,true => some ⟨false,true,1⟩
  | 2,false => some ⟨true,false,0⟩
  | 2,true => some ⟨true,true,2⟩
  | 3,false => some ⟨true,false,4⟩
  | 3,true => some ⟨false,false,0⟩
  | 4,false => some ⟨true,false,5⟩
  | 5,false => some ⟨true,false,2⟩
  | _,_ => none

def cfg (q : Fin 6) (l : List Bool) (b : Bool) (r : List Bool) : FiniteCfg := ⟨l,r,b,q⟩
abbrev D0 := cfg 3

def atR (q : Fin 6) (l r : List Bool) : FiniteCfg := cfg q l (r.headD false) r.tail
def atL (q : Fin 6) (l r : List Bool) : FiniteCfg := cfg q l.tail (l.headD false) r

def Run (k : Nat) (c d : FiniteCfg) : Prop := finiteRun machine k c = some d

theorem run_zero (c : FiniteCfg) : Run 0 c c := rfl

theorem run_append (m : Machine) (n k : Nat) (c : FiniteCfg) :
    finiteRun m (n+k) c = (finiteRun m n c).bind (finiteRun m k) := by
  induction n generalizing c with
  | zero => simp [finiteRun]
  | succ n ih =>
    rw [Nat.succ_add, finiteRun, finiteRun]
    cases h : step m c <;> simp [h,ih]

theorem Run.trans {n k : Nat} {c d e : FiniteCfg} (h : Run n c d) (g : Run k d e) : Run (n+k) c e := by
  unfold Run at *
  rw [run_append,h]
  exact g

def ones (n : Nat) := List.replicate n true
def zeros (n : Nat) := List.replicate n false

def alt : Nat → List Bool
  | 0 => []
  | n+1 => false :: true :: alt n

theorem alt_add (n k : Nat) : alt (n+k) = alt n ++ alt k := by
  induction n with
  | zero => simp [alt]
  | succ n ih => simp [Nat.succ_add,alt,ih]

theorem carry (l r : List Bool) :
    Run 5 (cfg 3 ([false,false,false,true,false]++l) false r)
      (cfg 3 l false (ones 5 ++ r)) := rfl

theorem carry_stop (l r : List Bool) :
    Run 5 (cfg 3 ([false,false,false,false]++l) false r)
      (atR 1 (true::l) (ones 4 ++ r)) := rfl

theorem c_scan (n : Nat) (l r : List Bool) :
    Run n (atR 2 l (ones n ++ r)) (atR 2 (ones n ++ l) r) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    have h : Run 1 (atR 2 l (ones (n+1) ++ r)) (atR 2 (true::l) (ones n ++ r)) := rfl
    have h' := h.trans (ih (true::l))
    rw [Nat.add_comm] at h'
    simpa only [ones, List.replicate_succ', List.append_assoc, List.cons_append, List.nil_append] using h'

theorem b_scan (n : Nat) (l r : List Bool) :
    Run n (atR 1 l (ones n ++ r)) (atR 1 (zeros n ++ l) r) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    have h : Run 1 (atR 1 l (ones (n+1) ++ r)) (atR 1 (false::l) (ones n ++ r)) := rfl
    have h' := h.trans (ih (false::l))
    rw [Nat.add_comm] at h'
    simpa only [zeros, List.replicate_succ', List.append_assoc, List.cons_append, List.nil_append] using h'

theorem a_scan (n : Nat) (l r : List Bool) :
    Run (2*n) (atL 0 (ones (2*n) ++ l) r) (atL 0 l (alt n ++ r)) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    have h : Run 2 (atL 0 (ones (2*n+2) ++ l) r) (atL 0 (ones (2*n) ++ l) ([false,true]++r)) := rfl
    have h' := h.trans (ih ([false,true]++r))
    rw [show 2+2*n = 2*(n+1) by omega] at h'
    rw [show 2*n+2 = 2*(n+1) by omega] at h'
    simpa [show alt (n+1) = alt n ++ [false,true] by rw [alt_add]; rfl, List.append_assoc] using h'

theorem a_scan_odd (n : Nat) (l r : List Bool) :
    Run (2*n+1) (atL 0 (ones (2*n+1) ++ l) r) (atL 3 l (true::(alt n ++ r))) := by
  have h := a_scan n (true::l) r
  have h' : Run 1 (atL 0 (true::l) (alt n ++ r)) (atL 3 l (true::(alt n ++ r))) := rfl
  have h'' := h.trans h'
  simpa [ones,List.replicate_succ',List.append_assoc] using h''

def word0 : Nat → List Bool
  | 0 => []
  | n+1 => true :: false :: word0 n

theorem word0_add (n k : Nat) : word0 (n+k) = word0 n ++ word0 k := by
  induction n with
  | zero => simp [word0]
  | succ n ih => simp [Nat.succ_add,word0,ih]

theorem alt_rotate (n : Nat) (r : List Bool) :
    true :: (alt n ++ r) = word0 n ++ true :: r := by
  induction n with
  | zero => rfl
  | succ n ih => simp [alt,word0,ih]

theorem ones_add (n k : Nat) : ones (n+k) = ones n ++ ones k := by
  induction k with
  | zero => simp [ones]
  | succ k ih => simp only [ones,List.replicate_succ',Nat.add_succ] at ih ⊢
                 rw [ih,List.append_assoc]

theorem zeros_add (n k : Nat) : zeros (n+k) = zeros n ++ zeros k := by
  induction k with
  | zero => simp [zeros]
  | succ k ih => simp only [zeros,List.replicate_succ',Nat.add_succ] at ih ⊢
                 rw [ih,List.append_assoc]

def carryWord : Nat → List Bool
  | 0 => []
  | n+1 => [false,false,false,true,false] ++ carryWord n

theorem carry_many (k : Nat) (l r : List Bool) :
    Run (5*k) (cfg 3 (carryWord k ++ l) false r)
      (cfg 3 l false (ones (5*k) ++ r)) := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
    have h := carry (carryWord k ++ l) r
    have h' := h.trans (ih (ones 5 ++ r))
    rw [show 5+5*k = 5*(k+1) by omega] at h'
    rw [show 5*(k+1) = 5*k+5 by omega, ones_add]
    simpa [carryWord,List.append_assoc,Nat.mul_add] using h'

/-- Left binary carry, then erase the temporary unary run. -/
theorem carry_to_B (k : Nat) (l r : List Bool) :
    Run (10*k+10) (cfg 3 (carryWord k ++ [false,false,false,false] ++ l) false (true::false::r))
      (cfg 1 (zeros (5*k+5) ++ true::l) false r) := by
  have h := carry_many k ([false,false,false,false]++l) (true::false::r)
  have h' := h.trans (carry_stop l (ones (5*k) ++ true::false::r))
  have h'' : Run (5*k+5) (atR 1 (true::l) (ones 4 ++ (ones (5*k) ++ true::false::r)))
      (cfg 1 (zeros (5*k+5) ++ true::l) false r) := by
    have s := b_scan (5*k+5) (true::l) (false::r)
    rw [show 5*k+5 = 4+(5*k)+1 by omega,ones_add,ones_add] at s
    simpa [atR, List.append_assoc,ones,show 4+5*k+1 = 5*k+5 by omega] using s
  have hfin := h'.trans h''
  rw [show 5*k+5+(5*k+5) = 10*k+10 by omega] at hfin
  simpa [List.append_assoc] using hfin

/-- The short preliminary pass for a=0 turns B0 into C scanning the
same right carry as a=1, with two ones immediately behind it. -/
theorem right_prepare_zero (l r : List Bool) :
    Run 7 (cfg 1 ([false,false]++l) false ([true,false]++r))
      (atR 2 (true::true::false::l) ([true,true]++r)) := rfl

theorem right_prepare_one (l r : List Bool) :
    Run 1 (cfg 1 ([false,false]++l) false ([true,true]++r))
      (atR 2 (true::false::false::l) ([true,true]++r)) := rfl

/-- A zero at the left boundary of an even A/D sweep admits one more
short pass, shifting left once and making the right phase bit 1. -/
theorem even_finish (l r : List Bool) :
    Run 7 (cfg 0 (false::l) false ([false,true,false,true]++r))
      (cfg 3 l false ([true,false,true,true,true]++r)) := rfl

theorem c_turn (n : Nat) (l r : List Bool) :
    Run (n+1) (atR 2 l (ones n ++ false::r)) (atL 0 (ones n ++ l) (true::r)) := by
  have h := c_scan n l (false::r)
  have h' : Run 1 (atR 2 (ones n ++ l) (false::r)) (atL 0 (ones n ++ l) (true::r)) := rfl
  exact h.trans h'

theorem right_inc_zero (k : Nat) (l r : List Bool) :
    Run (4*k+16) (cfg 1 ([false,false]++l) false ([true,false]++ones (2*k)++[true,false]++r))
      (cfg 3 l false ([true,false,true,false]++word0 k++[true,true]++r)) := by
  have h := right_prepare_zero l (ones (2*k)++[true,false]++r)
  have h1 : Run (2*k+3+1) (atR 2 (true::true::false::l) ([true,true]++(ones (2*k)++[true,false]++r)))
      (atL 0 (ones (2*k+5)++false::l) (true::r)) := by
    have h' := c_turn (2*k+3) (true::true::false::l) r
    rw [show 2*k+3=2+2*k+1 by omega,ones_add,ones_add] at h'
    rw [show 2*k+5=2+2*k+1+2 by omega,ones_add,ones_add,ones_add]
    simpa [ones,List.append_assoc,show 2+2*k+1 = 2*k+3 by omega] using h'
  have h2 := a_scan_odd (k+2) (false::l) (true::r)
  rw [show 2*(k+2)+1=2*k+5 by omega] at h2
  have hf := (h.trans h1).trans h2
  rw [show 7+(2*k+3+1)+(2*k+5)=4*k+16 by omega] at hf
  rw [alt_rotate,show k+2=2+k by omega,word0_add] at hf
  simpa [atL,cfg,word0,List.append_assoc] using hf

theorem right_inc_one (k : Nat) (l r : List Bool) :
    Run (4*k+16) (cfg 1 ([false,false]++l) false ([true,true]++ones (2*k)++[true,false]++r))
      (cfg 3 l false ([true,false,true,true]++word0 k++[true,true]++r)) := by
  have h := right_prepare_one l (ones (2*k)++[true,false]++r)
  have h1 : Run (2*k+3+1) (atR 2 (true::false::false::l) ([true,true]++(ones (2*k)++[true,false]++r)))
      (atL 0 (ones (2*k+4)++false::false::l) (true::r)) := by
    have h' := c_turn (2*k+3) (true::false::false::l) r
    rw [show 2*k+3=2+2*k+1 by omega,ones_add,ones_add] at h'
    rw [show 2*k+4=2+2*k+1+1 by omega,ones_add,ones_add,ones_add]
    simpa [ones,List.append_assoc,show 2+2*k+1 = 2*k+3 by omega] using h'
  have h2 := a_scan (k+2) (false::false::l) (true::r)
  rw [show 2*(k+2)=2*k+4 by omega] at h2
  have hf := (h.trans h1).trans h2
  rw [show k+2=2+k by omega,alt_add] at hf
  have he := even_finish l (alt k ++ true::r)
  have hf' : Run (1+(2*k+3+1)+(2*k+4)) (cfg 1 ([false,false]++l) false ([true,true]++ones (2*k)++[true,false]++r)) (cfg 0 (false::l) false ([false,true,false,true]++(alt k++true::r))) := by
    simpa [atL,alt,List.append_assoc] using hf
  have hh := hf'.trans he
  rw [show 1+(2*k+3+1)+(2*k+4)+7=4*k+16 by omega] at hh
  simpa [List.append_assoc,alt_rotate] using hh

/-- Common reset sweep: the total unary run has odd length. -/
theorem unary_odd (p q e : Nat) (l r : List Bool) (a : Bool) (h : p+q=2*e+5) :
    Run (p+2*q+1) (atR 2 (ones p++false::l) (ones q++false::true::a::r))
      (cfg 3 l false ([true,false,true,false]++word0 e++[true,true,true,a]++r)) := by
  have h1 := c_turn q (ones p++false::l) (true::a::r)
  have h2 := a_scan_odd (e+2) (false::l) (true::true::a::r)
  rw [show 2*(e+2)+1=q+p by omega,ones_add] at h2
  have h2' : Run (q+p) (atL 0 (ones q++(ones p++false::l)) (true::true::a::r))
      (cfg 3 l false ([true,false,true,false]++word0 e++[true,true,true,a]++r)) := by
    rw [alt_rotate,show e+2=2+e by omega,word0_add] at h2
    simpa [atL,cfg,word0,List.append_assoc] using h2
  have hf := h1.trans h2'
  rwa [show q+1+(q+p)=p+2*q+1 by omega] at hf

/-- Common reset sweep: an even unary run shifts one additional cell left. -/
theorem unary_even (p q e : Nat) (l r : List Bool) (a : Bool) (h : p+q=2*e+4) :
    Run (p+2*q+8) (atR 2 (ones p++false::false::l) (ones q++false::true::a::r))
      (cfg 3 l false ([true,false,true,true]++word0 e++[true,true,true,a]++r)) := by
  have h1 := c_turn q (ones p++false::false::l) (true::a::r)
  have h2 := a_scan (e+2) (false::false::l) (true::true::a::r)
  rw [show 2*(e+2)=q+p by omega,ones_add,show e+2=2+e by omega,alt_add] at h2
  have h2' : Run (q+p) (atL 0 (ones q++(ones p++false::false::l)) (true::true::a::r))
      (cfg 0 (false::l) false ([false,true,false,true]++(alt e++true::true::a::r))) := by
    simpa [atL,alt,List.append_assoc] using h2
  have hf := (h1.trans h2').trans (even_finish l (alt e++true::true::a::r))
  rw [show q+1+(q+p)+7=p+2*q+8 by omega] at hf
  simpa [List.append_assoc,alt_rotate] using hf

theorem collision2 (k : Nat) (l r : List Bool) (a : Bool) :
    Run (5*k+3) (cfg 3 (carryWord k++[false,false,true]++l) false ([true,false,true,a]++r))
      (atR 2 l (ones (5*k+5)++false::true::a::r)) := by
  have h1 := carry_many k ([false,false,true]++l) ([true,false,true,a]++r)
  have h2 : Run 3 (cfg 3 ([false,false,true]++l) false (ones (5*k)++[true,false,true,a]++r))
      (atR 2 l (ones (5*k+5)++false::true::a::r)) := by
    rw [show 5*k+5=4+5*k+1 by omega,ones_add,ones_add]
    simp only [List.append_assoc]
    rfl
  have h2a := h2
  rw [List.append_assoc] at h2a
  simpa [List.append_assoc] using h1.trans h2a

theorem collision4 (k : Nat) (l r : List Bool) (a : Bool) :
    Run (5*k+8) (cfg 3 (carryWord k++[false,false,false,true,true,false]++l) false ([true,false,true,a]++r))
      (atR 2 (true::true::l) (ones (5*k+6)++false::true::a::r)) := by
  have h1 := carry_many k ([false,false,false,true,true,false]++l) ([true,false,true,a]++r)
  have h2 : Run 8 (cfg 3 ([false,false,false,true,true,false]++l) false (ones (5*k)++[true,false,true,a]++r))
      (atR 2 (true::true::l) (ones (5*k+6)++false::true::a::r)) := by
    rw [show 5*k+6=5+5*k+1 by omega,ones_add,ones_add]
    simp only [List.append_assoc]
    rfl
  have h2a := h2
  rw [List.append_assoc] at h2a
  simpa [List.append_assoc] using h1.trans h2a

/-- Offset-2 reset, even carry length. The new left alignment is 3. -/
theorem reset2_even (k : Nat) (l r : List Bool) (a : Bool) :
    Run (30*k+14) (cfg 3 (carryWord (2*k)++[false,false,true,false]++l) false ([true,false,true,a]++r))
      (cfg 3 l false ([true,false,true,false]++word0 (5*k)++[true,true,true,a]++r)) := by
  have h1 := collision2 (2*k) (false::l) r a
  have h2 := unary_odd 0 (5*(2*k)+5) (5*k) l r a (by omega)
  have h2' : Run (2*(5*(2*k)+5)+1) (atR 2 (false::l) (ones (5*(2*k)+5)++false::true::a::r))
      (cfg 3 l false ([true,false,true,false]++word0 (5*k)++[true,true,true,a]++r)) := by simpa [ones] using h2
  have hf := h1.trans h2'
  rw [show 5*(2*k)+3+(2*(5*(2*k)+5)+1)=30*k+14 by omega] at hf
  simpa [List.append_assoc] using hf

/-- Offset-2 reset, odd carry length. The left alignment remains 2. -/
theorem reset2_odd (k : Nat) (l r : List Bool) (a : Bool) :
    Run (30*k+36) (cfg 3 (carryWord (2*k+1)++[false,false,true,false,false]++l) false ([true,false,true,a]++r))
      (cfg 3 l false ([true,false,true,true]++word0 (5*k+3)++[true,true,true,a]++r)) := by
  have h1 := collision2 (2*k+1) (false::false::l) r a
  have h2 := unary_even 0 (5*(2*k+1)+5) (5*k+3) l r a (by omega)
  have h2' : Run (2*(5*(2*k+1)+5)+8) (atR 2 (false::false::l) (ones (5*(2*k+1)+5)++false::true::a::r))
      (cfg 3 l false ([true,false,true,true]++word0 (5*k+3)++[true,true,true,a]++r)) := by simpa [ones] using h2
  have hf := h1.trans h2'
  rw [show 5*(2*k+1)+3+(2*(5*(2*k+1)+5)+8)=30*k+36 by omega] at hf
  simpa [List.append_assoc] using hf

/-- Offset-4 reset, even carry length. The new alignment is 1,
which is hazardous if a left bit remains. -/
theorem reset4_even (k : Nat) (l r : List Bool) (a : Bool) :
    Run (30*k+30) (cfg 3 (carryWord (2*k)++[false,false,false,true,true,false,false,false]++l) false ([true,false,true,a]++r))
      (cfg 3 l false ([true,false,true,true]++word0 (5*k+2)++[true,true,true,a]++r)) := by
  have h1 := collision4 (2*k) (false::false::l) r a
  have h2 := unary_even 2 (5*(2*k)+6) (5*k+2) l r a (by omega)
  have h2' : Run (2+2*(5*(2*k)+6)+8) (atR 2 (true::true::false::false::l) (ones (5*(2*k)+6)++false::true::a::r))
      (cfg 3 l false ([true,false,true,true]++word0 (5*k+2)++[true,true,true,a]++r)) := by exact h2
  have hf := h1.trans h2'
  rw [show 5*(2*k)+8+(2+2*(5*(2*k)+6)+8)=30*k+30 by omega] at hf
  simpa [List.append_assoc] using hf

/-- Offset-4 reset, odd carry length. The new alignment is 2. -/
theorem reset4_odd (k : Nat) (l r : List Bool) (a : Bool) :
    Run (30*k+38) (cfg 3 (carryWord (2*k+1)++[false,false,false,true,true,false,false]++l) false ([true,false,true,a]++r))
      (cfg 3 l false ([true,false,true,false]++word0 (5*k+4)++[true,true,true,a]++r)) := by
  have h1 := collision4 (2*k+1) (false::l) r a
  have h2 := unary_odd 2 (5*(2*k+1)+6) (5*k+4) l r a (by omega)
  have h2' : Run (2+2*(5*(2*k+1)+6)+1) (atR 2 (true::true::false::l) (ones (5*(2*k+1)+6)++false::true::a::r))
      (cfg 3 l false ([true,false,true,false]++word0 (5*k+4)++[true,true,true,a]++r)) := by exact h2
  have hf := h1.trans h2'
  rw [show 5*(2*k+1)+8+(2+2*(5*(2*k+1)+6)+1)=30*k+38 by omega] at hf
  simpa [List.append_assoc] using hf

/-- Right overflow with phase bit 0 shifts the head left by one. -/
theorem right_overflow_zero (k : Nat) (l r : List Bool) :
    Run (4*k+21) (cfg 1 ([false,false,false]++l) false ([true,false]++ones (2*k)++false::r))
      (cfg 3 l false ([true,false,true,true]++word0 k++[true,true]++r)) := by
  have h := right_prepare_zero (false::l) (ones (2*k)++false::r)
  have h1 : Run (2*k+2+1) (atR 2 (true::true::false::false::l) ([true,true]++(ones (2*k)++false::r)))
      (atL 0 (ones (2*k+4)++false::false::l) (true::r)) := by
    have h' := c_turn (2*k+2) (true::true::false::false::l) r
    rw [show 2*k+2=2+2*k by omega,ones_add] at h'
    rw [show 2*k+4=2+2*k+2 by omega,ones_add,ones_add]
    simpa [ones,List.append_assoc,show 2+2*k=2*k+2 by omega] using h'
  have h2 := a_scan (k+2) (false::false::l) (true::r)
  rw [show 2*(k+2)=2*k+4 by omega,show k+2=2+k by omega,alt_add] at h2
  have h2' : Run (2*k+4) (atL 0 (ones (2*k+4)++false::false::l) (true::r))
      (cfg 0 (false::l) false ([false,true,false,true]++(alt k++true::r))) := by simpa [atL,alt,List.append_assoc] using h2
  have hf := ((h.trans h1).trans h2').trans (even_finish l (alt k++true::r))
  rw [show 7+(2*k+2+1)+(2*k+4)+7=4*k+21 by omega] at hf
  simpa [List.append_assoc,alt_rotate] using hf

/-- Right overflow with phase bit 1 shifts the head right by one. -/
theorem right_overflow_one (k : Nat) (l r : List Bool) :
    Run (4*k+11) (cfg 1 ([false,false]++l) false ([true,true]++ones (2*(k+1))++false::r))
      (cfg 3 (false::l) false ([true,false,true,false]++word0 k++[true,true]++r)) := by
  have h := right_prepare_one l (ones (2*(k+1))++false::r)
  have h1 : Run (2*(k+1)+2+1) (atR 2 (true::false::false::l) ([true,true]++(ones (2*(k+1))++false::r)))
      (atL 0 (ones (2*(k+1)+3)++false::false::l) (true::r)) := by
    have h' := c_turn (2*(k+1)+2) (true::false::false::l) r
    rw [show 2*(k+1)+2=2+2*(k+1) by omega,ones_add] at h'
    rw [show 2*(k+1)+3=2+2*(k+1)+1 by omega,ones_add,ones_add]
    simpa [ones,List.append_assoc,show 2+2*(k+1)=2*(k+1)+2 by omega] using h'
  have h2 := a_scan_odd (k+2) (false::false::l) (true::r)
  rw [show 2*(k+2)+1=2*(k+1)+3 by omega,alt_rotate,show k+2=2+k by omega,word0_add] at h2
  have hf := (h.trans h1).trans h2
  rw [show 1+(2*(k+1)+2+1)+(2*(k+1)+3)=4*k+11 by omega] at hf
  simpa [atL,word0,List.append_assoc] using hf

/-- If the shifted counter reaches its first bit one cell too close,
F1 is the next undefined transition. -/
theorem offset1_hazard (k : Nat) (l r : List Bool) :
    Run (5*k+2) (cfg 3 (carryWord k++[false,true]++l) false r)
      (cfg 5 l true ([true,true]++ones (5*k)++r)) := by
  have h := carry_many k ([false,true]++l) r
  have h' : Run 2 (cfg 3 ([false,true]++l) false (ones (5*k)++r))
      (cfg 5 l true ([true,true]++ones (5*k)++r)) := rfl
  simpa [List.append_assoc] using h.trans h'

theorem offset1_hazard_halts (l r : List Bool) : step machine (cfg 5 l true r) = none := rfl

#print axioms carry
#print axioms carry_stop
#print axioms c_scan
#print axioms b_scan
#print axioms a_scan_odd
#print axioms carry_to_B
#print axioms right_inc_zero
#print axioms right_inc_one
#print axioms right_overflow_zero
#print axioms right_overflow_one
#print axioms reset2_even
#print axioms reset2_odd
#print axioms reset4_even
#print axioms reset4_odd
#print axioms offset1_hazard
end BB6.Agent32F418
