import BlockPump

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw124ZeroLF1LCCounter
open BB6Coverage BB6Coverage.Agent50Pump BB6Coverage.Agent50Zipper

def table (v : Bool) : PartialMachine := fun s =>
  match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨true,false,if v then 5 else 3⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => none
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => some (some ⟨true,true,0⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨true,true,4⟩)
  | (4,false) => some (some ⟨true,true,2⟩)
  | (4,true) => some (some ⟨true,false,5⟩)
  | (5,false) => some (some ⟨true,false,2⟩)
  | (5,true) => some (some ⟨false,false,5⟩)
  | _ => none

def A (l r : List Bool) : HZ := ⟨0,l,r⟩
def C (l r : List Bool) : HZ := ⟨2,l,r⟩
def F (l r : List Bool) : HZ := ⟨5,l,r⟩
def ones : Nat → List Bool | 0 => [] | n+1 => true::ones n
def zeros : Nat → List Bool | 0 => [] | n+1 => false::zeros n
def H : Nat → List Bool | 0 => [] | n+1 => true::true::false::H n
def K : Nat → List Bool | 0 => [] | n+1 => true::false::false::K n
def J : Nat → List Bool | 0 => [] | n+1 => false::false::true::J n
def L (n : Nat) : List Bool := false::H n

def enc : List Bool → List Bool
  | [] => []
  | b::ds => b::false::false::enc ds

theorem ones_add (a b : Nat) : ones (a+b) = ones a ++ ones b := by
  induction a with
  | zero => simp [ones]
  | succ a ih => rw [show a+1+b=a+b+1 by omega]; simp [ones,ih]
theorem zeros_add (a b : Nat) : zeros (a+b) = zeros a ++ zeros b := by
  induction a with
  | zero => simp [zeros]
  | succ a ih => rw [show a+1+b=a+b+1 by omega]; simp [zeros,ih]
theorem H_add (a b : Nat) : H (a+b) = H a ++ H b := by
  induction a with
  | zero => simp [H]
  | succ a ih => rw [show a+1+b=a+b+1 by omega]; simp [H,ih]
theorem K_add (a b : Nat) : K (a+b) = K a ++ K b := by
  induction a with
  | zero => simp [K]
  | succ a ih => rw [show a+1+b=a+b+1 by omega]; simp [K,ih]
theorem enc_append (a b : List Bool) : enc (a++b) = enc a ++ enc b := by
  induction a with
  | nil => rfl
  | cons h t ih => simp [enc,ih]
theorem enc_ones (n : Nat) : enc (ones n) = K n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ones,enc,K,ih]
theorem enc_zeros (n : Nat) : enc (zeros n) = zeros (3*n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show 3*(n+1)=3*n+3 by omega]; simp [zeros,enc,ih]
theorem K_J (k : Nat) (R : List Bool) : K k ++ true::R = true::(J k ++ R) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [K,J,ih]

def Reach (v : Bool) (a b : HZ) : Prop := ∃ t, hrun (table v) t a = some b

theorem reflR (v : Bool) (a : HZ) : Reach v a a := ⟨0,rfl⟩
theorem joinR {v : Bool} {a b c : HZ} (h : Reach v a b) (g : Reach v b c) : Reach v a c := by
  obtain ⟨t,ht⟩ := h; obtain ⟨u,hu⟩ := g; exact ⟨t+u,hjoin ht hu⟩
theorem exactR {v : Bool} {a b : HZ} {t : Nat} (h : hrun (table v) t a = some b) : Reach v a b := ⟨t,h⟩

-- Rightward scan consumes 100 blocks, leaving the current cell zero.
theorem scanR (v : Bool) (j k : Nat) (U R : List Bool) :
    Reach v (C (false::(H j++U)) (K k++R)) (C (false::(H (j+k)++U)) R) := by
  induction k generalizing j with
  | zero => exact reflR _ _
  | succ k ih =>
    have h : hrun (table v) 3 (C (false::(H j++U)) (K (k+1)++R)) =
      some (C (false::(H (j+1)++U)) (K k++R)) := by rfl
    rw [show j+(k+1)=j+1+k by omega]
    exact joinR (exactR h) (ih (j+1))

theorem scanRempty (v : Bool) (k : Nat) (R : List Bool) :
    Reach v (C [] (K (k+1)++R)) (C (L (k+1)) R) := by
  have h : hrun (table v) 3 (C [] (K (k+1)++R)) = some (C (L 1) (K k++R)) := by rfl
  have g := scanR v 1 k [] R
  simp only [List.append_nil] at g
  rw [show 1+k=k+1 by omega] at g
  exact joinR (exactR h) g

-- Leftward scan consumes 110 blocks, keeping the right word starting in 1.
def leftCost (v : Bool) : Nat := if v then 5 else 7

theorem leftUnit (v : Bool) (Ltail R : List Bool) :
    hrun (table v) (leftCost v) (C (true::true::false::Ltail) (true::R)) =
      some (C Ltail (true::false::false::true::R)) := by cases v <;> rfl

theorem scanL (v : Bool) (k j : Nat) (U R : List Bool) :
    Reach v (C (H k++U) (K j++true::R)) (C U (K (j+k)++true::R)) := by
  induction k generalizing j with
  | zero => exact reflR _ _
  | succ k ih =>
    have h : hrun (table v) (leftCost v) (C (H (k+1)++U) (K j++true::R)) =
      some (C (H k++U) (K (j+1)++true::R)) := by
      cases j <;> cases v <;> rfl
    rw [show j+(k+1)=j+1+k by omega]
    exact joinR (exactR h) (ih (j+1))

theorem drainF (v : Bool) (k j : Nat) (U R : List Bool) :
    Reach v (F (ones k++U) (zeros j++R)) (F U (zeros (j+k)++R)) := by
  induction k generalizing j with
  | zero => exact reflR _ _
  | succ k ih =>
    have h : hrun (table v) 1 (F (ones (k+1)++U) (zeros j++R)) =
      some (F (ones k++U) (zeros (j+1)++R)) := by rfl
    rw [show j+(k+1)=j+1+k by omega]
    exact joinR (exactR h) (ih (j+1))

theorem finishF (v : Bool) (k : Nat) (U R : List Bool) :
    Reach v (F (ones k++false::U) R) (C U (true::(zeros k++R))) := by
  have h := drainF v k 0 (false::U) R
  simp only [Nat.zero_add] at h
  have g : hrun (table v) 1 (F (false::U) (zeros k++R)) =
      some (C U (true::(zeros k++R))) := by rfl
  exact joinR h (exactR g)

theorem CtoF (v : Bool) (U R : List Bool) :
    hrun (table v) (if v then 2 else 4) (C (true::U) (true::R)) =
      some (F (true::U) (true::R)) := by cases v <;> rfl

theorem Fblock (v : Bool) (U R : List Bool) :
    hrun (table v) 3 (F (true::true::false::U) R) =
      some (C U (true::false::false::R)) := by rfl

theorem FdrainH (v : Bool) (k : Nat) (U R : List Bool) :
    Reach v (F (H k++true::U) (true::R)) (F (true::U) (K k++true::R)) := by
  cases k with
  | zero => exact reflR _ _
  | succ k =>
    have h := Fblock v (H k++true::U) (true::R)
    have g := scanL v k 1 (true::U) R
    rw [show 1+k=k+1 by omega] at g
    have f : Reach v (C (true::U) (K (k+1)++true::R)) (F (true::U) (K (k+1)++true::R)) :=
      exactR (CtoF v U (false::false::(K k++true::R)))
    exact joinR (joinR (exactR h) g) f

theorem zeroF (v : Bool) (U R : List Bool) :
    hrun (table v) 5 (C (false::true::U) (false::R)) =
      some (F (true::U) (true::true::R)) := by rfl

def S (m : Nat) (R : List Bool) : HZ := C [] (K m++R)

theorem prepare0 (v : Bool) (m : Nat) (R : List Bool) :
    Reach v (S (m+1) (false::R)) (S (m+1) (true::true::R)) := by
  have h := scanRempty v m (false::R)
  have g := zeroF v (true::false::H m) R
  have f := Fblock v (H m) (true::true::R)
  have z := scanL v m 1 [] (true::R)
  simp only [List.append_nil] at z
  rw [show 1+m=m+1 by omega] at z
  exact joinR (joinR (joinR h (exactR g)) (exactR f)) z

theorem prepare11 (v : Bool) (m : Nat) (R : List Bool) :
    Reach v (S (m+1) (true::true::R)) (S (m+1) (true::false::true::R)) := by
  have h := scanRempty v m (true::true::R)
  have g : hrun (table v) 5 (C (L (m+1)) (true::true::R)) =
      some (C (H (m+1)) (true::false::true::R)) := by rfl
  have z := scanL v (m+1) 0 [] (false::true::R)
  simp only [Nat.zero_add,List.append_nil] at z
  exact joinR (joinR h (exactR g)) z

theorem prepare101 (v : Bool) (m : Nat) (R : List Bool) :
    Reach v (S (m+1) (true::false::true::R)) (C (ones 3++L (m+1)) R) := by
  have h := scanRempty v m (true::false::true::R)
  have g : hrun (table v) 3 (C (L (m+1)) (true::false::true::R)) =
      some (C (ones 3++L (m+1)) R) := by rfl
  exact joinR h (exactR g)

theorem prepare (v : Bool) (m : Nat) (R : List Bool) :
    Reach v (S (m+1) (false::R)) (C (ones 3++L (m+1)) R) :=
  joinR (joinR (prepare0 v m R) (prepare11 v m R)) (prepare101 v m R)

-- After three initial zeros, the C-head is zero and five 1s precede the old left word.
theorem prefixZeros (v : Bool) (m : Nat) (R : List Bool) :
    hrun (table v) 3 (C (ones 3++L m) (false::false::false::R)) =
      some (C (false::(ones 5++L m)) R) := by rfl

theorem twoZeros (v : Bool) (m : Nat) (R : List Bool) :
    hrun (table v) 3 (C (ones 3++L m) (false::false::true::R)) =
      some (C (ones 6++L m) R) := by rfl

theorem scanOnes (v : Bool) (a k : Nat) (U R : List Bool) :
    Reach v (C (ones (a+1)++U) (J k++R)) (C (ones (a+1+3*k)++U) R) := by
  induction k generalizing a with
  | zero => exact reflR _ _
  | succ k ih =>
    have h : hrun (table v) 3 (C (ones (a+1)++U) (J (k+1)++R)) =
      some (C (ones (a+3+1)++U) (J k++R)) := by rfl
    rw [show a+1+3*(k+1)=a+3+1+3*k by omega]
    exact joinR (exactR h) (ih (a+3))

def P (m : Nat) (ds : List Bool) : HZ := S m (zeros 4++enc ds++[true])

-- The first half of a carry converts k consumed ones into a shifted word.
theorem back5 (v : Bool) (m k : Nat) (R : List Bool) :
    Reach v (F (H k++ones 5++L m) (true::true::R))
      (S (m+1) (zeros 3++K k++true::true::R)) := by
  have h := FdrainH v k (ones 4++L m) (true::R)
  have g := finishF v 5 (H m) (K k++true::true::R)
  have z := scanL v m 0 [] (zeros 5++K k++true::true::R)
  simp only [Nat.zero_add,List.append_nil] at z
  have f := joinR (joinR h g) z
  unfold S
  rw [K_add m 1]
  simpa only [List.append_assoc,ones,zeros,K,List.cons_append,List.nil_append] using f

theorem carry1 (v : Bool) (m k : Nat) (ds : List Bool) :
    Reach v (P (m+1) (ones k++false::ds))
      (S (m+2) (zeros 3++K k++true::true::false::false::enc ds++[true])) := by
  let R := enc ds++[true]
  have h := prepare v m (zeros 3++K k++false::false::false::R)
  have g := prefixZeros v (m+1) (K k++false::false::false::R)
  have z := scanR v 0 k (ones 5++L (m+1)) (false::false::false::R)
  simp only [Nat.zero_add] at z
  have zf : hrun (table v) 5 (C (false::(H k++(ones 5++L (m+1)))) (false::false::false::R)) =
       some (F (H k++ones 5++L (m+1)) (true::true::false::false::R)) := by
    rw [List.append_assoc]
    cases k <;> rfl
  have f := back5 v (m+1) k (false::false::R)
  have res := joinR (joinR (joinR (joinR h (exactR g)) z) (exactR zf)) f
  simpa only [P,enc_append,enc_ones,enc,R,List.append_assoc,zeros,List.cons_append,List.nil_append] using res

-- The second half restores ordinary digits and changes exactly the carried bits.
theorem carry2 (v : Bool) (m k : Nat) (ds : List Bool) :
    Reach v (S (m+1) (zeros 3++K k++true::true::false::false::enc ds++[true]))
      (P (m+2) (zeros k++true::ds)) := by
  let R := false::false::enc ds++[true]
  have h := prepare v m (false::false::(K k++true::true::R))
  have g : Reach v (C (ones 3++L (m+1)) (false::false::(K k++true::true::R)))
      (C (ones 6++L (m+1)) (J k++true::R)) := by
    rw [K_J k (true::R)]
    exact exactR (twoZeros v (m+1) (J k++true::R))
  have z := scanOnes v 5 k (L (m+1)) (true::R)
  have cf : Reach v (C (ones (6+3*k)++L (m+1)) (true::R))
      (F (ones (6+3*k)++L (m+1)) (true::R)) := by
    rw [show 6+3*k=5+3*k+1 by omega]
    exact exactR (CtoF v (ones (5+3*k)++L (m+1)) R)
  have f := finishF v (6+3*k) (H (m+1)) (true::R)
  have ls := scanL v (m+1) 0 [] (zeros (6+3*k)++true::R)
  simp only [Nat.zero_add,List.append_nil] at ls
  have res := joinR (joinR (joinR (joinR (joinR h g) z) cf) f) ls
  unfold P S
  rw [show m+2=m+1+1 by omega,K_add (m+1) 1,enc_append,enc_zeros,enc]
  have eq : zeros (6+3*k) = zeros 2++zeros 4++zeros (3*k) := by
    rw [←zeros_add 2 4,←zeros_add 6 (3*k)]
  rw [eq] at res
  simp only [R,S,List.append_assoc,zeros,K,List.cons_append,List.nil_append] at res ⊢
  exact res

theorem carry (v : Bool) (m k : Nat) (ds : List Bool) :
    Reach v (P (m+1) (ones k++false::ds)) (P (m+3) (zeros k++true::ds)) :=
  joinR (carry1 v m k ds) (carry2 v (m+1) k ds)

-- Enumerate all lower n bits, with an arbitrary unchanged upper suffix.
def walkInc (n : Nat) : Nat := 2*(2^n-1)

theorem walkInc_succ (n : Nat) : walkInc (n+1)=walkInc n+2+walkInc n := by
  unfold walkInc
  rw [Nat.pow_succ]
  have hp : 0 < 2^n := Nat.pow_pos (by decide)
  omega

theorem binaryWalk (v : Bool) (n m : Nat) (tail : List Bool) :
    Reach v (P (m+1) (zeros n++tail)) (P (m+walkInc n+1) (ones n++tail)) := by
  induction n generalizing m tail with
  | zero => exact reflR _ _
  | succ n ih =>
    have h1 := ih m (false::tail)
    have h2 := carry v (m+walkInc n) n tail
    have h3 := ih (m+walkInc n+2) (true::tail)
    have h := joinR (joinR h1 h2) h3
    rw [show zeros (n+1)=zeros n++[false] by rw [zeros_add]; rfl,
      show ones (n+1)=ones n++[true] by rw [ones_add]; rfl,walkInc_succ]
    rw [show m+(walkInc n+2+walkInc n)+1=m+walkInc n+2+walkInc n+1 by omega]
    simpa only [List.append_assoc,List.singleton_append] using h

-- Overflow consumes the final 1 on the right, then creates an extra 110 block.
theorem overflowF (v : Bool) (m k : Nat) :
    hrun (table v) 8 (C (false::(H k++(ones 5++L m))) [true]) =
      some (F (H (k+1)++ones 5++L m) [true,true]) := by
  rw [List.append_assoc]
  cases k <;> rfl

def secA (n b : Nat) : HZ := A (ones (7+3*n)++L b) []

theorem overflow (v : Bool) (m n : Nat) :
    Reach v (P (m+1) (ones n)) (secA (n+1) (m+2)) := by
  have h := prepare v m (zeros 3++K n++[true])
  have g := prefixZeros v (m+1) (K n++[true])
  have z := scanR v 0 n (ones 5++L (m+1)) [true]
  simp only [Nat.zero_add] at z
  have f := overflowF v (m+1) n
  have b := back5 v (m+1) (n+1) []
  have h1 := joinR (joinR (joinR (joinR h (exactR g)) z) (exactR f)) b
  have h2 := prepare v (m+1) (false::false::(K (n+1)++[true,true]))
  have h3 : Reach v (C (ones 3++L (m+2)) (false::false::(K (n+1)++[true,true])))
      (C (ones 6++L (m+2)) (J (n+1)++[true])) := by
    rw [show [true,true]=true::[true] by rfl,K_J]
    exact exactR (twoZeros v (m+2) (J (n+1)++[true]))
  have h4 := scanOnes v 5 (n+1) (L (m+2)) [true]
  have h5 : hrun (table v) 1 (C (ones (6+3*(n+1))++L (m+2)) [true]) =
      some (secA (n+1) (m+2)) := by
    rw [show 6+3*(n+1)=5+3*(n+1)+1 by omega]
    unfold secA
    rw [show 7+3*(n+1)=5+3*(n+1)+2 by omega]
    rfl
  have res := joinR (joinR (joinR (joinR h1 h2) h3) h4) (exactR h5)
  simpa only [P,enc_ones,List.append_assoc,zeros,List.cons_append,List.nil_append] using res

-- Enter the counter with all bits zero from A's secA.
theorem enter (v : Bool) (n b : Nat) :
    ∃ t, 0<t ∧ hrun (table v) t (secA n b) = some (P (b+1) (zeros n)) := by
  have h : hrun (table v) (if v then 1 else 3) (secA n b) =
      some (F (ones (6+3*n)++L b) [true]) := by
    unfold secA
    rw [show 7+3*n=(5+3*n+1)+1 by omega,show 6+3*n=5+3*n+1 by omega]
    cases v <;> rfl
  have g := finishF v (6+3*n) (H b) [true]
  have z := scanL v b 0 [] (zeros (6+3*n)++[true])
  simp only [Nat.zero_add,List.append_nil] at z
  have res := joinR g z
  have res' : Reach v (F (ones (6+3*n)++L b) [true]) (P (b+1) (zeros n)) := by
    unfold P S
    rw [enc_zeros,K_add b 1,←zeros_add 4]
    simp only [K,List.append_assoc]
    have eq : zeros (6+3*n) = zeros 2++zeros (4+3*n) := by
      rw [←zeros_add 2 (4+3*n),show 2+(4+3*n)=6+3*n by omega]
    rw [eq] at res
    simpa only [zeros,List.append_assoc,List.cons_append,List.nil_append,L] using res
  obtain ⟨t,ht⟩ := res'
  exact ⟨(if v then 1 else 3)+t,by cases v <;> simp <;> omega,hjoin h ht⟩

theorem growth (v : Bool) (n b : Nat) :
    ∃ t, 0<t ∧ hrun (table v) t (secA n b) = some (secA (n+1) (b+2^(n+1))) := by
  obtain ⟨t,ht,h⟩ := enter v n b
  have h1 := binaryWalk v n b []
  simp only [List.append_nil] at h1
  obtain ⟨u,hu⟩ := joinR h1 (overflow v (b+walkInc n) n)
  have eq : b+walkInc n+2=b+2^(n+1) := by
    unfold walkInc
    rw [Nat.pow_succ]
    have hp : 0 < 2^n := Nat.pow_pos (by decide)
    omega
  rw [eq] at hu
  exact ⟨t+u,by omega,hjoin h hu⟩

theorem root (v : Bool) :
    hrun (table v) (if v then 101 else 111) (A [] []) = some (secA 0 2) := by cases v <;> rfl

theorem arbitraryLive (v : Bool) (n : Nat) :
    ∃ t a b, n≤t ∧ hrun (table v) t (A [] []) = some (secA a b) := by
  induction n with
  | zero => exact ⟨if v then 101 else 111,0,2,by omega,root v⟩
  | succ n ih =>
    obtain ⟨t,a,b,ht,h⟩ := ih
    obtain ⟨u,hu,g⟩ := growth v a b
    exact ⟨t+u,a+1,b+2^(a+1),by omega,hjoin h g⟩
theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  intro n
  obtain ⟨k,a,b,hk,Hk⟩ := arbitraryLive v n
  obtain ⟨h',H'⟩ := hrun_sound (table v) k _ _ 0 Hk
  have H := zrun_sound (table v) m hm k _ _ H'
  rw [show embed (HZ.at (A [] []) 0) = blank from blank_embed] at H
  rw [show k=n+(k-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some z => rfl
#print axioms never
#print axioms growth
#print axioms arbitraryLive
end BB6.Agent7Raw124ZeroLF1LCCounter

namespace BB6.Agent7Raw124ZeroLF1LCM214
open BB6Coverage
abbrev table : PartialMachine := BB6.Agent7Raw124ZeroLF1LCCounter.table false
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent7Raw124ZeroLF1LCCounter.never false m hm
#print axioms never
end BB6.Agent7Raw124ZeroLF1LCM214

namespace BB6.Agent7Raw124ZeroLF1LCM215
open BB6Coverage
abbrev table : PartialMachine := BB6.Agent7Raw124ZeroLF1LCCounter.table true
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent7Raw124ZeroLF1LCCounter.never true m hm
#print axioms never
end BB6.Agent7Raw124ZeroLF1LCM215
