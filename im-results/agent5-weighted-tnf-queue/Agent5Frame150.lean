import Agent5TailPump
import Agent5MultiPump
import Root56Coverage
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace BB6Coverage.Agent31Pump.Frame150
open BB6Coverage Agent31Pump BB6.Agent13BlankDelay

/-- Equality of finite words when both are extended by infinite zeros. -/
def cell : List Bool → Nat → Bool
  | [], _ => false
  | a::_, 0 => a
  | _::xs, n+1 => cell xs n

def WEq (a b : List Bool) : Prop := ∀ n, cell a n = cell b n

theorem WEq.refl (a : List Bool) : WEq a a := fun _ => rfl
theorem WEq.symm {a b} (h : WEq a b) : WEq b a := fun n => (h n).symm
theorem WEq.trans {a b c} (h : WEq a b) (g : WEq b c) : WEq a c :=
  fun n => (h n).trans (g n)
theorem WEq.cons (v : Bool) {a b} (h : WEq a b) : WEq (v::a) (v::b) := by
  intro n
  cases n with
  | zero => rfl
  | succ n => exact h n
theorem cell_head (a : List Bool) : cell a 0 = a.headD false := by cases a <;> rfl
theorem cell_tail (a : List Bool) (n : Nat) : cell a.tail n = cell a (n+1) := by
  cases a <;> rfl
theorem WEq.head {a b} (h : WEq a b) : a.headD false = b.headD false := by
  simpa only [cell_head] using h 0
theorem WEq.tail {a b} (h : WEq a b) : WEq a.tail b.tail := by
  intro n
  simpa only [cell_tail] using h (n+1)
theorem zeroWord (n : Nat) : WEq (rep [false] n) [] := by
  intro i
  induction n generalizing i with
  | zero => rfl
  | succ n ih => cases i <;> simp [rep,cell,ih]
theorem WEq.pad (a : List Bool) (n : Nat) : WEq (a ++ rep [false] n) a := by
  induction a with
  | nil => exact zeroWord n
  | cons v a ih => exact WEq.cons v ih

structure ZEq (a b : Z0) : Prop where
  state : a.q = b.q
  left : WEq a.l b.l
  right : WEq a.r b.r

theorem ZEq.refl (a : Z0) : ZEq a a := ⟨rfl,WEq.refl _,WEq.refl _⟩
theorem ZEq.symm {a b} (h : ZEq a b) : ZEq b a :=
  ⟨h.state.symm,h.left.symm,h.right.symm⟩
theorem ZEq.trans {a b c} (h : ZEq a b) (g : ZEq b c) : ZEq a c :=
  ⟨h.state.trans g.state,h.left.trans g.left,h.right.trans g.right⟩
theorem moveEq (mv : Move) {a b : Z0} (h : ZEq a b) : ZEq (move0 mv a) (move0 mv b) := by
  cases hd : mv.right with
  | false =>
    simp only [move0,hd,Bool.false_eq_true,ite_false]
    exact ⟨rfl,h.left.tail,WEq.cons _ h.right⟩
  | true =>
    simp only [move0,hd,ite_true]
    have hr := h.right.head
    exact ⟨rfl,by rw [hr]; exact WEq.cons _ (WEq.cons _ h.left.tail),h.right.tail⟩

theorem runEq (p : PartialMachine) (k : Nat) {a b c : Z0}
    (hab : ZEq a b) (h : run0 p k a = some c) :
    ∃ d, run0 p k b = some d ∧ ZEq c d := by
  induction k generalizing a b c with
  | zero =>
    simp [run0] at h
    subst c
    exact ⟨b,rfl,hab⟩
  | succ k ih =>
    have he : (p (a.q,a.l.headD false)).bind id = (p (b.q,b.l.headD false)).bind id := by
      rw [hab.state,hab.left.head]
    cases hm : (p (a.q,a.l.headD false)).bind id with
    | none => simp [run0,step0,hm] at h
    | some mv =>
      have hm' : (p (b.q,b.l.headD false)).bind id = some mv := he.symm.trans hm
      have h' : run0 p k (move0 mv a) = some c := by simpa [run0,step0,hm] using h
      obtain ⟨d,hd,hcd⟩ := ih (moveEq mv hab) h'
      exact ⟨d,by simpa [run0,step0,hm'] using hd,hcd⟩

def RE (p : PartialMachine) (s t : Z0) : Prop :=
  ∃ k u, 0 < k ∧ run0 p k s = some u ∧ ZEq u t

theorem RE.ofRun {p : PartialMachine} {k : Nat} {a b s t : Z0}
    (h : run0 p k a = some b) (hk : 0 < k) (hs : ZEq s a) (ht : ZEq b t) :
    RE p s t := by
  obtain ⟨u,hu,hbu⟩ := runEq p k hs.symm h
  exact ⟨k,u,hk,hu,hbu.symm.trans ht⟩

theorem RE.transport {p s s' t} (h : ZEq s s') (a : RE p s' t) : RE p s t := by
  obtain ⟨k,u,hk,hu,ht⟩ := a
  exact RE.ofRun hu hk h ht
theorem RE.retarget {p s t t'} (a : RE p s t) (h : ZEq t t') : RE p s t' := by
  obtain ⟨k,u,hk,hu,ht⟩ := a
  exact ⟨k,u,hk,hu,ht.trans h⟩

def E (l r : List Bool) : Z0 := ⟨4,true::l,r⟩

inductive LC where
  | blank | one | two | large
  deriving DecidableEq, Repr
inductive RC where
  | one | two | oneEnd | twoEnd
  deriving DecidableEq, Repr

def leftPre : LC → List Bool → List Bool
  | .blank,_ => [false]
  | .one,X => [false,true,true,false] ++ X
  | .two,X => [false,false,true,true,false] ++ X
  | .large,X => [false,false,false] ++ X

def leftPost : LC → List Bool → List Bool
  | .blank,_ => [false]
  | _,X => [false,false] ++ X

def rightPre : RC → List Bool → List Bool
  | .one,Y => [false,true] ++ Y
  | .two,Y => [true,false,true] ++ Y
  | .oneEnd,_ => []
  | .twoEnd,_ => [true]

def rightPost (special : Bool) (c : LC) (d : RC) (Y : List Bool) : List Bool :=
  match d,c with
  | .one,.one => [false,true,false,true] ++ Y
  | .one,.two => [true,true,true,false,true] ++ Y
  | .one,_ => [true,false,true] ++ Y
  | .two,.one => [false,true,true,true,true] ++ Y
  | .two,.two => [true,true,true,true,true,true] ++ Y
  | .two,_ => [true,true,true,true] ++ Y
  | .oneEnd,.one => if special then [false,true,true,true,true] else [false,true]
  | .oneEnd,.two => if special then [true,true,true,true,true,true] else [true,true,true]
  | .oneEnd,_ => if special then [true,true,true,true] else [true]
  | .twoEnd,.one => [false,true,true,true]
  | .twoEnd,.two => [true,true,true,true,true]
  | .twoEnd,_ => [true,true,true]

structure Rules (p : PartialMachine) (special : Bool) where
  big : ∀ L R, RE p (E L ([true,true,true] ++ R)) (E ([false,true,true] ++ L) R)
  small : ∀ c d X Y, RE p (E (leftPre c X) (rightPre d Y))
    (E (leftPost c X) (rightPost special c d Y))

/-- Each frame stores m-1, rather than the positive zero-run length m. -/
def leftWord : List Nat → List Bool
  | [] => [false]
  | a::xs => rep [false] (a+1) ++ [true,true] ++ leftWord xs

def debt : List Nat → Nat
  | [] => 0
  | a::xs => a + debt xs

def bump : List Nat → List Nat
  | [] => []
  | a::xs => (a+1)::xs

def lclass : List Nat → LC
  | [] => .blank
  | 0::_ => .one
  | 1::_ => .two
  | (_+2)::_ => .large

def leftAfter : List Nat → List Nat
  | [] => []
  | 0::xs => bump xs
  | 1::xs => bump xs
  | (a+2)::xs => (a+1)::xs

theorem debt_bump (xs : List Nat) : debt (bump xs) ≤ debt xs + 1 := by
  cases xs <;> simp [bump,debt] <;> omega

theorem leftHead (xs : List Nat) : leftWord xs = false :: (leftWord xs).tail := by
  cases xs <;> rfl

theorem leftBump (xs : List Nat) : WEq (false::leftWord xs) (leftWord (bump xs)) := by
  cases xs with
  | nil => exact WEq.pad [false] 1
  | cons a xs => exact WEq.refl _

theorem leftCut (xs : List Nat) :
    ∃ X, leftWord xs = leftPre (lclass xs) X ∧
      WEq (leftPost (lclass xs) X) (leftWord (leftAfter xs)) := by
  cases xs with
  | nil => exact ⟨[],rfl,WEq.refl _⟩
  | cons a xs =>
    cases a with
    | zero =>
      refine ⟨(leftWord xs).tail, ?_, ?_⟩
      · change false::true::true::leftWord xs = false::true::true::false::(leftWord xs).tail
        rw [← leftHead xs]
      · change WEq (false::false::(leftWord xs).tail) (leftWord (bump xs))
        rw [← leftHead xs]
        exact leftBump xs
    | succ a =>
      cases a with
      | zero =>
        refine ⟨(leftWord xs).tail, ?_, ?_⟩
        · change false::false::true::true::leftWord xs = false::false::true::true::false::(leftWord xs).tail
          rw [← leftHead xs]
        · change WEq (false::false::(leftWord xs).tail) (leftWord (bump xs))
          rw [← leftHead xs]
          exact leftBump xs
      | succ a =>
        refine ⟨rep [false] a ++ [true,true] ++ leftWord xs, ?_, ?_⟩
        · simp [leftWord,leftPre,lclass,rep,List.append_assoc]
        · simpa [leftWord,leftAfter,leftPost,lclass,rep,List.append_assoc] using
            WEq.refl (leftWord ((a+1)::xs))

def triples (n : Nat) : List Bool := rep [true,true,true] n

def runs : List Nat → Option Nat → List Bool
  | [],none => []
  | [],some a => [false,true,true,true] ++ triples a
  | a::xs,z => [false,true] ++ triples a ++ runs xs z

structure Right where
  n : Nat
  b : Bool
  good : List Nat
  last : Option Nat
  deriving Repr

def rightWord (r : Right) : List Bool :=
  (if r.b then [true] else []) ++ triples r.n ++ runs r.good r.last

def capacity (r : Right) : Nat := r.good.length + if r.b then 0 else 1

def endFlag : List Nat → Option Nat → Bool
  | [],none => true
  | _,_ => false

def rightAfter (special : Bool) (c : LC) (b : Bool) (g : List Nat) (z : Option Nat) : Right :=
  if b then
    match c,g,z with
    | .one,a::xs,z => ⟨0,false,(a+1)::xs,z⟩
    | .one,[],some a => ⟨0,false,[],some (a+1)⟩
    | .one,[],none => ⟨0,false,[],some 0⟩
    | .two,a::xs,z => ⟨a+2,false,xs,z⟩
    | .two,[],_ => ⟨0,false,[],none⟩ -- unreachable by capacity
    | _,a::xs,z => ⟨a+1,true,xs,z⟩
    | _,[],some a => ⟨a+2,false,[],none⟩
    | _,[],none => ⟨1,false,[],none⟩
  else
    let e := special && endFlag g z
    match c with
    | .one => ⟨0,false,(if e then 1 else 0)::g,z⟩
    | .two => ⟨if e then 2 else 1,false,g,z⟩
    | _ => ⟨if e then 1 else 0,true,g,z⟩

theorem cap_one (sp b : Bool) (g : List Nat) (z : Option Nat) :
    capacity (rightAfter sp .one b g z) = capacity ⟨0,b,g,z⟩+1 := by
  cases b <;> cases g <;> cases z <;> cases sp <;>
    simp [rightAfter,endFlag,capacity] <;> omega

theorem cap_two (sp b : Bool) (g : List Nat) (z : Option Nat)
    (h : 1 ≤ capacity ⟨0,b,g,z⟩) :
    capacity (rightAfter sp .two b g z) = capacity ⟨0,b,g,z⟩ := by
  cases b <;> cases g <;> cases z <;> cases sp <;>
    simp [rightAfter,endFlag,capacity] at * <;> omega

theorem cap_large (sp b : Bool) (g : List Nat) (z : Option Nat)
    (h : 2 ≤ capacity ⟨0,b,g,z⟩) :
    capacity (rightAfter sp .large b g z)+1 = capacity ⟨0,b,g,z⟩ := by
  cases b <;> cases g <;> cases z <;> cases sp <;>
    simp [rightAfter,endFlag,capacity] at * <;> omega

theorem twoOK (L : List Nat) (b : Bool) (g : List Nat) (z : Option Nat)
    (h : debt L ≤ capacity ⟨0,b,g,z⟩) (hc : lclass L = .two) :
    1 ≤ capacity ⟨0,b,g,z⟩ := by
  cases L with
  | nil => simp [lclass] at hc
  | cons a xs =>
    cases a with
    | zero => simp [lclass] at hc
    | succ a =>
      cases a with
      | zero => simp only [debt] at h; omega
      | succ a => simp [lclass] at hc

theorem smallSafe (sp b : Bool) (g : List Nat) (z : Option Nat) (L : List Nat)
    (h : debt L ≤ capacity ⟨0,b,g,z⟩) :
    debt (leftAfter L) ≤ capacity (rightAfter sp (lclass L) b g z) := by
  cases L with
  | nil => exact Nat.zero_le _
  | cons a xs =>
    cases a with
    | zero =>
      change debt (bump xs) ≤ capacity (rightAfter sp .one b g z)
      rw [cap_one]
      have hd := debt_bump xs
      simp only [debt,Nat.zero_add] at h
      omega
    | succ a =>
      cases a with
      | zero =>
        have hc : 1 ≤ capacity ⟨0,b,g,z⟩ := by simp only [debt] at h; omega
        change debt (bump xs) ≤ capacity (rightAfter sp .two b g z)
        rw [cap_two sp b g z hc]
        have hd := debt_bump xs
        simp only [debt] at h
        omega
      | succ a =>
        have hc : 2 ≤ capacity ⟨0,b,g,z⟩ := by simp only [debt] at h; omega
        have hh := cap_large sp b g z hc
        change debt ((a+1)::xs) ≤ capacity (rightAfter sp .large b g z)
        simp only [debt] at h ⊢
        omega

theorem rightCut (sp : Bool) (c : LC) (b : Bool) (g : List Nat) (z : Option Nat)
    (hc : c = .two → 1 ≤ capacity ⟨0,b,g,z⟩) :
    ∃ d Y, rightWord ⟨0,b,g,z⟩ = rightPre d Y ∧
      rightPost sp c d Y = rightWord (rightAfter sp c b g z) := by
  cases g with
  | nil =>
    cases z with
    | none =>
      cases b with
      | false =>
        cases c <;> cases sp <;> exact ⟨.oneEnd,[],rfl,by simp [rightWord,rightPre,rightPost,rightAfter,endFlag,runs,triples,rep,List.append_assoc]⟩
      | true =>
        cases c with
        | two => have h := hc rfl; simp [capacity] at h
        | blank => exact ⟨.twoEnd,[],rfl,by simp [rightWord,rightPre,rightPost,rightAfter,endFlag,runs,triples,rep,List.append_assoc]⟩
        | one => exact ⟨.twoEnd,[],rfl,by simp [rightWord,rightPre,rightPost,rightAfter,endFlag,runs,triples,rep,List.append_assoc]⟩
        | large => exact ⟨.twoEnd,[],rfl,by simp [rightWord,rightPre,rightPost,rightAfter,endFlag,runs,triples,rep,List.append_assoc]⟩
    | some a =>
      cases b with
      | false =>
        cases c <;> cases sp <;>
          exact ⟨.one,[true,true] ++ triples a,rfl,rfl⟩
      | true =>
        cases c with
        | two => have h := hc rfl; simp [capacity] at h
        | blank => exact ⟨.two,[true,true] ++ triples a,rfl,rfl⟩
        | one => exact ⟨.two,[true,true] ++ triples a,rfl,rfl⟩
        | large => exact ⟨.two,[true,true] ++ triples a,rfl,rfl⟩
  | cons a xs =>
    cases b with
    | false =>
      cases c <;> cases sp <;>
        exact ⟨.one,triples a ++ runs xs z,rfl,by simp [rightWord,rightPre,rightPost,rightAfter,endFlag,runs,triples,rep,List.append_assoc]⟩
    | true =>
      cases c <;>
        exact ⟨.two,triples a ++ runs xs z,rfl,by simp [rightWord,rightPre,rightPost,rightAfter,endFlag,runs,triples,rep,List.append_assoc]⟩

def region (s : Z0) : Prop :=
  ∃ L r, debt L ≤ capacity r ∧ ZEq s (E (leftWord L) (rightWord r))

theorem closed {p sp} (rules : Rules p sp) (s : Z0) (hs : region s) :
    ∃ k t, 0 < k ∧ region t ∧ run0 p k s = some t := by
  obtain ⟨L,⟨n,b,g,z⟩,h,he⟩ := hs
  cases n with
  | succ n =>
    have hr : rightWord ⟨n+1,b,g,z⟩ = [true,true,true] ++ rightWord ⟨n,b,g,z⟩ := by
      cases b <;> rfl
    have hl : leftWord (0::L) = [false,true,true] ++ leftWord L := rfl
    have hh := rules.big (leftWord L) (rightWord ⟨n,b,g,z⟩)
    rw [← hr,← hl] at hh
    obtain ⟨k,t,hk,ht,he'⟩ := hh.transport he
    exact ⟨k,t,hk,⟨0::L,⟨n,b,g,z⟩,by simpa [debt,capacity] using h,he'⟩,ht⟩
  | zero =>
    obtain ⟨X,hX,hX'⟩ := leftCut L
    obtain ⟨d,Y,hY,hY'⟩ := rightCut sp (lclass L) b g z (twoOK L b g z h)
    have hh := rules.small (lclass L) d X Y
    rw [← hX,← hY,hY'] at hh
    have hz : ZEq (E (leftPost (lclass L) X) (rightWord (rightAfter sp (lclass L) b g z)))
        (E (leftWord (leftAfter L)) (rightWord (rightAfter sp (lclass L) b g z))) :=
      ⟨rfl,WEq.cons true hX',WEq.refl _⟩
    obtain ⟨k,t,hk,ht,he'⟩ := (hh.retarget hz).transport he
    exact ⟨k,t,hk,⟨leftAfter L,rightAfter sp (lclass L) b g z,smallSafe sp b g z L h,he'⟩,ht⟩

theorem never {p sp} (rules : Rules p sp)
    (entry : run0 p 7 ⟨0,[],[]⟩ = some ⟨4,[true,false,false],[false]⟩)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply Multi.never_of_region p region 7 ⟨4,[true,false,false],[false]⟩ entry _ (closed rules) m hm
  exact ⟨[],⟨0,false,[],none⟩,by decide,⟨rfl,WEq.pad [true,false] 1,WEq.pad [] 1⟩⟩

#print axioms never
end BB6Coverage.Agent31Pump.Frame150
