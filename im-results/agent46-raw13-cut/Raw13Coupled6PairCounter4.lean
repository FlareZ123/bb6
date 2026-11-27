import Agent46CounterCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Auto.PairCounter4
open BB6Coverage Agent31Pump Auto
inductive V where | a | b deriving DecidableEq
def p : V → PartialMachine
  | .a => fun s => match s.1.val,s.2 with
      | 0,false => some (some ⟨true,true,1⟩)
      | 0,true => some (some ⟨true,false,3⟩)
      | 1,false => some (some ⟨true,true,2⟩)
      | 1,true => some (some ⟨false,true,1⟩)
      | 2,false => some (some ⟨true,false,0⟩)
      | 2,true => some (some ⟨true,true,4⟩)
      | 3,false => some (some ⟨true,false,5⟩)
      | 3,true => some (some ⟨false,false,0⟩)
      | 4,false => some (some ⟨false,true,4⟩)
      | 4,true => some (some ⟨true,false,0⟩)
      | 5,false => some (some ⟨true,false,4⟩)
      | 5,true => none
      | _,_ => none
  | .b => fun s => match s.1.val,s.2 with
      | 0,false => some (some ⟨true,true,1⟩)
      | 0,true => some (some ⟨true,false,3⟩)
      | 1,false => some (some ⟨true,true,2⟩)
      | 1,true => some (some ⟨false,true,1⟩)
      | 2,false => some (some ⟨true,false,0⟩)
      | 2,true => some (some ⟨true,true,4⟩)
      | 3,false => some (some ⟨true,false,5⟩)
      | 3,true => some (some ⟨false,false,0⟩)
      | 4,false => some (some ⟨true,true,1⟩)
      | 4,true => some (some ⟨true,false,0⟩)
      | 5,false => some (some ⟨true,false,4⟩)
      | 5,true => none
      | _,_ => none

/-- Two binary digits are stored as b0,0,0,b1; an odd final digit occupies one cell. -/
def enc : List Bool → List Bool
  | [] => []
  | [b] => [b]
  | b::c::xs => b::false::false::c::enc xs

def next (bs : List Bool) : List Bool := Counter.next [true] bs

def r (k : Nat) : List Bool := List.replicate k true ++ [false,true,true]
def A (bs : List Bool) (k : Nat) : Z0 := ⟨0,enc bs,r k⟩
def B (bs : List Bool) (k : Nat) : Z0 := ⟨1,false::(List.replicate k false ++ enc bs),[true,true]⟩

theorem replicate_add (a : Bool) (m n : Nat) : List.replicate (m+n) a = List.replicate m a ++ List.replicate n a := by
  induction m with
  | zero => simp only [Nat.zero_add,List.replicate_zero,List.nil_append]
  | succ m ih =>
    rw [Nat.succ_add, List.replicate_succ, List.replicate_succ, ih]
    rfl

theorem replicate_snoc (k : Nat) (L : List Bool) :
    List.replicate k false ++ false::L = false::(List.replicate k false ++ L) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ,List.cons_append,ih]

theorem bscan (v : V) (k : Nat) (L : List Bool) :
    run0 (p v) (k+1) ⟨1,true::L,r k⟩ = some ⟨1,false::(List.replicate (k+1) false ++ L),[true,true]⟩ := by
  induction k generalizing L with
  | zero => cases v <;> rfl
  | succ k ih =>
    have h : run0 (p v) 1 ⟨1,true::L,r (k+1)⟩ = some ⟨1,true::false::L,r k⟩ := by
      cases v <;> rfl
    have h2 := join0 h (ih (false::L))
    simpa only [Nat.add_comm 1 (k+1),List.replicate_succ,List.cons_append,List.nil_append,replicate_snoc] using h2

theorem finish (v : V) (k : Nat) (L : List Bool) :
    run0 (p v) (k+1) ⟨0,false::L,r k⟩ = some ⟨1,false::(List.replicate k false ++ true::L),[true,true]⟩ := by
  cases k with
  | zero => cases v <;> rfl
  | succ k =>
    have h : run0 (p v) 1 ⟨0,false::L,r (k+1)⟩ = some ⟨1,true::true::L,r k⟩ := by
      cases v <;> rfl
    simpa only [Nat.add_comm 1 (k+1)] using join0 h (bscan v k (true::L))

theorem finish_empty (v : V) (k : Nat) :
    run0 (p v) (k+1) ⟨0,[],r k⟩ = some ⟨1,false::(List.replicate k false ++ [true]),[true,true]⟩ := by
  have h : step0 (p v) ⟨0,[],r k⟩ = step0 (p v) ⟨0,[false],r k⟩ := by cases v <;> rfl
  simpa only [run0,h] using finish v k []

def fc : V → Nat
  | .a => 9
  | .b => 7

theorem finish_pair (v : V) (k : Nat) (L : List Bool) :
    run0 (p v) (k+fc v) ⟨0,true::false::false::false::L,r k⟩ =
      some ⟨1,false::(List.replicate k false ++ false::false::false::true::L),[true,true]⟩ := by
  cases v with
  | a =>
    have h : run0 (p .a) 5 ⟨0,true::false::false::false::L,r k⟩ = some ⟨0,false::L,r (k+3)⟩ := by rfl
    have h2 := join0 h (finish .a (k+3) L)
    simpa only [fc,show 5+(k+3+1)=k+9 by omega, replicate_add, List.append_assoc,List.replicate_succ,List.cons_append,List.nil_append,replicate_snoc] using h2
  | b =>
    have h : run0 (p .b) 4 ⟨0,true::false::false::false::L,r k⟩ = some ⟨1,true::true::L,r (k+2)⟩ := by rfl
    have h2 := join0 h (bscan .b (k+2) (true::L))
    simpa only [fc,show 4+(k+2+1)=k+7 by omega, replicate_add, List.append_assoc,List.replicate_succ,List.cons_append,List.nil_append,replicate_snoc] using h2

theorem finish_single (v : V) (k : Nat) :
    run0 (p v) (k+fc v) ⟨0,[true],r k⟩ = some ⟨1,false::(List.replicate k false ++ [false,false,false,true]),[true,true]⟩ := by
  cases v with
  | a =>
    have h : run0 (p .a) 5 ⟨0,[true],r k⟩ = some ⟨0,[false],r (k+3)⟩ := by rfl
    have h2 := join0 h (finish .a (k+3) [])
    simpa only [fc,show 5+(k+3+1)=k+9 by omega,replicate_add,List.append_assoc,List.replicate_succ,List.cons_append,List.nil_append,replicate_snoc] using h2
  | b =>
    have h : run0 (p .b) 4 ⟨0,[true],r k⟩ = some ⟨1,[true,true],r (k+2)⟩ := by rfl
    have h2 := join0 h (bscan .b (k+2) [true])
    simpa only [fc,show 4+(k+2+1)=k+7 by omega,replicate_add,List.append_assoc,List.replicate_succ,List.cons_append,List.nil_append,replicate_snoc] using h2

theorem carry (v : V) (bs : List Bool) (k : Nat) :
    ∃ n, run0 (p v) n (A bs k) = some (B (next bs) k) := by
  cases bs with
  | nil => exact ⟨k+1,finish_empty v k⟩
  | cons b bs =>
    cases b with
    | false =>
      cases bs with
      | nil => exact ⟨k+1,finish v k []⟩
      | cons c xs => exact ⟨k+1,finish v k (false::false::c::enc xs)⟩
    | true =>
      cases bs with
      | nil => exact ⟨k+fc v,finish_single v k⟩
      | cons c xs =>
        cases c with
        | false => exact ⟨k+fc v,finish_pair v k (enc xs)⟩
        | true =>
          have h : run0 (p v) 4 (A (true::true::xs) k) = some (A xs (k+4)) := by cases v <;> rfl
          obtain ⟨n,hn⟩ := carry v xs (k+4)
          have h2 := join0 h hn
          exact ⟨4+n,by simpa only [B,next,Counter.next,enc,replicate_add,List.append_assoc,List.replicate_succ,List.cons_append,List.nil_append,replicate_snoc] using h2⟩
termination_by bs.length

theorem frame_init (v : V) (bs : List Bool) : run0 (p v) 5 (B bs 0) = some (A bs 0) := by cases v <;> rfl

theorem live (v : V) (bs : List Bool) : ∃ n, 0<n ∧ run0 (p v) n (B bs 0) = some (B (next bs) 0) := by
  obtain ⟨n,h⟩ := carry v bs 0
  exact ⟨5+n,by omega,join0 (frame_init v bs) h⟩

def iter : Nat → List Bool
  | 0 => [true]
  | k+1 => next (iter k)

theorem never (v : V) (m : Machine) (hm : compatible (p v) m) : NeverHalts m := by
  apply never_of_growth (p v) (fun k => B (iter k) 0) 6 (fun k => Classical.choose (live v (iter k))) _ _ _ m hm
  · cases v <;> rfl
  · intro k; exact (Classical.choose_spec (live v (iter k))).1
  · intro k; exact (Classical.choose_spec (live v (iter k))).2
#print axioms never
end BB6Coverage.Agent31Pump.Auto.PairCounter4
