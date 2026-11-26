import C9PairConjugacy

namespace BB6.Agent13.Box33BinaryCounter
open C9Pair
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def step (c : Config) : Option Config :=
  match c.q, c.a with
  | .A, false => some (right .B true c)
  | .A, true => some (right .E true c)
  | .B, false => some (left .C true c)
  | .B, true => some (left .D false c)
  | .C, false => some (left .A false c)
  | .C, true => some (left .D false c)
  | .D, false => some (right .A false c)
  | .D, true => some (left .F true c)
  | .E, false => some (right .A true c)
  | .E, true => none
  | .F, false => some (right .A false c)
  | .F, true => some (left .F false c)

def run : Nat → Config → Option Config
  | 0, c => some c
  | n+1, c => (step c).bind (run n)

theorem run_add (m n : Nat) (c : Config) :
    run (m+n) c = (run m c).bind (run n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih =>
    rw [Nat.succ_add]; simp only [run]
    cases h : step c <;> simp [ih]

def zeros : Stream := fun _ => false
@[simp] theorem zero_head : zeros 0 = false := rfl
@[simp] theorem zero_pop : pop zeros = zeros := rfl
@[simp] theorem zero_push : push false zeros = zeros := by funext n; cases n <;> rfl

def rep (b : Bool) : Nat → Stream → Stream
  | 0,s => s
  | n+1,s => push b (rep b n s)

theorem rep_add (b : Bool) (m n : Nat) (s : Stream) :
    rep b (m+n) s = rep b m (rep b n s) := by
  induction m with
  | zero => simp [rep]
  | succ m ih => rw [Nat.succ_add, rep, rep, ih]

def ones (n : Nat) : Stream := rep true n zeros
@[simp] theorem ones_succ (n : Nat) : ones (n+1) = push true (ones n) := rfl

def atA (l r : Stream) : Config := ⟨.A,l,r 0,pop r⟩

def pair (a b : Bool) (s : Stream) : Stream := push a (push b s)
inductive Digit where | zero | one | two deriving DecidableEq, Repr

def encode : List Digit → Stream
  | [] => zeros
  | .zero :: ds => pair false false (encode ds)
  | .one :: ds => pair true false (encode ds)
  | .two :: ds => pair false true (encode ds)

theorem encode_zeroes (k : Nat) (ds : List Digit) :
    encode (List.replicate k .zero ++ ds) = rep false (2*k) (encode ds) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, encode, ih]
    rw [show 2*(k+1) = 2*k+2 by omega]
    rfl

def root (b : Bool) (ds : List Digit) : Config := ⟨.A,zeros,false,push b (encode ds)⟩

theorem clearF (n : Nat) (r : Stream) :
    run (n+2) ⟨.F,ones n,true,r⟩ = some ⟨.A,zeros,false,rep false n r⟩ := by
  induction n generalizing r with
  | zero => simp [run,step,right,left,ones,rep]
  | succ n ih =>
    rw [show n+1+2 = (n+2)+1 by omega,run]
    simp only [step,left,ones_succ,pop_push,push_zero,Option.bind_some]
    rw [ih,rep_add false n 1 r]
    rfl

theorem carry (k : Nat) (s : Stream) :
    run 2 (atA (ones (2*k+2)) (pair true false s)) =
      some (atA (ones (2*(k+1)+2)) s) := by
  rw [show 2*(k+1)+2 = 2*k+2+1+1 by omega]
  simp [run,step,right,atA,pair]

theorem stopZero (k : Nat) (s : Stream) :
    run 4 (atA (ones (2*k+2)) (pair false false s)) =
      some ⟨.F,ones (2*k),true,push true (push false (push true s))⟩ := by
  rw [show 2*k+2 = 2*k+1+1 by omega]
  simp [run,step,right,left,atA,pair]

theorem stopTwo (k : Nat) (s : Stream) :
    run 3 (atA (ones (2*k+2)) (pair false true s)) =
      some ⟨.F,ones (2*k+1),true,push true (push false s)⟩ := by
  rw [show 2*k+2 = 2*k+1+1 by omega]
  simp [run,step,right,left,atA,pair]

theorem zeroReturn (k : Nat) (ds : List Digit) :
    ∃ n b ds', 0 < n ∧ run n (atA (ones (2*k+2)) (pair false false (encode ds))) = some (root b ds') := by
  have h := run_add 4 (2*k+2) (atA (ones (2*k+2)) (pair false false (encode ds)))
  rw [stopZero,Option.bind_some,clearF] at h
  cases k with
  | zero => exact ⟨6,true,.two::ds,by decide,h⟩
  | succ k =>
    refine ⟨4+(2*(k+1)+2),false,List.replicate k .zero ++ .two :: .two :: ds,by omega,?_⟩
    rw [h,root,encode_zeroes]
    simp only [encode,pair]
    rw [show 2*(k+1) = 1+(2*k+1) by omega,rep_add]
    rw [show 2*k+1 = 2*k+1 by rfl,rep_add]
    rfl

theorem twoReturn (k : Nat) (ds : List Digit) :
    ∃ n b ds', 0 < n ∧ run n (atA (ones (2*k+2)) (pair false true (encode ds))) = some (root b ds') := by
  refine ⟨3+(2*k+1+2),false,List.replicate k .zero ++ .one :: ds,by omega,?_⟩
  rw [run_add,stopTwo,Option.bind_some,clearF,root,encode_zeroes]
  simp only [encode,pair]
  rw [show 2*k+1 = 1+2*k by omega,rep_add]
  rfl

theorem walk (ds : List Digit) (k : Nat) :
    ∃ n b ds', 0 < n ∧ run n (atA (ones (2*k+2)) (encode ds)) = some (root b ds') := by
  induction ds generalizing k with
  | nil =>
    have h := zeroReturn k []
    simpa [encode,pair] using h
  | cons d ds ih =>
    cases d with
    | zero => exact zeroReturn k ds
    | two => exact twoReturn k ds
    | one =>
      obtain ⟨n,b,ds',hn,hr⟩ := ih (k+1)
      refine ⟨2+n,b,ds',by omega,?_⟩
      rw [encode,run_add,carry,Option.bind_some,hr]

theorem rootFalse (ds : List Digit) : run 4 (root false ds) = some (root true ds) := by
  simp [root,run,step,right,left]

theorem rootTrue (ds : List Digit) : run 6 (root true ds) = some (atA (ones 2) (encode ds)) := by
  simp [root,run,step,right,left,atA,ones,rep]

theorem progress (b : Bool) (ds : List Digit) :
    ∃ n b' ds', 0 < n ∧ run n (root b ds) = some (root b' ds') := by
  cases b with
  | false => exact ⟨4,true,ds,by decide,rootFalse ds⟩
  | true =>
    obtain ⟨n,b',ds',hn,hr⟩ := walk ds 0
    refine ⟨6+n,b',ds',by omega,?_⟩
    rw [run_add,rootTrue,Option.bind_some]
    exact hr

theorem never_root (n : Nat) (b : Bool) (ds : List Digit) : run n (root b ds) ≠ none := by
  induction n using Nat.strongRecOn generalizing b ds with
  | ind n ih =>
    intro h
    obtain ⟨k,b',ds',hk,hr⟩ := progress b ds
    by_cases hnk : n ≤ k
    · have he : n+(k-n) = k := by omega
      rw [←he,run_add,h] at hr
      contradiction
    · have he : k+(n-k) = n := by omega
      rw [←he,run_add,hr,Option.bind_some] at h
      exact ih (n-k) (by omega) b' ds' h

theorem never_blank (n : Nat) : run n ⟨.A,zeros,false,zeros⟩ ≠ none := by
  simpa [root,encode] using never_root n false []

#print axioms never_blank
end BB6.Agent13.Box33BinaryCounter
