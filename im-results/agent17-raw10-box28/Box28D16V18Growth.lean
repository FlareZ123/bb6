import C9PairConjugacy

namespace BB6.Agent17.Box28D16V18Growth
open C9Pair
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def zeros : Stream := fun _ => false
@[simp] theorem zero_head : zeros 0 = false := rfl
@[simp] theorem zero_pop : pop zeros = zeros := rfl
@[simp] theorem zero_push : push false zeros = zeros := by
  funext n; cases n <;> rfl
def rep (b : Bool) : Nat → Stream → Stream
  | 0,s => s
  | n+1,s => push b (rep b n s)
theorem rep_push (b : Bool) (n : Nat) (s : Stream) :
    rep b n (push b s) = push b (rep b n s) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,ih]
theorem rep_add (b : Bool) (m n : Nat) (s : Stream) :
    rep b (m+n) s = rep b m (rep b n s) := by
  induction m with
  | zero => simp [rep]
  | succ m ih => simp only [Nat.succ_add,rep,ih]
@[simp] theorem rep_zero (n : Nat) : rep false n zeros = zeros := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,ih,zero_push]
def ones (n : Nat) : Stream := rep true n zeros
def pair (r : Stream) : Stream := push true (push true r)
def atLeft (q : Q) (l r : Stream) : Config := ⟨q,pop l,l 0,r⟩
def atRight (q : Q) (l r : Stream) : Config := ⟨q,l,r 0,pop r⟩
-- k is the excess above two in the first left run.
def root (k : Nat) (r : Stream) : Config := ⟨.E,push false (ones (k+2)),true,r⟩
def mid (k j : Nat) (r : Stream) : Config :=
  ⟨.E,push false (rep true (k+2) (push false (ones j))),true,r⟩
@[simp] theorem mid_zero (k : Nat) (r : Stream) : mid k 0 r = root k r := by
  simp [mid,root,ones,rep]
def step (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (left .A false c)
  | .B,false => some (left .C true c)
  | .B,true => none
  | .C,false => some (left .C true c)
  | .C,true => some (left .D false c)
  | .D,false => some (right .D true c)
  | .D,true => some (right .E false c)
  | .E,false => some (right .C false c)
  | .E,true => some (right .F false c)
  | .F,false => some (left .F true c)
  | .F,true => some (right .A true c)
def run : Nat → Config → Option Config
  | 0,c => some c
  | n+1,c => (step c).bind (run n)
theorem run_add (m n : Nat) (c : Config) : run (m+n) c = (run m c).bind (run n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih =>
    simp only [Nat.succ_add,run]
    cases step c <;> simp [ih]
theorem clear_all (n : Nat) (l r : Stream) :
    run n (atLeft .A (rep true n l) r) =
      some (atLeft .A l (rep false n r)) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [show n+1=1+n by omega,run_add]
    change run n (atLeft .A (rep true n l) (push false r)) = _
    rw [ih,rep_push]
    rfl
theorem fill_all (n : Nat) (l r : Stream) :
    run n (atRight .D l (rep false n r)) =
      some (atRight .D (rep true n l) r) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [show n+1=1+n by omega,run_add]
    change run n (atRight .D (push true l) (rep false n r)) = _
    rw [ih,rep_push]
    rfl
theorem entry (k : Nat) (l r : Stream) :
    run 5 ⟨.E,push false (rep true (k+2) l),true,push false r⟩ =
      some (atLeft .A (rep true (k+3) l) (pair r)) := by
  rfl
theorem reset_finish (k : Nat) (r : Stream) :
    run 17 (atLeft .A zeros (rep false (k+3) (pair r))) =
      some (root 0 (rep false k (pair r))) := by
  simp [atLeft,root,run,step,left,right,rep,ones,pair]
theorem reset (k : Nat) (r : Stream) :
    run (k+25) (root k (push false r)) =
      some (root 0 (rep false k (pair r))) := by
  rw [show k+25=5+(k+3)+17 by omega,run_add,run_add]
  change ((run 5 ⟨.E,push false (rep true (k+2) zeros),true,push false r⟩).bind (run (k+3))).bind (run 17) = _
  rw [entry,Option.bind_some,clear_all,Option.bind_some,reset_finish]
theorem transfer_turn (k j : Nat) (r : Stream) :
    run 6 (atLeft .A (push false (ones (j+1))) (rep false (k+3) (pair r))) =
      some (atRight .D (push false (ones j)) (rep false (k+4) (pair r))) := by
  rfl
theorem transfer_end (k j : Nat) (r : Stream) :
    run 1 (atRight .D (rep true (k+4) (push false (ones j))) (pair r)) =
      some (mid (k+2) j r) := by
  rfl
theorem transfer (k j : Nat) (r : Stream) :
    run (2*k+19) (mid k (j+1) (push false r)) = some (mid (k+2) j r) := by
  rw [show 2*k+19=5+(k+3)+6+(k+4)+1 by omega,run_add,run_add,run_add,run_add]
  change ((((run 5 ⟨.E,push false (rep true (k+2) (push false (ones (j+1)))),true,push false r⟩).bind (run (k+3))).bind (run 6)).bind (run (k+4))).bind (run 1) = _
  rw [entry,Option.bind_some,clear_all,Option.bind_some,transfer_turn,Option.bind_some,
    fill_all,Option.bind_some,transfer_end]
theorem push_pair (k : Nat) (r : Stream) :
    run 21 (root k (pair (push false r))) = some (mid 0 (k+2) r) := by
  simp [root,mid,pair,run,step,left,right,ones,rep]

def Reaches (c d : Config) : Prop := ∃ n, run n c = some d
theorem reaches_trans {c d e : Config} (h : Reaches c d) (h' : Reaches d e) :
    Reaches c e := by
  obtain ⟨n,hn⟩ := h
  obtain ⟨m,hm⟩ := h'
  exact ⟨n+m,by rw [run_add,hn,Option.bind_some,hm]⟩
theorem transfer_all (j k : Nat) (r : Stream) :
    Reaches (mid k j (rep false j r)) (root (k+2*j) r) := by
  induction j generalizing k with
  | zero => exact ⟨0,by simp [run,rep]⟩
  | succ j ih =>
    apply reaches_trans (d := mid (k+2) j (rep false j r))
    · exact ⟨2*k+19,transfer k j (rep false j r)⟩
    · rw [show k+2*(j+1)=(k+2)+2*j by omega]
      exact ih (k+2)
theorem push_all (k : Nat) (r : Stream) :
    Reaches (root k (pair (rep false (k+3) r))) (root (2*k+4) r) := by
  apply reaches_trans (d := mid 0 (k+2) (rep false (k+2) r))
  · exact ⟨21,push_pair k (rep false (k+2) r)⟩
  · rw [show 2*k+4=0+2*(k+2) by omega]
    exact transfer_all (k+2) 0 r
def gap : Nat → Nat
  | 0 => 0
  | n+1 => 2*gap n+4
-- The prefix theorem is uniform in the entire right suffix.
theorem consume_prefix (n : Nat) (r : Stream) :
    Reaches (root 0 (rep false (gap n) r)) (root (gap n) r) := by
  induction n generalizing r with
  | zero => exact ⟨0,rfl⟩
  | succ n ih =>
    rw [gap,show 2*gap n+4=gap n+(gap n+4) by omega,rep_add]
    apply reaches_trans (ih (rep false (gap n+4) r))
    apply reaches_trans (d := root 0 (rep false (gap n) (pair (rep false (gap n+3) r))))
    · exact ⟨gap n+25,reset (gap n) (rep false (gap n+3) r)⟩
    apply reaches_trans (ih (pair (rep false (gap n+3) r)))
    rw [show gap n+(gap n+4)=2*gap n+4 by omega]
    exact push_all (gap n) r
theorem progress (n : Nat) :
    ∃ t, 0<t ∧ run t (root (gap n) zeros) = some (root (gap (n+1)) zeros) := by
  obtain ⟨u,hu⟩ := consume_prefix n (pair zeros)
  have hp := push_all (gap n) zeros
  rw [rep_zero] at hp
  obtain ⟨v,hv⟩ := hp
  refine ⟨(gap n+25)+u+v,by omega,?_⟩
  have hr := reset (gap n) zeros
  rw [zero_push] at hr
  rw [run_add,run_add,hr,Option.bind_some,hu,Option.bind_some,hv]
  rfl
theorem never_root (t n : Nat) : run t (root (gap n) zeros) ≠ none := by
  induction t using Nat.strongRecOn generalizing n with
  | ind t ih =>
    intro h
    obtain ⟨u,hu,hr⟩ := progress n
    by_cases ht : t ≤ u
    · rw [show u=t+(u-t) by omega,run_add,h] at hr
      contradiction
    · rw [show t=u+(t-u) by omega,run_add,hr,Option.bind_some] at h
      exact ih _ (by omega) (n+1) h
def blank : Config := ⟨.A,zeros,false,zeros⟩
theorem init : run 17 blank = some (root (gap 0) zeros) := by
  simp [blank,root,gap,run,step,left,right,ones,rep]
theorem never_blank (t : Nat) : run t blank ≠ none := by
  intro h
  by_cases ht : t ≤ 17
  · have hi := init
    rw [show 17=t+(17-t) by omega,run_add,h] at hi
    contradiction
  · rw [show t=17+(t-17) by omega,run_add,init,Option.bind_some] at h
    exact never_root _ 0 h
#print axioms never_blank
end BB6.Agent17.Box28D16V18Growth
