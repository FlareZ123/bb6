import Box33BinaryCounter

namespace BB6.Agent49.Box27GrowingBlock
open C9Pair
open BB6.Agent13.Box33BinaryCounter (zeros zero_head zero_pop zero_push rep rep_add ones ones_succ)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

-- Unknown E1 and F1 deliberately stop in this sparse model.
def step (c : Config) : Option Config :=
  match c.q, c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (left .A true c)
  | .B,false => some (left .C true c)
  | .B,true => some (right .A false c)
  | .C,_ => some (left .D false c)
  | .D,false => some (right .D false c)
  | .D,true => some (left .E false c)
  | .E,false => some (left .F false c)
  | .E,true => none
  | .F,false => some (left .A true c)
  | .F,true => none

def run : Nat → Config → Option Config
  | 0,c => some c
  | n+1,c => (step c).bind (run n)

theorem run_add (m n : Nat) (c : Config) :
    run (m+n) c = (run m c).bind (run n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih =>
    simp only [Nat.succ_add,run]
    cases step c <;> simp [ih]

def root (k : Nat) : Config :=
  ⟨.D,push false (push false (ones k)),true,zeros⟩

def scan (k : Nat) (r : Stream) : Config :=
  ⟨.A,pop (ones k),(ones k) 0,r⟩

def carry (k : Nat) (l : Stream) : Config := ⟨.B,l,true,ones k⟩

theorem rep_tail (n : Nat) (r : Stream) :
    rep true n (push true r) = rep true (n+1) r := by
  rw [rep_add true n 1 r]
  rfl

theorem open_root (k : Nat) :
    run 3 (root k) = some (scan k (push true zeros)) := by
  simp [root,scan,run,step,left]

theorem scan_step (k : Nat) (r : Stream) :
    step (scan (k+1) r) = some (scan k (push true r)) := by
  simp [scan,step,left]

theorem scan_iter (k : Nat) (r : Stream) :
    run k (scan k r) = some (scan 0 (rep true k r)) := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
    rw [run,scan_step,Option.bind_some,ih,rep_tail]

theorem start_carry (k : Nat) :
    run 1 (scan 0 (ones (k+1))) = some (carry k (ones 1)) := by
  simp [scan,carry,run,step,right,ones,rep]

theorem carry_one (k : Nat) (l : Stream) :
    run 3 (carry (k+1) l) = some (carry k (push true l)) := by
  simp [carry,run,step,right,left]

theorem carry_iter (k : Nat) (l : Stream) :
    run (3*k) (carry k l) = some (carry 0 (rep true k l)) := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih =>
    have h := run_add 3 (3*k) (carry (k+1) l)
    rw [carry_one,Option.bind_some,ih,rep_tail] at h
    simpa only [show 3+3*k = 3*(k+1) by omega] using h

theorem carry_finish (k : Nat) :
    run 6 (carry 0 (ones k)) = some (root k) := by
  simp [carry,root,run,step,right,left,ones,rep]

theorem recur (k : Nat) :
    run (10+4*k) (root k) = some (root (k+1)) := by
  have hs : run (3+k) (root k) = some (scan 0 (ones (k+1))) := by
    rw [run_add,open_root,Option.bind_some,scan_iter,rep_tail]
    rfl
  have hc : run (3+k+1) (root k) = some (carry k (ones 1)) := by
    rw [run_add,hs,Option.bind_some,start_carry]
  have hd : run (3+k+1+3*k) (root k) = some (carry 0 (ones (k+1))) := by
    rw [run_add,hc,Option.bind_some,carry_iter]
    change some (carry 0 (rep true k (push true zeros))) = some (carry 0 (ones (k+1)))
    rw [rep_tail]
    rfl
  have h := run_add (3+k+1+3*k) 6 (root k)
  rw [hd,Option.bind_some,carry_finish] at h
  simpa only [show 3+k+1+3*k+6 = 10+4*k by omega] using h

def blank : Config := ⟨.A,zeros,false,zeros⟩

theorem init : run 5 blank = some (root 0) := by rfl

theorem never_root (n k : Nat) : run n (root k) ≠ none := by
  induction n using Nat.strongRecOn generalizing k with
  | ind n ih =>
    intro h
    have hr := recur k
    by_cases hn : n ≤ 10+4*k
    · rw [show 10+4*k = n+(10+4*k-n) by omega,run_add,h] at hr
      contradiction
    · rw [show n = (10+4*k)+(n-(10+4*k)) by omega,run_add,hr] at h
      exact ih _ (by omega) (k+1) h

theorem never_blank (n : Nat) : run n blank ≠ none := by
  intro h
  by_cases hn : n ≤ 5
  · have hi := init
    rw [show 5=n+(5-n) by omega,run_add,h] at hi
    contradiction
  · rw [show n=5+(n-5) by omega,run_add,init] at h
    exact never_root (n-5) 0 h

#print axioms recur
#print axioms never_blank
end BB6.Agent49.Box27GrowingBlock
