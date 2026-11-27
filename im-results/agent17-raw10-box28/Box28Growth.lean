import Box33BinaryCounter

namespace BB6.Agent17.Box28Growth
open C9Pair
open BB6.Agent13.Box33BinaryCounter (zeros zero_head zero_pop zero_push rep rep_add ones ones_succ)

-- Only six entries are ever needed. An unknown entry is treated as failure.
def step (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .B,false => some (left .C true c)
  | .B,true => some (right .B false c)
  | .C,false => some (left .C true c)
  | .C,true => some (left .D false c)
  | .D,false => some (right .A false c)
  | _,_ => none

def run : Nat → Config → Option Config
  | 0,c => some c
  | n+1,c => (step c).bind (run n)

theorem run_add (m n : Nat) (c : Config) :
    run (m+n) c = (run m c).bind (run n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih =>
    rw [Nat.succ_add]
    simp only [run]
    cases step c <;> simp [ih]

def root (k : Nat) : Config := ⟨.A,zeros,false,ones k⟩
def atB (n : Nat) (l : Stream) : Config :=
  ⟨.B,l,(ones n) 0,pop (ones n)⟩
def atC (n : Nat) (r : Stream) : Config :=
  let l := rep false n (ones 1)
  ⟨.C,pop l,l 0,r⟩

theorem rep_push (b : Bool) (n : Nat) (s : Stream) :
    rep b n (push b s) = rep b (n+1) s := by
  rw [rep_add]
  rfl

theorem b_step (n : Nat) (l : Stream) :
    run 1 (atB (n+1) l) = some (atB n (push false l)) := by
  simp [run,step,atB,right]

theorem b_sweep (n : Nat) (l : Stream) :
    run n (atB n l) = some ⟨.B,rep false n l,false,zeros⟩ := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [show n+1=1+n by omega,run_add,show 1+n=n+1 by omega,b_step,Option.bind_some,ih,rep_push]

theorem c_step (n : Nat) (r : Stream) :
    run 1 (atC (n+1) r) = some (atC n (push true r)) := by
  simp [run,step,atC,left,rep]

theorem c_sweep (n : Nat) (r : Stream) :
    run n (atC n r) = some ⟨.C,zeros,true,rep true n r⟩ := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [show n+1=1+n by omega,run_add,show 1+n=n+1 by omega,c_step,Option.bind_some,ih,rep_push]

theorem enter (n : Nat) : run 1 (root n) = some (atB n (ones 1)) := rfl

theorem turn (n : Nat) :
    run 1 ⟨.B,rep false n (ones 1),false,zeros⟩ = some (atC n (ones 1)) := rfl

theorem finish (n : Nat) :
    run 2 ⟨.C,zeros,true,rep true n (ones 1)⟩ = some (root (n+1)) := by
  simp [run,step,left,right,root,ones,← rep_add]

theorem recur (n : Nat) : run (2*n+4) (root n) = some (root (n+1)) := by
  rw [show 2*n+4 = 1+n+1+n+2 by omega]
  rw [run_add,run_add,run_add,run_add,enter,Option.bind_some,b_sweep,Option.bind_some,
    turn,Option.bind_some,c_sweep,Option.bind_some,finish]

theorem never_root (n k : Nat) : run n (root k) ≠ none := by
  induction n using Nat.strongRecOn generalizing k with
  | ind n ih =>
    intro h
    have hr := recur k
    by_cases hn : n ≤ 2*k+4
    · have e : 2*k+4 = n+(2*k+4-n) := by omega
      rw [e,run_add,h] at hr
      contradiction
    · have e : n = (2*k+4)+(n-(2*k+4)) := by omega
      rw [e,run_add,hr] at h
      exact ih _ (by omega) (k+1) h

theorem never_blank (n : Nat) : run n ⟨.A,zeros,false,zeros⟩ ≠ none := never_root n 0

#print axioms recur
#print axioms never_blank
end BB6.Agent17.Box28Growth
