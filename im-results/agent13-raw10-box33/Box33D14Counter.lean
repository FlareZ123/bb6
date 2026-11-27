import Box33D14Growth
namespace BB6.Agent13.Box33D14Counter
open C9Pair
open Box33D14Growth (z word rep cfg ones rep_add rep_succ word_cons word_nil)
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

def step (v : Bool) (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => none
  | .B,false => some (left .C true c)
  | .B,true => some (right .F true c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (right .D false c)
  | .D,true => some (left .E false c)
  | .E,false => some (right .F false c)
  | .E,true => some (left (if v then .E else .C) false c)
  | .F,false => some (left .E true c)
  | .F,true => some (right .A true c)

def run (v : Bool) : Nat → Config → Option Config
  | 0,c => some c
  | n+1,c => (step v c).bind (run v n)

theorem run_add (v : Bool) (m n : Nat) (c : Config) : run v (m+n) c = (run v m c).bind (run v n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih => rw [Nat.succ_add]; simp only [run]; cases h : step v c <;> simp [ih]

abbrev zeros := rep [false,false,false]
def ep : Nat → Stream → Config
  | 0,r => ⟨.E,z,false,r⟩
  | k+1,r => ⟨.E,ones (3*k+2) z,true,r⟩

theorem eraseStep (v : Bool) (k : Nat) (r : Stream) : run v 3 (ep (k+1) r) = some (ep k (zeros 1 r)) := by
  cases k with
  | zero => cases v <;> simp [ep,run,step,left,ones,zeros,rep,word]
  | succ k =>
    have h : 3*(k+1)+2=3+(3*k+2) := by omega
    simp only [ep,h]
    rw [show ones (3+(3*k+2)) z = ones 3 (ones (3*k+2) z) from rep_add _ _ _ _]
    cases v <;> simp [run,step,left,ones,zeros,rep,word]

theorem eraseRun (v : Bool) (k : Nat) (r : Stream) : run v (3*k) (ep k r) = some (ep 0 (zeros k r)) := by
  induction k generalizing r with
  | zero => simp [run]
  | succ k ih =>
    rw [show 3*(k+1)=3+3*k by omega,run_add,eraseStep,Option.bind_some,ih]
    rw [show zeros (k+1) r = zeros k (zeros 1 r) from rep_add _ _ _ _]

theorem commute (k : Nat) (r : Stream) : zeros k (push false r) = push false (zeros k r) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [zeros,rep_succ,word_cons,word_nil,ih]

def phase (k : Nat) (r : Stream) : Config := cfg .A (ones (3*k+1) z) r

theorem begin0 (v : Bool) (k : Nat) (c : Bool) (r : Stream) :
    run v 4 (phase k (word [false,false,c] r)) = some (ep k (word [false,false,true,c] r)) := by
  cases k with
  | zero => simp [phase,cfg,ep,run,step,left,right,ones,rep,word]
  | succ k =>
    unfold phase
    rw [show 3*(k+1)+1=2+(3*k+2) by omega,show ones (2+(3*k+2)) z = ones 2 (ones (3*k+2) z) from rep_add _ _ _ _]
    simp [cfg,ep,run,step,left,right,ones,rep,word]

theorem begin10 (v : Bool) (k : Nat) (r : Stream) :
    run v 3 (phase k (word [false,true,false] r)) = some (ep (k+1) (push true r)) := by
  unfold phase
  simp only [ep]
  rw [show 3*k+2=1+(3*k+1) by omega,show ones (1+(3*k+1)) z = ones 1 (ones (3*k+1) z) from rep_add _ _ _ _]
  simp [cfg,ep,run,step,left,right,ones,rep,word]

theorem finish (v : Bool) (r : Stream) : run v 4 (ep 0 (word [false,false] r)) = some (phase 0 (push false r)) := by
  simp [phase,cfg,ep,run,step,left,right,ones,rep,word]

theorem ret0 (v : Bool) (k : Nat) (c : Bool) (r : Stream) :
    run v (3*k+8) (phase k (word [false,false,c] r)) = some (phase 0 (zeros k (word [false,true,c] r))) := by
  rw [show 3*k+8=4+3*k+4 by omega,run_add,run_add,begin0,Option.bind_some,eraseRun,Option.bind_some]
  simp only [word_cons,word_nil,commute]
  rw [show push false (push false (zeros k (push true (push c r)))) = word [false,false] (zeros k (push true (push c r))) by rfl,finish]

theorem ret10 (v : Bool) (k : Nat) (r : Stream) :
    run v (3*k+10) (phase k (word [false,true,false] r)) = some (phase 0 (zeros k (word [false,false,true] r))) := by
  rw [show 3*k+10=3+3*(k+1)+4 by omega,run_add,run_add,begin10,Option.bind_some,eraseRun,Option.bind_some]
  rw [show zeros (k+1) (push true r)=word [false,false] (push false (zeros k (push true r))) by rfl,finish]
  simp only [word_cons,word_nil,commute]

theorem ret11 (v : Bool) (k : Nat) (r : Stream) :
    run v 3 (phase k (word [false,true,true] r)) = some (phase (k+1) r) := by
  unfold phase
  rw [show 3*(k+1)+1=3+(3*k+1) by omega,show ones (3+(3*k+1)) z = ones 3 (ones (3*k+1) z) from rep_add _ _ _ _]
  simp [cfg,run,step,left,right,ones,rep,word]

def Guard (r : Stream) : Prop := ∀ j : Nat, r (3*j)=false

theorem guard_word (b c : Bool) (r : Stream) (h : Guard r) : Guard (word [false,b,c] r) := by
  intro j; cases j with
  | zero => rfl
  | succ j => rw [show 3*(j+1)=3*j+3 by omega]; exact h j

theorem guard_zeros (k : Nat) (r : Stream) (h : Guard r) : Guard (zeros k r) := by
  induction k with
  | zero => exact h
  | succ k ih => exact guard_word false false _ ih

theorem split (r : Stream) (h : Guard r) : ∃ b c t, Guard t ∧ r=word [false,b,c] t := by
  refine ⟨r 1,r 2,pop (pop (pop r)),?_,?_⟩
  · intro j; change r (3*j+1+1+1)=false; rw [show 3*j+1+1+1=3*(j+1) by omega]; exact h _
  · funext i; cases i with
    | zero => exact h 0
    | succ i => cases i with
      | zero => rfl
      | succ i => cases i <;> rfl

theorem progress (v : Bool) (k : Nat) (r : Stream) (h : Guard r) : ∃ n k' r', 0<n ∧ Guard r' ∧ run v n (phase k r)=some (phase k' r') := by
  obtain ⟨b,c,t,ht,rfl⟩ := split r h
  cases b with
  | false => exact ⟨3*k+8,0,_,by omega,guard_zeros k _ (guard_word true c t ht),ret0 v k c t⟩
  | true => cases c with
    | false => exact ⟨3*k+10,0,_,by omega,guard_zeros k _ (guard_word false true t ht),ret10 v k t⟩
    | true => exact ⟨3,k+1,t,by omega,ht,ret11 v k t⟩

theorem never_phase (v : Bool) (n k : Nat) (r : Stream) (hr : Guard r) : run v n (phase k r) ≠ none := by
  induction n using Nat.strongRecOn generalizing k r with
  | ind n ih =>
    intro h
    obtain ⟨m,k',r',hm,hr',he⟩ := progress v k r hr
    by_cases hn : n≤m
    · rw [←show n+(m-n)=m by omega,run_add,h] at he; contradiction
    · rw [←show m+(n-m)=n by omega,run_add,he,Option.bind_some] at h
      exact ih _ (by omega) k' r' hr' h

def blank : Config := cfg .A z z

theorem init (v : Bool) : run v 10 blank = some (phase 0 z) := by
  cases v <;> simp [blank,phase,cfg,run,step,left,right,ones,rep,word]

theorem never_blank (v : Bool) (n : Nat) : run v n blank ≠ none := by
  intro h
  by_cases hn : n≤10
  · have he := init v; rw [←show n+(10-n)=10 by omega,run_add,h] at he; contradiction
  · rw [←show 10+(n-10)=n by omega,run_add,init,Option.bind_some] at h
    exact never_phase v (n-10) 0 z (fun _ => rfl) h
#print axioms never_blank
end BB6.Agent13.Box33D14Counter
