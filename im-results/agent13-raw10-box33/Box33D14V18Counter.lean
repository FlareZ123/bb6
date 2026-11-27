import Box33D14Growth
namespace BB6.Agent13.Box33D14V18Counter
open C9Pair
open BB6.Agent13.Box33D14Growth (z word rep cfg ones rep_add)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def step (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (left .A false c)
  | .B,false => some (left .C true c)
  | .B,true => some (right .F true c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (right .D false c)
  | .D,true => some (right .E false c)
  | .E,false => some (left .A true c)
  | .E,true => none
  | .F,false => some (right .B false c)
  | .F,true => some (right .E false c)

def run : Nat → Config → Option Config
  | 0,c => some c
  | n+1,c => (step c).bind (run n)

theorem run_add (m n : Nat) (c : Config) : run (m+n) c = (run m c).bind (run n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih => rw [Nat.succ_add]; simp only [run]; cases h : step c <;> simp [ih]

def digits : List Bool → Stream
  | [] => z
  | b::bs => word [false,false,false,false,b] (digits bs)
abbrev phase (bs : List Bool) := cfg .A z (digits bs)
abbrev carry (k : Nat) (b : Bool) (r : Stream) := cfg .A (ones (5*k) z) (word [false,true,false,b] r)
abbrev zeros := rep [false]

theorem start (b : Bool) (r : Stream) : run 7 (cfg .A z (word [false,false,false,false,b] r)) = some (carry 0 b r) := by
  simp [cfg,run,step,left,right,ones,rep,word]

theorem advance (k : Nat) (b : Bool) (r : Stream) : run 21 (carry k true (word [false,false,false,false,b] r)) = some (carry (k+1) b r) := by
  unfold carry
  rw [show 5*(k+1)=5+5*k by omega,show ones (5+5*k) z=ones 5 (ones (5*k) z) from rep_add _ _ _ _]
  simp [cfg,run,step,left,right,ones,rep,word]

theorem turn (k : Nat) (r : Stream) : run 5 (carry k false r) = some (cfg .A (ones (5*k+1) z) (word [true,false,true] r)) := by
  simp [cfg,run,step,left,right,ones,rep,word]

theorem clear (n : Nat) (r : Stream) : run (n+1) (cfg .A (ones n z) (push true r)) = some (cfg .A z (zeros (n+2) r)) := by
  induction n generalizing r with
  | zero => simp [cfg,run,step,left,right,ones,zeros,rep,word]
  | succ n ih =>
    rw [show n+1+1=1+(n+1) by omega,run_add]
    have h : run 1 (cfg .A (ones (n+1) z) (push true r)) = some (cfg .A (ones n z) (push true (push false r))) := by simp [cfg,run,step,left,right,ones,rep,word]
    rw [h,Option.bind_some,ih]
    rw [show n+1+2=(n+2)+1 by omega,show zeros ((n+2)+1) r=zeros (n+2) (zeros 1 r) from rep_add _ _ _ _]
    rfl

theorem zero_digits (k : Nat) (bs : List Bool) : digits (List.replicate k false ++ true::bs) = zeros (5*k+4) (push true (digits bs)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ,List.cons_append,digits,ih]
    rw [show 5*(k+1)+4=5+(5*k+4) by omega,show zeros (5+(5*k+4)) (push true (digits bs))=zeros 5 (zeros (5*k+4) (push true (digits bs))) from rep_add _ _ _ _]
    rfl

theorem finish (k : Nat) (bs : List Bool) : run (5*k+7) (carry k false (digits bs)) = some (phase (List.replicate k false ++ true::bs)) := by
  rw [show 5*k+7=5+(5*k+1+1) by omega,run_add,turn,Option.bind_some]
  change run (5*k+1+1) (cfg .A (ones (5*k+1) z) (push true (push false (push true (digits bs))))) = _
  rw [clear]
  unfold phase
  rw [zero_digits,show 5*k+4=(5*k+1+2)+1 by omega,show zeros ((5*k+1+2)+1) (push true (digits bs))=zeros (5*k+1+2) (zeros 1 (push true (digits bs))) from rep_add _ _ _ _]
  rfl

theorem empty_digit : digits [false] = digits [] := by simp [digits,word]

theorem carry_progress (bs : List Bool) (b : Bool) (k : Nat) : ∃ n ds, 0<n ∧ run n (carry k b (digits bs)) = some (phase ds) := by
  induction bs generalizing b k with
  | nil =>
    cases b
    · exact ⟨5*k+7,_,by omega,finish k []⟩
    · refine ⟨21+(5*(k+1)+7),List.replicate (k+1) false ++ [true],by omega,?_⟩
      rw [←empty_digit]
      change run (21+(5*(k+1)+7)) (carry k true (word [false,false,false,false,false] (digits []))) = _
      rw [run_add,advance,Option.bind_some,finish]
  | cons b' bs ih =>
    cases b
    · exact ⟨5*k+7,_,by omega,finish k (b'::bs)⟩
    · obtain ⟨n,ds,hn,he⟩ := ih b' (k+1)
      refine ⟨21+n,ds,by omega,?_⟩
      change run (21+n) (carry k true (word [false,false,false,false,b'] (digits bs))) = _
      rw [run_add,advance,Option.bind_some,he]

theorem progress (bs : List Bool) : ∃ n ds, 0<n ∧ run n (phase bs) = some (phase ds) := by
  cases bs with
  | nil =>
    refine ⟨14,[true],by decide,?_⟩
    rw [show 14=7+7 by decide,run_add]
    have h : run 7 (phase []) = some (carry 0 false (digits [])) := by
      have hz : word [false,false,false,false,false] z = z := by simp [word]
      simpa only [hz,digits,phase] using start false z
    rw [h,Option.bind_some]
    exact finish 0 []
  | cons b bs =>
    obtain ⟨n,ds,hn,he⟩ := carry_progress bs b 0
    refine ⟨7+n,ds,by omega,?_⟩
    rw [run_add,show run 7 (phase (b::bs)) = some (carry 0 b (digits bs)) from start b (digits bs),Option.bind_some,he]

theorem never_phase (n : Nat) (bs : List Bool) : run n (phase bs) ≠ none := by
  induction n using Nat.strongRecOn generalizing bs with
  | ind n ih =>
    intro h
    obtain ⟨m,ds,hm,he⟩ := progress bs
    by_cases hn : n≤m
    · rw [←show n+(m-n)=m by omega,run_add,h] at he; contradiction
    · rw [←show m+(n-m)=n by omega,run_add,he,Option.bind_some] at h
      exact ih _ (by omega) ds h

theorem never_blank (n : Nat) : run n (cfg .A z z) ≠ none := never_phase n []
#print axioms never_blank
end BB6.Agent13.Box33D14V18Counter
