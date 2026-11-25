import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent43Raw122Counter
open BB6Coverage BB6Coverage.Agent31Pump

/-- Nonhalting from a positive-progress invariant, with no uniform bound on the return time. -/
theorem never_of_invariant (p : PartialMachine) (I : Z0 → Prop) (initial : Z0) (entry : Nat)
    (first : run0 p entry ⟨0,[],[]⟩ = some initial) (init : I initial)
    (advance : ∀ c, I c → ∃ k d, 0 < k ∧ run0 p k c = some d ∧ I d)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  classical
  let S := {c : Z0 // I c}
  have step : ∀ s : S, ∃ k : Nat, ∃ d : S, 0 < k ∧ run0 p k s.val = some d.val := by
    intro s
    obtain ⟨k,d,hk,h,hd⟩ := advance s.val s.property
    exact ⟨k,⟨d,hd⟩,hk,h⟩
  let k : S → Nat := fun s => Classical.choose (step s)
  let d : S → S := fun s => Classical.choose (Classical.choose_spec (step s))
  have hstep (s : S) : 0 < k s ∧ run0 p (k s) s.val = some (d s).val := Classical.choose_spec (Classical.choose_spec (step s))
  let seq : Nat → S := Nat.rec ⟨initial,init⟩ (fun _ s => d s)
  apply never_of_growth p (fun n => (seq n).val) entry (fun n => k (seq n)) first _ _ m hm
  · intro n; exact (hstep (seq n)).1
  · intro n; exact (hstep (seq n)).2

-- C1 = 1RC (false) or 1RD (true).
def table (variant : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,if variant then 3 else 2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def pair : List Bool := [true,false]
def block : List Bool := [true,false,true,false]
def zero : List Bool := [false,false,false,false]
def one : List Bool := [false,false,false,true]
def ending : List Bool := [true,true,true,false]
def bits : List Bool → List Bool
  | [] => []
  | b::bs => (if b then one else zero) ++ bits bs

def left (v : Bool) (n : Nat) : List Bool :=
  [false,false] ++ rep block n ++ (if v then pair else []) ++ ending

def scan (v : Bool) (n : Nat) : List Bool :=
  (if v then block else pair) ++ rep block n ++ ending

def config (v : Bool) (n : Nat) (bs : List Bool) : Z0 := ⟨3,left v n,bits bs⟩

theorem pair_comm (n : Nat) : pair ++ rep block n = rep block n ++ pair := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rep, List.append_assoc, ← ih, ← List.append_assoc, ← List.append_assoc]
    rfl

-- A consumes a whole 1010 block and pushes a 0000 block.
theorem sweep_local (v : Bool) (L R : List Bool) :
    run0 (table v) 8 ⟨0,[false] ++ block ++ L,[true] ++ R⟩ =
      some ⟨0,[false] ++ L,[true] ++ zero ++ R⟩ := by cases v <;> rfl

theorem enter_sweep (v : Bool) (n : Nat) (R : List Bool) :
    run0 (table v) 9 ⟨3,left v (n+1),R⟩ =
      some ⟨0,[false] ++ rep block n ++ (if v then pair else []) ++ ending,[true,false,false,false,true] ++ R⟩ := by
  cases v <;> rfl

theorem sweep_blocks (v : Bool) (n : Nat) (R : List Bool) :
    run0 (table v) (8*n) ⟨0,[false] ++ rep block n ++ (if v then pair else []) ++ ending,[true,false,false,false,true] ++ R⟩ =
      some ⟨0,[false] ++ (if v then pair else []) ++ ending,[true] ++ rep zero n ++ one ++ R⟩ := by
  simpa only [one,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using
    sweepL (table v) 0 [false] [true] block zero 8 (sweep_local v) n ((if v then pair else []) ++ ending) (one ++ R)

theorem finish_sweep0 (n : Nat) (R : List Bool) :
    run0 (table false) 11 ⟨0,[false] ++ [] ++ ending,[true] ++ rep zero n ++ one ++ R⟩ =
      some ⟨3,left false 0,rep zero n ++ one ++ R⟩ := by
  cases n <;> rfl

theorem finish_sweep1 (n : Nat) (R : List Bool) :
    run0 (table true) 17 ⟨0,[false] ++ pair ++ ending,[true] ++ rep zero n ++ one ++ R⟩ =
      some ⟨3,left true 0,rep zero n ++ one ++ R⟩ := by
  cases n <;> rfl

theorem encode_zeros (n : Nat) (bs : List Bool) :
    bits (List.replicate n false ++ true::bs) = rep zero n ++ one ++ bits bs := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ]; simp only [List.cons_append,bits,Bool.false_eq_true,ite_false,ih,rep,List.append_assoc]

theorem push_blocks (v : Bool) (n : Nat) (bs : List Bool) :
    run0 (table v) (9+8*n+(if v then 17 else 11)) (config v (n+1) bs) =
      some (config v 0 (List.replicate n false ++ true::bs)) := by
  unfold config
  rw [encode_zeros]
  cases v
  · exact join0 (join0 (enter_sweep false n _) (sweep_blocks false n _)) (finish_sweep0 n _)
  · exact join0 (join0 (enter_sweep true n _) (sweep_blocks true n _)) (finish_sweep1 n _)

-- D scans a 0001 block, converting it to another alternating block on the left.
theorem start_scan (v : Bool) (R : List Bool) :
    run0 (table v) (if v then 18 else 12) ⟨3,left v 0,R⟩ = some ⟨3,scan v 0,R⟩ := by cases v <;> rfl

theorem scan_one (v : Bool) (n : Nat) (R : List Bool) :
    run0 (table v) 4 ⟨3,scan v n,one ++ R⟩ = some ⟨3,scan v (n+1),R⟩ := by cases v <;> rfl

theorem scan_zero (v : Bool) (n : Nat) (R : List Bool) :
    run0 (table v) 4 ⟨3,scan v n,zero ++ R⟩ = some ⟨3,left v (n+1),R⟩ := by
  cases v
  · simp only [scan,left,ite_false,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil]
    rfl
  · simp only [scan,left,ite_true,rep,List.append_assoc]
    rw [← List.append_assoc (rep block n) pair ending, ← pair_comm n]
    rfl

theorem scan_nil (v : Bool) (n : Nat) :
    run0 (table v) 4 ⟨3,scan v n,[]⟩ = some ⟨3,left v (n+1),[]⟩ := by
  cases v
  · simp only [scan,left,ite_false,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil]
    rfl
  · simp only [scan,left,ite_true,rep,List.append_assoc]
    rw [← List.append_assoc (rep block n) pair ending, ← pair_comm n]
    rfl

theorem scan_progress (v : Bool) (bs : List Bool) (n : Nat) :
    ∃ k j cs, 0 < k ∧ run0 (table v) k ⟨3,scan v n,bits bs⟩ = some (config v j cs) := by
  induction bs generalizing n with
  | nil => exact ⟨4,n+1,[],by decide,scan_nil v n⟩
  | cons b bs ih =>
    cases b
    · exact ⟨4,n+1,bs,by decide,scan_zero v n (bits bs)⟩
    · obtain ⟨k,j,cs,hk,h⟩ := ih (n+1)
      exact ⟨4+k,j,cs,by omega,join0 (scan_one v n (bits bs)) h⟩

theorem advance (v : Bool) (n : Nat) (bs : List Bool) :
    ∃ k j cs, 0 < k ∧ run0 (table v) k (config v n bs) = some (config v j cs) := by
  cases n with
  | zero =>
    obtain ⟨k,j,cs,hk,h⟩ := scan_progress v bs 0
    exact ⟨(if v then 18 else 12)+k,j,cs,by omega,join0 (start_scan v (bits bs)) h⟩
  | succ n => exact ⟨9+8*n+(if v then 17 else 11),0,List.replicate n false ++ true::bs,by omega,push_blocks v n bs⟩

theorem entry0 : run0 (table false) 57 ⟨0,[],[]⟩ = some (config false 2 []) := by rfl
theorem entry1 : run0 (table true) 39 ⟨0,[],[]⟩ = some (config true 1 []) := by rfl

theorem never0 (m : Machine) (hm : compatible (table false) m) : NeverHalts m := by
  apply never_of_invariant (table false) (fun c => ∃ n bs, c = config false n bs) (config false 2 []) 57 entry0 ⟨2,[],rfl⟩ _ m hm
  rintro _ ⟨n,bs,rfl⟩
  obtain ⟨k,j,cs,hk,h⟩ := advance false n bs
  exact ⟨k,config false j cs,hk,h,⟨j,cs,rfl⟩⟩

theorem never1 (m : Machine) (hm : compatible (table true) m) : NeverHalts m := by
  apply never_of_invariant (table true) (fun c => ∃ n bs, c = config true n bs) (config true 1 []) 39 entry1 ⟨1,[],rfl⟩ _ m hm
  rintro _ ⟨n,bs,rfl⟩
  obtain ⟨k,j,cs,hk,h⟩ := advance true n bs
  exact ⟨k,config true j cs,hk,h,⟨j,cs,rfl⟩⟩
#print axioms never0
#print axioms never1
end BB6Coverage.Agent43Raw122Counter
