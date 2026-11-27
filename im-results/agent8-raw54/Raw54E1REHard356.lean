import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.E1RE.M356
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,true,4⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def P : List Bool := [false,true]
def Q : List Bool := [true,false]
def PP : List Bool := [false,true,false,true]
def W : List Bool := [true,true,true,true]
def Z : List Bool := [false,false]
def sec (n : Nat) (r : List Bool) : Z0 := ⟨0,[],P++rep PP n++Z++r⟩
def mid (n : Nat) (r : List Bool) : Z0 := ⟨2,[false]++W++rep W n,r⟩

theorem prep (n : Nat) (r : List Bool) :
    run0 table (4*n+4) (sec n r) = some (mid n r) := by
  have a (R : List Bool) : run0 table 2 ⟨0,[],P++R⟩ = some ⟨2,[true,true,true],R⟩ := by rfl
  have b := sweepR table 2 [true,true,true] [] PP W 4 (fun _ _ => rfl) n [] (Z++r)
  have c (L R : List Bool) : run0 table 2 ⟨2,true::L,Z++R⟩ = some ⟨2,false::true::true::L,R⟩ := by rfl
  have h1 := join0 (a (rep PP n++Z++r)) (by simpa only [List.append_assoc,List.append_nil,List.nil_append] using b)
  have h2 := join0 h1 (c ([true,true]++rep W n) r)
  rw [show 2+4*n+2=4*n+4 by omega] at h2
  unfold sec mid
  simpa only [W,List.append_assoc,List.cons_append,List.nil_append] using h2

-- Ordinary return: transfer one right alternating pair to two left pairs.
theorem transfer (n : Nat) (r : List Bool) :
    run0 table (12*n+18) (sec n (Q++r)) = some (sec (n+1) r) := by
  have a := prep n (Q++r)
  have b (L R : List Bool) : run0 table 4 ⟨2,false::true::L,Q++R⟩ = some ⟨0,true::true::L,Z++R⟩ := by rfl
  have c := sweepL table 0 [true,true,true,true,true] [] W PP 8 (fun _ _ => rfl) n [] (Z++r)
  have d (R : List Bool) : run0 table 10 ⟨0,true::W,R⟩ = some ⟨0,[],[false,true,false,true,false,true]++R⟩ := by rfl
  have h1 := join0 a (by simpa only [mid,W,List.append_assoc,List.cons_append,List.nil_append] using b ([true,true,true]++rep W n) r)
  have h2 := join0 h1 (by simpa only [List.append_assoc,List.nil_append,List.append_nil,W,List.cons_append] using c)
  have h3 := join0 h2 (d (rep PP n++(Z++r)))
  rw [show 4*n+4+4+8*n+10=12*n+18 by omega] at h3
  simpa only [sec,rep,P,PP,List.append_assoc,List.cons_append,List.nil_append] using h3

theorem reset (n : Nat) (r : List Bool) :
    run0 table (12*n+21) (sec n (false::r)) =
      some (sec 0 (rep Q (2*n+1)++false::true::r)) := by
  have a := prep n (false::r)
  have b (L R : List Bool) : run0 table 10 ⟨2,false::true::true::L,false::R⟩ = some ⟨0,true::L,Z++true::R⟩ := by rfl
  have c := sweepL table 0 [true,true,true] [] W PP 8 (fun _ _ => rfl) n [] (Z++true::r)
  have d (R : List Bool) : run0 table 7 ⟨0,[true,true,true],R⟩ = some ⟨0,[],[false,true,false,false,true]++R⟩ := by rfl
  have h1 := join0 a (by simpa only [mid,W,List.append_assoc,List.cons_append,List.nil_append] using b ([true,true]++rep W n) r)
  have h2 := join0 h1 (by simpa only [List.append_assoc,List.append_nil,List.nil_append,W,List.cons_append] using c)
  have h3 := join0 h2 (d (rep PP n++(Z++true::r)))
  rw [show 4*n+4+10+8*n+7=12*n+21 by omega] at h3
  have rot (j : Nat) : [true]++rep PP j++[false] = rep Q (2*j+1) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [show 2*(j+1)+1=2*j+1+2 by omega]
      simp only [rep,PP,Q,List.append_assoc,List.cons_append,List.nil_append] at ih ⊢
      exact congrArg (fun xs => true::false::true::false::xs) ih
  -- The final seven steps insert a marker before the rotated alternating block.
  simp only [sec,rep,P,Z,List.append_assoc,List.cons_append,List.nil_append] at h3 ⊢
  have hrot := congrArg (fun x => x++false::true::r) (rot n)
  simp only [List.append_assoc,List.cons_append,List.nil_append] at hrot
  rw [hrot] at h3
  exact h3

def family (s : Nat × Nat × Nat) : Z0 := sec s.1 (rep Q s.2.1++false::rep [true] s.2.2)
def next (s : Nat × Nat × Nat) : Nat × Nat × Nat :=
  match s.2.1 with
  | 0 => (0,2*s.1+1,s.2.2+1)
  | m+1 => (s.1+1,m,s.2.2)
def cost (s : Nat × Nat × Nat) : Nat := if s.2.1=0 then 12*s.1+21 else 12*s.1+18

theorem epoch (s : Nat × Nat × Nat) : run0 table (cost s) (family s) = some (family (next s)) := by
  rcases s with ⟨n,m,k⟩
  cases m with
  | zero => simpa [cost,family,next,rep] using reset n (rep [true] k)
  | succ m => simpa [cost,family,next,rep,List.append_assoc] using transfer n (rep Q m++false::rep [true] k)

def orbit : Nat → Nat × Nat × Nat
  | 0 => (0,3,1)
  | n+1 => next (orbit n)
def states (n : Nat) : Z0 := family (orbit n)
theorem entry : run0 table 65 ⟨0,[],[]⟩ = some (states 0) := by rfl
theorem positive (s : Nat × Nat × Nat) : 0 < cost s := by unfold cost; split <;> omega
theorem growth (n : Nat) : run0 table (cost (orbit n)) (states n) = some (states (n+1)) := epoch (orbit n)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table states 65 (fun n => cost (orbit n)) entry (fun n => positive (orbit n)) growth m hm
#print axioms never
end BB6.Agent8Raw54.E1RE.M356
