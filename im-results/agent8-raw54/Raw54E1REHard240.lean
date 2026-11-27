import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.E1RE.M240
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,4⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def P : List Bool := [true,false,true,false]
def Z : List Bool := [false,false,false,false]
def O : List Bool := [true,true,true,true]
def T : List Bool := [true,false,true]

def sec (r : List Bool) : Z0 := ⟨0,[false,false],r⟩

theorem scan (n : Nat) (r : List Bool) :
    run0 table (4*n) (sec (rep P n ++ r)) =
      some ⟨0,[false] ++ rep O n ++ [false],r⟩ := by
  simpa only [sec,List.append_assoc,List.cons_append,List.nil_append] using
    (sweepR table 0 [false] [] P O 4 (fun _ _ => rfl) n [false] r)

theorem carry (n : Nat) (r : List Bool) :
    run0 table (8*n+16) (sec (rep P n ++ Z ++ r)) =
      some (sec (rep Z n ++ P ++ r)) := by
  have a := scan n (Z++r)
  have b (L R : List Bool) : run0 table 14 ⟨0,false::L,Z++R⟩ =
      some ⟨5,true::L,P++R⟩ := by rfl
  have c := sweepL table 5 [true] [] O Z 4 (fun _ _ => rfl) n [false] (P++r)
  have d (R : List Bool) : run0 table 2 ⟨5,[true,false],R⟩ = some (sec R) := by rfl
  have ab := join0 a (b (rep O n++[false]) r)
  have abc := join0 ab (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using c)
  have h := join0 abc (d (rep Z n++(P++r)))
  rw [show 4*n+14+4*n+2=8*n+16 by omega] at h
  simpa only [List.append_assoc] using h

theorem overflow (n : Nat) :
    run0 table (8*n+24) (sec (rep P n ++ T)) =
      some (sec (rep Z n ++ Z ++ T)) := by
  have a := scan n T
  have b (L : List Bool) : run0 table 18 ⟨0,false::L,T⟩ =
      some ⟨5,[true,true,true,true,true]++L,T⟩ := by rfl
  have c := sweepL table 5 [true,true,true,true,true] [] O Z 4
    (fun _ _ => rfl) n [false] T
  have d (R : List Bool) : run0 table 6 ⟨5,[true,true,true,true,true,false],R⟩ =
      some (sec (Z++R)) := by rfl
  have ab := join0 a (b (rep O n++[false]))
  have abc := join0 ab (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using c)
  have h := join0 abc (d (rep Z n++T))
  rw [show 4*n+18+4*n+6=8*n+24 by omega] at h
  simpa only [List.append_assoc,← List.append_assoc (rep Z n) Z T,rep_snoc Z n] using h

def digits : List Bool → List Bool
  | [] => T
  | false::bs => Z ++ digits bs
  | true::bs => P ++ digits bs

def increment : List Bool → List Bool
  | [] => [false]
  | false::bs => true::bs
  | true::bs => false::increment bs

def lead : List Bool → Nat
  | true::bs => lead bs+1
  | _ => 0

def cost : List Bool → Nat
  | [] => 24
  | false::_ => 16
  | true::bs => cost bs + 8

theorem carryWord (bs : List Bool) (n : Nat) :
    run0 table (8*n+cost bs) (sec (rep P n ++ digits bs)) =
      some (sec (rep Z n ++ digits (increment bs))) := by
  induction bs generalizing n with
  | nil => simpa only [digits,cost,increment,List.append_assoc] using overflow n
  | cons b bs ih =>
    cases b with
    | false => simpa only [digits,cost,increment,List.append_assoc] using carry n (digits bs)
    | true =>
      have h := ih (n+1)
      rw [show 8*(n+1)+cost bs = 8*n+(cost bs+8) by omega] at h
      simp only [rep,digits,increment,cost,List.append_assoc] at h ⊢
      simpa only [← List.append_assoc P (rep P n), ← rep_snoc P n,
        ← List.append_assoc Z (rep Z n), ← rep_snoc Z n,List.append_assoc] using h

def orbit : Nat → List Bool
  | 0 => []
  | n+1 => increment (orbit n)
def family (n : Nat) : Z0 := sec (digits (orbit n))

theorem positive (bs : List Bool) : 0 < cost bs := by
  cases bs with
  | nil => decide
  | cons b bs => cases b <;> simp [cost] <;> omega

theorem entry : run0 table 16 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (cost (orbit n)) (family n) = some (family (n+1)) := by
  simpa [family,orbit,rep] using carryWord (orbit n) 0

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 16 (fun n => cost (orbit n)) entry (fun n => positive (orbit n)) growth m hm
#print axioms carry
#print axioms overflow
#print axioms never
end BB6.Agent8Raw54.E1RE.M240
