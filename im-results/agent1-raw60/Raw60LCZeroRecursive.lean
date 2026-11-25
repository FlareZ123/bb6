import SweepPumping
namespace BB6.Agent1Raw60LCZeroRecursive
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
inductive V where | m63 | m64 | m66 | m75
  deriving DecidableEq

def table (v : V) : PartialMachine := fun (q,b) =>
  match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => if v = .m75 then some (some ⟨false,false,0⟩) else none
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => match v with
    | .m64 => some (some ⟨false,false,2⟩)
    | .m66 => some (some ⟨true,false,3⟩)
    | _ => none
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => match v with
    | .m63 => some (some ⟨false,false,3⟩)
    | .m64 | .m66 => some (some ⟨false,false,4⟩)
    | .m75 => some (some ⟨true,false,0⟩)
  | _,_ => none

def extra : V → Nat | .m63 => 1 | .m64 => 3 | .m66 => 1 | .m75 => 5
def T (v : V) : Nat → Nat
  | 0 => 9
  | n+1 => 2*T v n + extra v + 4

def W : Nat → List Bool
  | 0 => [false,false,false,true,true]
  | n+1 => false::false::W n

def C (L R : List Bool) : Z0 := ⟨2,L,R⟩
def D (L R : List Bool) : Z0 := ⟨3,L,R⟩
def F (L R : List Bool) : Z0 := ⟨5,L,R⟩

theorem t_pos (v : V) (n : Nat) : 0 < T v n := by
  cases n with
  | zero => simp [T]
  | succ n => simp [T]

theorem fill_clear (v : V) (t : Nat) (ht : 0 < t) (L R : List Bool)
    (h : run0 (table v) t (D (false::false::L) (false::R)) =
      some (F (false::false::false::L) R)) :
    run0 (table v) (t+extra v) (F (true::false::false::L) R) =
      some (F (false::false::false::L) R) := by
  have hd : run0 (table v) 1 (D (false::false::L) (false::R)) =
      some (D (false::L) (true::false::R)) := by cases v <;> rfl
  have hf : run0 (table v) (extra v+1) (F (true::false::false::L) R) =
      some (D (false::L) (true::false::R)) := by cases v <;> rfl
  rw [show t=1+(t-1) by omega,run0_add,hd] at h
  change run0 (table v) (t-1) (D (false::L) (true::false::R)) = _ at h
  have H := join0 hf h
  rw [show extra v+1+(t-1)=t+extra v by omega] at H
  exact H

theorem fill (v : V) (n : Nat) (b : Bool) (L R : List Bool) :
    run0 (table v) (T v n) (D (W n++L) (b::R)) =
      some (F (b::(W n++L)) R) := by
  induction n generalizing b R with
  | zero => cases v <;> cases b <;> rfl
  | succ n ih =>
    have h1 : run0 (table v) 2 (D (W (n+1)++L) (b::R)) =
        some (D (W n++L) (true::true::b::R)) := by cases v <;> rfl
    have h2 := ih true (true::b::R)
    have h3 : run0 (table v) (T v n+extra v) (F (true::(W n++L)) (true::b::R)) =
        some (F (false::(W n++L)) (true::b::R)) := by
      cases n <;> exact fill_clear v _ (t_pos v _) _ _ (ih false (true::b::R))
    have h4 : run0 (table v) 2 (F (false::(W n++L)) (true::b::R)) =
        some (F (b::(W (n+1)++L)) R) := by cases v <;> rfl
    have H := join0 (join0 (join0 h1 h2) h3) h4
    rw [show 2+T v n+(T v n+extra v)+2=T v (n+1) by simp [T]; omega] at H
    exact H

def family (n : Nat) : Z0 := C (W n) []
def cost (v : V) (n : Nat) := 2*T v n+extra v+3

theorem entry (v : V) : run0 (table v) 10 ⟨0,[],[]⟩ = some (family 0) := by cases v <;> rfl

theorem growth (v : V) (n : Nat) :
    run0 (table v) (cost v n) (family n) = some (family (n+1)) := by
  have h1 : run0 (table v) 2 (family n) = some (D (W n) [true]) := by
    cases n <;> cases v <;> rfl
  have h2 := fill v n true [] []
  simp only [List.append_nil] at h2
  have h3 : run0 (table v) (T v n+extra v) (F (true::W n) []) =
      some (F (false::W n) []) := by
    have H := fill v n false [] []
    simp only [List.append_nil] at H
    cases n <;> exact fill_clear v _ (t_pos v _) _ _ H
  have h4 : run0 (table v) 1 (F (false::W n) []) = some (family (n+1)) := by
    cases v <;> rfl
  have H := join0 (join0 (join0 h1 h2) h3) h4
  rw [show 2+T v n+(T v n+extra v)+1=cost v n by unfold cost; omega] at H
  exact H

theorem cost_pos (v : V) (n : Nat) : 0 < cost v n := by unfold cost; omega
theorem never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) family 10 (cost v) (entry v) (cost_pos v) (growth v) m hm
#print axioms growth
#print axioms never
namespace M63
def table : PartialMachine := BB6.Agent1Raw60LCZeroRecursive.table .m63
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent1Raw60LCZeroRecursive.never .m63 m hm
end M63
namespace M64
def table : PartialMachine := BB6.Agent1Raw60LCZeroRecursive.table .m64
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent1Raw60LCZeroRecursive.never .m64 m hm
end M64
namespace M66
def table : PartialMachine := BB6.Agent1Raw60LCZeroRecursive.table .m66
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent1Raw60LCZeroRecursive.never .m66 m hm
end M66
namespace M75
def table : PartialMachine := BB6.Agent1Raw60LCZeroRecursive.table .m75
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent1Raw60LCZeroRecursive.never .m75 m hm
end M75
end BB6.Agent1Raw60LCZeroRecursive
