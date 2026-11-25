import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw107LBSweep
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,true,1⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨true,true,5⟩)
  | _,_ => none
abbrev P := [true,true]
abbrev U := [true]
abbrev B (L R : List Bool) : Z0 := ⟨1,L,R⟩
abbrev C (L R : List Bool) : Z0 := ⟨2,L,R⟩
abbrev F (L R : List Bool) : Z0 := ⟨5,L,R⟩
abbrev Fs (L R : List Bool) : Z0 := F (R.headD false::L) R.tail
def family (n : Nat) := B [] (rep U (2*n+5))

theorem entry : run0 table 17 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem pairUnary (n : Nat) : rep P n = rep U (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,ih,show 2*(n+1)=2*n+1+1 by omega]; rfl

theorem rep_add (W : List Bool) (n k : Nat) : rep W n ++ rep W k = rep W (n+k) := by
  induction n with
  | zero => simp [rep]
  | succ n ih => rw [show n+1+k=(n+k)+1 by omega]; simp only [rep,List.append_assoc,ih]

theorem B_one (L R : List Bool) : run0 table 1 (B (U++L) R) = some (B L (U++R)) := by rfl

theorem B_many (n : Nat) (L R : List Bool) : run0 table n (B (rep U n++L) R) = some (B L (rep U n++R)) := by
  simpa only [List.nil_append,Nat.one_mul] using sweepL table 1 [] [] U U 1 B_one n L R

theorem F_pair (L R : List Bool) : run0 table 2 (Fs L (P++R)) = some (Fs (P++L) R) := by rfl

theorem F_many (n : Nat) (L R : List Bool) : run0 table (2*n) (Fs L (rep P n++R)) = some (Fs (rep P n++L) R) := by
  induction n generalizing L with
  | zero => simp [rep,run0]
  | succ n ih =>
    have h := join0 (F_pair L (rep P n++R)) (ih (P++L))
    have e : rep P n ++ (P++L) = rep P (n+1) ++ L := by rw [← List.append_assoc,rep_snoc P n]; rfl
    rw [e] at h
    simpa only [rep,List.append_assoc,show 2+2*n=2*(n+1) by omega] using h

theorem B_turn (L R : List Bool) : run0 table 2 (B (false::L) (true::R)) = some (Fs (false::true::L) R) := by rfl

theorem F_turn (L R : List Bool) : run0 table 2 (F (false::true::L) R) = some (B L (false::true::R)) := by rfl

theorem inner (n : Nat) (L R : List Bool) :
    run0 table (4*n+5) (F (false::(rep P (n+1)++false::L)) R) = some (F (false::(rep P n++false::true::L)) (true::R)) := by
  have h1 := F_turn (true::rep P n++false::L) R
  have h2 := B_many (2*n+1) (false::L) (false::true::R)
  have h2' : run0 table (2*n+1) (B (true::(rep P n++false::L)) (false::true::R)) = some (B (false::L) (true::(rep P n++false::true::R))) := by
    rw [pairUnary]; exact h2
  have h3 := B_turn L (rep P n++false::true::R)
  have h4 := F_many n (false::true::L) (false::true::R)
  have h := join0 (join0 (join0 h1 h2') h3) h4
  change run0 table (2+(2*n+1)+2+2*n) _ = some (F (false::(rep P n++false::true::L)) (true::R)) at h
  simpa only [rep,List.cons_append,List.nil_append,List.append_assoc,show 2+(2*n+1)+2+2*n=4*n+5 by omega] using h

def innerCost : Nat → Nat
  | 0 => 0
  | n+1 => 4*n+5+innerCost n

theorem allInner (n : Nat) (L R : List Bool) :
    run0 table (innerCost n) (F (false::(rep P n++false::L)) R) = some (F (false::false::(rep U n++L)) (rep U n++R)) := by
  induction n generalizing L R with
  | zero => rfl
  | succ n ih =>
    have h := join0 (inner n L R) (ih (true::L) (true::R))
    have eq (T : List Bool) : rep U n ++ true::T = rep U (n+1) ++ T := by
      change rep U n ++ (U++T) = (U++rep U n)++T
      rw [← List.append_assoc,rep_snoc U n]
    rw [eq L,eq R] at h
    exact h

theorem start (n : Nat) : run0 table (2*(n+2)+2) (family n) = some (F (false::(rep P (n+2)++[false,true])) []) := by
  have h0 : run0 table 2 (family n) = some (Fs [false,true] (rep P (n+2))) := by
    unfold family; rw [pairUnary,show 2*n+5=2*(n+2)+1 by omega]; rfl
  have h1 := F_many (n+2) [false,true] []
  simp only [List.append_nil] at h1
  have h := join0 h0 h1
  change run0 table (2+2*(n+2)) _ = some (F (false::(rep P (n+2)++[false,true])) []) at h
  simpa only [show 2+2*(n+2)=2*(n+2)+2 by omega] using h

theorem finish (n : Nat) : run0 table (n+5) (F (false::false::(rep U n++[true])) (rep U n)) = some (B [] (rep U (2*n+3))) := by
  have h1 : run0 table 2 (F (false::false::(rep U n++[true])) (rep U n)) = some (B (true::true::(rep U n++[true])) (rep U n)) := by rfl
  have h2 := B_many (n+3) [] (rep U n)
  have eq : true::true::(rep U n++[true]) = rep U (n+3)++[] := by
    simp only [rep,List.cons_append,List.nil_append,List.append_nil]
    change true::true::(rep U n++U)=true::true::(U++rep U n)
    rw [rep_snoc]
  rw [← eq,rep_add,show n+3+n=2*n+3 by omega] at h2
  have h := join0 h1 h2
  simpa only [show 2+(n+3)=n+5 by omega] using h

def cost (n : Nat) := (2*(n+2)+2)+innerCost (n+2)+(n+2+5)
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 := allInner (n+2) [true] []
  simp only [List.append_nil] at h1
  have h := join0 (join0 (start n) h1) (finish (n+2))
  simpa only [cost,family,List.append_nil,show 2*(n+2)+3=2*(n+1)+5 by omega] using h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 17 cost entry (by intro n; unfold cost; omega) growth m hm
#print axioms growth
#print axioms never
end BB6.Agent11Raw107LBSweep
