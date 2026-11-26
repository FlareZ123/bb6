import SweepPumping
namespace BB6Coverage.Agent7Raw57LE1M672
open BB6Coverage Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none
abbrev I4 : List Bool := [true,true,true,true]
abbrev I8 : List Bool := I4 ++ I4
abbrev Z4 : List Bool := [false,true,false,true]
abbrev R4 : List Bool := [true,false,true,false]
abbrev R8 : List Bool := R4 ++ R4
abbrev pre : List Bool := [false,false,true]
abbrev tailB : List Bool := [false,true,false,true,true]
def U (n : Nat) : Z0 := ⟨3,pre++rep I4 n++[true],[]⟩
def V (a b : Nat) : Z0 := ⟨3,pre++rep I8 a++rep Z4 b++tailB,[]⟩

theorem rep_add' (P : List Bool) (a b : Nat) : rep P (a+b) = rep P a ++ rep P b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [show a+1+b=a+b+1 by omega]; simp only [rep,ih,List.append_assoc]
theorem rep_double (n : Nat) : rep I8 n = rep I4 (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      rep I8 (n+1) = I8 ++ rep I8 n := rfl
      _ = rep I4 2 ++ rep I4 (2*n) := by rw [ih]; rfl
      _ = rep I4 (2+2*n) := (rep_add' I4 2 (2*n)).symm
      _ = rep I4 (2*(n+1)) := by congr 1; omega

theorem entry : run0 table 32 ⟨0,[],[]⟩ = some (U 2) := by rfl

theorem convert (n : Nat) : run0 table (13+8*n) (U n) = some (V 0 n) := by
  have h0 : run0 table 3 (U n) = some ⟨4,[true,true]++rep I4 n++[true],[true]⟩ := by rfl
  have h1 := sweepL table 4 [true,true] [] I4 R4 4 (by intro L R; rfl) n [true] [true]
  have h2 : run0 table 4 ⟨4,[true,true,true],rep R4 n++[true]⟩ = some ⟨1,[false,true], [true,false]++rep R4 n++[true]⟩ := by rfl
  have h3 := sweepR table 1 [false] [true,false] R4 Z4 4 (by intro L R; rfl) n [true] [true]
  have h4 : run0 table 6 ⟨1,[false]++rep Z4 n++[true],[true,false,true]⟩ = some ⟨3,pre++Z4++rep Z4 n++[true],[]⟩ := by rfl
  simp only [List.append_assoc,List.nil_append,List.append_nil] at h0 h1 h2 h3 h4
  have h := join0 (join0 (join0 (join0 h0 h1) h2) h3) h4
  rw [show 3+4*n+4+4*n+6=13+8*n by omega] at h
  have e := rep_snoc Z4 n
  simp only [V,rep,List.nil_append,List.append_assoc]
  rw [show tailB = Z4++[true] by rfl, ← List.append_assoc (rep Z4 n) Z4 [true], e]
  exact h

theorem core (a : Nat) (L : List Bool) :
    run0 table (16+16*a) ⟨3,pre++rep I8 a++Z4++L,[]⟩ =
      some ⟨3,pre++rep I8 (a+1)++L,[]⟩ := by
  have h0 : run0 table 3 ⟨3,pre++rep I8 a++Z4++L,[]⟩ = some ⟨4,[true,true]++rep I8 a++Z4++L,[true]⟩ := by rfl
  have h1 := sweepL table 4 [true,true] [] I8 R8 8 (by intro L R; rfl) a (Z4++L) [true]
  have h2 : run0 table 4 ⟨4,[true,true]++Z4++L,rep R8 a++[true]⟩ = some ⟨0,[false,true]++L,R4++rep R8 a++[true]⟩ := by rfl
  have h3 := sweepR table 0 [false] R4 R8 I8 8 (by intro L R; rfl) a ([true]++L) [true]
  have h4 : run0 table 9 ⟨0,[false]++rep I8 a++[true]++L,R4++[true]⟩ = some ⟨3,[false,false]++I8++rep I8 a++[true]++L,[]⟩ := by rfl
  simp only [List.append_assoc,List.nil_append,List.append_nil] at h0 h1 h2 h3 h4
  have h := join0 (join0 (join0 (join0 h0 h1) h2) h3) h4
  rw [show 3+8*a+4+8*a+9=16+16*a by omega] at h
  have e : rep I8 a ++ [true] = [true] ++ rep I8 a := by
    exact (rotate true [true,true,true,true,true,true,true] a).symm
  simp only [List.append_assoc] at h ⊢
  rw [← List.append_assoc (rep I8 a) [true] L, e, List.append_assoc] at h
  change run0 table (16+16*a) ⟨3,pre++(rep I8 a++(Z4++L)),[]⟩ =
    some ⟨3,pre++(I8++(rep I8 a++L)),[]⟩ at h
  simpa only [rep,List.append_assoc] using h

theorem transfer (a b : Nat) : run0 table (16+16*a) (V a (b+1)) = some (V (a+1) b) := by
  simpa only [V,rep,List.append_assoc] using core a (rep Z4 b++tailB)

theorem finish (a : Nat) : run0 table (16+16*a) (V a 0) = some (U (2*a+2)) := by
  have h := core a [true]
  have eV : V a 0 = ⟨3,pre++rep I8 a++Z4++[true],[]⟩ := by
    simp only [V,rep,List.nil_append,List.append_assoc]; rfl
  have eU : U (2*a+2) = ⟨3,pre++rep I8 (a+1)++[true],[]⟩ := by
    unfold U; rw [rep_double,show 2*(a+1)=2*a+2 by omega]
  rw [eV,eU]; exact h

def transferCost (a : Nat) : Nat → Nat
  | 0 => 0
  | b+1 => (16+16*a)+transferCost (a+1) b

theorem consume (a b : Nat) : run0 table (transferCost a b) (V a b) = some (V (a+b) 0) := by
  induction b generalizing a with
  | zero => simp [transferCost,run0]
  | succ b ih =>
    have h := join0 (transfer a b) (ih (a+1))
    simpa only [transferCost,show a+1+b=a+(b+1) by omega] using h

def cost (n : Nat) : Nat := 13+8*n+transferCost 0 n+(16+16*n)
theorem epoch (n : Nat) : run0 table (cost n) (U n) = some (U (2*n+2)) := by
  exact join0 (join0 (convert n) (by simpa using consume 0 n)) (finish n)

def index : Nat → Nat
  | 0 => 2
  | n+1 => 2*index n+2

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table (fun n => U (index n)) 32 (fun n => cost (index n)) entry
    (by intro n; unfold cost; omega) (by intro n; exact epoch (index n)) m hm
#print axioms entry
#print axioms epoch
#print axioms never
end BB6Coverage.Agent7Raw57LE1M672
