import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw13Shared
open BB6Coverage Agent31Pump

def P : List Bool := [false,true]
def T : List Bool := [true,false]
def Q : List Bool := [true,true]

theorem rotT (a : Nat) : [false]++rep T a++[true]=rep P (a+1) := by
  induction a with
  | zero => rfl
  | succ a ih =>
    change P++([false]++rep T a++[true])=P++rep P (a+1)
    rw [ih]
theorem rotP (a : Nat) : [true]++rep P a=rep T a++[true] := by
  induction a with
  | zero => rfl
  | succ a ih =>
    change T++([true]++rep P a)=T++(rep T a++[true])
    rw [ih]
theorem rotP0 (a : Nat) : rep P a++[false]=[false]++rep T a := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [rep,List.append_assoc,ih]
    rfl

def A (n : Nat) : Z0 := ⟨0,[],rep Q (2*n+1)++[true]⟩
def D (a b : Nat) : Z0 := ⟨3,[],rep P (a+1)++rep Q b⟩
def E (z : List Bool) (a b : Nat) : Z0 := ⟨4,z,rep T (a+1)++rep Q (2*b+1)⟩

/-- Exact local rules common to three raw13 sibling tables. -/
structure Rules (p : PartialMachine) (z : List Bool) (d : Nat) : Prop where
  firstPass : ∀ a R, run0 p (5+2*(a+d)) ⟨4,z,rep T (a+1)++Q++R⟩ =
    some ⟨3,rep P (a+d)++[false,false,true]++z,[false]++R⟩
  init : ∀ R, run0 p 3 ⟨0,[],[true]++R⟩ = some ⟨4,[],T++R⟩
  zeroFrame : ∀ R, step0 p ⟨4,[],R⟩ = step0 p ⟨4,z,R⟩
  leftD : ∀ L R, run0 p 2 ⟨3,P++L,R⟩ = some ⟨3,L,P++R⟩
  turnD : ∀ R, run0 p 3 ⟨3,[false,false,true]++z,[false]++R⟩ =
    some ⟨1,[false,false,true,true]++z,R⟩
  rightB : ∀ L R, run0 p 2 ⟨1,[false,false]++L,T++R⟩ =
    some ⟨1,[false,false]++T++L,R⟩
  turnB : ∀ L R, run0 p 3 ⟨1,[false,false]++L,Q++R⟩ =
    some ⟨3,[false,true,false]++L,[false]++R⟩
  returnE : ∀ R, run0 p 1 ⟨3,[true]++z,R⟩ = some ⟨4,z,[true]++R⟩
  turnA : ∀ L, run0 p 2 ⟨1,[false,false]++L,[]⟩ = some ⟨0,T++L,[true]⟩
  leftA : ∀ L R, run0 p 2 ⟨0,T++L,R⟩ = some ⟨0,L,Q++R⟩
  tailA : ∀ R, run0 p 3 ⟨0,[true,true]++z,[true]++R⟩ =
    some ⟨3,[false]++z,[false,true]++R⟩
  tailD : ∀ R, run0 p 10 ⟨3,[false]++z,[false,true,true,true]++R⟩ =
    some ⟨3,[],rep P 3++R⟩
  startD : ∀ R, run0 p 3 ⟨3,[],P++R⟩ = some ⟨1,[false,false,true],[true]++R⟩
  rightD : ∀ L R, run0 p 2 ⟨1,[false,false]++L,[true]++P++R⟩ =
    some ⟨1,[false,false]++T++L,[true]++R⟩
  endD : ∀ L, run0 p 4 ⟨1,[false,false]++L,[true]⟩ =
    some ⟨0,T++T++L,[true]⟩
  endA : ∀ R, run0 p 2 ⟨0,[true],R⟩ = some ⟨0,[],Q++R⟩

variable {p : PartialMachine} {z : List Bool} {d : Nat} (r : Rules p z d)
include r

theorem scanE (a : Nat) (R : List Bool) :
    run0 p (8+4*(a+d)) ⟨4,z,rep T (a+1)++Q++R⟩ =
      some ⟨1,[false,false,true,true]++z,rep T (a+d)++R⟩ := by
  have h1 := r.firstPass a R
  have h2 := sweepL p 3 [] [] P P 2 r.leftD (a+d) ([false,false,true]++z) ([false]++R)
  simp only [List.nil_append] at h2
  have h3 := r.turnD (rep T (a+d)++R)
  have h2' : run0 p (2*(a+d)) ⟨3,rep P (a+d)++[false,false,true]++z,[false]++R⟩ =
      some ⟨3,[false,false,true]++z,[false]++(rep T (a+d)++R)⟩ := by
    simp only [List.append_assoc] at h2 ⊢
    rw [← List.append_assoc (rep P (a+d)) [false] R,rotP0] at h2
    exact h2
  have h := join0 (join0 h1 h2') h3
  rw [show 5+2*(a+d)+2*(a+d)+3=8+4*(a+d) by omega] at h
  exact h

theorem Epos (a b : Nat) : run0 p (16+8*(a+d)) (E z a (b+1)) = some (E z (a+d+2) b) := by
  have h1 := scanE r a (Q++rep Q (2*b+1))
  have h2 := sweepR p 1 [false,false] [] T T 2 r.rightB (a+d) ([true,true]++z) (Q++rep Q (2*b+1))
  simp only [List.nil_append] at h2
  have h2' : run0 p (2*(a+d)) ⟨1,[false,false,true,true]++z,rep T (a+d)++(Q++rep Q (2*b+1))⟩ =
      some ⟨1,[false,false]++rep T (a+d)++([true,true]++z),Q++rep Q (2*b+1)⟩ := by
    exact h2
  have h3 := r.turnB (rep T (a+d)++([true,true]++z)) (rep Q (2*b+1))
  have h3' : run0 p 3 ⟨1,[false,false]++rep T (a+d)++([true,true]++z),Q++rep Q (2*b+1)⟩ =
      some ⟨3,rep P (a+d+2)++([true]++z),[false]++rep Q (2*b+1)⟩ := by
    have hh : [false,true,false]++(rep T (a+d)++([true,true]++z))=rep P (a+d+2)++([true]++z) := by
      change P++([false]++(rep T (a+d)++([true]++([true]++z))))=P++(rep P (a+d+1)++([true]++z))
      rw [← List.append_assoc (rep T (a+d)) [true] ([true]++z), ← List.append_assoc [false] (rep T (a+d)++[true]) ([true]++z)]
      rw [← List.append_assoc [false] (rep T (a+d)) [true],rotT]
    rw [hh] at h3
    simpa only [List.append_assoc] using h3
  have h4 := sweepL p 3 [] [] P P 2 r.leftD (a+d+2) ([true]++z) ([false]++rep Q (2*b+1))
  simp only [List.nil_append] at h4
  have h5 := r.returnE (rep P (a+d+2)++([false]++rep Q (2*b+1)))
  have h := join0 (join0 (join0 (join0 h1 h2') h3') h4) h5
  rw [show 8+4*(a+d)+2*(a+d)+3+2*(a+d+2)+1=16+8*(a+d) by omega] at h
  unfold E
  have hh : [true]++(rep P (a+d+2)++([false]++rep Q (2*b+1))) = rep T (a+d+2+1)++rep Q (2*b+1) := by
    rw [← List.append_assoc (rep P (a+d+2)) [false] (rep Q (2*b+1)),rotP0,← List.append_assoc [true] ([false]++rep T (a+d+2)) (rep Q (2*b+1))]
    rfl
  rw [hh] at h
  rw [show 2*(b+1)+1=(2*b+1)+2 by omega]
  simp only [rep,List.append_assoc] at h ⊢
  exact h

theorem Ezero (a : Nat) : run0 p (25+8*(a+d)) (E z a 0) = some (D 2 (a+d)) := by
  have h1 := scanE r a []
  simp only [List.append_nil] at h1
  have h2 := sweepR p 1 [false,false] [] T T 2 r.rightB (a+d) ([true,true]++z) []
  simp only [List.nil_append,List.append_nil] at h2
  have h3 := r.turnA (rep T (a+d)++([true,true]++z))
  have h3' : run0 p 2 ⟨1,[false,false]++rep T (a+d)++([true,true]++z),[]⟩ =
    some ⟨0,rep T (a+d+1)++([true,true]++z),[true]⟩ := by
    simpa only [rep,List.append_assoc] using h3
  have h4 := sweepL p 0 [] [] T Q 2 r.leftA (a+d+1) ([true,true]++z) [true]
  simp only [List.nil_append] at h4
  have aux : ∀ k, rep Q k++[true]=[true]++rep Q k := by
    intro k; induction k with
    | zero => rfl
    | succ k ih =>
      change Q++(rep Q k++[true])=[true]++(Q++rep Q k)
      rw [ih]
      rfl
  have h5 := r.tailA (Q++rep Q (a+d))
  have h5' : run0 p 3 ⟨0,[true,true]++z,rep Q (a+d+1)++[true]⟩ =
      some ⟨3,[false]++z,[false,true,true,true]++rep Q (a+d)⟩ := by
    simp only [rep,List.append_assoc,aux]
    exact h5
  have h6 := r.tailD (rep Q (a+d))
  have h := join0 (join0 (join0 (join0 (join0 h1 h2) h3') h4) h5') h6
  rw [show 8+4*(a+d)+2*(a+d)+2+2*(a+d+1)+3+10=25+8*(a+d) by omega] at h
  simpa only [E,D,rep,List.append_nil] using h

private theorem scanD (a : Nat) (R : List Bool) :
    run0 p (3+2*a) ⟨3,[],rep P (a+1)++R⟩ =
      some ⟨1,[false,false]++rep T a++[true],[true]++R⟩ := by
  have h := join0 (r.startD (rep P a++R))
    (sweepR p 1 [false,false] [true] P T 2 r.rightD a [true] R)
  simpa only [rep,List.append_assoc] using h

theorem Dpos (a b : Nat) : run0 p (4*a+10) (D a (b+1)) = some (D (a+2) b) := by
  have h1 := scanD r a (rep Q (b+1))
  have h2 := r.turnB (rep T a++[true]) ([true]++rep Q b)
  have h2' : run0 p 3 ⟨1,[false,false]++rep T a++[true],[true]++rep Q (b+1)⟩ =
      some ⟨3,rep P (a+2),P++rep Q b⟩ := by
    have hh : [false,true,false]++(rep T a++[true])=rep P (a+2) := by
      change P++([false]++rep T a++[true])=P++rep P (a+1)
      rw [rotT]
    rw [hh] at h2
    simp only [rep,List.append_assoc] at h2 ⊢
    exact h2
  have h3 := sweepL p 3 [] [] P P 2 r.leftD (a+2) [] (P++rep Q b)
  simp only [List.nil_append,List.append_nil] at h3
  have h := join0 (join0 h1 h2') h3
  rw [show 3+2*a+3+2*(a+2)=4*a+10 by omega] at h
  have hh : rep P (a+2)++P = rep P (a+2+1) := by rw [rep_snoc]; rfl
  unfold D
  rw [← hh]
  simpa only [List.append_assoc] using h

theorem Dzero (a : Nat) : run0 p (4*a+13) (D a 0) =
    some ⟨0,[],rep Q (a+3)++[true]⟩ := by
  have h1 := scanD r a []
  simp only [List.append_nil] at h1
  have h2 := r.endD (rep T a++[true])
  have h2' : run0 p 4 ⟨1,[false,false]++rep T a++[true],[true]⟩ =
      some ⟨0,rep T (a+2)++[true],[true]⟩ := by
    simp only [rep,List.append_assoc] at h2 ⊢
    exact h2
  have h3 := sweepL p 0 [] [] T Q 2 r.leftA (a+2) [true] [true]
  simp only [List.nil_append] at h3
  have h4 := r.endA (rep Q (a+2)++[true])
  have h := join0 (join0 (join0 h1 h2') h3) h4
  rw [show 3+2*a+4+2*(a+2)+2=4*a+13 by omega] at h
  simpa only [D,rep,List.append_nil,List.append_assoc] using h

def costD (a : Nat) : Nat → Nat
  | 0 => 0
  | b+1 => 4*a+10+costD (a+2) b

theorem iterD (a b : Nat) : run0 p (costD a b) (D a b) = some (D (a+2*b) 0) := by
  induction b generalizing a with
  | zero => simp [costD,run0]
  | succ b ih =>
    have h := join0 (Dpos r a b) (ih (a+2))
    simpa only [costD,show a+2+2*b=a+2*(b+1) by omega] using h

def costE (d a : Nat) : Nat → Nat
  | 0 => 0
  | b+1 => 16+8*(a+d)+costE d (a+d+2) b

theorem iterE (a b : Nat) : run0 p (costE d a b) (E z a b) = some (E z (a+(d+2)*b) 0) := by
  induction b generalizing a with
  | zero => simp [costE,run0]
  | succ b ih =>
    have h := join0 (Epos r a b) (ih (a+d+2))
    simpa only [costE,show a+d+2+(d+2)*b=a+(d+2)*(b+1) by simp [Nat.mul_succ];omega] using h

def hparam (d n : Nat) := (d+2)*n+d
def ecost (d n : Nat) := costE d 0 n+(25+8*hparam d n)
def total (d n : Nat) := 3+ecost d n+costD 2 (hparam d n)+(4*(2+2*hparam d n)+13)

theorem growth (n : Nat) : run0 p (total d n) (A n) = some (A (hparam d n+2)) := by
  have aux : ∀ k, rep Q k++[true]=[true]++rep Q k := by
    intro k; induction k with
    | zero => rfl
    | succ k ih =>
      change Q++(rep Q k++[true])=[true]++(Q++rep Q k)
      rw [ih];rfl
  have h1 := r.init (rep Q (2*n+1))
  rw [← aux] at h1
  have h1' : run0 p 3 (A n) = some ⟨4,[],T++rep Q (2*n+1)⟩ := h1
  have h2 := iterE r 0 n
  simp only [Nat.zero_add] at h2
  have h3 := Ezero r ((d+2)*n)
  have hE := join0 h2 h3
  have hE' : run0 p (ecost d n) ⟨4,[],T++rep Q (2*n+1)⟩ = some (D 2 (hparam d n)) := by
    change run0 p (costE d 0 n+(25+8*hparam d n)) _ = _
    have hpositive : 0 < costE d 0 n+(25+8*hparam d n) := by omega
    have heq : ∀ k, 0<k → run0 p k ⟨4,[],T++rep Q (2*n+1)⟩ = run0 p k (E z 0 n) := by
      intro k hk; cases k with
      | zero => omega
      | succ k => simp only [E,rep,List.append_nil,run0,r.zeroFrame]
    rw [heq _ hpositive]
    exact hE
  have hD := iterD r 2 (hparam d n)
  have hlast := Dzero r (2+2*hparam d n)
  have h := join0 (join0 (join0 h1' hE') hD) hlast
  unfold total A at *
  simpa only [show 2+2*hparam d n+3=2*(hparam d n+2)+1 by omega] using h
end BB6Coverage.Agent31Pump.Raw13Shared

namespace BB6Coverage.Agent31Pump.Raw13Shared

def table0RE : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,1⟩)
  | 3,true => some (some ⟨true,false,4⟩)
  | 4,false => some (some ⟨false,true,4⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | _,_ => none

def table0RF : PartialMachine := fun s => match s.1.val,s.2 with
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => none
  | 5,true => some (some ⟨true,true,5⟩)
  | _,_ => table0RE s

def table1LF : PartialMachine := fun s => match s.1.val,s.2 with
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => none
  | 5,false => some (some ⟨true,true,5⟩)
  | 5,true => some (some ⟨false,true,2⟩)
  | _,_ => table0RE s

private theorem cpair (p : PartialMachine) (h : ∀ L R, run0 p 2 ⟨2,Q++L,P++R⟩ = some ⟨2,Q++P++L,R⟩)
    (a : Nat) (L R : List Bool) : run0 p (2*a) ⟨2,Q++L,rep P a++R⟩ = some ⟨2,Q++rep P a++L,R⟩ := by
  simpa only [List.nil_append] using sweepR p 2 Q [] P P 2 h a L R

private theorem pass0 (p : PartialMachine)
    (base : ∀ R, run0 p 5 ⟨4,[false],T++Q++R⟩ = some ⟨3,[false,false,true,false],[false]++R⟩)
    (start : ∀ R, run0 p 5 ⟨4,[false],T++T++[true]++R⟩ = some ⟨2,Q++[false,false,true,false],R⟩)
    (pair : ∀ L R, run0 p 2 ⟨2,Q++L,P++R⟩ = some ⟨2,Q++P++L,R⟩)
    (turn : ∀ L R, run0 p 2 ⟨2,Q++L,[true]++R⟩ = some ⟨3,P++L,[false]++R⟩)
    (a : Nat) (R : List Bool) : run0 p (5+2*(a+0)) ⟨4,[false],rep T (a+1)++Q++R⟩ =
    some ⟨3,rep P (a+0)++[false,false,true]++[false],[false]++R⟩ := by
  cases a with
  | zero => exact base R
  | succ a =>
    have h1 := start (rep P a++[true]++R)
    have h2 := cpair p pair a [false,false,true,false] ([true]++R)
    have h3 := turn (rep P a++[false,false,true,false]) R
    simp only [List.append_assoc] at h1 h2 h3
    have h := join0 (join0 h1 h2) h3
    rw [show 5+2*a+2=5+2*(a+1+0) by omega] at h
    simp only [rep,List.append_assoc] at h ⊢
    rw [← List.append_assoc [true] (rep P a) ([true]++R), rotP, List.append_assoc] at h
    exact h

private theorem pass1 (a : Nat) (R : List Bool) :
    run0 table1LF (5+2*(a+1)) ⟨4,[],rep T (a+1)++Q++R⟩ =
    some ⟨3,rep P (a+1)++[false,false,true]++[],[false]++R⟩ := by
  have start : ∀ R, run0 table1LF 5 ⟨4,[],T++[true]++R⟩ = some ⟨2,Q++[false,false,true],R⟩ := by intros; rfl
  have pair : ∀ L R, run0 table1LF 2 ⟨2,Q++L,P++R⟩ = some ⟨2,Q++P++L,R⟩ := by intros; rfl
  have turn : ∀ L R, run0 table1LF 2 ⟨2,Q++L,[true]++R⟩ = some ⟨3,P++L,[false]++R⟩ := by intros; rfl
  have h1 := start (rep P a++[true]++R)
  have h2 := cpair table1LF pair a [false,false,true] ([true]++R)
  have h3 := turn (rep P a++[false,false,true]) R
  simp only [List.append_assoc] at h1 h2 h3
  have h := join0 (join0 h1 h2) h3
  rw [show 5+2*a+2=5+2*(a+1) by omega] at h
  simp only [rep,List.append_assoc,List.append_nil] at h ⊢
  rw [← List.append_assoc [true] (rep P a) ([true]++R), rotP, List.append_assoc] at h
  exact h

theorem rules0RE : Rules table0RE [false] 0 := by
  constructor
  · exact pass0 table0RE (by intros; rfl) (by intros; rfl) (by intros; rfl) (by intros; rfl)
  all_goals intros; rfl

theorem rules0RF : Rules table0RF [false] 0 := by
  constructor
  · exact pass0 table0RF (by intros; rfl) (by intros; rfl) (by intros; rfl) (by intros; rfl)
  all_goals intros; rfl

theorem rules1LF : Rules table1LF [] 1 := by
  constructor
  · exact pass1
  all_goals intros; rfl

theorem costD_eq (a b : Nat) : costD a b=4*b*b+(4*a+6)*b := by
  induction b generalizing a with
  | zero => simp [costD]
  | succ b ih => rw [costD,ih]; simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.mul_assoc]; omega

theorem costE_eq (d a b : Nat) : costE d a b=4*(d+2)*b*b+(8+8*a+4*d)*b := by
  induction b generalizing a with
  | zero => simp [costE]
  | succ b ih => rw [costE,ih]; simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.mul_assoc]; omega

theorem total0 (n : Nat) : total 0 n = 24*n*n+68*n+49 := by
  unfold total ecost hparam
  rw [costD_eq,costE_eq]
  simp only [Nat.zero_add,Nat.add_zero,Nat.mul_zero,Nat.mul_add,Nat.add_mul,Nat.mul_assoc]
  simp only [← Nat.mul_assoc]
  simp only [show 4*2*n*2=16*n by omega, show 4*2*n=8*n by omega]
  simp only [Nat.mul_assoc]
  omega

theorem total1 (n : Nat) : total 1 n = 48*n*n+126*n+83 := by
  unfold total ecost hparam
  rw [costD_eq,costE_eq]
  simp only [Nat.add_zero,Nat.mul_zero,Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.mul_assoc]
  simp only [← Nat.mul_assoc, Nat.mul_one]
  simp only [show 4*2*n*2=16*n by omega, show 4*2*n=8*n by omega, show 4*n*2=8*n by omega]
  simp only [Nat.mul_assoc]
  omega

theorem blank0RE : run0 table0RE 19 ⟨0,[],[]⟩ = some (A 1) := by rfl
theorem blank0RF : run0 table0RF 19 ⟨0,[],[]⟩ = some (A 1) := by rfl
theorem blank1LF : run0 table1LF 19 ⟨0,[],[]⟩ = some (A 1) := by rfl

theorem growth0RE (n : Nat) : run0 table0RE (24*n*n+68*n+49) (A n) = some (A (2*n+2)) := by
  simpa [total0,hparam] using growth rules0RE n
theorem growth0RF (n : Nat) : run0 table0RF (24*n*n+68*n+49) (A n) = some (A (2*n+2)) := by
  simpa [total0,hparam] using growth rules0RF n
theorem growth1LF (n : Nat) : run0 table1LF (48*n*n+126*n+83) (A n) = some (A (3*n+3)) := by
  have h := growth rules1LF n
  rw [total1] at h
  simpa [hparam,show (1+2)*n+1+2=3*n+3 by omega] using h

private def orbit2 : Nat → Nat
  | 0 => 1
  | k+1 => 2*orbit2 k+2
private def orbit3 : Nat → Nat
  | 0 => 1
  | k+1 => 3*orbit3 k+3

theorem never0RE (m : Machine) (hm : compatible table0RE m) : NeverHalts m :=
  never_of_growth table0RE (fun k => A (orbit2 k)) 19
    (fun k => 24*orbit2 k*orbit2 k+68*orbit2 k+49) blank0RE
    (fun k => by omega) (fun k => growth0RE (orbit2 k)) m hm
theorem never0RF (m : Machine) (hm : compatible table0RF m) : NeverHalts m :=
  never_of_growth table0RF (fun k => A (orbit2 k)) 19
    (fun k => 24*orbit2 k*orbit2 k+68*orbit2 k+49) blank0RF
    (fun k => by omega) (fun k => growth0RF (orbit2 k)) m hm
theorem never1LF (m : Machine) (hm : compatible table1LF m) : NeverHalts m :=
  never_of_growth table1LF (fun k => A (orbit3 k)) 19
    (fun k => 48*orbit3 k*orbit3 k+126*orbit3 k+83) blank1LF
    (fun k => by omega) (fun k => growth1LF (orbit3 k)) m hm

#print axioms never0RE
#print axioms never0RF
#print axioms never1LF
end BB6Coverage.Agent31Pump.Raw13Shared
