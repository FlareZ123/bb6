import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace BB6.Agent8Raw117Quadratic
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨true,true,3⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

abbrev O (n : Nat) := List.replicate n true

theorem repeat_add (n m : Nat) : O (n+m) = O n ++ O m := by
  unfold O
  induction n with
  | zero => simp
  | succ n ih => rw [show n+1+m=n+m+1 by omega,List.replicate_succ,ih,List.replicate_succ];rfl

def T : Nat → List Bool
  | 0 => [false]
  | k+1 => false::true::T k

def B (l : List Bool) (m k : Nat) : Z0 := ⟨1,l,O m ++ T k⟩
def Reach (a b : Z0) : Prop := ∃ t : Nat, 0<t ∧ run0 table t a = some b

theorem reachJoin {a b c : Z0} (h : Reach a b) (g : Reach b c) : Reach a c := by
  obtain ⟨t,ht,h⟩ := h; obtain ⟨u,hu,g⟩ := g
  exact ⟨t+u,by omega,join0 h g⟩

theorem eSweep (n : Nat) (L R : List Bool) :
    run0 table (2*n) ⟨4,true::L,O (2*n) ++ R⟩ = some ⟨4,true::(O (2*n) ++ L),R⟩ := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have e : 2*(n+1)=2*n+2 := by omega
    rw [e]
    have h : run0 table 2 ⟨4,true::L,O (2*n+2) ++ R⟩ = some ⟨4,true::true::true::L,O (2*n) ++ R⟩ := by rfl
    have g := join0 h (ih (true::true::L))
    rw [show 2+2*n=2*n+2 by omega] at g
    rw [repeat_add (2*n) 2] at g ⊢
    simp only [show O 2 = [true,true] by rfl,List.append_assoc,List.cons_append,List.nil_append] at g ⊢
    exact g

theorem bSweep (n : Nat) (L R : List Bool) :
    run0 table n ⟨1,O n ++ L,R⟩ = some ⟨1,L,O n ++ R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h : run0 table 1 ⟨1,O (n+1) ++ L,R⟩ = some ⟨1,O n ++ L,true::R⟩ := by rfl
    have g := join0 h (ih (true::R))
    rw [show 1+n=n+1 by omega] at g
    simpa only [O,List.replicate_succ',List.append_assoc,List.cons_append,List.nil_append] using g

theorem evenReturn (a k : Nat) (l L : List Bool)
    (hh : l.headD false=false) (ht : l.tail=L) :
    run0 table (4*a+11) (B l (2*a+2) (k+1)) = some (B (false::true::L) (2*a+1) (k+1)) := by
  have h1 : run0 table 2 (B l (2*a+2) (k+1)) = some ⟨4,true::false::true::L,O (2*a) ++ T (k+1)⟩ := by
    simp only [B,run0,step0,hh,ht,table,move0]
    rfl
  have h2 := eSweep a (false::true::L) (T (k+1))
  have h3 : run0 table 8 ⟨4,true::(O (2*a) ++ false::true::L),T (k+1)⟩ = some ⟨1,true::(O (2*a) ++ false::true::L),T (k+1)⟩ := by
    cases k <;> rfl
  have h4 := bSweep (2*a+1) (false::true::L) (T (k+1))
  have g := join0 (join0 (join0 h1 h2) h3) h4
  rw [show 2+2*a+8+(2*a+1)=4*a+11 by omega] at g
  exact g

theorem oddReturn (a k : Nat) (l L : List Bool)
    (hh : l.headD false=false) (ht : l.tail=L) :
    run0 table (4*a+7) (B l (2*a+3) k) = some (B (false::true::L) (2*a) (k+1)) := by
  have h1 : run0 table 2 (B l (2*a+3) k) = some ⟨4,true::false::true::L,O (2*a+1) ++ T k⟩ := by
    simp only [B,run0,step0,hh,ht,table,move0]
    rfl
  have h2 := eSweep a (false::true::L) (true::T k)
  have e : O (2*a+1) ++ T k=O (2*a) ++ (true::T k) := by
    rw [repeat_add (2*a) 1,List.append_assoc];rfl
  rw [e] at h1
  have h3 : run0 table 5 ⟨4,true::(O (2*a) ++ false::true::L),true::T k⟩ = some ⟨1,O (2*a) ++ false::true::L,T (k+1)⟩ := by cases k <;> rfl
  have h4 := bSweep (2*a) (false::true::L) (T (k+1))
  have g := join0 (join0 (join0 h1 h2) h3) h4
  rw [show 2+2*a+5+2*a=4*a+7 by omega] at g
  exact g

def rcost : Nat → Nat
  | 0 => 11
  | n+1 => (4*(2*n+2)+11)+(4*(2*n+1)+7)+rcost n

theorem reduce (n k : Nat) (l L : List Bool)
    (hh : l.headD false=false) (ht : l.tail=L) :
    run0 table (rcost n) (B l (4*n+2) (k+1)) = some (B (false::(O (2*n+1) ++ L)) 1 (k+n+1)) := by
  induction n generalizing k l L with
  | zero => exact evenReturn 0 k l L hh ht
  | succ n ih =>
    have h1 := evenReturn (2*n+2) k l L hh ht
    have h2 := oddReturn (2*n+1) (k+1) (false::true::L) (true::L) rfl rfl
    have e1 : 2*(2*n+2)+2=4*(n+1)+2 := by omega
    have e2 : 2*(2*n+2)+1=2*(2*n+1)+3 := by omega
    rw [e1,e2] at h1
    have h3 := ih (k+1) (false::true::true::L) (true::true::L) rfl rfl
    have e3 : 2*(2*n+1)=4*n+2 := by omega
    rw [e3] at h1 h2
    have g := join0 (join0 h1 h2) h3
    have e4 : k+1+n+1=k+(n+1)+1 := by omega
    have e5 : O (2*n+1) ++ true::true::L = O (2*(n+1)+1) ++ L := by
      rw [show 2*(n+1)+1=2*n+1+2 by omega,repeat_add (2*n+1) 2,List.append_assoc];rfl
    rw [e4,e5] at g
    exact g

theorem rcost_pos (n : Nat) : 0 < rcost n := by cases n <;> simp [rcost] <;> omega

theorem finishPairs (k : Nat) (L : List Bool) :
    Reach (B (false::L) 1 k) ⟨1,false::(O (2*(k+1)) ++ L),[]⟩ := by
  induction k generalizing L with
  | zero => exact ⟨4,by decide,by rfl⟩
  | succ k ih =>
    have h : run0 table 4 (B (false::L) 1 (k+1)) = some (B (false::true::true::L) 1 k) := by rfl
    have g := reachJoin ⟨4,by decide,h⟩ (ih (true::true::L))
    have e : O (2*(k+1)) ++ true::true::L = O (2*(k+1+1)) ++ L := by
      rw [show 2*(k+1+1)=2*(k+1)+2 by omega,repeat_add (2*(k+1)) 2,List.append_assoc];rfl
    rw [e] at g
    exact g

theorem finishBlank (a : Nat) :
    Reach ⟨1,false::O a,[]⟩ (B [] (a+1) 1) := by
  have h : run0 table 10 ⟨1,false::O a,[]⟩ = some ⟨1,true::O a,T 1⟩ := by rfl
  have h2 := bSweep (a+1) [] (T 1)
  simp only [List.append_nil] at h2
  have g := join0 h h2
  refine ⟨10+(a+1),by omega,?_⟩
  simpa only [B,List.append_nil] using g

def family (n : Nat) : Z0 := B [] (4*n+2) 1

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : Reach (family n) (family (n+1)) := by
  have h1 := reduce n 0 [] [] rfl rfl
  simp only [Nat.zero_add] at h1
  have h2 := finishPairs (n+1) (O (2*n+1) ++ [])
  have g := reachJoin ⟨rcost n,rcost_pos n,h1⟩ h2
  have e : O (2*(n+1+1)) ++ (O (2*n+1) ++ [])=O (4*n+5) := by
    rw [← List.append_assoc,←repeat_add]
    rw [show 2*(n+1+1)+(2*n+1)=4*n+5 by omega,List.append_nil]
  rw [e] at g
  have h3 := finishBlank (4*n+5)
  have h4 := reachJoin g h3
  unfold family
  rw [show 4*(n+1)+2=4*n+5+1 by omega]
  exact h4

noncomputable def cost (n : Nat) : Nat := Classical.choose (growth n)
theorem cost_pos (n : Nat) : 0<cost n := (Classical.choose_spec (growth n)).1
theorem cost_run (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := (Classical.choose_spec (growth n)).2
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 cost entry cost_pos cost_run m hm
#print axioms growth
#print axioms never
end BB6.Agent8Raw117Quadratic
