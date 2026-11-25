import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent3Raw120RBPumps
open BB6Coverage BB6Coverage.Agent31Pump
namespace M973

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
abbrev four : List Bool := [true,true,true,true]
abbrev three : List Bool := [true,true,true]
def Q (n : Nat) : List Bool := rep four n ++ three
def L (n : Nat) (b : Bool) : List Bool := b :: (Q n ++ [false])
def A (n : Nat) (b : Bool) (r : List Bool) : Z0 := ⟨0,L n b,r⟩
theorem ones_append (a b : Nat) : List.replicate a true ++ List.replicate b true = List.replicate (a+b) true := by
  induction a with
  | zero => simp
  | succ a ih => rw [show a+1+b=a+b+1 by omega]; simp only [List.replicate_succ,List.cons_append,ih]
theorem rep_four (n : Nat) : rep four n = List.replicate (4*n) true := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show 4*(n+1)=4+4*n by omega,← ones_append]; simp only [rep,ih]; rfl
theorem Q_succ (n : Nat) : Q (n+1) = four ++ Q n := by simp [Q,rep,List.append_assoc]
theorem Q_comm (n : Nat) : Q n = three ++ rep four n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Q_succ,ih]; rfl
theorem bridge0 (l r : List Bool) :
    run0 table 6 ⟨0,false::l,three++r⟩ = some ⟨0,r.headD false::four++l,r.tail⟩ := by rfl
theorem bridge (j : Nat) (r : List Bool) :
    run0 table 6 (A j false (three++r)) = some (A (j+1) (r.headD false) r.tail) := by
  simpa only [A,L,Q_succ,List.append_assoc,List.cons_append] using bridge0 (Q j++[false]) r
theorem sweep4 (l r : List Bool) : run0 table 4 ⟨4,four++l,r⟩ = some ⟨4,l,four++r⟩ := by rfl
theorem seed1 (n : Nat) (r : List Bool) :
    run0 table 1 (A (n+1) true r) = some ⟨4,rep four n++[true,true,true,true,true,true,true,false],false::r⟩ := by
  have h : Q (n+1) ++ [false] = rep four n ++ [true,true,true,true,true,true,true,false] := by
    unfold Q
    rw [show rep four (n+1) = rep four n ++ four by exact (rep_snoc four n).symm]
    simp only [List.append_assoc]
    rfl
  simp only [A,L,h]
  rfl
theorem seed2 (r : List Bool) :
    run0 table 13 ⟨4,[true,true,true,true,true,true,true,false],r⟩ = some (A 0 true (three++r)) := by rfl
theorem seed (n : Nat) (r : List Bool) :
    run0 table (1+4*n+13) (A (n+1) true r) = some (A 0 true (Q n++false::r)) := by
  have h1 := seed1 n r
  have h2 := sweepL table 4 [] [] four four 4 sweep4 n [true,true,true,true,true,true,true,false] (false::r)
  simp only [List.nil_append] at h2
  have h3 := seed2 (rep four n++false::r)
  have h := join0 (join0 h1 h2) h3
  simpa only [Q_comm,List.append_assoc] using h

def Toggle (n : Nat) : Prop := ∀ r : List Bool, ∃ t : Nat, 0 < t ∧ run0 table t (A n true r) = some (A n false r)
theorem fill (N : Nat) (small : ∀ j < N, Toggle j) (m j : Nat) (hj : j+m < N) (r : List Bool) :
    ∃ t : Nat, 0 < t ∧ run0 table t (A j true (Q m++r)) = some (A (j+m+1) (r.headD false) r.tail) := by
  induction m generalizing j with
  | zero =>
    obtain ⟨t,ht,h⟩ := small j (by omega) (Q 0++r)
    have g := bridge j r
    refine ⟨t+6,by omega,?_⟩
    simpa only [Q,rep,List.nil_append,Nat.add_zero] using join0 h g
  | succ m ih =>
    obtain ⟨t,ht,h⟩ := small j (by omega) (Q (m+1)++r)
    have g := bridge j (true::Q m++r)
    have g' : run0 table 6 (A j false (Q (m+1)++r)) = some (A (j+1) true (Q m++r)) := by
      simpa only [Q_succ,List.append_assoc,List.cons_append,List.headD,List.tail,List.nil_append] using g
    obtain ⟨u,hu,h'⟩ := ih (j+1) (by omega)
    refine ⟨t+6+u,by omega,?_⟩
    have out := join0 (join0 h g') h'
    simpa only [show j+1+m+1=j+(m+1)+1 by omega] using out

theorem toggle (n : Nat) : Toggle n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      intro r
      exact ⟨10,by decide,by rfl⟩
    | succ n =>
      intro r
      have h := seed n r
      obtain ⟨u,hu,g⟩ := fill (n+1) ih n 0 (by omega) (false::r)
      exact ⟨1+4*n+13+u,by omega,by simpa using join0 h g⟩
theorem grow1 (n : Nat) :
    run0 table 6 (A n false []) = some ⟨4,rep four n++[true,true,true,true,true,true,false],[true]⟩ := by
  have h : Q n ++ [false] = three ++ (rep four n ++ [false]) := by rw [Q_comm,List.append_assoc]
  simp only [A,L,h]
  change some (⟨4,[true,true,true,true,true,true] ++ (rep four n ++ [false]),[true]⟩ : Z0) = _
  have hq : [true,true,true,true,true,true] ++ rep four n = rep four n ++ [true,true,true,true,true,true] := by
    rw [rep_four]
    change List.replicate 6 true ++ List.replicate (4*n) true = List.replicate (4*n) true ++ List.replicate 6 true
    rw [ones_append,ones_append,Nat.add_comm]
  rw [← List.append_assoc,hq,List.append_assoc]
  rfl

theorem grow2 (r : List Bool) :
    run0 table 12 ⟨4,[true,true,true,true,true,true,false],r⟩ = some (A 0 true ([true,true]++r)) := by rfl

theorem growth (n : Nat) : ∃ t : Nat, 0 < t ∧ run0 table t (A n false []) = some (A (n+1) false []) := by
  have h1 := grow1 n
  have h2 := sweepL table 4 [] [] four four 4 sweep4 n [true,true,true,true,true,true,false] [true]
  simp only [List.nil_append] at h2
  have h3 := grow2 (rep four n++[true])
  have h4 := join0 (join0 h1 h2) h3
  have h4' : run0 table (6+4*n+12) (A n false []) = some (A 0 true (Q n++[])) := by
    have he : [true,true] ++ (rep four n ++ [true]) = Q n := by
      unfold Q
      rw [rep_four]
      change List.replicate 2 true ++ (List.replicate (4*n) true ++ List.replicate 1 true) = List.replicate (4*n) true ++ List.replicate 3 true
      rw [ones_append,ones_append,ones_append]
      congr 1
      omega
    rw [he] at h4
    simpa only [List.append_nil] using h4
  obtain ⟨u,hu,h5⟩ := fill (n+1) (fun j _ => toggle j) n 0 (by omega) []
  exact ⟨6+4*n+12+u,by omega,by simpa using join0 h4' h5⟩

def family (n : Nat) : Z0 := A (n+1) false []
theorem entry : run0 table 59 ⟨0,[],[]⟩ = some (family 0) := by decide
noncomputable def cost (n : Nat) := Classical.choose (growth (n+1))
theorem cost_pos (n : Nat) : 0 < cost n := (Classical.choose_spec (growth (n+1))).1
theorem advance (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) :=
  (Classical.choose_spec (growth (n+1))).2
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 59 cost entry cost_pos advance m hm
#print axioms toggle
#print axioms growth
#print axioms never
end M973
end BB6.Agent3Raw120RBPumps
