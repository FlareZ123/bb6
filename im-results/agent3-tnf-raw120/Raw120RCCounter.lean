import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent3Raw120RCCounter
open BB6Coverage BB6Coverage.Agent31Pump

/-- Two machines share one counter dynamics, differing only in the
    fixed-length block that restores four one cells. -/
def table (v : Bool) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨v,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,true => if v then some (some ⟨true,true,2⟩) else some (some ⟨false,false,0⟩)
  | _,_ => none
abbrev four : List Bool := [true,true,true,true]
abbrev three : List Bool := [true,true,true]
def Q (n : Nat) : List Bool := rep four n ++ three
def A (n : Nat) (b : Bool) (r : List Bool) : Z0 := ⟨0,b::(rep four n++[true,false]),r⟩
def K (v : Bool) : Nat := if v then 4 else 6

theorem Q_succ (n : Nat) : Q (n+1) = four ++ Q n := by simp [Q,rep]
theorem Q_comm (n : Nat) : Q n = three ++ rep four n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Q_succ,ih]; rfl

theorem bridge0 (v : Bool) (l r : List Bool) :
    run0 (table v) (K v) ⟨0,false::l,three++r⟩ = some ⟨0,r.headD false::four++l,r.tail⟩ := by cases v <;> rfl

theorem bridge (v : Bool) (j : Nat) (r : List Bool) :
    run0 (table v) (K v) (A j false (three++r)) = some (A (j+1) (r.headD false) r.tail) := by
  simpa only [A,rep,List.append_assoc,List.cons_append] using bridge0 v (rep four j++[true,false]) r

theorem sweep4 (v : Bool) (l r : List Bool) : run0 (table v) 4 ⟨4,four++l,r⟩ = some ⟨4,l,four++r⟩ := by rfl

theorem seed1 (v : Bool) (n : Nat) (r : List Bool) :
    run0 (table v) 1 (A (n+1) true r) = some ⟨4,rep four n++[true,true,true,true,true,false],false::r⟩ := by
  have h : rep four (n+1) = rep four n ++ four := (rep_snoc four n).symm
  simp only [A,h,List.append_assoc]
  rfl

theorem seed2 (v : Bool) (r : List Bool) :
    run0 (table v) 7 ⟨4,[true,true,true,true,true,false],r⟩ = some (A 0 true (three++r)) := by rfl

theorem seed (v : Bool) (n : Nat) (r : List Bool) :
    run0 (table v) (1+4*n+7) (A (n+1) true r) = some (A 0 true (Q n++false::r)) := by
  have h1 := seed1 v n r
  have h2 := sweepL (table v) 4 [] [] four four 4 (sweep4 v) n [true,true,true,true,true,false] (false::r)
  simp only [List.nil_append] at h2
  have h3 := seed2 v (rep four n++false::r)
  simpa only [Q_comm,List.append_assoc] using join0 (join0 h1 h2) h3

def Toggle (v : Bool) (n : Nat) : Prop := ∀ r : List Bool, ∃ t : Nat, 0 < t ∧ run0 (table v) t (A n true r) = some (A n false r)

theorem fill (v : Bool) (N : Nat) (small : ∀ j < N, Toggle v j) (m j : Nat) (hj : j+m < N) (r : List Bool) :
    ∃ t : Nat, 0 < t ∧ run0 (table v) t (A j true (Q m++r)) = some (A (j+m+1) (r.headD false) r.tail) := by
  induction m generalizing j with
  | zero =>
    obtain ⟨t,ht,h⟩ := small j (by omega) (Q 0++r)
    have g := bridge v j r
    refine ⟨t+K v,by omega,?_⟩
    simpa only [Q,rep,List.nil_append,Nat.add_zero] using join0 h g
  | succ m ih =>
    obtain ⟨t,ht,h⟩ := small j (by omega) (Q (m+1)++r)
    have g := bridge v j (true::Q m++r)
    have g' : run0 (table v) (K v) (A j false (Q (m+1)++r)) = some (A (j+1) true (Q m++r)) := by
      simpa only [Q_succ,List.append_assoc,List.cons_append,List.headD,List.tail,List.nil_append] using g
    obtain ⟨u,hu,h'⟩ := ih (j+1) (by omega)
    refine ⟨t+K v+u,by omega,?_⟩
    simpa only [show j+1+m+1=j+(m+1)+1 by omega] using join0 (join0 h g') h'

theorem toggle (v : Bool) (n : Nat) : Toggle v n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      intro r
      exact ⟨4,by decide,by rfl⟩
    | succ n =>
      intro r
      have h := seed v n r
      obtain ⟨u,hu,g⟩ := fill v (n+1) ih n 0 (by omega) (false::r)
      exact ⟨1+4*n+7+u,by omega,by simpa using join0 h g⟩

theorem grow1 (v : Bool) (n : Nat) :
    run0 (table v) 6 (A n false []) = some ⟨4,rep four n++[true,true,true,true,false],[true]⟩ := by
  change some (⟨4,three ++ (rep four n ++ [true,false]),[true]⟩ : Z0) = _
  rw [← List.append_assoc,← Q_comm]
  unfold Q
  rw [List.append_assoc]
  rfl

theorem grow2 (v : Bool) (r : List Bool) :
    run0 (table v) 6 ⟨4,[true,true,true,true,false],r⟩ = some (A 0 true ([true,true]++r)) := by rfl

theorem ones_append (a b : Nat) : List.replicate a true ++ List.replicate b true = List.replicate (a+b) true := by
  induction a with
  | zero => simp
  | succ a ih => rw [show a+1+b=a+b+1 by omega]; simp only [List.replicate_succ,List.cons_append,ih]
theorem rep_four (n : Nat) : rep four n = List.replicate (4*n) true := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show 4*(n+1)=4+4*n by omega,← ones_append]; simp only [rep,ih]; rfl

theorem growth (v : Bool) (n : Nat) : ∃ t : Nat, 0 < t ∧ run0 (table v) t (A n false []) = some (A (n+1) false []) := by
  have h1 := grow1 v n
  have h2 := sweepL (table v) 4 [] [] four four 4 (sweep4 v) n [true,true,true,true,false] [true]
  simp only [List.nil_append] at h2
  have h3 := grow2 v (rep four n++[true])
  have h4 := join0 (join0 h1 h2) h3
  have h4' : run0 (table v) (6+4*n+6) (A n false []) = some (A 0 true (Q n++[])) := by
    have he : [true,true] ++ (rep four n ++ [true]) = Q n := by
      unfold Q
      rw [rep_four]
      change List.replicate 2 true ++ (List.replicate (4*n) true ++ List.replicate 1 true) = List.replicate (4*n) true ++ List.replicate 3 true
      rw [ones_append,ones_append,ones_append]
      congr 1
      omega
    rw [he] at h4
    simpa only [List.append_nil] using h4
  obtain ⟨u,hu,h5⟩ := fill v (n+1) (fun j _ => toggle v j) n 0 (by omega) []
  exact ⟨6+4*n+6+u,by omega,by simpa using join0 h4' h5⟩

def family (n : Nat) : Z0 := A (n+1) false []
def entryCost (v : Bool) : Nat := if v then 53 else 59
theorem entry (v : Bool) : run0 (table v) (entryCost v) ⟨0,[],[]⟩ = some (family 0) := by cases v <;> decide
noncomputable def cost (v : Bool) (n : Nat) := Classical.choose (growth v (n+1))
theorem cost_pos (v : Bool) (n : Nat) : 0 < cost v n := (Classical.choose_spec (growth v (n+1))).1
theorem advance (v : Bool) (n : Nat) : run0 (table v) (cost v n) (family n) = some (family (n+1)) :=
  (Classical.choose_spec (growth v (n+1))).2
theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) family (entryCost v) (cost v) (entry v) (cost_pos v) (advance v) m hm
#print axioms entry
#print axioms growth
#print axioms never
end BB6.Agent3Raw120RCCounter
