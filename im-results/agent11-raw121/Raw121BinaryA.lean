import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw121BinaryA
open BB6Coverage BB6Coverage.Agent31Pump
inductive V | plain | pair | triple | extra deriving DecidableEq

def table (v : V) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some (match v with | .triple => ⟨true,false,4⟩ | _ => ⟨true,false,5⟩))
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some (match v with | .plain => ⟨false,false,0⟩ | .extra => ⟨true,true,5⟩ | _ => ⟨true,false,5⟩))
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev B (L R : List Bool) : Z0 := ⟨1,L,R⟩
abbrev E (L R : List Bool) : Z0 := ⟨4,L,R⟩
abbrev F (L R : List Bool) : Z0 := ⟨5,L,R⟩
abbrev U : List Bool := [true]
abbrev Z : List Bool := [false]
def P : V → List Bool | .triple => [true,true,true] | _ => [true,true]
def Q : V → List Bool | .triple => [false,false,false] | _ => [false,false]
def width : V → Nat | .triple => 3 | _ => 2
def suffix : V → List Bool | .plain => [false,false,false,true,false] | _ => [false,false,false]
def rightWord (v : V) (n : Nat) (T : List Bool) := true::(rep (P v) n++suffix v++T)

def Reach (v : V) (c d : Z0) : Prop := ∃ t, run0 (table v) t c = some d
theorem reflReach (v : V) (c : Z0) : Reach v c c := ⟨0,rfl⟩
theorem reach {v c d k} (h : run0 (table v) k c = some d) : Reach v c d := ⟨k,h⟩
theorem join {v c d e} (h : Reach v c d) (h' : Reach v d e) : Reach v c e := by
  obtain ⟨t,ht⟩:=h; obtain ⟨u,hu⟩:=h'; exact ⟨t+u,join0 ht hu⟩

theorem b_one (v : V) (L R : List Bool) :
    run0 (table v) (width v) (B ([true]++L) (P v++R)) = some (B ([true]++Q v++L) R) := by
  cases v <;> rfl

theorem b_many (v : V) (n : Nat) (L R : List Bool) :
    run0 (table v) (width v*n) (B (true::L) (rep (P v) n++R)) = some (B (true::(rep (Q v) n++L)) R) := by
  simpa only [List.nil_append,List.cons_append,List.append_assoc] using
    sweepR (table v) 1 [true] [] (P v) (Q v) (width v) (b_one v) n L R

theorem beginA (v : V) (n : Nat) (L T : List Bool) :
    run0 (table v) 1 (A (false::L) (rightWord v n T)) = some (B (true::true::L) (rep (P v) n++suffix v++T)) := by rfl

theorem front_plain (L T : List Bool) :
    run0 (table .plain) 15 (B (true::L) ([false,false,false,true,false]++T)) = some (A L ([true,false,false,false,true,false]++T)) := by rfl

theorem front (v : V) (hv : v ≠ .plain) (L T : List Bool) :
    run0 (table v) 6 (B (true::L) ([false,false,false]++T)) = some (E ([true,true,false]++L) (true::T)) := by
  cases v <;> first | contradiction | rfl

theorem onesSplit (T : List Bool) : ∃ j U, T = rep [true] j ++ U ∧ U.headD false = false := by
  induction T with
  | nil => exact ⟨0,[],rfl,rfl⟩
  | cons b T ih =>
    cases b with
    | false => exact ⟨0,false::T,rfl,rfl⟩
    | true => obtain ⟨j,U,h,e⟩:=ih; exact ⟨j+1,U,by simp only [rep,List.cons_append,List.nil_append,h],e⟩

theorem e_one (v : V) (L R : List Bool) :
    run0 (table v) 1 (E ([true]++L) (U++R)) = some (E ([true]++U++L) R) := by rfl

theorem e_many (v : V) (j : Nat) (L R : List Bool) :
    run0 (table v) j (E (true::L) (rep U j++R)) = some (E (true::(rep U j++L)) R) := by
  simpa only [List.nil_append,Nat.one_mul,List.cons_append,List.append_assoc] using sweepR (table v) 4 [true] [] U U 1 (e_one v) j L R

theorem e_exit (v : V) (L R : List Bool) (hR : R.headD false=false) :
    run0 (table v) 1 (E (true::L) R) = some (E (false::true::L) R.tail) := by
  cases R with
  | nil => rfl
  | cons b R => have hb : b=false := hR; subst b; rfl

theorem f_one (v : V) (L R : List Bool) :
    run0 (table v) 1 (F (U++L) R) = some (F L (Z++R)) := by rfl

theorem f_many (v : V) (j : Nat) (L R : List Bool) :
    run0 (table v) j (F (rep U j++L) R) = some (F L (rep Z j++R)) := by
  simpa only [List.nil_append,Nat.one_mul] using sweepL (table v) 5 [] [] U Z 1 (f_one v) j L R

theorem turn (v : V) (hv : v ≠ .plain) (L R : List Bool) :
    ∃ R', Reach v (E (false::L) R) (F L R') := by
  cases v with
  | plain => contradiction
  | pair => exact ⟨true::R,reach (show run0 (table .pair) 1 (E (false::L) R) = some (F L (true::R)) by rfl)⟩
  | triple => exact ⟨true::R,reach (show run0 (table .triple) 1 (E (false::L) R) = some (F L (true::R)) by rfl)⟩
  | extra =>
    cases R with
    | nil => exact ⟨[true,true],reach (show run0 (table .extra) 3 (E (false::L) []) = some (F L [true,true]) by rfl)⟩
    | cons b R => cases b with
      | false => exact ⟨true::true::R,reach (show run0 (table .extra) 3 (E (false::L) (false::R)) = some (F L (true::true::R)) by rfl)⟩
      | true => exact ⟨false::false::R,reach (show run0 (table .extra) 3 (E (false::L) (true::R)) = some (F L (false::false::R)) by rfl)⟩

theorem desc_general (v : V) (hv : v ≠ .plain) (n : Nat) (L T : List Bool) :
    ∃ T', Reach v (A (false::L) (rightWord v n T)) (A (rep (Q v) n++true::L) (rightWord v 0 T')) := by
  obtain ⟨j,Vtail,hT,hV⟩ := onesSplit T
  have h0 := beginA v n L T
  have h1 := b_many v n (true::L) (suffix v++T)
  have h2 := front v hv (rep (Q v) n++true::L) T
  have hS : suffix v = [false,false,false] := by cases v <;> first | contradiction | rfl
  rw [hS] at h1 h0
  have h3 := e_many v (j+1) (true::false::(rep (Q v) n++true::L)) Vtail
  have h4 := e_exit v (rep U (j+1)++true::false::(rep (Q v) n++true::L)) Vtail hV
  have h0' : run0 (table v) 1 (A (false::L) (rightWord v n T)) = some (B (true::true::L) (rep (P v) n++([false,false,false]++T))) := by simpa only [List.append_assoc] using h0
  have h23 := reach (join0 (join0 h0' h1) h2)
  rw [hT] at h23
  have h23' : Reach v (A (false::L) (rightWord v n (rep U j++Vtail)))
    (E (true::true::false::(rep (Q v) n++true::L)) (rep U (j+1)++Vtail)) := by
    simpa only [rep,List.cons_append,List.nil_append,List.append_assoc] using h23
  have h5 := join (join h23' (reach h3)) (reach h4)
  let X := false::(rep (Q v) n++true::L)
  have he : true::(rep U (j+1)++true::X) = rep U (j+3)++X := by
    change U ++ (rep U (j+1) ++ (U++X)) = _
    rw [← List.append_assoc (rep U (j+1)) U X,rep_snoc U (j+1)]
    rfl
  have h5' : Reach v (A (false::L) (rightWord v n (rep U j++Vtail))) (E (false::(rep U (j+3)++X)) Vtail.tail) := by
    change Reach v _ (E (false::(true::(rep U (j+1)++true::X))) Vtail.tail) at h5
    rw [he] at h5
    exact h5
  obtain ⟨R',h6⟩ := turn v hv (rep U (j+3)++X) Vtail.tail
  have h7 := f_many v (j+3) X R'
  have h8 : run0 (table v) 1 (F X (rep Z (j+3)++R')) = some (A (rep (Q v) n++true::L) (true::(rep Z (j+3)++R'))) := by rfl
  refine ⟨rep Z j++R',?_⟩
  have h := join (join (join h5' h6) (reach h7)) (reach h8)
  rw [hT]
  simpa only [rightWord,hS,rep,List.cons_append,List.nil_append,List.append_assoc] using h

theorem desc (v : V) (n : Nat) (L T : List Bool) :
    ∃ T', Reach v (A (false::L) (rightWord v n T)) (A (rep (Q v) n++true::L) (rightWord v 0 T')) := by
  by_cases h : v = .plain
  · subst v
    have h0 := beginA .plain n L T
    have h1 := b_many .plain n (true::L) (suffix .plain++T)
    rw [List.append_assoc] at h0
    have h2 := front_plain (rep (Q .plain) n++true::L) T
    exact ⟨T,reach (join0 (join0 h0 h1) h2)⟩
  · exact desc_general v h n L T

theorem carry (v : V) (L R : List Bool) :
    run0 (table v) (width v) (A (true::(Q v).tail++L) R) = some (A L (P v++R)) := by cases v <;> rfl

theorem fillClear (v : V) (n : Nat) :
    (∀ L T, ∃ T', Reach v (A (rep (Q v) n++L) (rightWord v 0 T)) (A L (rightWord v n T'))) ∧
    (∀ L T, ∃ T', Reach v (A (false::L) (rightWord v n T)) (A (true::L) (rightWord v n T'))) := by
  induction n with
  | zero =>
    constructor
    · intro L T; exact ⟨T,reflReach v _⟩
    · intro L T; exact desc v 0 L T
  | succ n ih =>
    obtain ⟨fill,clear⟩ := ih
    have fillNext : ∀ L T, ∃ T', Reach v (A (rep (Q v) (n+1)++L) (rightWord v 0 T)) (A L (rightWord v (n+1) T')) := by
      intro L T
      obtain ⟨T1,h1⟩:=fill (Q v++L) T
      obtain ⟨T2,h2⟩:=clear ((Q v).tail++L) T1
      have h3 := reach (carry v L (rightWord v n T2))
      have hP : P v++rightWord v n T2 = rightWord v (n+1) T2 := by cases v <;> rfl
      rw [hP] at h3
      have h1' : Reach v (A (rep (Q v) (n+1)++L) (rightWord v 0 T)) (A (false::((Q v).tail++L)) (rightWord v n T1)) := by
        have hQ' : Q v++L = false::((Q v).tail++L) := by cases v <;> rfl
        rw [← hQ']
        have e : rep (Q v) (n+1)++L = rep (Q v) n++(Q v++L) := by
          rw [← List.append_assoc,rep_snoc (Q v) n]
          rfl
        rw [e]
        exact h1
      exact ⟨T2,join (join h1' h2) h3⟩
    refine ⟨fillNext,?_⟩
    intro L T
    obtain ⟨T1,h1⟩:=desc v (n+1) L T
    obtain ⟨T2,h2⟩:=fillNext (true::L) T1
    exact ⟨T2,join h1 h2⟩

def family (v : V) (n : Nat) (T : List Bool) := A [] (rightWord v n T)

theorem blank_same (v : V) (n : Nat) (T : List Bool) (k : Nat) (hk : 0<k) :
    run0 (table v) k (family v n T) = run0 (table v) k (A [false] (rightWord v n T)) := by
  cases k with
  | zero => omega
  | succ k => rfl

theorem clearPositive (v : V) (n : Nat) (L T : List Bool) :
    ∃ T' k, 0<k ∧ run0 (table v) k (A (false::L) (rightWord v n T)) = some (A (true::L) (rightWord v n T')) := by
  obtain ⟨T',k,h⟩ := (fillClear v n).2 L T
  refine ⟨T',k,?_,h⟩
  by_cases e : k=0
  · subst k; simp [run0] at h
  · omega

theorem blank_carry (v : V) (R : List Bool) :
    run0 (table v) (width v) (A [true] R) = some (A [] (P v++R)) := by cases v <;> rfl

theorem growth (v : V) (n : Nat) (T : List Bool) :
    ∃ T' k, 0<k ∧ run0 (table v) k (family v n T) = some (family v (n+1) T') := by
  obtain ⟨T',k,hk,h⟩:=clearPositive v n [] T
  have h1 := (blank_same v n T k hk).trans h
  have h2 := blank_carry v (rightWord v n T')
  have hP : P v++rightWord v n T' = rightWord v (n+1) T' := by cases v <;> rfl
  rw [hP] at h2
  exact ⟨T',k+width v,by omega,join0 h1 h2⟩

def initialTail : V → List Bool
  | .plain => []
  | .pair => [false,true]
  | .triple => [false,true]
  | .extra => [false,true,true]
def entryTime : V → Nat | .extra => 16 | _ => 14

theorem entry (v : V) : run0 (table v) (entryTime v) ⟨0,[],[]⟩ = some (family v 0 (initialTail v)) := by cases v <;> rfl

noncomputable def tailAt (v : V) : Nat → List Bool
  | 0 => initialTail v
  | n+1 => Classical.choose (growth v n (tailAt v n))
noncomputable def fam (v : V) (n : Nat) := family v n (tailAt v n)
noncomputable def cost (v : V) (n : Nat) := Classical.choose (Classical.choose_spec (growth v n (tailAt v n)))

theorem positive (v : V) (n : Nat) : 0 < cost v n :=
  (Classical.choose_spec (Classical.choose_spec (growth v n (tailAt v n)))).1

theorem grow (v : V) (n : Nat) : run0 (table v) (cost v n) (fam v n) = some (fam v (n+1)) :=
  (Classical.choose_spec (Classical.choose_spec (growth v n (tailAt v n)))).2

theorem never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) (fam v) (entryTime v) (cost v) (entry v) (positive v) (grow v) m hm

#print axioms entry
#print axioms growth
#print axioms grow
#print axioms never
end BB6.Agent11Raw121BinaryA
