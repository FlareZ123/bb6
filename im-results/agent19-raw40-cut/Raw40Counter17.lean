import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.Counter17
open BB6Coverage BB6Coverage.Agent31Pump
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨false,false,3⟩)
  | 5,true => some (some ⟨false,true,2⟩)
  | _,_ => none

def U : List Bool := [true,true,true]
def P : List Bool := [false,true,true]
def V : List Bool := [true,true,false]
def tail (b : Bool) : List Bool := if b then [false] else []

inductive Blocks : List Bool → Prop where
  | nil : Blocks []
  | one {w} : Blocks w → Blocks (U++w)
  | zero {w} : Blocks w → Blocks (V++w)

def full (k : Nat) (b : Bool) : Z0 :=
  ⟨2,[true,true],rep U (k+1)++[true,true]++tail b⟩
def carry (k : Nat) (w : List Bool) (b : Bool) : Z0 :=
  ⟨2,[true,true]++w,rep U (k+1)++[true]++tail b⟩

inductive Good : Z0 → Prop where
  | full (k : Nat) (b : Bool) : Good (full k b)
  | carry (k : Nat) (w : List Bool) (b : Bool) : Blocks w → Good (carry k w b)

theorem comm1 (k : Nat) : [true]++rep U k = rep U k++[true] :=
  rotate true [true,true] k

theorem comm2 (k : Nat) : [true,true]++rep U k = rep U k++[true,true] := by
  change [true]++([true]++rep U k) = _
  rw [comm1 k,← List.append_assoc,comm1 k,List.append_assoc]
  rfl

theorem rotateBlocks (k : Nat) :
    [true,true]++rep P k++[true] = rep V k++U := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change [true,true]++(P++rep P k)++[true] = V++rep V k++U
    have h : [true,true]++P = V++[true,true] := by rfl
    rw [← List.append_assoc [true,true] P, h]
    simp only [List.append_assoc] at ih ⊢
    simpa only [List.append_assoc] using congrArg (fun xs => V++xs) ih

theorem blocks_prefix (k : Nat) {w : List Bool} (hw : Blocks w) :
    Blocks (rep V k++U++w) := by
  induction k with
  | zero => exact Blocks.one hw
  | succ k ih =>
    simpa only [rep,List.append_assoc] using Blocks.zero ih

theorem Btriple (L R : List Bool) :
    run0 table 3 ⟨1,U++L,R⟩ = some ⟨1,L,U++R⟩ := by rfl
theorem Bzero (L R : List Bool) :
    run0 table 3 ⟨1,V++L,R⟩ = some ⟨2,[true,true]++L,[true]++R⟩ := by rfl
theorem Bblank (R : List Bool) :
    run0 table 1 ⟨1,[],U++R⟩ = some ⟨2,[true,true],[true,true]++R⟩ := by rfl
theorem Bsingle (L R : List Bool) :
    run0 table 1 ⟨1,[true]++L,R⟩ = some ⟨1,L,[true]++R⟩ := by rfl
theorem Bstop (L R : List Bool) :
    run0 table 1 ⟨1,[false]++L,[true]++R⟩ = some ⟨2,[true,true]++L,R⟩ := by rfl

/-- Scan whole blocks from their low-order end. Encountering V restarts C;
    reaching the blank edge restarts a full-width C pass. -/
theorem walk (w : List Bool) (hw : Blocks w) (m : Nat) (b : Bool) :
    ∃ t z, 0<t ∧ run0 table t ⟨1,w,rep U (m+2)++tail b⟩ = some z ∧ Good z := by
  induction hw generalizing m with
  | nil =>
    refine ⟨1,full m b,by omega,?_,Good.full _ _⟩
    have h := Bblank (rep U (m+1)++tail b)
    have h' : run0 table 1 ⟨1,[],rep U (m+2)++tail b⟩ =
        some ⟨2,[true,true],[true,true]++(rep U (m+1)++tail b)⟩ := by
      simpa only [rep,List.append_assoc] using h
    unfold full
    rw [← comm2 (m+1)]
    simpa only [List.append_assoc] using h' 
  | @one w hw ih =>
    have h := Btriple w (rep U (m+2)++tail b)
    have h' : run0 table 3 ⟨1,U++w,rep U (m+2)++tail b⟩ =
        some ⟨1,w,rep U (m+1+2)++tail b⟩ := by
      simpa only [show m+1+2=(m+2)+1 by omega,rep,List.append_assoc] using h
    obtain ⟨t,z,ht,hr,hz⟩ := ih (m+1)
    exact ⟨3+t,z,by omega,join0 h' hr,hz⟩
  | @zero w hw ih =>
    refine ⟨3,carry (m+1) w b,by omega,?_,Good.carry _ _ _ hw⟩
    have h := Bzero w (rep U (m+2)++tail b)
    unfold carry
    rw [show m+1+1=m+2 by omega]
    simpa only [← List.append_assoc [true],comm1,List.append_assoc] using h

/-- The unprocessed zero/triple prefix is either nonempty (an immediate
    restart) or exhausted (scan the binary-block word). -/
theorem resume (k m : Nat) (w : List Bool) (b : Bool) (hw : Blocks w) :
    ∃ t z, 0<t ∧ run0 table t ⟨1,rep P k++[true]++w,rep U (m+1)++[true,true]++tail b⟩ = some z ∧ Good z := by
  cases k with
  | zero =>
    have h := Bsingle w (rep U (m+1)++[true,true]++tail b)
    have h' : run0 table 1 ⟨1,rep P 0++[true]++w,rep U (m+1)++[true,true]++tail b⟩ =
        some ⟨1,w,rep U (m+2)++tail b⟩ := by
      have eq : [true]++(rep U (m+1)++[true,true]++tail b) =
          rep U (m+2)++tail b := by
        calc
          _ = ([true]++rep U (m+1))++[true,true]++tail b := by simp only [List.append_assoc]
          _ = rep U (m+1)++U++tail b := by
            rw [comm1]; simp only [List.append_assoc]; rfl
          _ = _ := by rw [rep_snoc]; rfl
      rw [eq] at h
      exact h
    obtain ⟨t,z,ht,hr,hz⟩ := walk w hw m b
    exact ⟨1+t,z,by omega,join0 h' hr,hz⟩
  | succ k =>
    refine ⟨1,carry m (rep V k++U++w) b,by omega,?_,Good.carry _ _ _ (blocks_prefix k hw)⟩
    have h := Bstop ([true,true]++rep P k++[true]++w) (rep U (m+1)++[true]++tail b)
    unfold carry
    have hr : [true]++(rep U (m+1)++[true]++tail b) =
        rep U (m+1)++[true,true]++tail b := by
      calc
        _ = ([true]++rep U (m+1))++[true]++tail b := by simp only [List.append_assoc]
        _ = _ := by rw [comm1]; simp only [List.append_assoc]; rfl
    have li : [false]++([true,true]++rep P k++[true]++w) =
        rep P (k+1)++[true]++w := by
      simp only [rep,P,List.append_assoc,List.cons_append,List.nil_append]
    have lo : [true,true]++([true,true]++rep P k++[true]++w) =
        [true,true]++(rep V k++U++w) := by
      have e := congrArg (fun xs => xs++w) (rotateBlocks k)
      exact congrArg (fun xs => [true,true]++xs) e
    rw [hr,li,lo] at h
    simpa only [List.append_assoc] using h

theorem Ctriple (L R : List Bool) :
    run0 table 3 ⟨2,[true]++L,U++R⟩ = some ⟨2,[true]++P++L,R⟩ := by rfl

theorem fullTail (L : List Bool) (b : Bool) :
    run0 table 16 ⟨2,[true,false,true,true]++L,[true,true]++tail b⟩ =
      some ⟨1,L,rep U 2++[true,true]⟩ := by cases b <;> rfl

theorem carryTail (L : List Bool) (b : Bool) :
    run0 table 12 ⟨2,[true,false,true,true]++L,[true]++tail b⟩ =
      some ⟨1,L,rep U 1++[true,true]++[false]⟩ := by cases b <;> rfl

theorem full_next (k : Nat) (b : Bool) :
    ∃ t z, 0<t ∧ run0 table t (full k b) = some z ∧ Good z := by
  have h1 := sweepR table 2 [true] [] U P 3 Ctriple (k+1) [true] ([true,true]++tail b)
  have h1' : run0 table (3*(k+1)) (full k b) =
      some ⟨2,[true,false,true,true]++rep P k++[true],[true,true]++tail b⟩ := by
    simpa only [full,rep,List.nil_append,List.append_assoc,P,List.cons_append] using h1
  have h2 := fullTail (rep P k++[true]) b
  have h2' : run0 table 16 ⟨2,[true,false,true,true]++rep P k++[true],[true,true]++tail b⟩ =
      some ⟨1,rep P k++[true],rep U 2++[true,true]⟩ := by
    simpa only [List.append_assoc] using h2
  obtain ⟨t,z,ht,hr,hz⟩ := resume k 1 [] false Blocks.nil
  have hr' : run0 table t ⟨1,rep P k++[true],rep U 2++[true,true]⟩ = some z := by
    simpa only [tail,Bool.false_eq_true,if_false,List.append_nil] using hr
  exact ⟨3*(k+1)+16+t,z,by omega,join0 (join0 h1' h2') hr',hz⟩

theorem carry_next (k : Nat) (w : List Bool) (b : Bool) (hw : Blocks w) :
    ∃ t z, 0<t ∧ run0 table t (carry k w b) = some z ∧ Good z := by
  have h1 := sweepR table 2 [true] [] U P 3 Ctriple (k+1) ([true]++w) ([true]++tail b)
  have h1' : run0 table (3*(k+1)) (carry k w b) =
      some ⟨2,[true,false,true,true]++rep P k++[true]++w,[true]++tail b⟩ := by
    simpa only [carry,rep,List.nil_append,List.append_assoc,P,List.cons_append] using h1
  have h2 := carryTail (rep P k++[true]++w) b
  have h2' : run0 table 12 ⟨2,[true,false,true,true]++rep P k++[true]++w,[true]++tail b⟩ =
      some ⟨1,rep P k++[true]++w,rep U 1++[true,true]++[false]⟩ := by
    simpa only [List.append_assoc] using h2
  obtain ⟨t,z,ht,hr,hz⟩ := resume k 0 w true hw
  have hr' : run0 table t ⟨1,rep P k++[true]++w,rep U 1++[true,true]++[false]⟩ = some z := hr
  exact ⟨3*(k+1)+12+t,z,by omega,join0 (join0 h1' h2') hr',hz⟩

theorem next {z : Z0} (h : Good z) :
    ∃ t z', 0<t ∧ run0 table t z = some z' ∧ Good z' := by
  cases h with
  | full k b => exact full_next k b
  | carry k w b hw => exact carry_next k w b hw

theorem entry : run0 table 30 ⟨0,[],[]⟩ = some (full 0 true) := by rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  have arbitrary : ∀ k, ∃ t z, k≤t ∧ run0 table t ⟨0,[],[]⟩ = some z ∧ Good z := by
    intro k
    induction k with
    | zero => exact ⟨30,full 0 true,by omega,entry,Good.full _ _⟩
    | succ k ih =>
      obtain ⟨t,z,ht,hr,hz⟩ := ih
      obtain ⟨d,z',hd,hs,hz'⟩ := next hz
      exact ⟨t+d,z',by omega,join0 hr hs,hz'⟩
  intro n
  obtain ⟨t,z,ht,hr,hz⟩ := arbitrary n
  have hproj : (BB6Coverage.Agent50Zipper.zrun table t start).map project = some z :=
    (run_project table t start).trans hr
  cases h : BB6Coverage.Agent50Zipper.zrun table t start with
  | none => simp [h] at hproj
  | some z' =>
    have H := BB6Coverage.Agent50Zipper.zrun_sound table m hm t start z' h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms never
end BB6.Agent19Raw40.Counter17
