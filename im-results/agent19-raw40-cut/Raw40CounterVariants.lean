import Raw40Counter17
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.CounterVariants
open BB6Coverage BB6Coverage.Agent31Pump
open Counter17

inductive Variant where
  | a | b | d

def target : Variant → Fin 6
  | .a => 0
  | .b => 1
  | .d => 3

def machine (v : Variant) : PartialMachine := fun s =>
  if s = (0,true) then some (some ⟨true,false,0⟩)
  else if s = (5,false) then some (some ⟨false,false,target v⟩)
  else Counter17.table s

def carryCost : Variant → Nat
  | .a => 10
  | .b => 14
  | .d => 10

theorem Btriple (v : Variant) (L R : List Bool) :
    run0 (machine v) 3 ⟨1,U++L,R⟩ = some ⟨1,L,U++R⟩ := by rfl
theorem Bzero (v : Variant) (L R : List Bool) :
    run0 (machine v) 3 ⟨1,V++L,R⟩ = some ⟨2,[true,true]++L,[true]++R⟩ := by rfl
theorem Bblank (v : Variant) (R : List Bool) :
    run0 (machine v) 1 ⟨1,[],U++R⟩ = some ⟨2,[true,true],[true,true]++R⟩ := by rfl
theorem Bsingle (v : Variant) (L R : List Bool) :
    run0 (machine v) 1 ⟨1,[true]++L,R⟩ = some ⟨1,L,[true]++R⟩ := by rfl
theorem Bstop (v : Variant) (L R : List Bool) :
    run0 (machine v) 1 ⟨1,[false]++L,[true]++R⟩ = some ⟨2,[true,true]++L,R⟩ := by rfl

/-- Scan whole blocks from their low-order end. Encountering V restarts C;
    reaching the blank edge restarts a full-width C pass. -/
theorem walk (v : Variant) (w : List Bool) (hw : Blocks w) (m : Nat) (b : Bool) :
    ∃ t z, 0<t ∧ run0 (machine v) t ⟨1,w,rep U (m+2)++tail b⟩ = some z ∧ Good z := by
  induction hw generalizing m with
  | nil =>
    refine ⟨1,full m b,by omega,?_,Good.full _ _⟩
    have h := Bblank v (rep U (m+1)++tail b)
    have h' : run0 (machine v) 1 ⟨1,[],rep U (m+2)++tail b⟩ =
        some ⟨2,[true,true],[true,true]++(rep U (m+1)++tail b)⟩ := by
      simpa only [rep,List.append_assoc] using h
    unfold full
    rw [← comm2 (m+1)]
    simpa only [List.append_assoc] using h' 
  | @one w hw ih =>
    have h := Btriple v w (rep U (m+2)++tail b)
    have h' : run0 (machine v) 3 ⟨1,U++w,rep U (m+2)++tail b⟩ =
        some ⟨1,w,rep U (m+1+2)++tail b⟩ := by
      simpa only [show m+1+2=(m+2)+1 by omega,rep,List.append_assoc] using h
    obtain ⟨t,z,ht,hr,hz⟩ := ih (m+1)
    exact ⟨3+t,z,by omega,join0 h' hr,hz⟩
  | @zero w hw ih =>
    refine ⟨3,carry (m+1) w b,by omega,?_,Good.carry _ _ _ hw⟩
    have h := Bzero v w (rep U (m+2)++tail b)
    unfold carry
    rw [show m+1+1=m+2 by omega]
    simpa only [← List.append_assoc [true],comm1,List.append_assoc] using h

/-- The unprocessed zero/triple prefix is either nonempty (an immediate
    restart) or exhausted (scan the binary-block word). -/
theorem resume (v : Variant) (k m : Nat) (w : List Bool) (b : Bool) (hw : Blocks w) :
    ∃ t z, 0<t ∧ run0 (machine v) t ⟨1,rep P k++[true]++w,rep U (m+1)++[true,true]++tail b⟩ = some z ∧ Good z := by
  cases k with
  | zero =>
    have h := Bsingle v w (rep U (m+1)++[true,true]++tail b)
    have h' : run0 (machine v) 1 ⟨1,rep P 0++[true]++w,rep U (m+1)++[true,true]++tail b⟩ =
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
    obtain ⟨t,z,ht,hr,hz⟩ := walk v w hw m b
    exact ⟨1+t,z,by omega,join0 h' hr,hz⟩
  | succ k =>
    refine ⟨1,carry m (rep V k++U++w) b,by omega,?_,Good.carry _ _ _ (blocks_prefix k hw)⟩
    have h := Bstop v ([true,true]++rep P k++[true]++w) (rep U (m+1)++[true]++tail b)
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

theorem Ctriple (v : Variant) (L R : List Bool) :
    run0 (machine v) 3 ⟨2,[true]++L,U++R⟩ = some ⟨2,[true]++P++L,R⟩ := by rfl

theorem fullTail (v : Variant) (L : List Bool) (b : Bool) :
    run0 (machine v) 14 ⟨2,[true,false,true,true]++L,[true,true]++tail b⟩ =
      some ⟨1,L,rep U 2++[true,true]⟩ := by cases v <;> cases b <;> rfl

theorem carryTail (v : Variant) (L : List Bool) (b : Bool) :
    run0 (machine v) (carryCost v) ⟨2,[true,false,true,true]++L,[true]++tail b⟩ =
      some ⟨1,L,rep U 1++[true,true]++[false]⟩ := by cases v <;> cases b <;> rfl

theorem full_next (v : Variant) (k : Nat) (b : Bool) :
    ∃ t z, 0<t ∧ run0 (machine v) t (full k b) = some z ∧ Good z := by
  have h1 := sweepR (machine v) 2 [true] [] U P 3 (Ctriple v) (k+1) [true] ([true,true]++tail b)
  have h1' : run0 (machine v) (3*(k+1)) (full k b) =
      some ⟨2,[true,false,true,true]++rep P k++[true],[true,true]++tail b⟩ := by
    simpa only [full,rep,List.nil_append,List.append_assoc,P,List.cons_append] using h1
  have h2 := fullTail v (rep P k++[true]) b
  have h2' : run0 (machine v) 14 ⟨2,[true,false,true,true]++rep P k++[true],[true,true]++tail b⟩ =
      some ⟨1,rep P k++[true],rep U 2++[true,true]⟩ := by
    simpa only [List.append_assoc] using h2
  obtain ⟨t,z,ht,hr,hz⟩ := resume v k 1 [] false Blocks.nil
  have hr' : run0 (machine v) t ⟨1,rep P k++[true],rep U 2++[true,true]⟩ = some z := by
    simpa only [tail,Bool.false_eq_true,if_false,List.append_nil] using hr
  exact ⟨3*(k+1)+14+t,z,by omega,join0 (join0 h1' h2') hr',hz⟩

theorem carry_next (v : Variant) (k : Nat) (w : List Bool) (b : Bool) (hw : Blocks w) :
    ∃ t z, 0<t ∧ run0 (machine v) t (carry k w b) = some z ∧ Good z := by
  have h1 := sweepR (machine v) 2 [true] [] U P 3 (Ctriple v) (k+1) ([true]++w) ([true]++tail b)
  have h1' : run0 (machine v) (3*(k+1)) (carry k w b) =
      some ⟨2,[true,false,true,true]++rep P k++[true]++w,[true]++tail b⟩ := by
    simpa only [carry,rep,List.nil_append,List.append_assoc,P,List.cons_append] using h1
  have h2 := carryTail v (rep P k++[true]++w) b
  have h2' : run0 (machine v) (carryCost v) ⟨2,[true,false,true,true]++rep P k++[true]++w,[true]++tail b⟩ =
      some ⟨1,rep P k++[true]++w,rep U 1++[true,true]++[false]⟩ := by
    simpa only [List.append_assoc] using h2
  obtain ⟨t,z,ht,hr,hz⟩ := resume v k 0 w true hw
  have hr' : run0 (machine v) t ⟨1,rep P k++[true]++w,rep U 1++[true,true]++[false]⟩ = some z := hr
  exact ⟨3*(k+1)+carryCost v+t,z,by omega,join0 (join0 h1' h2') hr',hz⟩

theorem next (v : Variant) {z : Z0} (h : Good z) :
    ∃ t z', 0<t ∧ run0 (machine v) t z = some z' ∧ Good z' := by
  cases h with
  | full k b => exact full_next v k b
  | carry k w b hw => exact carry_next v k w b hw

theorem entry (v : Variant) : run0 (machine v) 11 ⟨0,[],[]⟩ = some (carry 0 [] false) := by
  cases v <;> rfl

theorem never (v : Variant) (m : Machine) (hm : compatible (machine v) m) : NeverHalts m := by
  have arbitrary : ∀ k, ∃ t z, k≤t ∧ run0 (machine v) t ⟨0,[],[]⟩ = some z ∧ Good z := by
    intro k
    induction k with
    | zero => exact ⟨11,carry 0 [] false,by omega,entry v,Good.carry _ _ _ Blocks.nil⟩
    | succ k ih =>
      obtain ⟨t,z,ht,hr,hz⟩ := ih
      obtain ⟨d,z',hd,hs,hz'⟩ := next v hz
      exact ⟨t+d,z',by omega,join0 hr hs,hz'⟩
  intro n
  obtain ⟨t,z,ht,hr,hz⟩ := arbitrary n
  have hproj : (BB6Coverage.Agent50Zipper.zrun (machine v) t start).map project = some z :=
    (run_project (machine v) t start).trans hr
  cases h : BB6Coverage.Agent50Zipper.zrun (machine v) t start with
  | none => simp [h] at hproj
  | some z' =>
    have H := BB6Coverage.Agent50Zipper.zrun_sound (machine v) m hm t start z' h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

namespace A
def table := machine .a
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  CounterVariants.never .a m hm
end A
namespace B
def table := machine .b
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  CounterVariants.never .b m hm
end B
namespace D
def table := machine .d
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  CounterVariants.never .d m hm
end D
#print axioms never
end BB6.Agent19Raw40.CounterVariants
