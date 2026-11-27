import Agent46OpenLeftSweep
import Agent46CounterCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Auto.Raw36Counter1
open BB6Coverage Agent31Pump Auto Agent50Zipper
def p0 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨false,false,3⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => none
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none
def normIn : PZ := ⟨0,(.periodic [] [true,true,true] (.lit [true,true,false])),(.lit [false,true,false,false,false])⟩
def normOut : PZ := ⟨0,(.periodic [] [true,true,false] (.lit [true,true,true])),(.lit [false,true,false,false,false])⟩
def normOps : List Action := ([.left [] [] [true,true,true] [false,false,true] (.lit [true,true,false]) (.lit [false,true,false,false,false]) 3] ++
    List.replicate 3 .step ++
    [.right [false] [true] [false,false,true] [false,true,true] (.lit [true]) (.lit [false,true,false,false,false]) 5] ++
    List.replicate 21 .step)
def normActual : Result := ⟨⟨0,(.periodic [true,true] [false,true,true] (.lit [true])),(.lit [false,true,false,false,false])⟩,8,24⟩
theorem normTrace : OpenLeft.traceRun p0 normOps normIn = some normActual := by decide
theorem normNorm : normActual.z.norm = normOut.norm := by decide
theorem normRun (n : Nat) (tail : List Bool) : run0 p0 (8*n+24) ((OpenLeft.attachZ normIn tail).eval n) = some ((OpenLeft.attachZ normOut tail).eval n) := by
  have h := OpenLeft.traceRun_sound p0 normOps normTrace n tail
  have hh := congrArg (fun z => (OpenLeft.attachZ z tail).eval n) normNorm
  rw [OpenLeft.norm_attachZ_eval,OpenLeft.norm_attachZ_eval] at hh
  rw [hh] at h
  exact h
def over0In : PZ := ⟨0,(.periodic [true,true,true] [true,true,true] (.lit [])),(.lit [false,true,false,false,false])⟩
def over0Out : PZ := ⟨0,(.periodic [] [true,true,false] (.lit [true,true,true,true])),(.lit [false,true,false,false,false])⟩
def over0Ops : List Action := ([.left [true,true,true] [] [true,true,true] [false,false,true] (.lit []) (.lit [false,true,false,false,false]) 3] ++
    List.replicate 5 .step ++
    [.right [false] [true] [false,false,true] [false,true,true] (.lit [true,true]) (.lit [false,true,false,false,false]) 5] ++
    List.replicate 21 .step)
def over0Actual : Result := ⟨⟨0,(.periodic [true,true] [false,true,true] (.lit [true,true])),(.lit [false,true,false,false,false])⟩,8,26⟩
theorem over0Trace : Auto.traceRun p0 over0Ops over0In = some over0Actual := by decide
theorem over0Norm : over0Actual.z.norm = over0Out.norm := by decide
theorem over0Run (n : Nat) : run0 p0 (8*n+26) (over0In.eval n) = some (over0Out.eval n) := by
  have h := Auto.traceRun_sound p0 over0Ops over0Trace n
  have hh := congrArg (fun z : PZ => z.eval n) over0Norm
  rw [PZ.norm_sound,PZ.norm_sound] at hh
  rw [hh] at h
  exact h
def over1In : PZ := ⟨0,(.periodic [] [true,true,true] (.lit [true])),(.lit [false,true,false,false,false])⟩
def over1Out : PZ := ⟨0,(.periodic [] [true,true,false] (.lit [true,true,false])),(.lit [false,true,false,false,false])⟩
def over1Ops : List Action := ([.left [] [] [true,true,true] [false,false,true] (.lit [true]) (.lit [false,true,false,false,false]) 3] ++
    List.replicate 3 .step ++
    [.right [false] [true] [false,false,true] [false,true,true] (.lit [false]) (.lit [false,true,false,false,false]) 5] ++
    List.replicate 21 .step)
def over1Actual : Result := ⟨⟨0,(.periodic [true,true] [false,true,true] (.lit [false])),(.lit [false,true,false,false,false])⟩,8,24⟩
theorem over1Trace : Auto.traceRun p0 over1Ops over1In = some over1Actual := by decide
theorem over1Norm : over1Actual.z.norm = over1Out.norm := by decide
theorem over1Run (n : Nat) : run0 p0 (8*n+24) (over1In.eval n) = some (over1Out.eval n) := by
  have h := Auto.traceRun_sound p0 over1Ops over1Trace n
  have hh := congrArg (fun z : PZ => z.eval n) over1Norm
  rw [PZ.norm_sound,PZ.norm_sound] at hh
  rw [hh] at h
  exact h
def shape : Counter.Shape := ⟨0,[],[],[true,true,false],[true,true,true],[],[]⟩
def terminal (ph : Bool) : List Bool := if ph then [true] else []
def frame (ph : Bool) (bs : List Bool) : Z0 := ⟨0,Counter.encode shape bs ++ terminal ph,[false,true,false,false,false]⟩

theorem normal (ph : Bool) (k : Nat) (rest : List Bool) :
    run0 p0 (8*k+24) (frame ph (rep [true] k ++ false::rest)) = some (frame ph (rep [false] k ++ true::rest)) := by
  have h := normRun k (Counter.encode shape rest ++ terminal ph)
  simpa [normIn,normOut,OpenLeft.attachZ_eval,Word.eval,frame,Counter.encode_append,Counter.encode_rep,Counter.encode,shape,List.append_assoc] using h

theorem overflow0 (k : Nat) :
    run0 p0 (8*k+26) (frame false (true::rep [true] k)) = some (frame true (rep [false] k ++ [true])) := by
  have h := over0Run k
  simpa [over0In,over0Out,PZ.eval,Word.eval,frame,Counter.encode_append,Counter.encode_rep,Counter.encode,shape,terminal,List.append_assoc] using h

theorem overflow1 (k : Nat) :
    run0 p0 (8*k+24) (frame true (rep [true] k)) = some (frame false (rep [false] k ++ [false])) := by
  have h := over1Run k
  simpa [over1In,over1Out,PZ.eval,Word.eval,frame,Counter.encode_append,Counter.encode_rep,Counter.encode,shape,terminal,List.append_assoc] using h

def admissible (ph : Bool) (bs : List Bool) : Prop := ph = true ∨ bs ≠ []

theorem live (ph : Bool) (bs : List Bool) (ha : admissible ph bs) :
    ∃ t ph' bs', 0<t ∧ admissible ph' bs' ∧ run0 p0 t (frame ph bs) = some (frame ph' bs') := by
  obtain ⟨k,h⟩ := Counter.split_next [] bs
  rcases h with ⟨h,_⟩ | ⟨rest,h,_⟩
  · subst bs
    cases ph with
    | false =>
      cases k with
      | zero => simp [admissible,rep] at ha
      | succ k =>
        exact ⟨8*k+26,true,rep [false] k ++ [true],by omega,Or.inl rfl,by simpa [rep] using overflow0 k⟩
    | true => exact ⟨8*k+24,false,rep [false] k ++ [false],by omega,Or.inr (by simp),overflow1 k⟩
  · subst bs
    exact ⟨8*k+24,ph,rep [false] k ++ true::rest,by omega,Or.inr (by simp),normal ph k rest⟩

theorem seed : run0 p0 17 ⟨0,[],[]⟩ = some (frame true []) := by decide

theorem never (m : Machine) (hm : compatible p0 m) : NeverHalts m := by
  have arbitrary : ∀ k : Nat, ∃ t ph bs, k ≤ t ∧ admissible ph bs ∧ run0 p0 t ⟨0,[],[]⟩ = some (frame ph bs) := by
    intro k
    induction k with
    | zero => exact ⟨17,true,[],by omega,Or.inl rfl,seed⟩
    | succ k ih =>
      obtain ⟨t,ph,bs,ht,ha,hr⟩ := ih
      obtain ⟨d,ph',bs',hd,ha',hs⟩ := live ph bs ha
      exact ⟨t+d,ph',bs',by omega,ha',join0 hr hs⟩
  intro n
  obtain ⟨t,ph,bs,ht,_,hr⟩ := arbitrary n
  have hz : (zrun p0 t start).map project = some (frame ph bs) := (run_project p0 t start).trans hr
  cases h : zrun p0 t start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound p0 m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl
#print axioms never
end BB6Coverage.Agent31Pump.Auto.Raw36Counter1
