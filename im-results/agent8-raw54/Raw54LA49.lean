import Raw54RAClosedCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.LA.M49
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent8Raw54.RAClosed

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,false,3⟩)
  | _,_ => none

def R (k : Nat) : List Bool := true :: (rep [true,true] k ++ [false,true,false])
def stack : List Bool → List Bool
  | [] => [true]
  | b::w => b::false::stack w

theorem resetCore (k : Nat) (L : List Bool) :
    run0 table (2*k+7) ⟨1,[true,true]++L,rep [true,true] k ++ [false,true,false]⟩ =
      some ⟨0,rep [false,false] k ++ true::L,R 0⟩ := by
  have h : run0 table (2*k) ⟨1,[true,true]++L,rep [true,true] k ++ [false,true,false]⟩ =
      some ⟨1,true::(rep [false,false] k ++ true::L),[false,true,false]⟩ :=
    sweepR table 1 [true] [] [true,true] [false,false] 2 (fun _ _ => rfl) k (true::L) [false,true,false]
  have g (T : List Bool) : run0 table 7 ⟨1,true::T,[false,true,false]⟩ = some ⟨0,T,R 0⟩ := by rfl
  exact join0 h (g _)

theorem resetZero (k : Nat) (L : List Bool) :
    run0 table (2*k+8) ⟨0,false::L,R k⟩ = some ⟨0,rep [false,false] k ++ true::L,R 0⟩ := by
  have h : run0 table 1 ⟨0,false::L,R k⟩ =
      some ⟨1,[true,true]++L,rep [true,true] k ++ [false,true,false]⟩ := by rfl
  have g := join0 h (resetCore k L)
  rwa [show 1+(2*k+7)=2*k+8 by omega] at g

theorem resetEmpty (k : Nat) :
    run0 table (2*k+8) ⟨0,[],R k⟩ = some ⟨0,rep [false,false] k ++ [true],R 0⟩ := by
  have h : run0 table 1 ⟨0,[],R k⟩ =
      some ⟨1,[true,true],rep [true,true] k ++ [false,true,false]⟩ := by rfl
  have g := join0 h (resetCore k [])
  rwa [show 1+(2*k+7)=2*k+8 by omega] at g

theorem pop (k : Nat) (L : List Bool) :
    run0 table 2 ⟨0,true::false::L,R k⟩ = some ⟨0,L,R (k+1)⟩ := by rfl

theorem popLast (k : Nat) :
    run0 table 2 ⟨0,[true],R k⟩ = some ⟨0,[],R (k+1)⟩ := by rfl

theorem stackRep (k : Nat) (w : List Bool) :
    stack (List.replicate k false ++ w) = rep [false,false] k ++ stack w := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ,List.cons_append,stack,rep,List.cons_append,List.nil_append,ih]

def sect (s : Option (List Bool) × Nat) : Z0 :=
  ⟨0,s.1.elim [] stack,R s.2⟩

theorem sectionReturn (s : Option (List Bool) × Nat) :
    ∃ t s', 0 < t ∧ run0 table t (sect s) = some (sect s') := by
  rcases s with ⟨w,k⟩
  cases w with
  | none =>
    refine ⟨2*k+8,(some (List.replicate k false),0),by omega,?_⟩
    have h : stack (List.replicate k false) = rep [false,false] k ++ [true] := by
      simpa only [List.append_nil,stack] using stackRep k []
    change run0 table (2*k+8) ⟨0,[],R k⟩ = some ⟨0,stack (List.replicate k false),R 0⟩
    rw [h]
    exact resetEmpty k
  | some w =>
    cases w with
    | nil => exact ⟨2,(none,k+1),by decide,popLast k⟩
    | cons b w =>
      cases b with
      | false =>
        refine ⟨2*k+8,(some (List.replicate k false ++ true::w),0),by omega,?_⟩
        simpa only [sect,Option.elim,stackRep,stack] using resetZero k (false::stack w)
      | true => exact ⟨2,(some w,k+1),by decide,pop k (stack w)⟩

theorem entry : run0 table 30 ⟨0,[],[]⟩ = some (sect (some [false,false],0)) := by rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  neverOfSection table _ sect (some [false,false],0) 30 entry sectionReturn m hm
#print axioms sectionReturn
#print axioms never
end BB6.Agent8Raw54.LA.M49
