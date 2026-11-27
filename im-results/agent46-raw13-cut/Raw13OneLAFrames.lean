import Raw13TapeValue

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13OneLAFrames
open BB6Coverage BB6Coverage.Agent31Pump
open BB6.Agent46Raw13Frames (E pair pairs ones zeros pairs_append ones_add zeros_add rep_ones rep_single mixed_prefix)
open BB6.Agent46Raw13TapeValue (val nv NConf headBool headVal tailVal val_pad)

def p : PartialMachine := FAR.fromCodes [7,14,11,5,2,19,22,0,2,13,10,24]
def F (b : Bool) (L U : List Bool) : Z0 := ⟨0,L,[false,true,b]++pairs U⟩
def B := [true,false,false,false]
def Path (x y : Z0) : Prop := ∃ k, 0<k ∧ run0 p k x = some y

theorem join {a b c : Z0} (h : Path a b) (g : Path b c) : Path a c := by
  obtain ⟨k,hk,hr⟩ := h
  obtain ⟨j,hj,hs⟩ := g
  exact ⟨k+j,by omega,join0 hr hs⟩

theorem a11 (L R : List Bool) :
    run0 p 2 ⟨0,[]++[true,true]++L,[]++R⟩ = some ⟨0,[]++L,[]++[false,true]++R⟩ := rfl

theorem a1000 (L R : List Bool) :
    run0 p 4 ⟨0,[]++B++L,[]++R⟩ = some ⟨0,[]++L,[]++[true,true,true,true]++R⟩ := rfl

theorem a1001 (L R : List Bool) :
    run0 p 6 ⟨0,true::false::false::true::L,R⟩ = some ⟨0,false::true::L,false::true::R⟩ := rfl

theorem b_one (L R : List Bool) :
    run0 p 1 ⟨1,[true]++L,[]++[true]++R⟩ = some ⟨1,[true]++[false]++L,[]++R⟩ := rfl

theorem a0_back (n : Nat) (L U : List Bool) (c : Bool) :
    run0 p (n+3) ⟨0,false::L,ones n ++ [false,true,c] ++ pairs U⟩ =
      some (E c (zeros n++true::L) U) := by
  cases n with
  | zero => rfl
  | succ n =>
    have h1 : run0 p 1 ⟨0,false::L,ones (n+1) ++ [false,true,c] ++ pairs U⟩ =
        some ⟨1,true::true::L,ones n ++ [false,true,c] ++ pairs U⟩ := rfl
    have h2 := sweepR p 1 [true] [] [true] [false] 1 b_one n (true::L) ([false,true,c]++pairs U)
    have h2' : run0 p n ⟨1,true::true::L,ones n ++ [false,true,c] ++ pairs U⟩ =
        some ⟨1,true::(zeros n++true::L),[false,true,c]++pairs U⟩ := by
      simpa only [rep_single,ones,zeros,Nat.one_mul,List.nil_append,List.cons_append,List.singleton_append,List.append_assoc] using h2
    have h3 : run0 p 3 ⟨1,true::(zeros n++true::L),[false,true,c]++pairs U⟩ =
        some (E c (zeros (n+1)++true::L) U) := rfl
    simpa only [show 1+n+3=n+1+3 by omega] using join0 (join0 h1 h2') h3

theorem preRun (n : Nat) (b : Bool) (L U : List Bool) :
    run0 p (4*n) (F b (rep B n++L) U) = some ⟨0,L,ones (4*n)++[false,true,b]++pairs U⟩ := by
  have h := sweepL p 0 [] [] B [true,true,true,true] 4 a1000 n L ([false,true,b]++pairs U)
  simpa only [F,rep_ones,List.nil_append,List.append_assoc] using h

theorem carryFrame (n : Nat) (b : Bool) (L U : List Bool) :
    Path (F b (rep B n++false::L) U) (E b (zeros (4*n)++true::L) U) := by
  exact ⟨4*n+(4*n+3),by omega,join0 (preRun n b (false::L) U) (a0_back (4*n) L U b)⟩

theorem e0 (X U : List Bool) : Path (E false X U) (F true X U) := ⟨3,by decide,rfl⟩

theorem consumePair (b : Bool) (L U : List Bool) : Path (F b (true::true::L) U) (F false L (b::U)) := ⟨2,by decide,rfl⟩
theorem consumeSpecial (b : Bool) (L U : List Bool) : Path (F b (true::false::false::true::L) U) (F false (false::true::L) (b::U)) := ⟨6,by decide,rfl⟩

theorem mixed_align (n : Nat) (b : Bool) (U : List Bool) :
    [false,true]++ones (4*(n+1))++[false,true,b]++pairs U =
      [false,true,true]++pairs (ones (2*n+1)++[false,b]++U) := by
  rw [← rep_ones,mixed_prefix]
  simp only [pairs_append,List.append_assoc]
  rfl

theorem mixed11 (n : Nat) (b : Bool) (L U : List Bool) :
    Path (F b (rep B (n+1)++true::true::L) U) (F true L (ones (2*n+1)++[false,b]++U)) := by
  have h1 := preRun (n+1) b (true::true::L) U
  have h2 := a11 L (ones (4*(n+1))++[false,true,b]++pairs U)
  refine ⟨4*(n+1)+2,by omega,?_⟩
  have h := join0 h1 h2
  have ha := mixed_align n b U
  simp only [List.append_assoc] at ha
  simpa only [F,List.nil_append,List.append_assoc,ha] using h

theorem mixed1001 (n : Nat) (b : Bool) (L U : List Bool) :
    Path (F b (rep B (n+1)++true::false::false::true::L) U) (F true (false::true::L) (ones (2*n+1)++[false,b]++U)) := by
  have h1 := preRun (n+1) b (true::false::false::true::L) U
  have h2 := a1001 L (ones (4*(n+1))++[false,true,b]++pairs U)
  refine ⟨4*(n+1)+6,by omega,?_⟩
  have h := join0 h1 h2
  have ha := mixed_align n b U
  simp only [List.append_assoc,List.cons_append,List.nil_append] at ha ⊢
  simpa only [F,List.nil_append,List.cons_append,List.append_assoc,ha] using h

inductive IncResult where
  | even : List Bool → IncResult
  | odd : List Bool → IncResult
  deriving DecidableEq, Repr

def inc : List Bool → IncResult
  | [] => .even [true]
  | false::U => .even (true::U)
  | [true] => .odd [true]
  | [true,_] => .odd [false,true]
  | true::_::false::U => .even (false::false::true::U)
  | true::_::true::U => match inc U with
    | .even V => .even (false::false::false::V)
    | .odd V => .odd (false::false::false::V)

def target (X : List Bool) : IncResult → Z0
  | .even V => F false X V
  | .odd V => F false (true::X) V

theorem e_false (X U : List Bool) : Path (E true X (false::U)) (F false X (true::U)) := ⟨9,by decide,rfl⟩
theorem e_empty (X : List Bool) : Path (E true X []) (F false X [true]) := ⟨13,by decide,rfl⟩
theorem e_single (X : List Bool) : Path (E true X [true]) (E false (ones 3++X) []) := ⟨5,by decide,rfl⟩
theorem e_double (c : Bool) (X : List Bool) : Path (E true X [true,c]) (F false (ones 3++X) [true]) := ⟨if c then 14 else 18,by cases c <;> decide,by cases c <;> rfl⟩
theorem e_triple (c d : Bool) (X U : List Bool) : Path (E true X (true::c::d::U)) (E d (ones 6++X) U) := ⟨if c then 10 else 14,by cases c <;> decide,by cases c <;> cases d <;> rfl⟩

theorem threePairs (b : Bool) (X U : List Bool) : Path (F b (ones 6++X) U) (F false X (false::false::b::U)) := by
  exact ⟨6,by decide,rfl⟩

theorem increment (U X : List Bool) : Path (E true X U) (target X (inc U)) := by
  match U with
  | [] => exact e_empty X
  | false::U => exact e_false X U
  | [true] => exact join (e_single X) (join (e0 (ones 3++X) []) (consumePair true (true::X) []))
  | [true,c] => exact join (e_double c X) (consumePair false (true::X) [true])
  | true::c::false::U => exact join (e_triple c false X U) (join (e0 (ones 6++X) U) (threePairs true X U))
  | true::c::true::U =>
    have h := increment U (ones 6++X)
    cases e : inc U with
    | even V =>
      simp only [inc,e,target]
      exact join (e_triple c true X U) (join (by simpa [e,target] using h) (threePairs false X V))
    | odd V =>
      simp only [inc,e,target]
      have h' : Path (E true (ones 6++X) U) (F false (ones 6++true::X) V) := by
        rw [e,target] at h
        exact h
      exact join (e_triple c true X U) (join h' (threePairs false (true::X) V))
termination_by U.length

def stepN (z : NConf) : Option NConf := do
  let mv ← (p (z.q,z.l%2=1)).join
  if mv.right then return ⟨mv.next,z.r%2+2*(mv.write.toNat+2*(z.l/2)),z.r/2⟩
  else return ⟨mv.next,z.l/2,mv.write.toNat+2*z.r⟩

theorem step_project (z : Z0) : stepN (nv z) = (step0 p z).map nv := by
  obtain ⟨q,l,r⟩ := z
  unfold stepN step0 nv
  simp only [headBool]
  cases h : p (q,l.headD false) with
  | none => rfl
  | some o =>
    cases o with
    | none => rfl
    | some mv =>
      cases hh : mv.right <;> simp [h,hh,move0,nv,val,headVal,tailVal]; cases r with | nil => rfl | cons b r => exact (headVal (b::r)).symm

def runN : Nat → NConf → Option NConf
  | 0,z => some z
  | n+1,z => (stepN z).bind (runN n)

theorem project_run (n : Nat) (z : Z0) : runN n (nv z) = (run0 p n z).map nv := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    rw [runN,step_project,run0]
    cases h : step0 p z with
    | none => rfl
    | some z' => simpa only [Option.map_some,Option.bind_some] using ih z'

theorem runN_add (n m : Nat) (z : NConf) : runN (n+m) z = (runN n z).bind (runN m) := by
  induction n generalizing z with
  | zero => simp [runN]
  | succ n ih =>
    rw [show n+1+m=n+m+1 by omega,runN,runN]
    cases h : stepN z with
    | none => rfl
    | some z' => simpa only [Option.bind_some] using ih z'

def Reach (x y : NConf) : Prop := ∃ k, 0<k ∧ runN k x = some y

theorem reach_trans {a b c : NConf} (h : Reach a b) (g : Reach b c) : Reach a c := by
  obtain ⟨k,hk,hr⟩ := h
  obtain ⟨j,hj,hs⟩ := g
  exact ⟨k+j,by omega,by rw [runN_add,hr,Option.bind_some,hs]⟩

theorem path_reach {a b : Z0} (h : Path a b) : Reach (nv a) (nv b) := by
  obtain ⟨k,hk,hr⟩ := h
  exact ⟨k,hk,by rw [project_run,hr];rfl⟩

def FN (b : Bool) (L U : List Bool) := nv (F b L U)

theorem pad (b : Bool) (L U : List Bool) (n : Nat) : FN b (L++zeros n) U = FN b L U := by
  simp [FN,F,nv,val_pad]

theorem seed : runN 70 (nv ⟨0,[],[]⟩) = some (FN false [] [true,true,false,true]) := by decide

#print axioms increment
#print axioms seed
end BB6.Agent46Raw13OneLAFrames
