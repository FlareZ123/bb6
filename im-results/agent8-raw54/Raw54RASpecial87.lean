import Raw54RAClosedCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.RA.M87
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent8Raw54.RACounter BB6.Agent8Raw54.RAClosed
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none
def special : List Bool := [false,false,true,true,true,true]
inductive Digit where | z | o | s
def D : Digit → List Bool | .z => zero | .o => one | .s => special
def encD : List Digit → List Bool | [] => [] | d::w => D d ++ encD w
def preZ : Nat → List Digit → List Digit | 0,w => w | k+1,w => .z::preZ k w
theorem enc_preZ (k : Nat) (w : List Digit) : encD (preZ k w) = rep zero k ++ encD w := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [preZ,encD,D,ih,rep,List.append_assoc]
theorem inc (T : List Bool) : run0 table 8 (A (zero ++ T)) = some (A (mark ++ T)) := by rfl
theorem incS (T : List Bool) : run0 table 14 (A (special ++ T)) = some (A (mark ++ one ++ T)) := by rfl
theorem stopZero (n : Nat) (T : List Bool) : run0 table (8*n+20) ⟨0,[false,false],([false,true,true] ++ (rep [true,true,true] n ++ ([false,false,false] ++ T)))⟩ = some ⟨0,[false,false],([] ++ (rep [false,false,false] n ++ ([false,false,true,true,true,true] ++ T)))⟩ := by
  have h0 : run0 table (5*n) ⟨0,[false,false],([false,true,true] ++ (rep [true,true,true] n ++ ([false,false,false] ++ T)))⟩ = some ⟨0,([false] ++ (rep [true,true,true] n ++ [false])),([false,true,true,false,false,false] ++ T)⟩ := by
    exact sweepR table 0 [false] [false,true,true] [true,true,true] [true,true,true] 5 (fun _ _ => rfl) n [false] ([false,false,false] ++ T)
  have h1 : run0 table 17 ⟨0,([false] ++ (rep [true,true,true] n ++ [false])),([false,true,true,false,false,false] ++ T)⟩ = some ⟨4,([true,true] ++ (rep [true,true,true] n ++ [false])),([false,true,true,true,true] ++ T)⟩ := by rfl
  have g1 := join0 h0 h1
  have h2 : run0 table (3*n) ⟨4,([true,true] ++ (rep [true,true,true] n ++ [false])),([false,true,true,true,true] ++ T)⟩ = some ⟨4,[true,true,false],([] ++ (rep [false,false,false] n ++ ([false,true,true,true,true] ++ T)))⟩ := by
    exact sweepL table 4 [true,true] [] [true,true,true] [false,false,false] 3 (fun _ _ => rfl) n [false] ([false,true,true,true,true] ++ T)
  have g2 := join0 g1 h2
  have h3 : run0 table 3 ⟨4,[true,true,false],([] ++ (rep [false,false,false] n ++ ([false,true,true,true,true] ++ T)))⟩ = some ⟨0,[false,false],([false] ++ (rep [false,false,false] n ++ ([false,true,true,true,true] ++ T)))⟩ := by rfl
  have g3 := join0 g2 h3
  have e4 : (⟨0,[false,false],([false] ++ (rep [false,false,false] n ++ ([false,true,true,true,true] ++ T)))⟩ : Z0) = ⟨0,[false,false],([] ++ (rep [false,false,false] n ++ ([false,false,true,true,true,true] ++ T)))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [] ([false,true,true,true,true] ++ T) [false,false] false n)
  rw [e4] at g3
  rw [show (5*n)+17+(3*n)+3=8*n+20 by omega] at g3
  exact g3
theorem stopSpecial (n : Nat) (T : List Bool) : run0 table (8*n+26) ⟨0,[false,false],([false,true,true] ++ (rep [true,true,true] n ++ ([false,false,true,true,true,true] ++ T)))⟩ = some ⟨0,[false,false],([] ++ (rep [false,false,false] n ++ ([false,false,true,true,true,true,true,true,true] ++ T)))⟩ := by
  have h0 : run0 table (5*n) ⟨0,[false,false],([false,true,true] ++ (rep [true,true,true] n ++ ([false,false,true,true,true,true] ++ T)))⟩ = some ⟨0,([false] ++ (rep [true,true,true] n ++ [false])),([false,true,true,false,false,true,true,true,true] ++ T)⟩ := by
    exact sweepR table 0 [false] [false,true,true] [true,true,true] [true,true,true] 5 (fun _ _ => rfl) n [false] ([false,false,true,true,true,true] ++ T)
  have h1 : run0 table 23 ⟨0,([false] ++ (rep [true,true,true] n ++ [false])),([false,true,true,false,false,true,true,true,true] ++ T)⟩ = some ⟨4,([true,true] ++ (rep [true,true,true] n ++ [false])),([false,true,true,true,true,true,true,true] ++ T)⟩ := by rfl
  have g1 := join0 h0 h1
  have h2 : run0 table (3*n) ⟨4,([true,true] ++ (rep [true,true,true] n ++ [false])),([false,true,true,true,true,true,true,true] ++ T)⟩ = some ⟨4,[true,true,false],([] ++ (rep [false,false,false] n ++ ([false,true,true,true,true,true,true,true] ++ T)))⟩ := by
    exact sweepL table 4 [true,true] [] [true,true,true] [false,false,false] 3 (fun _ _ => rfl) n [false] ([false,true,true,true,true,true,true,true] ++ T)
  have g2 := join0 g1 h2
  have h3 : run0 table 3 ⟨4,[true,true,false],([] ++ (rep [false,false,false] n ++ ([false,true,true,true,true,true,true,true] ++ T)))⟩ = some ⟨0,[false,false],([false] ++ (rep [false,false,false] n ++ ([false,true,true,true,true,true,true,true] ++ T)))⟩ := by rfl
  have g3 := join0 g2 h3
  have e4 : (⟨0,[false,false],([false] ++ (rep [false,false,false] n ++ ([false,true,true,true,true,true,true,true] ++ T)))⟩ : Z0) = ⟨0,[false,false],([] ++ (rep [false,false,false] n ++ ([false,false,true,true,true,true,true,true,true] ++ T)))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [] ([false,true,true,true,true,true,true,true] ++ T) [false,false] false n)
  rw [e4] at g3
  rw [show (5*n)+23+(3*n)+3=8*n+26 by omega] at g3
  exact g3
theorem overflow (n : Nat) : run0 table (8*n+20) ⟨0,[false,false],([false,true,true] ++ (rep [true,true,true] n ++ []))⟩ = some ⟨0,[false,false],([] ++ (rep [false,false,false] n ++ [false,false,true,true,true,true]))⟩ := by
  have h0 : run0 table (5*n) ⟨0,[false,false],([false,true,true] ++ (rep [true,true,true] n ++ []))⟩ = some ⟨0,([false] ++ (rep [true,true,true] n ++ [false])),[false,true,true]⟩ := by
    exact sweepR table 0 [false] [false,true,true] [true,true,true] [true,true,true] 5 (fun _ _ => rfl) n [false] []
  have h1 : run0 table 17 ⟨0,([false] ++ (rep [true,true,true] n ++ [false])),[false,true,true]⟩ = some ⟨4,([true,true] ++ (rep [true,true,true] n ++ [false])),[false,true,true,true,true]⟩ := by rfl
  have g1 := join0 h0 h1
  have h2 : run0 table (3*n) ⟨4,([true,true] ++ (rep [true,true,true] n ++ [false])),[false,true,true,true,true]⟩ = some ⟨4,[true,true,false],([] ++ (rep [false,false,false] n ++ [false,true,true,true,true]))⟩ := by
    exact sweepL table 4 [true,true] [] [true,true,true] [false,false,false] 3 (fun _ _ => rfl) n [false] [false,true,true,true,true]
  have g2 := join0 g1 h2
  have h3 : run0 table 3 ⟨4,[true,true,false],([] ++ (rep [false,false,false] n ++ [false,true,true,true,true]))⟩ = some ⟨0,[false,false],([false] ++ (rep [false,false,false] n ++ [false,true,true,true,true]))⟩ := by rfl
  have g3 := join0 g2 h3
  have e4 : (⟨0,[false,false],([false] ++ (rep [false,false,false] n ++ [false,true,true,true,true]))⟩ : Z0) = ⟨0,[false,false],([] ++ (rep [false,false,false] n ++ [false,false,true,true,true,true]))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [] [false,true,true,true,true] [false,false] false n)
  rw [e4] at g3
  rw [show (5*n)+17+(3*n)+3=8*n+20 by omega] at g3
  exact g3
theorem norm (k : Nat) (w : List Digit) : ∃ t w', 0<t ∧
    run0 table t (A (rep zero k ++ special ++ encD w)) = some (A (mark ++ encD w')) := by
  cases k with
  | zero =>
    refine ⟨14,.o::w,by omega,?_⟩
    simpa only [rep,List.nil_append,encD,D,List.append_assoc] using incS (encD w)
  | succ k =>
    refine ⟨8,preZ k (.s::w),by omega,?_⟩
    simpa only [rep,enc_preZ,encD,D,List.append_assoc] using inc (rep zero k ++ special ++ encD w)

theorem returnSection (w : List Digit) (k : Nat) : ∃ t w', 0<t ∧
    run0 table t (A (mark ++ rep one k ++ encD w)) = some (A (mark ++ encD w')) := by
  induction w generalizing k with
  | nil =>
    obtain ⟨t,w',ht,h⟩ := norm k []
    have g : run0 table (8*k+20) (A (mark ++ rep one k)) = some (A (rep zero k ++ special)) := by
      simpa only [A,mark,one,zero,special,List.append_nil,List.nil_append] using overflow k
    refine ⟨8*k+20+t,w',by omega,?_⟩
    simpa only [encD,List.append_nil] using join0 g (by simpa only [encD,List.append_nil] using h)
  | cons d w ih =>
    cases d with
    | z =>
      obtain ⟨t,w',ht,h⟩ := norm k w
      have g : run0 table (8*k+20) (A (mark ++ rep one k ++ encD (.z::w))) = some (A (rep zero k ++ special ++ encD w)) := by
        simpa only [A,mark,one,zero,special,encD,D,List.append_assoc,List.nil_append] using stopZero k (encD w)
      exact ⟨8*k+20+t,w',by omega,join0 g h⟩
    | s =>
      obtain ⟨t,w',ht,h⟩ := norm k (.o::w)
      have g : run0 table (8*k+26) (A (mark ++ rep one k ++ encD (.s::w))) = some (A (rep zero k ++ special ++ encD (.o::w))) := by
        simpa only [A,mark,one,zero,special,encD,D,List.append_assoc,List.nil_append,List.cons_append] using stopSpecial k (encD w)
      exact ⟨8*k+26+t,w',by omega,join0 g h⟩
    | o =>
      obtain ⟨t,w',ht,h⟩ := ih (k+1)
      refine ⟨t,w',ht,?_⟩
      simpa only [encD,D,rep,← rep_snoc one k,List.append_assoc] using h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  apply neverOfSection table (List Digit) (fun w => A (mark ++ encD w)) [] 8 (by rfl) _ m hm
  intro w
  simpa only [rep,List.nil_append,List.append_nil] using returnSection w 0
#print axioms never
end BB6.Agent8Raw54.RA.M87
