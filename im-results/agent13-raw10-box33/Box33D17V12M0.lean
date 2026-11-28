import Box33PrefixMacro
namespace BB6.Agent13.Box33D17V12M0
open C9Pair
open BB6.Agent13.Box33D14Growth (z word rep rep_add rep_succ rep_zero word_cons word_nil cfg)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
abbrev A := cfg .A
abbrev ones := rep [true]
abbrev zeros := rep [false]
abbrev L := rep [true,false,false]
abbrev R := rep [true,false,true]
abbrev T := rep [false,false,true]
def step (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (left .A true c)
  | .B,false => some (left .C true c)
  | .B,true => some (right .F false c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (left .C true c)
  | .E,false => some (right .C true c)
  | .E,true => none
  | .F,false => some (right .A true c)
  | .F,true => some (right .F false c)
abbrev run := BB6.Agent13.Box33PrefixMacro.run step
theorem run_add (m n : Nat) (c : Config) : run (m+n) c = (run m c).bind (run n) := BB6.Agent13.Box33PrefixMacro.run_add step m n c

theorem lblock (l r : Stream) : run 5 (A (L 1 l) (zeros 2 r)) = some (A l (zeros 2 (R 1 r))) := by
  simp [A,cfg,L,R,zeros,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem lsweep (n : Nat) (l r : Stream) : run (5*n) (A (L n l) (zeros 2 r)) = some (A l (zeros 2 (R n r))) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [show 5*(n+1)=5+5*n by omega,run_add]
    change (run 5 (A (L 1 (L n l)) (zeros 2 r))).bind _ = _
    rw [lblock,Option.bind_some,ih,show R (n+1) r=R n (R 1 r) from rep_add _ _ _ _]
theorem lturn (l r : Stream) : run 5 (A (R 1 l) (zeros 2 r)) = some (A l (word [true,false] (R 1 r))) := by
  simp [A,cfg,R,zeros,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem leftPhase (n : Nat) (l : Stream) : run (5*n+5) (A (L n (R 1 l)) z) = some (A l (word [true,false] (R (n+1) z))) := by
  have h := lsweep n (R 1 l) z
  have e : zeros 2 z=z := by simp [zeros,rep,word]
  rw [e] at h
  rw [run_add,h,Option.bind_some,lturn]
  rfl

theorem aone (l r : Stream) : run 1 (A (push true l) (push true r)) = some (A l (ones 2 r)) := by
  rfl
theorem asweep (k : Nat) (l r : Stream) : run k (A (ones k l) (push true r)) = some (A l (ones (k+1) r)) := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
    rw [show k+1=1+k by omega,run_add,show ones (1+k) l=ones 1 (ones k l) from rep_add _ _ _ _]
    change (run 1 (A (push true (ones k l)) (push true r))).bind _ = _
    rw [aone,Option.bind_some]
    change run k (A (ones k l) (push true (push true r))) = _
    rw [ih,show 1+k+1=k+1+1 by omega,show ones (k+1+1) r=ones (k+1) (ones 1 r) from rep_add _ _ _ _]
    rfl

theorem azero (l r : Stream) : run 1 (A (push false l) (push true r)) = some (A l (word [false,true] r)) := by rfl
abbrev F := cfg .F
theorem fstep (l r : Stream) : run 1 (F l (push true r)) = some (F (push false l) r) := by rfl
theorem fsweep (k : Nat) (l r : Stream) : run k (F l (ones k r)) = some (F (zeros k l) r) := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih =>
    rw [show k+1=1+k by omega,run_add,show ones (1+k) r=ones 1 (ones k r) from rep_add _ _ _ _]
    change (run 1 (F l (push true (ones k r)))).bind _ = _
    rw [fstep,Option.bind_some,ih,show 1+k=k+1 by omega,show zeros (k+1) l=zeros k (zeros 1 l) from rep_add _ _ _ _]
    rfl
theorem fstart (l r : Stream) : run 2 (A l (word [false,true] r)) = some (F (word [false,true] l) r) := by rfl
theorem ffinish (l r : Stream) : run 1 (F l (push false r)) = some (A (push true l) r) := by rfl

theorem carry (k : Nat) (l r : Stream) :
  run (2*k+4) (A (ones k (push false l)) (word [true,false] r)) =
    some (A (word [true,false] (zeros k (push true l))) r) := by
  rw [show 2*k+4=k+1+2+k+1 by omega,run_add,run_add,run_add,run_add]
  rw [show word [true,false] r=push true (push false r) by rfl,asweep,Option.bind_some]
  rw [show ones (k+1) (push false r)=push true (ones k (push false r)) by rfl,azero,Option.bind_some,fstart,Option.bind_some,fsweep,Option.bind_some,ffinish]
  have he : zeros k (word [false,true] l) = push false (zeros k (push true l)) := by
    change zeros k (zeros 1 (push true l)) = zeros 1 (zeros k (push true l))
    rw [←show zeros (k+1) (push true l)=zeros k (zeros 1 (push true l)) from rep_add _ _ _ _,←show zeros (1+k) (push true l)=zeros 1 (zeros k (push true l)) from rep_add _ _ _ _,show k+1=1+k by omega]
  rw [he]
  rfl

theorem rstart (l r : Stream) : run 6 (A (word [true,false] l) (R 1 r)) = some (A (word [true,false,false,true] l) (push true r)) := by
  simp [A,cfg,R,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem rblock (l r : Stream) : run 7 (A (word [true,false] l) (push true (R 1 r))) = some (A (word [true,false,false,false,true] l) (push true r)) := by
  simp [A,cfg,R,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem rsweep (n : Nat) (l r : Stream) : run (7*n) (A (word [true,false] l) (push true (R n r))) = some (A (word [true,false] (T n l)) (push true r)) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [show 7*(n+1)=7+7*n by omega,run_add]
    change (run 7 (A (word [true,false] l) (push true (R 1 (R n r))))).bind _ = _
    rw [rblock,Option.bind_some]
    change run (7*n) (A (word [true,false] (T 1 l)) (push true (R n r))) = _
    rw [ih,show T (n+1) l=T n (T 1 l) from rep_add _ _ _ _]
theorem rend (l : Stream) : run 6 (A (word [true,false] l) (push true z)) = some (A (word [true,false,false,true] l) z) := by
  simp [A,cfg,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem shift (n : Nat) (l : Stream) : push true (T n (word [false,true] l)) = L n (R 1 l) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change word [true,false,false] (push true (T n (word [false,true] l))) = L (n+1) (R 1 l)
    rw [ih]
    rfl

theorem rightPhase (n : Nat) (l : Stream) : run (6+7*n+6) (A (word [true,false] l) (R (n+1) z)) = some (A (L (n+1) (R 1 l)) z) := by
  rw [run_add,run_add]
  change ((run 6 (A (word [true,false] l) (R 1 (R n z)))).bind _).bind _ = _
  rw [rstart,Option.bind_some]
  change (run (7*n) (A (word [true,false] (word [false,true] l)) (push true (R n z)))).bind _ = _
  rw [rsweep,Option.bind_some,rend]
  change some (A (word [true,false,false] (push true (T n (word [false,true] l)))) z) = _
  rw [shift]
  rfl

theorem grow (n k : Nat) (l : Stream) :
  run (5*n+5+(2*k+4)+(6+7*n+6)) (A (L n (R 1 (ones k (push false l)))) z) =
    some (A (L (n+1) (R 1 (zeros k (push true l)))) z) := by
  rw [run_add,run_add,leftPhase,Option.bind_some,carry,Option.bind_some,rightPhase]

inductive Finite : Stream → Prop
  | blank : Finite z
  | cons (b : Bool) {s : Stream} : Finite s → Finite (push b s)
theorem split {s : Stream} (h : Finite s) : ∃ k l, Finite l ∧ s=ones k (push false l) := by
  induction h with
  | blank => exact ⟨0,z,.blank,by simp [ones,rep,word]⟩
  | @cons b s h ih =>
    cases b
    · exact ⟨0,s,h,rfl⟩
    · obtain ⟨k,l,hl,he⟩ := ih
      exact ⟨k+1,l,hl,by rw [he]; rfl⟩
theorem finite_zeros (k : Nat) {s : Stream} (h : Finite s) : Finite (zeros k s) := by
  induction k with
  | zero => exact h
  | succ k ih => exact .cons false ih

theorem never (t n : Nat) (b : Stream) (hb : Finite b) : run t (A (L n (R 1 b)) z) ≠ none := by
  induction t using Nat.strongRecOn generalizing n b with
  | ind t ih =>
    obtain ⟨k,l,hl,rfl⟩ := split hb
    intro hn
    let d := 5*n+5+(2*k+4)+(6+7*n+6)
    have hd : 0<d := by dsimp [d]; omega
    have hr := grow n k l
    change run d _ = _ at hr
    by_cases h : t≤d
    · rw [←show t+(d-t)=d by omega,run_add,hn] at hr; contradiction
    · rw [←show d+(t-d)=t by omega,run_add,hr,Option.bind_some] at hn
      exact ih (t-d) (by omega) (n+1) _ (finite_zeros k (.cons true hl)) hn

theorem init : run 13 (A z z) = some (A (R 1 (R 1 z)) z) := by
  simp [A,cfg,R,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem neverBlank (t : Nat) : run t (A z z) ≠ none := by
  intro hn
  have hr := init
  by_cases h : t≤13
  · rw [←show t+(13-t)=13 by omega,run_add,hn] at hr; contradiction
  · rw [←show 13+(t-13)=t by omega,run_add,hr,Option.bind_some] at hn
    exact never (t-13) 0 _ (.cons true (.cons false (.cons true .blank))) hn
#print axioms neverBlank
open BB6Coverage
open Box17 (index decode)
def codes  : List (Fin 25) := [8,3,11,22,1,13,17,11,12,0,4,22]
def table  : Machine := fun a => decode (codes.getD (index a).val 0)
theorem project_step  (c : BB6Coverage.Config) :
    (rawStep table c).map BB6.Agent13.Box33PrefixMacro.project = step (BB6.Agent13.Box33PrefixMacro.project c) := by
  rw [BB6.Agent13.Box33PrefixMacro.map_step]
  rcases c with ⟨q,p,t⟩
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t p <;>
    simp only [readSlot,Box33Source.project,hb] <;> rfl
theorem source_never : NeverHalts table := by
  apply BB6.Agent13.Box33PrefixMacro.sourceNever table step project_step
  intro n
  have hb : BB6.Agent13.Box33PrefixMacro.project BB6Coverage.blank = A z z := by
    change Box33Source.project false BB6Coverage.blank = A z z
    rw [Box33Source.project_blank false]
    simp [A,cfg,Box33UnarySweeper.blank] <;> rfl
  rw [hb]
  exact neverBlank n
def partialTable  : PartialMachine := fun a => some (table a)
theorem compatible_never  (m : Machine) (hm : compatible (partialTable) m) : NeverHalts m := by
  have he : m = table := funext fun a => hm a _ rfl
  rw [he]
  exact source_never
#print axioms compatible_never
end BB6.Agent13.Box33D17V12M0
