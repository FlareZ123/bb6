import Box33PrefixMacro
namespace BB6.Agent13.Box33D17V12Unary
open C9Pair
open BB6.Agent13.Box33D14Growth (z word rep rep_add rep_succ rep_zero word_cons word_nil cfg)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
abbrev A := cfg .A
abbrev ones := rep [true]
abbrev blocks := rep [false,false,true]
namespace Triple
-- false = m4, true = m9.
def step (s : Bool) (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (right .F true c)
  | .B,false => some (left .C true c)
  | .B,true => some (right (if s then .E else .B) s c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (left (if s then .F else .E) false c)
  | .E,false => some (right .C true c)
  | .E,true => if s then none else some (left .C true c)
  | .F,false => some (right .A true c)
  | .F,true => if s then some (left .C true c) else none
abbrev run (s : Bool) := BB6.Agent13.Box33PrefixMacro.run (step s)
theorem run_add (s : Bool) (m n : Nat) (c : Config) : run s (m+n) c = (run s m c).bind (run s n) := BB6.Agent13.Box33PrefixMacro.run_add (step s) m n c
abbrev X (s : Bool) := cfg (if s then .F else .E)
abbrev cost (s : Bool) : Nat := if s then 8 else 10

theorem start (s : Bool) (l : Stream) : run s 4 (A (ones 2 l) z) = some (X s l (push true (blocks 1 z))) := by
  cases s <;> simp [A,X,cfg,ones,blocks,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem lblock (s : Bool) (l r : Stream) : run s 3 (X s (ones 3 l) (push true r)) = some (X s l (push true (blocks 1 r))) := by
  cases s <;> simp [X,cfg,ones,blocks,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem lsweep (s : Bool) (n : Nat) (l r : Stream) : run s (3*n) (X s (ones (3*n) l) (push true r)) = some (X s l (push true (blocks n r))) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [show 3*(n+1)=3+3*n by omega,show ones (3+3*n) l = ones 3 (ones (3*n) l) from rep_add _ _ _ _,run_add,lblock,Option.bind_some,ih]
    rw [show blocks (n+1) r=blocks n (blocks 1 r) from rep_add _ _ _ _]
theorem turn (s : Bool) (r : Stream) : run s 5 (X s (push true z) (push true r)) = some (A z (push true (blocks 1 r))) := by
  cases s <;> simp [A,X,cfg,ones,blocks,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem lbase (s : Bool) : run s 6 (A z z) = some (A z (push true (blocks 1 z))) := by
  cases s <;> simp [A,cfg,blocks,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem leftPhase (s : Bool) (k : Nat) : run s (6*k+6) (A (ones (6*k) z) z) = some (A z (push true (blocks (2*k+1) z))) := by
  cases k with
  | zero => exact lbase s
  | succ k =>
    rw [show 6*(k+1)+6=4+3*(2*k+1)+5 by omega,show 6*(k+1)=2+3*(2*k+1)+1 by omega,show ones (2+3*(2*k+1)+1) z=ones 2 (ones (3*(2*k+1)) (push true z)) by rw [show 2+3*(2*k+1)+1=2+(3*(2*k+1)+1) by omega,show ones (2+(3*(2*k+1)+1)) z=ones 2 (ones (3*(2*k+1)+1) z) from rep_add _ _ _ _,show ones (3*(2*k+1)+1) z=ones (3*(2*k+1)) (ones 1 z) from rep_add _ _ _ _]; rfl,run_add,run_add,start,Option.bind_some,lsweep,Option.bind_some,turn]
    rw [show blocks (2*(k+1)+1) z = blocks 1 (blocks (2*k+1) (blocks 1 z)) by rw [show 2*(k+1)+1=1+((2*k+1)+1) by omega,show blocks (1+((2*k+1)+1)) z=blocks 1 (blocks ((2*k+1)+1) z) from rep_add _ _ _ _,show blocks ((2*k+1)+1) z=blocks (2*k+1) (blocks 1 z) from rep_add _ _ _ _]]
theorem rblock (s : Bool) (l r : Stream) : run s (cost s) (A l (push true (blocks 2 r))) = some (A (ones 6 l) (push true r)) := by
  cases s <;> simp [cost,A,cfg,ones,blocks,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem rbase (s : Bool) (l : Stream) : run s (cost s) (A l (push true (blocks 1 z))) = some (A (ones 6 l) z) := by
  cases s <;> simp [cost,A,cfg,ones,blocks,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem rightPhase (s : Bool) (k : Nat) (l : Stream) : run s (cost s*(k+1)) (A l (push true (blocks (2*k+1) z))) = some (A (ones (6*(k+1)) l) z) := by
  induction k generalizing l with
  | zero => simpa using rbase s l
  | succ k ih =>
    rw [show cost s*(k+1+1)=cost s+cost s*(k+1) by cases s <;> simp [cost] <;> omega,show 2*(k+1)+1=2+(2*k+1) by omega,show blocks (2+(2*k+1)) z=blocks 2 (blocks (2*k+1) z) from rep_add _ _ _ _,run_add,rblock,Option.bind_some,ih]
    rw [show 6*(k+1+1)=6*(k+1)+6 by omega,show ones (6*(k+1)+6) l=ones (6*(k+1)) (ones 6 l) from rep_add _ _ _ _]
theorem grow (s : Bool) (k : Nat) : run s (6*k+6+cost s*(k+1)) (A (ones (6*k) z) z) = some (A (ones (6*(k+1)) z) z) := by
  rw [run_add,leftPhase,Option.bind_some,rightPhase]
theorem never (s : Bool) (n k : Nat) : run s n (A (ones (6*k) z) z) ≠ none := by
  induction n using Nat.strongRecOn generalizing k with
  | ind n ih =>
    intro hn
    let t := 6*k+6+cost s*(k+1)
    have ht : 0<t := by dsimp [t]; omega
    have hr := grow s k
    change run s t _ = _ at hr
    by_cases h : n≤t
    · rw [←show n+(t-n)=t by omega,run_add,hn] at hr; contradiction
    · rw [←show t+(n-t)=n by omega,run_add,hr,Option.bind_some] at hn
      exact ih (n-t) (by omega) (k+1) hn
#print axioms never
open BB6Coverage
open Box17 (index decode)
def codes (s : Bool) : List (Fin 25) := if s then [8,24,11,20,1,13,17,21,12,0,4,11] else [8,24,11,6,1,13,17,17,12,11,4,0]
def table (s : Bool) : Machine := fun a => decode ((codes s).getD (index a).val 0)
theorem project_step (s : Bool) (c : BB6Coverage.Config) :
    (rawStep (table s) c).map BB6.Agent13.Box33PrefixMacro.project = step s (BB6.Agent13.Box33PrefixMacro.project c) := by
  rw [BB6.Agent13.Box33PrefixMacro.map_step]
  rcases c with ⟨q,p,t⟩
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t p <;> cases s <;>
    simp only [readSlot,Box33Source.project,hb] <;> rfl
theorem source_never (s : Bool) : NeverHalts (table s) := by
  apply BB6.Agent13.Box33PrefixMacro.sourceNever (table s) (step s) (project_step s)
  intro n
  have hb : BB6.Agent13.Box33PrefixMacro.project BB6Coverage.blank = A z z := by
    change Box33Source.project false BB6Coverage.blank = A z z
    rw [Box33Source.project_blank false]
    simp [A,cfg,Box33UnarySweeper.blank] <;> rfl
  rw [hb]
  exact never s n 0
def partialTable (s : Bool) : PartialMachine := fun a => some (table s a)
theorem compatible_never (s : Bool) (m : Machine) (hm : compatible (partialTable s) m) : NeverHalts m := by
  have he : m = table s := funext fun a => hm a _ rfl
  rw [he]
  exact source_never s
#print axioms compatible_never
end Triple
namespace Quint
inductive Mode where | m5 | m7 | m8 deriving DecidableEq
open Mode
def step (m : Mode) (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (right .F true c)
  | .B,false => some (left .C true c)
  | .B,true => some (match m with | .m5 => right .A true c | .m7 => left .A false c | .m8 => left .F false c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (right .C false c)
  | .E,false => some (right .C true c)
  | .E,true => none
  | .F,false => some (right .A true c)
  | .F,true => some (right .D false c)
abbrev run (m : Mode) := BB6.Agent13.Box33PrefixMacro.run (step m)
theorem run_add (m : Mode) (a b : Nat) (c : Config) : run m (a+b) c = (run m a c).bind (run m b) := BB6.Agent13.Box33PrefixMacro.run_add (step m) a b c
abbrev zeros := rep [false]
abbrev cost (m : Mode) : Nat := match m with | .m5 => 2 | .m7 => 4 | .m8 => 8

theorem lblock (m : Mode) (l r : Stream) : run m 5 (A (push true l) (zeros 2 r)) = some (A l (zeros 2 (push true r))) := by
  cases m <;> simp [A,cfg,zeros,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem lsweep (m : Mode) (n : Nat) (l r : Stream) : run m (5*n) (A (ones n l) (zeros 2 r)) = some (A l (zeros 2 (ones n r))) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [show 5*(n+1)=5+5*n by omega,run_add]
    change (run m 5 (A (push true (ones n l)) (zeros 2 r))).bind _ = _
    rw [lblock,Option.bind_some,ih,show ones (n+1) r=ones n (ones 1 r) from rep_add _ _ _ _]
    rfl
theorem lturn (m : Mode) (r : Stream) : run m 6 (A z (zeros 2 r)) = some (A z (word [true,false,false,true] r)) := by
  cases m <;> simp [A,cfg,zeros,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem rhead (m : Mode) (l r : Stream) : run m 2 (A l (word [true,false] r)) = some (A (ones 2 l) r) := by
  cases m <;> simp [A,cfg,ones,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem rzeroOne (m : Mode) (l r : Stream) : run m (cost m) (A l (word [false,true] r)) = some (A (ones 2 l) r) := by
  cases m <;> simp [cost,A,cfg,ones,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem rturn (m : Mode) (l r : Stream) : run m (2+cost m) (A l (word [true,false,false,true] r)) = some (A (ones 4 l) r) := by
  rw [run_add]
  change (run m 2 (A l (word [true,false] (word [false,true] r)))).bind _ = _
  rw [rhead,Option.bind_some,rzeroOne]
  rfl
theorem rjump (m : Mode) (l r : Stream) : run m 7 (A l (ones 4 r)) = some (A (push true l) (word [true,false,false] r)) := by
  cases m <;> simp [A,cfg,ones,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem rblock (m : Mode) (l r : Stream) : run m (9+cost m) (A l (ones 5 r)) = some (A (ones 5 l) r) := by
  rw [show 9+cost m=7+(2+cost m) by omega,run_add]
  change (run m 7 (A l (ones 4 (push true r)))).bind _ = _
  rw [rjump,Option.bind_some]
  exact rturn m (push true l) r
theorem rbase (m : Mode) (l : Stream) : run m 7 (A l (ones 2 z)) = some (A (ones 3 l) z) := by
  cases m <;> simp [A,cfg,ones,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem rsweep (m : Mode) (n : Nat) (l : Stream) : run m ((9+cost m)*n+7) (A l (ones (5*n+2) z)) = some (A (ones (5*n+3) l) z) := by
  induction n generalizing l with
  | zero => exact rbase m l
  | succ n ih =>
    rw [show (9+cost m)*(n+1)+7=(9+cost m)+((9+cost m)*n+7) by cases m <;> simp [cost] <;> omega,show 5*(n+1)+2=5+(5*n+2) by omega,show ones (5+(5*n+2)) z=ones 5 (ones (5*n+2) z) from rep_add _ _ _ _,run_add,rblock,Option.bind_some,ih]
    rw [show 5*(n+1)+3=(5*n+3)+5 by omega,show ones ((5*n+3)+5) l=ones (5*n+3) (ones 5 l) from rep_add _ _ _ _]
theorem leftPhase (m : Mode) (n : Nat) : run m (5*n+6) (A (ones n z) z) = some (A z (word [true,false,false,true] (ones n z))) := by
  -- Avoid expanding the blank inside other arguments.
  have h := lsweep m n z z
  have e : zeros 2 z=z := by simp [zeros,rep,word]
  rw [e] at h
  -- Reexpress the exact composition without rewriting every occurrence of z.
  have hc := run_add m (5*n) 6 (A (ones n z) z)
  rw [h,Option.bind_some,lturn] at hc
  exact hc

theorem grow (m : Mode) (k : Nat) :
    run m (5*(5*k+7)+6+(2+cost m)+((9+cost m)*(k+1)+7)) (A (ones (5*k+7) z) z) =
    some (A (ones (5*(k+1)+7) z) z) := by
  rw [run_add,run_add,leftPhase,Option.bind_some,rturn,Option.bind_some]
  rw [show 5*k+7=5*(k+1)+2 by omega,rsweep]
  rw [show 5*(k+1)+7=(5*(k+1)+3)+4 by omega,show ones ((5*(k+1)+3)+4) z=ones (5*(k+1)+3) (ones 4 z) from rep_add _ _ _ _]
theorem never (m : Mode) (n k : Nat) : run m n (A (ones (5*k+7) z) z) ≠ none := by
  induction n using Nat.strongRecOn generalizing k with
  | ind n ih =>
    intro hn
    let t := 5*(5*k+7)+6+(2+cost m)+((9+cost m)*(k+1)+7)
    have ht : 0<t := by dsimp [t]; omega
    have hr := grow m k
    change run m t _ = _ at hr
    by_cases h : n≤t
    · rw [←show n+(t-n)=t by omega,run_add,hn] at hr; contradiction
    · rw [←show t+(n-t)=n by omega,run_add,hr,Option.bind_some] at hn
      exact ih (n-t) (by omega) (k+1) hn
abbrev initCost (m : Mode) : Nat := match m with | .m5 => 49 | .m7 => 53 | .m8 => 61
theorem init (m : Mode) : run m (initCost m) (A z z) = some (A (ones 7 z) z) := by
  have h₁ := leftPhase m 0
  have h₂ := rturn m z z
  have h₃ := leftPhase m 4
  have h₄ := rturn m z (ones 4 z)
  have h₅ := rjump m (ones 4 z) z
  have h₆ := rhead m (ones 5 z) (push false z)
  have hcost : initCost m = 6+(2+cost m)+26+(2+cost m)+7+2 := by cases m <;> decide
  rw [hcost,run_add,run_add,run_add,run_add,run_add]
  simp only [Nat.mul_zero,Nat.zero_add,rep_zero] at h₁
  rw [h₁,Option.bind_some,h₂,Option.bind_some,h₃,Option.bind_some,h₄,Option.bind_some,h₅,Option.bind_some]
  simpa using h₆

theorem neverBlank (m : Mode) (n : Nat) : run m n (A z z) ≠ none := by
  intro hn
  have hr := init m
  by_cases h : n≤initCost m
  · rw [←show n+(initCost m-n)=initCost m by omega,run_add,hn] at hr; contradiction
  · rw [←show initCost m+(n-initCost m)=n by omega,run_add,hr,Option.bind_some] at hn
    exact never m (n-initCost m) 0 hn
#print axioms neverBlank
open BB6Coverage
open Box17 (index decode)
def codes (s : Mode) : List (Fin 25) := match s with | .m5 => [8,24,11,4,1,13,17,10,12,0,4,14] | .m7 => [8,24,11,1,1,13,17,10,12,0,4,14] | .m8 => [8,24,11,21,1,13,17,10,12,0,4,14]
def table (s : Mode) : Machine := fun a => decode ((codes s).getD (index a).val 0)
theorem project_step (s : Mode) (c : BB6Coverage.Config) :
    (rawStep (table s) c).map BB6.Agent13.Box33PrefixMacro.project = step s (BB6.Agent13.Box33PrefixMacro.project c) := by
  rw [BB6.Agent13.Box33PrefixMacro.map_step]
  rcases c with ⟨q,p,t⟩
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t p <;> cases s <;>
    simp only [readSlot,Box33Source.project,hb] <;> rfl
theorem source_never (s : Mode) : NeverHalts (table s) := by
  apply BB6.Agent13.Box33PrefixMacro.sourceNever (table s) (step s) (project_step s)
  intro n
  have hb : BB6.Agent13.Box33PrefixMacro.project BB6Coverage.blank = A z z := by
    change Box33Source.project false BB6Coverage.blank = A z z
    rw [Box33Source.project_blank false]
    simp [A,cfg,Box33UnarySweeper.blank] <;> rfl
  rw [hb]
  exact neverBlank s n
def partialTable (s : Mode) : PartialMachine := fun a => some (table s a)
theorem compatible_never (s : Mode) (m : Machine) (hm : compatible (partialTable s) m) : NeverHalts m := by
  have he : m = table s := funext fun a => hm a _ rfl
  rw [he]
  exact source_never s
#print axioms compatible_never
end Quint
end BB6.Agent13.Box33D17V12Unary
