import Box33PrefixMacro
namespace BB6.Agent13.Box33D17V16Counters
open C9Pair
open BB6.Agent13.Box33D14Growth (z word rep rep_add rep_succ cfg)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

def step (short : Bool) (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (left (if short then .F else .E) true c)
  | .B,false => some (left .C true c)
  | .B,true => some (right .D false c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (right .D false c)
  | .E,false => some (right .D true c)
  | .E,true => some (left (if short then .A else .F) true c)
  | .F,false => some (left (if short then .E else .A) true c)
  | .F,true => none
abbrev run (s : Bool) := BB6.Agent13.Box33PrefixMacro.run (step s)
theorem run_add (s : Bool) (m n : Nat) (c : Config) : run s (m+n) c = (run s m c).bind (run s n) :=
  BB6.Agent13.Box33PrefixMacro.run_add (step s) m n c
abbrev A := cfg .A
abbrev D := cfg .D
abbrev ones := rep [true]
abbrev zeros := rep [false]
abbrev tail (r : Stream) := word [false,false,true] r

theorem aStart (s : Bool) (l r : Stream) : run s 2 (A l (word [false,true] r)) = some (D (word [false,true] l) r) := by
  simp [A,D,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem dOne (s : Bool) (l r : Stream) : run s 1 (D l (push true r)) = some (D (push false l) r) := by
  simp [D,cfg,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem dSweep (s : Bool) (n : Nat) (l r : Stream) : run s n (D l (ones n r)) = some (D (zeros n l) r) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [show n+1=1+n by omega,show ones (1+n) r = ones 1 (ones n r) from rep_add _ _ _ _,run_add]
    change (run s 1 (D l (push true (ones n r)))).bind (run s n) = _
    rw [dOne,Option.bind_some,ih,show 1+n=n+1 by omega,show zeros (n+1) l = zeros n (zeros 1 l) from rep_add _ _ _ _]
    rfl

theorem longExit (l r : Stream) : run false 5 (D (zeros 3 l) (tail r)) = some (A l (word [false,true,true,false,false,true] r)) := by
  simp [A,D,cfg,zeros,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem longBase (l r : Stream) : run false 5 (D (word [false,false,true] l) (tail r)) = some (A l (word [true,true,true,false,false,true] r)) := by
  simp [A,D,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem shortExit (l r : Stream) : run true 4 (D (zeros 2 l) (tail r)) = some (A l (word [false,true,false,false,true] r)) := by
  simp [A,D,cfg,zeros,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem shortBase (l r : Stream) : run true 4 (D (word [false,true] l) (tail r)) = some (A l (word [true,true,false,false,true] r)) := by
  simp [A,D,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem longClear (l r : Stream) : run false 2 (A (push false l) (push true r)) = some (D (push true l) (push true r)) := by
  simp [A,D,cfg,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem shortClear (l r : Stream) : run true 3 (A (word [false,false] l) (push true r)) = some (D (push true l) (word [true,true] r)) := by
  simp [A,D,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem longCarry (b : Bool) (l r : Stream) : run false 3 (A (word [true,false,b] l) (push true r)) = some (A l (word [b,true,true,true] r)) := by
  simp [A,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem shortCarry (b : Bool) (l r : Stream) : run true 3 (A (word [false,true,b] l) (push true r)) = some (A l (word [b,true,true,true] r)) := by
  simp [A,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]

abbrev P (s : Bool) (j : Nat) (l : Stream) := A l (push false (ones (3*j + if s then 1 else 2) (tail z)))
abbrev Qp (s : Bool) (j : Nat) (l : Stream) := A l (ones (3*j + if s then 2 else 3) (tail z))
theorem pBase (s : Bool) (l : Stream) : run s (if s then 6 else 8) (P s 0 l) = some (Qp s 0 l) := by
  cases s <;> simp [P,Qp,A,cfg,ones,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]

theorem pLong (j : Nat) (l : Stream) : run false (3*j+11) (P false (j+1) l) = some (P false 0 (zeros (3*j) (word [false,false,true] l))) := by
  have h : ones (3*(j+1)+2) (tail z) = push true (ones (3*j+4) (tail z)) := by
    rw [show 3*(j+1)+2=(3*j+4)+1 by omega]; rfl
  change run false (3*j+11) (A l (push false (ones (3*(j+1)+2) (tail z)))) = _
  rw [h,show 3*j+11=2+(3*j+4)+5 by omega,run_add,run_add]
  change ((run false 2 (A l (word [false,true] (ones (3*j+4) (tail z))))).bind _).bind _ = _
  rw [aStart,Option.bind_some,dSweep,Option.bind_some]
  have hz : zeros (3*j+4) (word [false,true] l) = zeros 3 (zeros (3*j) (word [false,false,true] l)) := by
    rw [show 3*j+4=3+(3*j+1) by omega,show zeros (3+(3*j+1)) (word [false,true] l) = zeros 3 (zeros (3*j+1) (word [false,true] l)) from rep_add _ _ _ _,show zeros (3*j+1) (word [false,true] l) = zeros (3*j) (zeros 1 (word [false,true] l)) from rep_add _ _ _ _]
    rfl
  rw [hz,longExit]
  rfl

theorem pShort (j : Nat) (l : Stream) : run true (3*j+9) (P true (j+1) l) = some (P true 0 (zeros (3*j) (word [false,false,true] l))) := by
  have h : ones (3*(j+1)+1) (tail z) = push true (ones (3*j+3) (tail z)) := by
    rw [show 3*(j+1)+1=(3*j+3)+1 by omega]; rfl
  change run true (3*j+9) (A l (push false (ones (3*(j+1)+1) (tail z)))) = _
  rw [h,show 3*j+9=2+(3*j+3)+4 by omega,run_add,run_add]
  change ((run true 2 (A l (word [false,true] (ones (3*j+3) (tail z))))).bind _).bind _ = _
  rw [aStart,Option.bind_some,dSweep,Option.bind_some]
  have hz : zeros (3*j+3) (word [false,true] l) = zeros 2 (zeros (3*j) (word [false,false,true] l)) := by
    rw [show 3*j+3=2+(3*j+1) by omega,show zeros (2+(3*j+1)) (word [false,true] l) = zeros 2 (zeros (3*j+1) (word [false,true] l)) from rep_add _ _ _ _,show zeros (3*j+1) (word [false,true] l) = zeros (3*j) (zeros 1 (word [false,true] l)) from rep_add _ _ _ _]
    rfl
  rw [hz,shortExit]
  rfl

theorem qLongClear (j : Nat) (l : Stream) : run false (3*j+10) (Qp false j (push false l)) = some (P false 0 (zeros (3*j) (push true l))) := by
  change run false (3*j+10) (A (push false l) (ones (3*j+3) (tail z))) = _
  rw [show 3*j+3=(3*j+2)+1 by omega,show 3*j+10=2+(3*j+3)+5 by omega,run_add,run_add]
  change ((run false 2 (A (push false l) (push true (ones (3*j+2) (tail z))))).bind _).bind _ = _
  rw [longClear,Option.bind_some]
  change (run false (3*j+3) (D (push true l) (ones (3*j+3) (tail z)))).bind _ = _
  rw [dSweep,Option.bind_some,show zeros (3*j+3) (push true l) = zeros 3 (zeros (3*j) (push true l)) by rw [show 3*j+3=3+3*j by omega]; exact rep_add _ _ _ _,longExit]
  rfl

theorem qShortClear (j : Nat) (l : Stream) : run true (3*j+10) (Qp true j (word [false,false] l)) = some (P true 0 (zeros (3*j) (word [false,true] l))) := by
  change run true (3*j+10) (A (word [false,false] l) (ones (3*j+2) (tail z))) = _
  rw [show 3*j+2=(3*j+1)+1 by omega,show 3*j+10=3+(3*j+3)+4 by omega,run_add,run_add]
  change ((run true 3 (A (word [false,false] l) (push true (ones (3*j+1) (tail z))))).bind _).bind _ = _
  rw [shortClear,Option.bind_some]
  change (run true (3*j+3) (D (push true l) (ones (3*j+3) (tail z)))).bind _ = _
  rw [dSweep,Option.bind_some]
  have hz : zeros (3*j+3) (push true l) = zeros 2 (zeros (3*j) (word [false,true] l)) := by
    rw [show 3*j+3=2+(3*j+1) by omega,show zeros (2+(3*j+1)) (push true l) = zeros 2 (zeros (3*j+1) (push true l)) from rep_add _ _ _ _,show zeros (3*j+1) (push true l) = zeros (3*j) (zeros 1 (push true l)) from rep_add _ _ _ _]; rfl
  rw [hz,shortExit]
  rfl

theorem qCarry (s b : Bool) (j : Nat) (l : Stream) :
    run s 3 (Qp s j (word (if s then [false,true,b] else [true,false,b]) l)) =
      some (if b then Qp s (j+1) l else P s (j+1) l) := by
  cases s <;> cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · change run false 3 (A (word [true,false,false] l) (push true (ones (3*j+2) (tail z)))) = _
    rw [longCarry]
    change some (A l (push false (ones (3*j+2+3) (tail z)))) = some (P false (j+1) l)
    rw [show 3*j+2+3=3*(j+1)+2 by omega]; rfl
  · change run false 3 (A (word [true,false,true] l) (push true (ones (3*j+2) (tail z)))) = _
    rw [longCarry]
    change some (A l (ones (3*j+2+4) (tail z))) = some (Qp false (j+1) l)
    rw [show 3*j+2+4=3*(j+1)+3 by omega]; rfl
  · change run true 3 (A (word [false,true,false] l) (push true (ones (3*j+1) (tail z)))) = _
    rw [shortCarry]
    change some (A l (push false (ones (3*j+1+3) (tail z)))) = some (P true (j+1) l)
    rw [show 3*j+1+3=3*(j+1)+1 by omega]; rfl
  · change run true 3 (A (word [false,true,true] l) (push true (ones (3*j+1) (tail z)))) = _
    rw [shortCarry]
    change some (A l (ones (3*j+1+4) (tail z))) = some (Qp true (j+1) l)
    rw [show 3*j+1+4=3*(j+1)+2 by omega]; rfl

def Guard (s : Bool) (l : Stream) : Prop := ∀ n, l (3*n + if s then 0 else 1) = false

theorem guard_decomp (s : Bool) (l : Stream) (h : Guard s l) :
    ∃ a b c u, l = word [a,b,c] u ∧ Guard s u ∧ (if s then a else b) = false := by
  refine ⟨l 0,l 1,l 2,fun n => l (n+3),?_,?_,?_⟩
  · funext n; cases n with
    | zero => rfl
    | succ n => cases n with
      | zero => rfl
      | succ n => cases n with
        | zero => rfl
        | succ n => change l (n+1+1+1) = l (n+3); rfl
  · intro n
    change l ((3*n + if s then 0 else 1)+3) = false
    rw [show (3*n + if s then 0 else 1)+3=3*(n+1)+(if s then 0 else 1) by omega]
    exact h (n+1)
  · cases s <;> exact h 0

theorem guard_prefix (s : Bool) (a b c : Bool) (u : Stream) (h : Guard s u) (hb : (if s then a else b)=false) : Guard s (word [a,b,c] u) := by
  intro n
  cases n with
  | zero => cases s <;> exact hb
  | succ n =>
    rw [show 3*(n+1)+(if s then 0 else 1)=(3*n+(if s then 0 else 1))+3 by omega]
    exact h n

theorem guard_zeros (s : Bool) (j : Nat) (l : Stream) (h : Guard s l) : Guard s (zeros (3*j) l) := by
  induction j with
  | zero => exact h
  | succ j ih =>
    rw [show 3*(j+1)=3+3*j by omega,show zeros (3+3*j) l = zeros 3 (zeros (3*j) l) from rep_add _ _ _ _]
    exact guard_prefix s false false false _ ih (by cases s <;> rfl)

def phase (s q : Bool) (j : Nat) (l : Stream) : Config := if q then Qp s j l else P s j l

theorem progress (s q : Bool) (j : Nat) (l : Stream) (h : Guard s l) :
    ∃ t q' j' l', 0<t ∧ Guard s l' ∧ run s t (phase s q j l) = some (phase s q' j' l') := by
  cases q with
  | false =>
    cases j with
    | zero => exact ⟨if s then 6 else 8,true,0,l,by cases s <;> decide,h,pBase s l⟩
    | succ j =>
      have hg := guard_zeros s j _ (guard_prefix s false false true l h (by cases s <;> rfl))
      cases s
      · exact ⟨3*j+11,false,0,_,by omega,hg,pLong j l⟩
      · exact ⟨3*j+9,false,0,_,by omega,hg,pShort j l⟩
  | true =>
    obtain ⟨a,b,c,u,rfl,hu,hb⟩ := guard_decomp s l h
    cases s with
    | false =>
      change b=false at hb; subst b
      cases a with
      | false =>
        have hg := guard_zeros false j _ (guard_prefix false true false c u hu rfl)
        exact ⟨3*j+10,false,0,_,by omega,hg,qLongClear j (word [false,c] u)⟩
      | true => exact ⟨3,c,j+1,u,by decide,hu,by simpa [phase] using qCarry false c j u⟩
    | true =>
      change a=false at hb; subst a
      cases b with
      | false =>
        have hg := guard_zeros true j _ (guard_prefix true false true c u hu rfl)
        exact ⟨3*j+10,false,0,_,by omega,hg,qShortClear j (push c u)⟩
      | true => exact ⟨3,c,j+1,u,by decide,hu,by simpa [phase] using qCarry true c j u⟩

theorem neverPhase (s : Bool) (n : Nat) (q : Bool) (j : Nat) (l : Stream) (h : Guard s l) : run s n (phase s q j l) ≠ none := by
  induction n using Nat.strongRecOn generalizing q j l with
  | ind n ih =>
    intro hn
    obtain ⟨t,q',j',l',ht,hg,hr⟩ := progress s q j l h
    by_cases hnt : n ≤ t
    · rw [←show n+(t-n)=t by omega,run_add,hn] at hr
      contradiction
    · rw [←show t+(n-t)=n by omega,run_add,hr,Option.bind_some] at hn
      exact ih (n-t) (by omega) q' j' l' hg hn

theorem init (s : Bool) : run s (if s then 7 else 8) (A z z) = some (phase s false 0 z) := by
  cases s <;> simp [phase,P,A,cfg,ones,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]

theorem neverBlank (s : Bool) (n : Nat) : run s n (A z z) ≠ none := by
  intro hn
  let t : Nat := if s then 7 else 8
  have hr : run s t (A z z) = some (phase s false 0 z) := init s
  by_cases h : n ≤ t
  · rw [←show n+(t-n)=t by omega,run_add,hn] at hr
    contradiction
  · rw [←show t+(n-t)=n by omega,run_add,hr,Option.bind_some] at hn
    exact neverPhase s (n-t) false 0 z (fun _ => rfl) hn
#print axioms neverBlank

open BB6Coverage
open Box17 (index decode)
def codes (s : Bool) : List (Fin 25) := if s then [8,23,11,14,1,13,17,14,16,3,19,0] else [8,19,11,14,1,13,17,14,16,23,3,0]
def table (s : Bool) : Machine := fun a => decode ((codes s).getD (index a).val 0)
theorem project_step (s : Bool) (c : BB6Coverage.Config) :
    (rawStep (table s) c).map BB6.Agent13.Box33PrefixMacro.project = step s (BB6.Agent13.Box33PrefixMacro.project c) := by
  rw [BB6.Agent13.Box33PrefixMacro.map_step]
  rcases c with ⟨q,p,t⟩
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t p <;> cases s <;>
    simp only [readSlot,Box33Source.project,hb] <;> rfl
theorem never (s : Bool) : NeverHalts (table s) := by
  apply BB6.Agent13.Box33PrefixMacro.sourceNever (table s) (step s) (project_step s)
  intro n
  have hb : BB6.Agent13.Box33PrefixMacro.project BB6Coverage.blank = A z z := by
    change Box33Source.project false BB6Coverage.blank = A z z
    rw [Box33Source.project_blank false]
    simp [A,cfg,Box33UnarySweeper.blank] <;> rfl
  rw [hb]
  exact neverBlank s n
def partialTable (s : Bool) : PartialMachine := fun a => some (table s a)
theorem compatible_never (s : Bool) (m : Machine) (hm : compatible (partialTable s) m) : NeverHalts m := by
  have he : m = table s := funext fun a => hm a _ rfl
  rw [he]
  exact never s
#print axioms compatible_never
end BB6.Agent13.Box33D17V16Counters
