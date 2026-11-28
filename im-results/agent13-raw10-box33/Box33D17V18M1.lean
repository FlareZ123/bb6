import Box33PrefixMacro
namespace BB6.Agent13.Box33D17V18M1
open C9Pair
open BB6.Agent13.Box33D14Growth (z word rep cfg)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
def step (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (right .E true c)
  | .B,false => some (left .C true c)
  | .B,true => some (right .F true c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (left .C false c)
  | .E,false => some (right .E false c)
  | .E,true => some (right .B false c)
  | .F,false => some (right .D true c)
  | .F,true => none
abbrev run := BB6.Agent13.Box33PrefixMacro.run step
theorem run_add (m n : Nat) (c : Config) : run (m+n) c = (run m c).bind (run n) :=
  BB6.Agent13.Box33PrefixMacro.run_add step m n c
abbrev A := cfg .A
abbrev blocks := rep [false,false,true]
theorem root0 (b : Bool) (r : Stream) :
    run 14 (A z (word [false,false,true,false,false,b] r)) =
      some (A z (word [true,false,true,b] r)) := by
  cases b <;> simp [A,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem blankRight (r : Stream) :
    run 10 (A z (word [false,false,false] r)) = some (A z (word [false,false,true] r)) := by
  simp [A,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem root1a (b : Bool) (r : Stream) :
    run 14 (A z (word [false,false,true,false,true,b] r)) =
      some (A z (word [false,false,false,false,false,b] r)) := by
  cases b <;> simp [A,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem root1 (b : Bool) (r : Stream) :
    run 24 (A z (word [false,false,true,false,true,b] r)) =
      some (A z (word [false,false,true,false,false,b] r)) := by
  rw [show 24=14+10 by decide,run_add,root1a,Option.bind_some]
  exact blankRight (word [false,false,b] r)
theorem carryFalse (l r : Stream) :
    run 5 (A l (word [true,false,true,false] r)) =
      some (A (push true l) (word [false,false,true] r)) := by
  simp [A,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem carryTrue0 (b : Bool) (l r : Stream) :
    run 9 (A l (word [true,false,true,true,false,false,b] r)) =
      some (A (word [false,false,true] l) (word [true,false,true,b] r)) := by
  cases b <;> simp [A,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem carryTrue1 (b : Bool) (l r : Stream) :
    run 9 (A l (word [true,false,true,true,false,true,b] r)) =
      some (A (push true l) (word [false,false,false,false,false,b] r)) := by
  cases b <;> simp [A,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem retPos (b : Bool) (l r : Stream) :
    run 5 (A (word [true,false,false,true] l) (word [false,false,b] r)) =
      some (A (push true l) (word [false,false,false,false,true,b] r)) := by
  cases b <;> simp [A,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem retZeroA (b : Bool) (r : Stream) :
    run 5 (A (push true z) (word [false,false,b] r)) =
      some (A z (word [false,false,false,false,true,b] r)) := by
  cases b <;> simp [A,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem retZero (b : Bool) (r : Stream) :
    run 15 (A (push true z) (word [false,false,b] r)) =
      some (A z (word [false,false,true,false,true,b] r)) := by
  rw [show 15=5+10 by decide,run_add,retZeroA,Option.bind_some]
  exact blankRight (word [false,true,b] r)
def digits : List (Bool × Bool) → Stream
  | [] => z
  | (a,b)::ds => word [false,a,b] (digits ds)
inductive Phase where
  | root (ds : List (Bool × Bool))
  | carry (k : Nat) (b : Bool) (ds : List (Bool × Bool))
  | ret (k : Nat) (b : Bool) (ds : List (Bool × Bool))
def phase : Phase → Config
  | .root ds => A z (word [false,false,true] (digits ds))
  | .carry k b ds => A (blocks k z) (word [true,false,true,b] (digits ds))
  | .ret k b ds => A (push true (blocks k z)) (word [false,false,b] (digits ds))
theorem progress (p : Phase) : ∃ t p', 0 < t ∧ run t (phase p) = some (phase p') := by
  cases p with
  | root ds =>
    cases ds with
    | nil => exact ⟨14,.carry 0 false [],by decide,by simpa [phase,digits,word] using root0 false z⟩
    | cons d ds =>
      obtain ⟨a,b⟩ := d
      cases a with
      | false => exact ⟨14,.carry 0 b ds,by decide,root0 b (digits ds)⟩
      | true => exact ⟨24,.root ((false,b)::ds),by decide,root1 b (digits ds)⟩
  | carry k b ds =>
    cases b with
    | false => exact ⟨5,.ret k true ds,by decide,carryFalse _ _⟩
    | true =>
      cases ds with
      | nil => exact ⟨9,.carry (k+1) false [],by decide,by simpa [phase,digits,word] using carryTrue0 false (blocks k z) z⟩
      | cons d ds =>
        obtain ⟨a,b⟩ := d
        cases a with
        | false => exact ⟨9,.carry (k+1) b ds,by decide,carryTrue0 b _ _⟩
        | true => exact ⟨9,.ret k false ((false,b)::ds),by decide,carryTrue1 b _ _⟩
  | ret k b ds =>
    cases k with
    | zero => exact ⟨15,.root ((true,b)::ds),by decide,retZero b _⟩
    | succ k => exact ⟨5,.ret k false ((true,b)::ds),by decide,retPos b _ _⟩
theorem neverPhase (n : Nat) (p : Phase) : run n (phase p) ≠ none := by
  induction n using Nat.strongRecOn generalizing p with
  | ind n ih =>
    obtain ⟨t,p',ht,hr⟩ := progress p
    intro hn
    by_cases h : n ≤ t
    · rw [←show n+(t-n)=t by omega,run_add,hn] at hr
      contradiction
    · rw [←show t+(n-t)=n by omega,run_add,hr,Option.bind_some] at hn
      exact ih (n-t) (by omega) p' hn
theorem init : run 10 (A z z) = some (phase (.root [])) := by
  simp [phase,digits,A,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem neverBlank (n : Nat) : run n (A z z) ≠ none := by
  intro hn
  by_cases h : n ≤ 10
  · have hr := init
    rw [←show n+(10-n)=10 by omega,run_add,hn] at hr
    contradiction
  · rw [←show 10+(n-10)=n by omega,run_add,init,Option.bind_some] at hn
    exact neverPhase _ _ hn
open BB6Coverage
open Box17 (index decode)
def codes : List (Fin 25) := [8,20,11,24,1,13,17,9,18,6,16,0]
def table : Machine := fun s => decode (codes.getD (index s).val 0)
theorem project_step (c : BB6Coverage.Config) :
    (rawStep table c).map BB6.Agent13.Box33PrefixMacro.project = step (BB6.Agent13.Box33PrefixMacro.project c) := by
  rw [BB6.Agent13.Box33PrefixMacro.map_step]
  rcases c with ⟨s,p,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t p <;>
    simp only [readSlot,Box33Source.project,hb] <;> rfl
theorem never : NeverHalts table := by
  apply BB6.Agent13.Box33PrefixMacro.sourceNever table step project_step
  intro n
  have hb : BB6.Agent13.Box33PrefixMacro.project BB6Coverage.blank = A z z := by
    change Box33Source.project false BB6Coverage.blank = A z z
    rw [Box33Source.project_blank false]
    simp [A,cfg,Box33UnarySweeper.blank] <;> rfl
  rw [hb]
  exact neverBlank n
def partialTable : PartialMachine := fun s => some (table s)
theorem compatible_never (m : Machine) (hm : compatible partialTable m) : NeverHalts m := by
  have he : m = table := funext fun s => hm s _ rfl
  rw [he]
  exact never
#print axioms neverBlank
#print axioms compatible_never
end BB6.Agent13.Box33D17V18M1
