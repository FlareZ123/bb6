import Box33SourceBridge
import Box17AuditCore
import Box33D14Growth

namespace BB6.Agent13.Box33D17V22Counter
open C9Pair
open BB6.Agent13.Box33D14Growth (z word rep cfg)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

-- A1 and D1 are arbitrary, including halting instructions.
variable (a1 d1 : C9Pair.Config → Option C9Pair.Config)

def step (c : C9Pair.Config) : Option C9Pair.Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => a1 c
  | .B,false => some (left .C true c)
  | .B,true => some (right .F true c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => d1 c
  | .E,false => some (right .F false c)
  | .E,true => some (left .C false c)
  | .F,false => some (left .E true c)
  | .F,true => some (right .A false c)

def run : Nat → C9Pair.Config → Option C9Pair.Config
  | 0,c => some c
  | n+1,c => (step a1 d1 c).bind (run n)

theorem run_add (m n : Nat) (c : C9Pair.Config) :
    run a1 d1 (m+n) c = (run a1 d1 m c).bind (run a1 d1 n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih => rw [Nat.succ_add]; simp only [run]; cases h : step a1 d1 c <;> simp [ih]

abbrev A (l r : Stream) := cfg .A l (push false r)
abbrev C (l r : Stream) := cfg .C l (push true r)

theorem digit0 (l r : Stream) :
    run a1 d1 2 (A l (word [false,false,false] r)) =
      some (C l (word [true,false,false] r)) := by
  simp [A,C,cfg,run,step,left,right,word]

theorem digit1 (l r : Stream) :
    run a1 d1 4 (A l (word [true,false,false] r)) =
      some (C l (word [false,true,false] r)) := by
  simp [A,C,cfg,run,step,left,right,word]

theorem digit2 (l r : Stream) :
    run a1 d1 2 (A l (word [false,true,false] r)) =
      some (C l (word [true,true,false] r)) := by
  simp [A,C,cfg,run,step,left,right,word]

theorem digit3 (l r : Stream) :
    run a1 d1 3 (A l (word [true,true,false] r)) =
      some (A (word [false,true,true] l) r) := by
  simp [A,C,cfg,run,step,left,right,word]

theorem popCarry (l r : Stream) :
    run a1 d1 3 (C (word [false,true,true] l) r) =
      some (C l (word [false,false,false] r)) := by
  simp [A,C,cfg,run,step,left,right,word]

theorem turn (r : Stream) :
    run a1 d1 6 (C z r) = some (A z r) := by
  simp [A,C,cfg,run,step,left,right,word]

def digits : List (Bool × Bool) → Stream
  | [] => z
  | (a,b)::w => word [a,b,false] (digits w)

abbrev stack (k : Nat) := rep [false,true,true] k z

def phase (b : Bool) (k : Nat) (w : List (Bool × Bool)) : C9Pair.Config :=
  if b then C (stack k) (digits w) else A (stack k) (digits w)

theorem progress (b : Bool) (k : Nat) (w : List (Bool × Bool)) :
    ∃ t : Nat, 0<t ∧ ∃ b' k' w', run a1 d1 t (phase b k w) = some (phase b' k' w') := by
  cases b with
  | true =>
    cases k with
    | zero =>
      exact ⟨6,by decide,false,0,w,by simpa [phase,stack] using turn a1 d1 (digits w)⟩
    | succ k =>
      exact ⟨3,by decide,true,k,(false,false)::w,
        by simpa [phase,stack,digits] using popCarry a1 d1 (stack k) (digits w)⟩
  | false =>
    cases w with
    | nil =>
      exact ⟨2,by decide,true,k,[(true,false)],
        by simpa [phase,digits,word] using digit0 a1 d1 (stack k) z⟩
    | cons d w =>
      rcases d with ⟨a,b⟩
      cases a <;> cases b
      · exact ⟨2,by decide,true,k,(true,false)::w,
          by simpa [phase,digits] using digit0 a1 d1 (stack k) (digits w)⟩
      · exact ⟨2,by decide,true,k,(true,true)::w,
          by simpa [phase,digits] using digit2 a1 d1 (stack k) (digits w)⟩
      · exact ⟨4,by decide,true,k,(false,true)::w,
          by simpa [phase,digits] using digit1 a1 d1 (stack k) (digits w)⟩
      · exact ⟨3,by decide,false,k+1,w,
          by simpa [phase,digits,stack] using digit3 a1 d1 (stack k) (digits w)⟩

theorem never_phase (n : Nat) (b : Bool) (k : Nat) (w : List (Bool × Bool)) :
    run a1 d1 n (phase b k w) ≠ none := by
  induction n using Nat.strongRecOn generalizing b k w with
  | ind n ih =>
    intro h
    obtain ⟨t,ht,b',k',w',he⟩ := progress a1 d1 b k w
    by_cases hn : n≤t
    · rw [←show n+(t-n)=t by omega,run_add,h] at he
      contradiction
    · rw [←show t+(n-t)=n by omega,run_add,he,Option.bind_some] at h
      exact ih _ (by omega) b' k' w' h

theorem never_blank (n : Nat) : run a1 d1 n (cfg .A z z) ≠ none := by
  simpa [phase,stack,digits,A] using never_phase a1 d1 n false 0 []

open BB6Coverage
open Box17 (index decode)

def codes : List (Option (Fin 25)) :=
  [some 8,none,some 11,some 24,some 1,some 13,some 17,none,some 22,some 9,some 19,some 2]
def partialTable : PartialMachine := fun s => (codes.getD (index s).val none).map decode

abbrev project := Box33Source.project false
def unknown (mv : Option Move) (c : C9Pair.Config) : Option C9Pair.Config :=
  mv.map fun x => if x.right then C9Pair.right (Box33Source.q false x.next) x.write c
                    else C9Pair.left (Box33Source.q false x.next) x.write c

theorem map_step (m : Machine) (c : BB6Coverage.Config) :
    (rawStep m c).map project = unknown (m (readSlot c)) (project c) := by
  unfold rawStep unknown
  cases ht : m (readSlot c) with
  | none => rfl
  | some mv => simp only [Option.map_some,Box33Source.project_applyMove]

theorem project_step (m : Machine) (hm : compatible partialTable m) (c : BB6Coverage.Config) :
    (rawStep m c).map project =
      step (unknown (m (0,true))) (unknown (m (3,true))) (project c) := by
  rw [map_step]
  rcases c with ⟨s,p,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  have h0 := hm (0,false) (decode 8) (by decide)
  have h2 := hm (1,false) (decode 11) (by decide)
  have h3 := hm (1,true) (decode 24) (by decide)
  have h4 := hm (2,false) (decode 1) (by decide)
  have h5 := hm (2,true) (decode 13) (by decide)
  have h6 := hm (3,false) (decode 17) (by decide)
  have h8 := hm (4,false) (decode 22) (by decide)
  have h9 := hm (4,true) (decode 9) (by decide)
  have h10 := hm (5,false) (decode 19) (by decide)
  have h11 := hm (5,true) (decode 2) (by decide)
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t p <;>
    simp only [readSlot,Box33Source.project,hb,h0,h2,h3,h4,h5,h6,h8,h9,h10,h11] <;> rfl

theorem project_run (m : Machine) (hm : compatible partialTable m) (n : Nat) (c : BB6Coverage.Config) :
    (BB6Coverage.run m n c).map project =
      run (unknown (m (0,true))) (unknown (m (3,true))) n (project c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run_add _ _ n 1,←ih]
    simp only [BB6Coverage.run]
    cases ht : BB6Coverage.run m n c with
    | none => rfl
    | some c' =>
      simp only [Option.bind_some,Option.map_some]
      simpa [run] using project_step m hm c'

theorem compatible_never (m : Machine) (hm : compatible partialTable m) : NeverHalts m := by
  intro n
  have he := project_run m hm n BB6Coverage.blank
  have hn : run (unknown (m (0,true))) (unknown (m (3,true))) n (project BB6Coverage.blank) ≠ none :=
    never_blank _ _ n
  cases hr : BB6Coverage.run m n BB6Coverage.blank with
  | none =>
    rw [hr] at he
    exact False.elim (hn he.symm)
  | some c => rfl

#print axioms progress
#print axioms compatible_never
end BB6.Agent13.Box33D17V22Counter
