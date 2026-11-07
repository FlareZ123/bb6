import BB429PhysicalFrontier
import Lean.Elab.Tactic.Omega
namespace BB429WindowR4
open BB6Coverage BB429PhysicalFrontier
set_option maxRecDepth 30000
set_option maxHeartbeats 50000000

structure W where
  l4 : Bool
  l3 : Bool
  l2 : Bool
  l1 : Bool
  c : Bool
  r1 : Bool
  r2 : Bool
  r3 : Bool
  r4 : Bool
  deriving DecidableEq, Repr

def shiftR (w : W) (write fresh : Bool) : W :=
  ⟨w.l3,w.l2,w.l1,write,w.r1,w.r2,w.r3,w.r4,fresh⟩
def shiftL (w : W) (write fresh : Bool) : W :=
  ⟨fresh,w.l4,w.l3,w.l2,w.l1,write,w.r1,w.r2,w.r3⟩

def code (w : W) : Nat :=
  1*w.l4.toNat +
  2*w.l3.toNat +
  4*w.l2.toNat +
  8*w.l1.toNat +
  16*w.c.toNat +
  32*w.r1.toNat +
  64*w.r2.toNat +
  128*w.r3.toNat +
  256*w.r4.toNat

def mask : Nat := 0xf0f0000000000000ffffffff00000000ffffffff00000000f0f0000000000000f0f0000000000000ffffff0000000000ffffffff00000000f0f00000ffffffff00000000fffffc0000000000ffffffff000000000000fc0000000000ffffffff00000000ff00fc0000000000ffffcc00000000000000fc000000000000a000a000a0ffe000a0ffa000a000e000a000a000a0f0e000a0ffa000a000e000a000a000a0ffe000a0ffa000a000e000a000a000a0f0e000a0ffa000a000e0fc00cc00cc00cc00fc00cc00cc00dc00fc00cc00cc00cc00fc00cc00cc00dc00fc00cc00cc00cc00fc00cc00cc00dc00fc00cc00cc00cc00fc00cc00cc00dc00a0e0ffa0f0e0a0a0a0e0e0a0ffe0a0a0a0e0ffa0ffe0a0a0a0e0e0a0f0e0a1a0a0e0ffa0f0e0a0a0a0e0e0a0ffe0a0a0a0e0ffa0ffe0a0a0a0e0e0a0f0e0a1a0cc00cc00ffffffffff00ff00cc00cc00cc00cc00fff0fc00ffffffffcc00cc00cc00cc00ffffffffffffffffcc00cc00cc00cc00fff0fc00ff00ff00cc00cc01
def allowed (q : Fin 6) (w : W) : Bool :=
  mask.testBit (q.val*512 + code w)

def step (q : Fin 6) (w : W) (far : Bool) : Option (Fin 6 × W) :=
  (target429 (q,w.c)).map (fun t =>
    (t.next, if t.right then shiftR w t.write far else shiftL w t.write far))

/-- All 6*512 abstract windows and both far-side bits are exhaustively checked. -/
theorem allowed_closed :
    ∀ (q : Fin 6) (l4 l3 l2 l1 c r1 r2 r3 r4 far : Bool),
    allowed q ⟨l4,l3,l2,l1,c,r1,r2,r3,r4⟩ = true →
    (match step q ⟨l4,l3,l2,l1,c,r1,r2,r3,r4⟩ far with
     | none => true
     | some next => allowed next.1 next.2) = true := by
  decide

def view (c : Config) : W :=
  ⟨c.tape (c.head-4),c.tape (c.head-3),c.tape (c.head-2),
   c.tape (c.head-1), c.tape c.head,
   c.tape (c.head+1), c.tape (c.head+2),c.tape (c.head+3),c.tape (c.head+4)⟩

theorem view_move (c : Config) (t : Move) :
    ∃ far : Bool, view (applyMove c t) =
      if t.right then shiftR (view c) t.write far
      else shiftL (view c) t.write far := by
  rcases t with ⟨write,right,next⟩
  cases right with
  | false =>
      refine ⟨c.tape (c.head-5),?_⟩
      simp [view,applyMove,shiftL,Int.sub_eq_add_neg,Int.add_assoc] <;> omega
  | true =>
      refine ⟨c.tape (c.head+5),?_⟩
      simp [view,applyMove,shiftR,Int.sub_eq_add_neg,Int.add_assoc] <;> omega

def obs (c : Config) : Fin 6 × W := (c.state,view c)

theorem step_sound (c d : Config) (h : rawStep target429 c = some d) :
    ∃ far, step c.state (view c) far = some (obs d) := by
  cases hm : target429 (readSlot c) with
  | none => simp [rawStep,hm] at h
  | some t =>
      have hd : d = applyMove c t := by
        simpa [rawStep,hm] using h.symm
      obtain ⟨far,hview⟩ := view_move c t
      refine ⟨far,?_⟩
      rw [hd]
      have hread : (c.state, (view c).c) = readSlot c := rfl
      simp only [step,hread,hm,Option.map_some,obs]
      apply congrArg Option.some
      apply Prod.ext
      · rfl
      · exact hview.symm

theorem allowed_step (q : Fin 6) (w : W) (far : Bool)
    (h : allowed q w = true) :
    (match step q w far with
     | none => true
     | some nxt => allowed nxt.1 nxt.2) = true := by
  rcases w with ⟨l4,l3,l2,l1,c,r1,r2,r3,r4⟩
  exact allowed_closed q l4 l3 l2 l1 c r1 r2 r3 r4 far h

theorem allowed_raw (c d : Config)
    (hr : rawStep target429 c = some d)
    (ha : allowed c.state (view c) = true) :
    allowed d.state (view d) = true := by
  obtain ⟨far,hstep⟩ := step_sound c d hr
  have hc := allowed_step c.state (view c) far ha
  rw [hstep] at hc
  exact hc

theorem all_blank_runs_allowed (n : Nat) (c : Config)
    (hr : run target429 n blank = some c) :
    allowed c.state (view c) = true := by
  induction n generalizing c with
  | zero =>
      have hc : c=blank := by simpa [run] using hr.symm
      subst c
      decide
  | succ n ih =>
      cases hp : run target429 n blank with
      | none => simp [run,hp] at hr
      | some d =>
          have hs : rawStep target429 d = some c := by
            simpa [run,hp] using hr
          exact allowed_raw d c hs (ih d hp)

def bad (q : Fin 6) (w : W) : Bool :=
  q.val==0 && !w.c && w.l1 && !w.l3 && !w.r1 && !w.r2 && !w.r3

theorem allowed_excludes_bad :
    ∀ (q : Fin 6) (l4 l3 l2 l1 c r1 r2 r3 r4 : Bool),
    allowed q ⟨l4,l3,l2,l1,c,r1,r2,r3,r4⟩ = true →
    bad q ⟨l4,l3,l2,l1,c,r1,r2,r3,r4⟩ = false := by
  decide

theorem allowed_no_bad (q : Fin 6) (w : W)
    (h : allowed q w = true) : bad q w = false := by
  rcases w with ⟨l4,l3,l2,l1,c,r1,r2,r3,r4⟩
  exact allowed_excludes_bad q l4 l3 l2 l1 c r1 r2 r3 r4 h

/-- Authentic blank-root machine #429 cannot scan A/0 with the seven
neighboring symbols demanded by a chosen forward route into D/0. -/
theorem forbidden_blank_A0_window (n : Nat) (c : Config)
    (hr : run target429 n blank = some c) :
    ¬ (c.state = (⟨0,by decide⟩ : Fin 6) ∧
       c.tape c.head = false ∧
       c.tape (c.head-1) = true ∧
       c.tape (c.head-3) = false ∧
       c.tape (c.head+1) = false ∧
       c.tape (c.head+2) = false ∧
       c.tape (c.head+3) = false) := by
  intro hb
  have hvalid := all_blank_runs_allowed n c hr
  have hcontra := allowed_no_bad c.state (view c) hvalid
  rcases hb with ⟨hs,h0,hl1,hl3,hr1,hr2,hr3⟩
  simp [bad,view,hs,h0,hl1,hl3,hr1,hr2,hr3] at hcontra

#print axioms allowed_closed
#print axioms view_move
#print axioms step_sound
#print axioms all_blank_runs_allowed
#print axioms forbidden_blank_A0_window
end BB429WindowR4
