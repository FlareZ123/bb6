import BlockMacro

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6BlockFAR1
export BB6BlockFAR (Q Ray Move Table Prim run primBlank)
open BB6BlockFAR (cons tail blankRay primStep run_add blank_cons tail_cons)

structure Sym where
  a : Bool
  deriving DecidableEq, Repr

def Sym.zero : Sym := ⟨false⟩
def Sym.code (s : Sym) : Nat := s.a.toNat
def Sym.ofCode (n : Nat) : Sym := ⟨n%2 == 1⟩
def symbols : List Sym := (List.range 2).map Sym.ofCode

theorem symbols_complete (s : Sym) : s ∈ symbols := by
  rcases s with ⟨a⟩
  cases a <;> decide

def ray : List Sym → Ray
  | [] => blankRay
  | a::r => cons a.a (ray r)

theorem ray_unfold (l : List Sym) :
    ray l = cons (l.headD Sym.zero).a (ray l.tail) := by
  cases l with
  | nil => simp [ray,Sym.zero,blank_cons]
  | cons a r => rfl

structure BlockConfig where
  q : Q
  dir : Bool
  l : List Sym
  r : List Sym

def BlockConfig.render (c : BlockConfig) : Prim := ⟨c.q,ray c.l,ray c.r⟩

def BlockConfig.next (c : BlockConfig) (q : Q) (dir : Bool) (w : Sym) : BlockConfig :=
  if dir then ⟨q,true,w::c.l,c.r.tail⟩
  else ⟨q,false,c.l.tail,c.l.headD Sym.zero::w::c.r.tail⟩

structure Exit where
  steps : Nat
  q : Q
  dir : Bool
  w : Sym
  deriving DecidableEq, Repr

def blockExit (M : Table) (q : Q) (_dir : Bool) (a : Sym) : Option Exit :=
  (M q a.a).map fun mv => ⟨1,mv.next,mv.right,⟨mv.write⟩⟩

theorem macro_sound (M : Table) (c : BlockConfig) (e : Exit)
    (h : blockExit M c.q c.dir (c.r.headD Sym.zero) = some e) :
    0 < e.steps ∧ run M e.steps c.render = some (c.next e.q e.dir e.w).render := by
  unfold blockExit at h
  cases hm : M c.q (c.r.headD Sym.zero).a with
  | none => rw [hm] at h; contradiction
  | some mv =>
    rw [hm] at h
    simp only [Option.map_some,Option.some.injEq] at h
    subst e
    constructor
    · exact Nat.zero_lt_one
    · change (primStep M c.render).bind (run M 0) = some _
      unfold primStep BlockConfig.render
      rw [ray_unfold c.r]
      simp only [cons, tail_cons]
      rw [hm]
      cases hd : mv.right
      · simp only [Bind.bind,Pure.pure,Option.bind,hd,Bool.false_eq_true,ite_false,BB6BlockFAR.run,BlockConfig.next]
        rw [ray_unfold c.l]
        rfl
      · simp only [Bind.bind,Pure.pure,Option.bind,hd,ite_true,BB6BlockFAR.run,BlockConfig.next]
        rfl

def blockBlank : BlockConfig := ⟨0,true,[],[]⟩

theorem render_blank : blockBlank.render = primBlank := rfl

theorem forever_of_invariant (M : Table) (P : BlockConfig → Prop)
    (closed : ∀ c, P c → ∃ e, blockExit M c.q c.dir (c.r.headD Sym.zero) = some e ∧ P (c.next e.q e.dir e.w))
    (c : BlockConfig) (hc : P c) : ∀ n, ∃ d, run M n c.render = some d := by
  intro n
  induction n using Nat.strongRecOn generalizing c with
  | ind n ih =>
    obtain ⟨e,he,hnext⟩ := closed c hc
    obtain ⟨hpos,hrun⟩ := macro_sound M c e he
    by_cases hle : e.steps ≤ n
    · obtain ⟨d,hd⟩ := ih (n-e.steps) (by omega) _ hnext
      refine ⟨d,?_⟩
      rw [show n=e.steps+(n-e.steps) by omega,run_add,hrun]
      exact hd
    · have hrun' := hrun
      rw [show e.steps=n+(e.steps-n) by omega,run_add] at hrun'
      cases hh : run M n c.render with
      | none => simp [hh] at hrun'
      | some d => exact ⟨d,rfl⟩

#print axioms macro_sound
#print axioms forever_of_invariant
end BB6BlockFAR1
