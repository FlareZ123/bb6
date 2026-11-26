import Lean

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32MaskBiDFA
/-- Sparse low-bit map with explicit default on absent keys. -/
inductive Map (α : Type) where
  | empty
  | leaf (value : α)
  | branch (even odd : Map α)

def Map.lookup {α} : Map α → Nat → Option α
  | .empty, _ => none
  | .leaf v, n => if n = 0 then some v else none
  | .branch e o, n => if n % 2 = 0 then e.lookup (n/2) else o.lookup (n/2)

def Map.all {α} : Map α → (Nat → α → Bool) → Bool
  | .empty, _ => true
  | .leaf v, f => f 0 v
  | .branch e o, f => e.all (fun n v => f (2*n) v) && o.all (fun n v => f (2*n+1) v)

theorem Map.all_sound {α} {m : Map α} {f : Nat → α → Bool} {n v}
    (h : m.all f = true) (hv : m.lookup n = some v) : f n v = true := by
  induction m generalizing f n with
  | empty => simp [lookup] at hv
  | leaf x =>
    simp only [lookup] at hv
    split at hv <;> rename_i he
    · subst n
      simp only [Option.some.injEq] at hv
      subst x
      exact h
    · contradiction
  | branch e o he ho =>
    simp only [all,Bool.and_eq_true] at h
    by_cases hn : n % 2 = 0
    · have hv' : e.lookup (n/2) = some v := by simpa [lookup,hn] using hv
      have hh := he h.1 hv'
      have eq : 2*(n/2)=n := by omega
      simpa only [eq] using hh
    · have hv' : o.lookup (n/2) = some v := by simpa [lookup,hn] using hv
      have hh := ho h.2 hv'
      have eq : 2*(n/2)+1=n := by omega
      simpa only [eq] using hh

/-- Check every listed source and collect the union of its image. -/
def image (f : Nat → Option Nat) : List Nat → Option Nat
  | [] => some 0
  | i::is => do
      let a ← f i
      let b ← image f is
      pure (a ||| b)

theorem image_sound {f is out i} (h : image f is = some out)
    (hi : i ∈ is) : ∃ x, f i = some x ∧ ∀ j, x.testBit j = true → out.testBit j = true := by
  induction is generalizing out with
  | nil => contradiction
  | cons v vs ih =>
    cases hf : f v with
    | none => simp [image,hf] at h
    | some a =>
      cases hg : image f vs with
      | none => simp [image,hf,hg] at h
      | some b =>
        simp [image,hf,hg] at h
        subst out
        rcases List.mem_cons.mp hi with he|ht
        · subst v
          exact ⟨a,hf,fun j hj => by simp [Nat.testBit_or,hj]⟩
        · obtain ⟨x,hx,hsub⟩ := ih hg ht
          exact ⟨x,hx,fun j hj => by simp [Nat.testBit_or,hsub j hj]⟩

def listMask : List Nat → Nat
  | [] => 0
  | i::is => 2^i ||| listMask is

theorem listMask_mem {is i} (h : (listMask is).testBit i = true) : i ∈ is := by
  induction is with
  | nil => simp [listMask] at h
  | cons j js ih =>
    simp only [listMask,Nat.testBit_or,Bool.or_eq_true,Nat.testBit_two_pow,decide_eq_true_eq] at h
    rcases h with he|ht
    · exact List.mem_cons.mpr (Or.inl he.symm)
    · exact List.mem_cons.mpr (Or.inr (ih ht))

def subset (x y : Nat) : Bool := (x &&& y) == x

theorem subset_sound {x y i : Nat} (h : subset x y = true) (hi : x.testBit i = true) : y.testBit i = true := by
  have he : x &&& y = x := by simpa [subset] using h
  have hb := congrArg (fun n => n.testBit i) he
  simpa [Nat.testBit_and,hi] using hb

structure Cell where
  mask : Nat
  indices : List Nat

end BB6.Agent32MaskBiDFA
