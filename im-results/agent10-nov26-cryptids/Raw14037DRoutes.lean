import Raw14037DTerm
namespace Raw14037DRoutes
open BB6BlockFAR Raw140Orbit Raw140Extra Raw14037DTerm Raw14042Counter
open Raw140Double (Reach)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
attribute [local irreducible] boundary run

def follow : Nat → List Sym → Option (Nat × List Sym)
  | 0, s => some (0,s)
  | n+1, s => do
    let r ← rules.find? (fun r => r.src == s)
    let (a,t) ← follow n r.dst
    return (r.extra5+r.extra4+a,t)

theorem follow_sound (k a j : Nat) (s t X : List Sym)
    (h : follow k s = some (j,t)) :
    Reach base (boundary 3 false (U 6 k ++ X) (U 4 (a+1) ++ s))
      (boundary 3 false X (U 4 (a+1+j) ++ t)) := by
  induction k generalizing a j s with
  | zero => simp [follow] at h; obtain ⟨rfl,rfl⟩ := h; simpa [U] using Reach.refl base (boundary 3 false X (U 4 (a+1) ++ s))
  | succ k ih =>
    simp only [follow] at h
    cases hr : rules.find? (fun r => r.src == s) with
    | none => simp [hr] at h
    | some r =>
      have hmem : r ∈ rules := List.mem_of_find?_eq_some hr
      have hsrc : r.src = s := by
        have he := List.find?_some hr
        simpa using he
      cases ht : follow k r.dst with
      | none => simp [hr,ht] at h
      | some p =>
        rcases p with ⟨b,u⟩
        simp [hr,ht] at h
        obtain ⟨rfl,rfl⟩ := h
        have h0 := soundRule r hmem a (U 6 k ++ X)
        have h1 := ih (a+r.extra5+r.extra4) b r.dst ht
        rw [show a+r.extra5+r.extra4+1=a+1+r.extra5+r.extra4 by omega] at h1
        rw [hsrc] at h0
        simpa only [U,List.replicate_succ,List.cons_append,show a+1+r.extra5+r.extra4+b=a+1+(r.extra5+r.extra4+b) by omega] using Reach.trans h0 h1

def route (n : Bool) (s : CTail) : Nat × Nat × List Sym :=
  match n,s with
  | false,.c31 => (0,0,[S 2,S 3,S 1])
  | false,.c32 => (3,6,[S 6,S 2])
  | false,.c315 => (6,11,[S 6,S 2])
  | false,.c325 => (5,10,[S 6,S 2])
  | false,.c3242 => (5,10,[S 6,S 2])
  | false,.c35221 => (4,9,[S 6,S 2])
  | true,.c31 => (8,15,[S 6,S 2])
  | true,.c32 => (1,5,[S 2,S 1,S 5])
  | true,.c315 => (9,18,[S 6,S 2])
  | true,.c325 => (9,18,[S 6,S 2])
  | true,.c3242 => (3,9,[S 2,S 3,S 1])
  | true,.c35221 => (3,9,[S 2,S 3,S 1])

def source (n : Bool) (s : CTail) := S 2::(T (if n then 1 else 0) ++ cword s)

theorem route_correct (n : Bool) (s : CTail) :
    follow (route n s).1 (source n s) = some (route n s).2 := by
  cases n <;> cases s <;> decide +kernel

theorem route_sound (n : Bool) (s : CTail) (a k : Nat) (X : List Sym) (h : (route n s).1 ≤ k) :
    Reach base (boundary 3 false (U 6 k ++ X) (U 4 (a+1) ++ source n s))
      (boundary 3 false (U 6 (k-(route n s).1) ++ X) (U 4 (a+1+(route n s).2.1) ++ (route n s).2.2)) := by
  have hs := follow_sound (route n s).1 a (route n s).2.1 (source n s) (route n s).2.2 (U 6 (k-(route n s).1) ++ X) (route_correct n s)
  rw [merge,show (route n s).1+(k-(route n s).1)=k by omega] at hs
  exact hs

#print axioms route_sound
end Raw14037DRoutes
