import Lean

namespace BB6.DRootL

structure S where
 a : Nat
 q : Nat
 b : Nat
 deriving DecidableEq, Repr

/-- Arithmetic table for regular L-family first-return endpoints, subject to
    the known original-source family compositions and physical tape padding. -/
def step (s : S) : Option S := Id.run do
 let a := s.a
 let q := s.q
 let b := s.b
 if a % 3 == 2 then
   let k := (a-2)/3
   if q == 0 then return some ⟨8*k+9,0,0⟩
   if q == 1 then return some ⟨8*k+10+b,0,0⟩
   return some ⟨8*k+10,q-1,b⟩
 if a % 3 == 0 then
   let k := (a-3)/3
   if q == 0 then return some ⟨8*k+11,0,0⟩
   let r := (b+1)/3
   let d := q-1+4*r
   if (b+1)%3 == 0 then return some ⟨8*k+11+2*d,0,0⟩
   if (b+1)%3 == 1 then return some ⟨8*k+13+2*d,0,0⟩
   return some ⟨8*k+7+2*d,1,5⟩
 let k := (a-4)/3
 if q == 0 then return some ⟨8*k+5,1,5⟩
 if b == 0 then return some ⟨8*k+5,1,2*q+5⟩
 if b == 2 then return some ⟨8*k+9,q+1,0⟩
 if b >= 3 then return some ⟨8*k+9,q+2,b-3⟩
 return none

def run : Nat → Option S → Option S
 | 0,s => s
 | n+1,s => run n (s.bind step)

set_option maxRecDepth 180000
set_option maxHeartbeats 0

theorem run_add (m n : Nat) (s : Option S) :
    run (m+n) s = run n (run m s) := by
  induction m generalizing s with
  | zero => simp only [Nat.zero_add,run]
  | succ m ih =>
    simpa only [Nat.succ_add,run] using ih (s.bind step)

theorem run_none (n : Nat) : run n none = none := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [run] using ih

theorem no_early_exit (seed : Option S) (N : Nat)
    (h : run N seed ≠ none) (i : Nat) (hi : i ≤ N) :
    run i seed ≠ none := by
  intro hn
  have heq : i + (N-i) = N := Nat.add_sub_of_le hi
  have hconcat := run_add i (N-i) seed
  rw [heq,hn,run_none] at hconcat
  exact h hconcat

def seed5 : Option S := some ⟨5,0,0⟩
def seed9 : Option S := some ⟨9,0,0⟩
def seed15 : Option S := some ⟨15,0,0⟩
def seed39 : Option S := some ⟨39,0,0⟩

/-- Each certificate names the first regular-language exit in the
    source-derived arithmetic section model. None means OUTSIDE this model,
    and does NOT mean the original Turing machine halts. -/
theorem seed5_exception :
  (run 1711 seed5).any (fun s => s.a%243 == 211 && s.q == 5 && s.b == 1) = true := by decide
theorem seed9_exception :
  (run 8394 seed9).any (fun s => s.a%243 == 157 && s.q == 6 && s.b == 1) = true := by decide
theorem seed15_exception :
  (run 9458 seed15).any (fun s => s.a%243 == 121 && s.q == 9 && s.b == 1) = true := by decide
theorem seed39_exception :
  (run 7611 seed39).any (fun s => s.a%243 == 46 && s.q == 7 && s.b == 1) = true := by decide

theorem seed5_exit : run 1712 seed5 = none := by decide
theorem seed9_exit : run 8395 seed9 = none := by decide
theorem seed15_exit : run 9459 seed15 = none := by decide
theorem seed39_exit : run 7612 seed39 = none := by decide

/-- All modeled earlier sections are within the L-family. -/
theorem seed5_prior (i : Nat) (hi : i ≤ 1711) : run i seed5 ≠ none := by
  apply no_early_exit seed5 1711 _ i hi
  intro hn
  simpa [hn] using seed5_exception

theorem seed9_prior (i : Nat) (hi : i ≤ 8394) : run i seed9 ≠ none := by
  apply no_early_exit seed9 8394 _ i hi
  intro hn
  simpa [hn] using seed9_exception

theorem seed15_prior (i : Nat) (hi : i ≤ 9458) : run i seed15 ≠ none := by
  apply no_early_exit seed15 9458 _ i hi
  intro hn
  simpa [hn] using seed15_exception

theorem seed39_prior (i : Nat) (hi : i ≤ 7611) : run i seed39 ≠ none := by
  apply no_early_exit seed39 7611 _ i hi
  intro hn
  simpa [hn] using seed39_exception

#print axioms seed5_exception
#print axioms seed9_exception
#print axioms seed15_exception
#print axioms seed39_exception
#print axioms seed5_prior
#print axioms seed9_prior
#print axioms seed15_prior
#print axioms seed39_prior
end BB6.DRootL
