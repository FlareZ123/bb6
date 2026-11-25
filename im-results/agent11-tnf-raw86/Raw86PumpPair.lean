import SweepPumping

set_option maxRecDepth 100000
namespace BB6.Agent11Raw86PumpPair
open BB6Coverage BB6Coverage.Agent31Pump

/-- Both one-hole leaves have the same moving-zero sweep. The false branch
    is open leaf 6; the true branch is open leaf 170. -/
def table (b : Bool) : PartialMachine := fun (q,s) =>
  match q.val,s with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨b,true,if b then 1 else 4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true  => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨b, b, 0⟩)
  | 4,true  => some (some ⟨false,false,1⟩)
  | 5,false => none
  | 5,true  => some (some ⟨false,false,1⟩)
  | _,_ => none

abbrev Zs (n : Nat) := rep [false] n
abbrev Os (n : Nat) := rep [true] n
abbrev C (l r : List Bool) : Z0 := ⟨2,l,r⟩
abbrev D (l r : List Bool) : Z0 := ⟨3,l,r⟩
def marker (b : Bool) : List Bool := if b then [true,true,true,true,false] else [true,true,false]
def tail (b : Bool) : Nat := if b then 2 else 1

def family (b : Bool) (n : Nat) : Z0 :=
  C (Zs (n+2) ++ marker b ++ Os (n+tail b)) []

theorem first (b : Bool) :
    run0 (table b) (if b then 31 else 18) ⟨0,[],[]⟩ = some (family b 0) := by
  cases b <;> decide

theorem enter (b : Bool) (L : List Bool) :
    run0 (table b) 1 (C (false::L) []) = some (D (false::false::L) []) := by
  cases b <;> rfl

theorem left_one (b : Bool) (L R : List Bool) :
    run0 (table b) 1 (D ([false]++L) R) = some (D L ([true]++R)) := by
  cases b <;> rfl

theorem left_many (b : Bool) (n : Nat) (L : List Bool) :
    run0 (table b) n (D (Zs n ++ L) []) = some (D L (Os n)) := by
  simpa using sweepL (table b) 3 [] [] [false] [true] 1 (left_one b) n L []

theorem turn (b : Bool) (L R : List Bool) :
    run0 (table b) 12 (D (marker b ++ L) ([true,true,true]++R)) =
    some (C ([true]++marker b++[true]++L) ([true]++R)) := by
  cases b <;> rfl

theorem right_one (b : Bool) (L R : List Bool) :
    run0 (table b) 1 (C ([true]++L) ([true]++R)) =
      some (C ([true,false]++L) R) := by
  cases b <;> rfl

theorem right_many (b : Bool) (n : Nat) (L : List Bool) :
    run0 (table b) n (C ([true]++L) (Os n)) =
      some (C ([true]++Zs n++L) []) := by
  simpa using sweepR (table b) 2 [true] [] [true] [false] 1 (right_one b) n L []

theorem finish (b : Bool) (L : List Bool) :
    run0 (table b) 1 (C ([true]++L) []) = some (C ([false,false]++L) []) := by
  cases b <;> rfl

/-- Exact primitive renewal cost, with unbounded sweep length. -/
theorem growth (b : Bool) (n : Nat) :
    run0 (table b) (2*n+18) (family b n) = some (family b (n+1)) := by
  have h0 := enter b (Zs (n+1) ++ marker b ++ Os (n+tail b))
  have h1 := left_many b (n+3) (marker b ++ Os (n+tail b))
  have h2 := turn b (Os (n+tail b)) (Os n)
  have h3 := right_many b (n+1) (marker b ++ Os (n+tail b+1))
  have h4 := finish b (Zs (n+1) ++ marker b ++ Os (n+tail b+1))
  have a0 : run0 (table b) 1 (family b n) =
      some (D (Zs (n+3)++marker b++Os (n+tail b)) []) := by
    simpa only [family, rep, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append,
      show n+3=(n+2)+1 by omega, show n+2=(n+1)+1 by omega] using h0
  have a1 : run0 (table b) (n+3) (D (Zs (n+3)++marker b++Os (n+tail b)) []) =
      some (D (marker b++Os (n+tail b)) (Os (n+3))) := by
    simpa only [List.append_assoc] using h1
  have a2 : run0 (table b) 12 (D (marker b++Os (n+tail b)) (Os (n+3))) =
      some (C ([true]++(marker b++Os (n+tail b+1))) (Os (n+1))) := by
    simpa only [rep, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append,
      show n+3=(n+2)+1 by omega, show n+2=(n+1)+1 by omega] using h2
  have a4 : run0 (table b) 1 (C ([true]++Zs (n+1)++(marker b++Os (n+tail b+1))) []) =
      some (family b (n+1)) := by
    simpa only [family, rep, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append,
      show n+1+2=(n+2)+1 by omega, show n+2=(n+1)+1 by omega,
      show n+1+tail b=n+tail b+1 by omega] using h4
  have H := join0 (join0 (join0 (join0 a0 a1) a2) h3) a4
  rw [show 2*n+18=1+(n+3)+12+(n+1)+1 by omega]
  exact H

theorem never (b : Bool) (m : Machine) (hm : compatible (table b) m) : NeverHalts m :=
  never_of_growth (table b) (family b) (if b then 31 else 18)
    (fun n => 2*n+18) (first b) (by intro n; omega) (growth b) m hm

#print axioms first
#print axioms growth
#print axioms never
end BB6.Agent11Raw86PumpPair
