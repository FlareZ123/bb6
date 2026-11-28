import Raw14037Terminal
import Raw140Framed
namespace Raw14037GTerm
open BB6BlockFAR Raw140Orbit Raw140Extra
open Raw140Double (Reach)
open Raw140ERSuffix Raw140ERSuffixLocal Raw140ERExit
open Raw14037SixBank (F loopMany seed)
open Raw14037Counter (G)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
attribute [local irreducible] boundary run

theorem finish (v c : Nat) (X R : List Sym) :
    Reach base (boundary 1 false (U 6 v ++ S 7::S 3::X) (U 2 (c+1) ++ R))
      (G (v+c) X R) := by
  have h0 := sweepL base 1 (S 6) (S 2) 3 v (S 7::S 3::X) (U 2 (c+1) ++ R) (by rfl)
  change run base (v*3) (boundary 1 false (U 6 v ++ S 7::S 3::X) (U 2 (c+1) ++ R)) = some (boundary 1 false (S 7::S 3::X) (U 2 v ++ (U 2 (c+1) ++ R))) at h0
  rw [merge,show v+(c+1)=v+c+1 by omega] at h0
  have h0' : Reach base (boundary 1 false (U 6 v ++ S 7::S 3::X) (U 2 (c+1) ++ R)) (boundary 1 false (S 7::S 3::X) (S 2::(U 2 (v+c) ++ R))) := by
    exact ⟨_,by simpa only [List.append_assoc,merge,show v+(c+1)=v+c+1 by omega,U,List.replicate_succ,List.cons_append] using h0⟩
  have h1 := seed X (U 2 (v+c) ++ R)
  have h2 := loopMany (v+c) (S 7::X) R
  exact Reach.trans h0' ⟨_,join h1 h2⟩

structure Rule where
  src : List Sym
  extra : Nat
  dst : List Sym
  fuel : Nat
  time : Nat
  deriving DecidableEq, Repr

def Rule.valid (q : Q) (d : Bool) (L : List Sym) (r : Rule) : Prop :=
  Raw140Framed.execute base true false r.fuel ⟨q,d,L,r.src⟩ = some (r.time,⟨1,false,[],U 2 (r.extra+1) ++ r.dst⟩)
instance (q : Q) (d : Bool) (L : List Sym) (r : Rule) : Decidable (r.valid q d L) := inferInstanceAs (Decidable (_ = _))

theorem Rule.sound (q : Q) (d : Bool) (L : List Sym) (r : Rule) (hr : r.valid q d L) (v : Nat) (X : List Sym) :
    Reach base (boundary q d (L ++ U 6 v ++ S 7::S 3::X) r.src)
      (G (v+r.extra) X r.dst) := by
  have h0 := Raw140Framed.execute_sound base true false r.fuel r.time
    ⟨q,d,L,r.src⟩ ⟨1,false,[],U 2 (r.extra+1) ++ r.dst⟩ (U 6 v ++ S 7::S 3::X) [] hr
  simp only [Raw140Framed.prim,List.nil_append,List.append_nil,ite_true,ite_false,Bool.false_eq_true,List.append_assoc] at h0
  exact Reach.trans ⟨_,by simpa only [List.append_assoc] using h0⟩ (finish v r.extra X r.dst)

def zeroRule (s : Tail) : Rule :=
  match s with
  | .t542 => ⟨[S 1,S 1,S 5,S 2],5,[],10,30⟩
  | .t152 => ⟨[S 1,S 1,S 1,S 2,S 1],4,[S 1,S 5],16,50⟩
  | .t1121 => ⟨[S 1,S 5,S 2,S 1,S 5],4,[S 1,S 5],8,24⟩
  | .t5215 => ⟨[S 1,S 1,S 1,S 5,S 5],5,[S 5],12,36⟩
  | .t1155 => ⟨[S 1,S 1,S 1,S 5,S 1,S 1],5,[S 1,S 1],12,36⟩
  | .t11511 => ⟨[S 1,S 1,S 1,S 5,S 5,S 4,S 2],5,[S 5,S 4,S 2],12,36⟩

theorem zero_valid (s : Tail) : (zeroRule s).valid 4 false [S 2,S 2] := by cases s <;> decide +kernel

theorem zeroPrep (j v : Nat) (r : Rule) (Y X : List Sym) (h : r.src = U 1 (j+1) ++ Y)
    (hr : r.valid 4 false [S 2,S 2]) :
    Reach base (boundary 4 false (U 3 (j+1) ++ S 2::S 2::(U 6 v ++ S 7::S 3::X)) Y)
      (G (v+r.extra) X r.dst) := by
  have h0 := sweepL base 4 (S 3) (S 1) 3 (j+1) (S 2::S 2::(U 6 v ++ S 7::S 3::X)) Y (by rfl)
  have h1 := r.sound 4 false [S 2,S 2] hr v X
  rw [h] at h1
  exact Reach.trans ⟨_,h0⟩ h1

theorem zero (v w : Nat) (s : Tail) (X : List Sym) :
    Reach base (F 0 v (w+1) s X) (G (v+(zeroRule s).extra) (U 3 w ++ X) (zeroRule s).dst) := by
  let Z := S 2::S 2::(U 6 v ++ S 7::(U 3 (w+1) ++ X))
  cases s with
  | t542 => exact Reach.trans ⟨_,prep542 Z⟩ (zeroPrep 1 v _ [S 5,S 2] (U 3 w ++ X) rfl (zero_valid .t542))
  | t152 => exact Reach.trans ⟨_,prep152 Z⟩ (zeroPrep 1 v _ [S 1,S 2,S 1] (U 3 w ++ X) rfl (zero_valid .t152))
  | t1121 => exact Reach.trans ⟨_,prep1121 Z⟩ (zeroPrep 0 v _ [S 5,S 2,S 1,S 5] (U 3 w ++ X) rfl (zero_valid .t1121))
  | t5215 => exact Reach.trans ⟨_,prep5215 Z⟩ (zeroPrep 0 v _ [S 1,S 1,S 5,S 5] (U 3 w ++ X) rfl (zero_valid .t5215))
  | t1155 => exact Reach.trans ⟨_,prep1155 Z⟩ (zeroPrep 2 v _ [S 5,S 1,S 1] (U 3 w ++ X) rfl (zero_valid .t1155))
  | t11511 => exact Reach.trans ⟨_,prep11511 Z⟩ (zeroPrep 2 v _ [S 5,S 5,S 4,S 2] (U 3 w ++ X) rfl (zero_valid .t11511))

def rules : List Rule := [
  ⟨[S 1,S 5,S 2],2,[S 5,S 2],9,27⟩,
  ⟨[S 5,S 2],3,[S 1],13,37⟩,
  ⟨[S 1],2,[],9,27⟩,
  ⟨[],0,[S 1,S 5],9,27⟩,
  ⟨[S 1,S 5],2,[S 5],9,27⟩,
  ⟨[S 5],1,[S 4,S 2],11,29⟩,
  ⟨[S 4,S 2],0,[S 5,S 2,S 2,S 1],15,43⟩,
  ⟨[S 5,S 2,S 2,S 1],3,[S 3,S 1],13,37⟩,
  ⟨[S 1,S 1,S 2,S 1],2,[S 1,S 2,S 1],9,27⟩,
  ⟨[S 1,S 2,S 1],3,[S 1],9,27⟩,
  ⟨[S 1,S 1,S 5,S 1,S 1],2,[S 1,S 5,S 1,S 1],9,27⟩,
  ⟨[S 1,S 5,S 1,S 1],2,[S 5,S 1,S 1],9,27⟩,
  ⟨[S 5,S 1,S 1],3,[S 4,S 2],27,85⟩,
  ⟨[S 1,S 1,S 5,S 5,S 4,S 2],2,[S 1,S 5,S 5,S 4,S 2],9,27⟩,
  ⟨[S 1,S 5,S 5,S 4,S 2],2,[S 5,S 5,S 4,S 2],9,27⟩,
  ⟨[S 5,S 5,S 4,S 2],5,[],23,69⟩,
  ⟨[S 1,S 1],2,[S 1],9,27⟩,
  ⟨[S 5,S 2,S 1,S 5],2,[S 1,S 5,S 5],15,45⟩,
  ⟨[S 1,S 5,S 5],2,[S 5,S 5],9,27⟩,
  ⟨[S 1,S 1,S 5,S 5],2,[S 1,S 5,S 5],9,27⟩,
  ⟨[S 5,S 4,S 2],1,[S 4,S 6,S 2],11,29⟩,
  ⟨[S 4,S 6,S 2],0,[S 5,S 4,S 4,S 4],23,65⟩,
  ⟨[S 5,S 4,S 4,S 4],1,[S 4,S 6,S 4,S 4],11,29⟩,
  ⟨[S 4,S 6,S 4,S 4],0,[S 5,S 4,S 4,S 4,S 2,S 2,S 1],39,109⟩,
  ⟨[S 5,S 4,S 4,S 4,S 2,S 2,S 1],1,[S 4,S 6,S 4,S 4,S 2,S 2,S 1],11,29⟩,
  ⟨[S 4,S 6,S 4,S 4,S 2,S 2,S 1],0,[S 5,S 4,S 4,S 4,S 4,S 4,S 2,S 1],39,109⟩,
  ⟨[S 5,S 4,S 4,S 4,S 4,S 4,S 2,S 1],1,[S 4,S 6,S 4,S 4,S 4,S 4,S 2,S 1],11,29⟩,
  ⟨[S 4,S 6,S 4,S 4,S 4,S 4,S 2,S 1],0,[S 5,S 4,S 4,S 4,S 4,S 4,S 4,S 0,S 5],55,155⟩,
  ⟨[S 5,S 4,S 4,S 4,S 4,S 4,S 4,S 0,S 5],1,[S 4,S 6,S 4,S 4,S 4,S 4,S 4,S 0,S 5],11,29⟩,
  ⟨[S 4,S 6,S 4,S 4,S 4,S 4,S 4,S 0,S 5],0,[S 5,S 4,S 4,S 4,S 4,S 4,S 4,S 2,S 5,S 4,S 2],69,191⟩,
  ⟨[S 5,S 4,S 4,S 4,S 4,S 4,S 4,S 2,S 5,S 4,S 2],1,[S 4,S 6,S 4,S 4,S 4,S 4,S 4,S 2,S 5,S 4,S 2],11,29⟩,
  ⟨[S 4,S 6,S 4,S 4,S 4,S 4,S 4,S 2,S 5,S 4,S 2],0,[S 5,S 4,S 4,S 4,S 4,S 4,S 4,S 4,S 4,S 4,S 6,S 2],67,185⟩]

theorem validRules : ∀ r ∈ rules, r.valid 3 true [S 6,S 2] := by decide +kernel

def follow : Nat → List Sym → Option (Nat × List Sym)
  | 0, s => some (0,s)
  | n+1, s => do
    let r ← rules.find? (fun r => r.src == s)
    let (a,t) ← follow n r.dst
    return (r.extra+a,t)

theorem follow_sound (k v j : Nat) (s t X : List Sym)
    (h : follow k s = some (j,t)) :
    Reach base (G v (U 3 k ++ X) s) (G (v+j) X t) := by
  induction k generalizing v j s with
  | zero => simp [follow] at h; obtain ⟨rfl,rfl⟩ := h; simpa [U] using Reach.refl base (G v X s)
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
        have h0 := r.sound 3 true [S 6,S 2] (validRules r hmem) v (U 3 k ++ X)
        rw [hsrc] at h0
        have h1 := ih (v+r.extra) b r.dst ht
        simpa only [G,U,List.replicate_succ,List.cons_append,List.nil_append,Nat.add_assoc] using Reach.trans h0 h1

def terminalRoute (n : Bool) (s : Tail) : Nat × Nat × List Sym :=
  match n,s with
  | false,.t542 => (5,6,[S 3,S 1])
  | false,.t152 => (4,6,[S 3,S 1])
  | false,.t1121 => (4,6,[S 3,S 1])
  | false,.t5215 => (3,4,[S 3,S 1])
  | false,.t1155 => (7,10,[S 3,S 1])
  | false,.t11511 => (0,0,[S 5,S 4,S 2])
  | true,.t542 => (8,13,[S 3,S 1])
  | true,.t152 => (8,13,[S 3,S 1])
  | true,.t1121 => (2,4,[S 5,S 5])
  | true,.t5215 => (2,4,[S 5,S 5])
  | true,.t1155 => (5,10,[S 3,S 1])
  | true,.t11511 => (8,15,[S 3,S 1])

def terminalSource (n : Bool) (s : Tail) :=
  if n then trip115 (extra s) ++ tailWord (rho s) else (zeroRule s).dst

def terminalExtra (n : Bool) (s : Tail) := if n then 5 else (zeroRule s).extra

theorem route_correct (n : Bool) (s : Tail) :
    follow (terminalRoute n s).1 (terminalSource n s) = some (terminalRoute n s).2 := by
  cases n <;> cases s <;> decide +kernel

theorem terminal_sound (n : Bool) (s : Tail) (v w : Nat) (X : List Sym) (hw : (terminalRoute n s).1+1 ≤ w) :
    Reach base (F (if n then 1 else 0) v w s X)
      (G (v+terminalExtra n s+(terminalRoute n s).2.1) (U 3 (w-1-(terminalRoute n s).1) ++ X) (terminalRoute n s).2.2) := by
  have hw' : w-1+1=w := by omega
  have h0 : Reach base (F (if n then 1 else 0) v w s X)
      (G (v+terminalExtra n s) (U 3 (w-1) ++ X) (terminalSource n s)) := by
    cases n with
    | false => simpa only [terminalExtra,terminalSource,if_false,Bool.false_eq_true,hw'] using zero v (w-1) s X
    | true => simpa only [terminalExtra,terminalSource,if_true,hw'] using Raw14037Terminal.one v (w-1) s X
  have h1 := follow_sound (terminalRoute n s).1 (v+terminalExtra n s) (terminalRoute n s).2.1
    (terminalSource n s) (terminalRoute n s).2.2 (U 3 (w-1-(terminalRoute n s).1) ++ X) (route_correct n s)
  rw [merge,show (terminalRoute n s).1+(w-1-(terminalRoute n s).1)=w-1 by omega] at h1
  exact Reach.trans h0 h1

#print axioms zero
#print axioms terminal_sound
end Raw14037GTerm
