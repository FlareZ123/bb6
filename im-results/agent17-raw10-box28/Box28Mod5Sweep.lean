import Box33BinaryCounter
namespace BB6.Agent17.Box28Mod5Sweep
open C9Pair
open BB6.Agent13.Box33BinaryCounter (zeros zero_head zero_pop zero_push rep rep_add ones ones_succ)
def bc (alt : Bool) : Q := if alt then .C else .B
-- The two rows differ only in E1; B and C have identical behavior.
def step (alt : Bool) (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (right .F true c)
  | .B,false | .C,false => some (left .C true c)
  | .B,true | .C,true => some (left .D false c)
  | .D,false => some (right .A false c)
  | .D,true => some (left .F true c)
  | .E,false => none
  | .E,true => some (right (bc alt) false c)
  | .F,false => some (right .A true c)
  | .F,true => some (right .E true c)

def run (alt : Bool) : Nat → Config → Option Config
  | 0,c => some c
  | n+1,c => (step alt c).bind (run alt n)

theorem run_add (alt : Bool) (m n : Nat) (c : Config) :
    run alt (m+n) c = (run alt m c).bind (run alt n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih =>
    rw [Nat.succ_add]; simp only [run]
    cases step alt c <;> simp [ih]

def root (l r : Nat) : Config := ⟨.A,push false (ones l),false,ones r⟩
def sweep (alt : Bool) (l r : Nat) : Config := ⟨bc alt,push false (ones l),false,ones r⟩

theorem right5 (alt : Bool) (l r : Nat) : run alt 11 (root l (r+5)) = some (root (l+5) r) := by
  cases alt <;> rfl

theorem zero (alt : Bool) (l : Nat) : run alt 4 (root l 0) = some (root l 1) := by
  rfl

theorem start1 (alt : Bool) (l : Nat) : run alt 12 (root l 1) = some (sweep alt (l+2) 1) := by
  cases alt <;> rfl

theorem start4 (alt : Bool) (l : Nat) : run alt 9 (root l 4) = some (sweep alt (l+5) 0) := by
  cases alt <;> rfl

theorem left2 (alt : Bool) (l r : Nat) : run alt 6 (sweep alt (l+3) r) = some (sweep alt (l+1) (r+2)) := by
  cases alt <;> rfl

theorem end1 (alt : Bool) (r : Nat) : run alt 4 (sweep alt 1 r) = some (root 0 (r+2)) := by
  cases alt <;> rfl

theorem end2 (alt : Bool) (r : Nat) : run alt 12 (sweep alt 2 (r+3)) = some (root 5 (r+1)) := by
  cases alt <;> rfl

theorem special (alt : Bool) : run alt 38 (root 0 1) = some (root 0 6) := by
  cases alt <;> rfl

theorem leftPairs (alt : Bool) (k l r : Nat) :
    run alt (6*k) (sweep alt (l+1+2*k) r) = some (sweep alt (l+1) (r+2*k)) := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
    rw [show 6*(k+1)=6+6*k by omega,run_add,
      show l+1+2*(k+1)=l+2*k+3 by omega,left2,Option.bind_some,
      show l+2*k+1=l+1+2*k by omega,ih]
    congr 2 <;> omega

def good (l r : Nat) : Prop := l % 5 = 0 ∧ (r % 5 = 0 ∨ r % 5 = 1 ∨ r % 5 = 4)

theorem progress (alt : Bool) (l r : Nat) (hg : good l r) :
    ∃ n l' r', 0 < n ∧ run alt n (root l r) = some (root l' r') ∧ good l' r' := by
  rcases hg with ⟨hl,hr⟩
  by_cases h : 5 ≤ r
  · refine ⟨11,l+5,r-5,by decide,?_,?_⟩
    · rw [← right5 alt l (r-5),show r-5+5=r by omega]
    · unfold good; omega
  have hsmall : r=0 ∨ r=1 ∨ r=4 := by omega
  rcases hsmall with rfl|rfl|rfl
  · exact ⟨4,l,1,by decide,zero alt l,by unfold good; omega⟩
  · by_cases hz : l=0
    · subst l; exact ⟨38,0,6,by decide,special alt,by unfold good; decide⟩
    by_cases he : l%2=0
    · let k := l/2
      have hk : l=2*k := by dsimp [k]; omega
      have hk3 : 3 ≤ 1+2*k := by omega
      refine ⟨12+6*k+12,5,l-1,by omega,?_,by unfold good; omega⟩
      rw [run_add,run_add,start1,Option.bind_some,
        show l+2=1+1+2*k by omega,leftPairs,Option.bind_some,
        show 1+2*k=(l-2)+3 by omega,end2]
      congr 2 <;> omega
    · let k := (l+1)/2
      have hk : l+1=2*k := by dsimp [k]; omega
      refine ⟨12+6*k+4,0,l+4,by omega,?_,by unfold good; omega⟩
      rw [run_add,run_add,start1,Option.bind_some,
        show l+2=0+1+2*k by omega,leftPairs,Option.bind_some,end1]
      congr 2 <;> omega
  · by_cases he : l%2=0
    · let k := (l+4)/2
      have hk : l+4=2*k := by dsimp [k]; omega
      refine ⟨9+6*k+4,0,l+6,by omega,?_,by unfold good; omega⟩
      rw [run_add,run_add,start4,Option.bind_some,
        show l+5=0+1+2*k by omega,leftPairs,Option.bind_some,end1]
      congr 2 <;> omega
    · let k := (l+3)/2
      have hk : l+3=2*k := by dsimp [k]; omega
      have hk3 : 3 ≤ 2*k := by omega
      refine ⟨9+6*k+12,5,l+1,by omega,?_,by unfold good; omega⟩
      rw [run_add,run_add,start4,Option.bind_some,
        show l+5=1+1+2*k by omega,leftPairs,Option.bind_some,
        show 0+2*k=l+3 by omega,end2]

theorem never_root (alt : Bool) (n l r : Nat) (hg : good l r) : run alt n (root l r) ≠ none := by
  induction n using Nat.strongRecOn generalizing l r with
  | ind n ih =>
    intro h
    obtain ⟨k,l',r',hk,hs,hg'⟩ := progress alt l r hg
    by_cases hn : n ≤ k
    · have e : k=n+(k-n) := by omega
      rw [e,run_add,h] at hs
      contradiction
    · have e : n=k+(n-k) := by omega
      rw [e,run_add,hs] at h
      exact ih _ (by omega) l' r' hg' h

theorem never_blank (alt : Bool) (n : Nat) : run alt n ⟨.A,zeros,false,zeros⟩ ≠ none := by
  have h : root 0 0 = ⟨.A,zeros,false,zeros⟩ := by simp [root,ones,rep]
  rw [←h]; exact never_root alt n 0 0 (by unfold good; decide)
#print axioms never_blank
end BB6.Agent17.Box28Mod5Sweep
