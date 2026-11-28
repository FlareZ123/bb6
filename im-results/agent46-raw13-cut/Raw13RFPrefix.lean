import SweepPumping
import FastFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13RFPrefix
open BB6Coverage BB6Coverage.Agent31Pump
abbrev p : PartialMachine := FAR.fromCodes [7,14,11,8,2,19,5,0,1,21,0,24]
abbrev P : List Bool := [true,false]
abbrev V : List Bool := [true,true,true,true,true,true]
inductive Digit | d0 | d1 | d2 | d3
abbrev digit : Digit → List Bool
 | .d0 => [false,true,false,true,false,true]
 | .d1 => [false,true,true,false,false,true]
 | .d2 => [false,true,false,true,true,true]
 | .d3 => [false,true,true,false,true,true]
abbrev term (b : Bool) : List Bool := if b then [false,true,true,false,true] else [false,true,false,true,true]
def enc : List Digit → Bool → List Bool
 | [],b => term b
 | d::ds,b => digit d ++ enc ds b
def inc : List Digit → Bool → List Digit × Bool
 | [],false => ([],true)
 | [],true => ([.d0],false)
 | .d0::ds,b => (.d1::ds,b)
 | .d1::ds,b => (.d2::ds,b)
 | .d2::ds,b => (.d3::ds,b)
 | .d3::ds,b => let x:=inc ds b; (.d0::x.1,x.2)
abbrev A (l r : List Bool) : Z0 := ⟨0,l,r⟩
abbrev E (l r : List Bool) : Z0 := ⟨4,l,r⟩
def Reach (a b : Z0) : Prop := ∃ t, run0 p t a = some b
theorem reach {t : Nat} {a b : Z0} (h : run0 p t a = some b) : Reach a b := ⟨t,h⟩
theorem chain {a b c : Z0} (h : Reach a b) (g : Reach b c) : Reach a c := by
  obtain ⟨t,ht⟩ := h; obtain ⟨u,hu⟩ := g; exact ⟨t+u,join0 ht hu⟩
theorem unload (L R : List Bool) : run0 p 6 (A (true::(V++L)) R) = some (A (true::L) (digit .d0++R)) := by rfl
theorem carry (ds : List Digit) (b : Bool) (L : List Bool) :
  Reach (E (true::L) (enc ds b)) (A (true::L) (enc (inc ds b).1 (inc ds b).2)) := by
  induction ds generalizing L with
  | nil => cases b
           · exact ⟨12,rfl⟩
           · exact ⟨34,rfl⟩
  | cons d ds ih =>
    cases d with
    | d0 => exact ⟨12,rfl⟩
    | d1 => exact ⟨14,rfl⟩
    | d2 => exact ⟨12,rfl⟩
    | d3 =>
      have h1 : run0 p 10 (E (true::L) (enc (.d3::ds) b)) = some (E (true::(V++L)) (enc ds b)) := by rfl
      have h2 := ih (V++L)
      have h3 := unload L (enc (inc ds b).1 (inc ds b).2)
      exact chain (chain (reach h1) h2) (reach h3)
theorem startInc (ds : List Digit) (b : Bool) (L : List Bool) :
  Reach (A (false::false::L) (enc ds b)) (A (true::false::L) (enc (inc ds b).1 (inc ds b).2)) := by
  cases ds with
  | nil => cases b
           · exact ⟨10,rfl⟩
           · exact ⟨32,rfl⟩
  | cons d ds =>
    cases d with
    | d0 => exact ⟨10,rfl⟩
    | d1 => exact ⟨12,rfl⟩
    | d2 => exact ⟨10,rfl⟩
    | d3 =>
      have h1 : run0 p 8 (A (false::false::L) (enc (.d3::ds) b)) = some (E (true::(V++false::L)) (enc ds b)) := by rfl
      have h2 := carry ds b (V++false::L)
      have h3 := unload (false::L) (enc (inc ds b).1 (inc ds b).2)
      exact chain (chain (reach h1) h2) (reach h3)
theorem first (R : List Bool) : run0 p 4 (A [] (P++R)) = some (A [false,false,true] R) := by rfl
theorem scan (L R : List Bool) : run0 p 4 (A ([false,false]++L) (P++R)) = some (A ([false,false]++P++L) R) := by rfl
theorem restore (L R : List Bool) : run0 p 4 (A (P++L) R) = some (A L (P++R)) := by rfl
theorem last (R : List Bool) : run0 p 4 (A [true] R) = some (A [] (P++R)) := by rfl

def root (n : Nat) (x : List Digit × Bool) : Z0 := A [] (rep P (n+1)++enc x.1 x.2)
theorem rootGrowth (n : Nat) (x : List Digit × Bool) : ∃ t, 0<t ∧ run0 p t (root n x) = some (root (n+1) (inc x.1 x.2)) := by
  have h1 := first (rep P n++enc x.1 x.2)
  have h2 := sweepR p 0 [false,false] [] P P 4 (by intro L R; exact scan L R) n [true] (enc x.1 x.2)
  have h3 := startInc x.1 x.2 (rep P n++[true])
  have h4 := sweepL p 0 [] [] P P 4 (by intro L R; exact restore L R) (n+1) [true] (enc (inc x.1 x.2).1 (inc x.1 x.2).2)
  have h5 := last (rep P (n+1)++enc (inc x.1 x.2).1 (inc x.1 x.2).2)
  have h1' : run0 p 4 (root n x) = some (A [false,false,true] (rep P n++enc x.1 x.2)) := by simpa only [root,rep,List.append_assoc] using h1
  have h23 : Reach (A [false,false,true] (rep P n++enc x.1 x.2)) (A (rep P (n+1)++[true]) (enc (inc x.1 x.2).1 (inc x.1 x.2).2)) := by
    simpa only [rep,List.append_assoc,List.nil_append,List.cons_append] using chain (reach h2) h3
  have h45 : Reach (A (rep P (n+1)++[true]) (enc (inc x.1 x.2).1 (inc x.1 x.2).2)) (root (n+1) (inc x.1 x.2)) := by
    simpa only [root,rep,List.append_assoc,List.nil_append] using chain (reach h4) (reach h5)
  obtain ⟨t,ht⟩ := chain h23 h45
  exact ⟨4+t,by omega,join0 h1' ht⟩
def words : Nat → List Digit × Bool
 | 0 => ([],false)
 | n+1 => inc (words n).1 (words n).2
def family (n : Nat) := root n (words n)
theorem seed : run0 p 21 (A [] []) = some (family 0) := by rfl
theorem growth (n : Nat) : ∃ t, 0<t ∧ run0 p t (family n) = some (family (n+1)) := rootGrowth n (words n)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  let cost := fun n => Classical.choose (growth n)
  exact never_of_growth p family 21 cost seed (fun n => (Classical.choose_spec (growth n)).1) (fun n => (Classical.choose_spec (growth n)).2) m hm
#print axioms growth
#print axioms never
end BB6.Agent46Raw13RFPrefix
