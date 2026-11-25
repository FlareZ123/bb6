import Raw60LFUnaryCore
namespace BB6.Agent1Raw60LFPrefixCounter
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1Raw60LFUnaryCore
set_option maxRecDepth 4000
set_option maxHeartbeats 4000000
def table (g fast : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => if g then some (some ⟨true,fast,if fast then 0 else 3⟩) else if fast then some (some ⟨true,true,1⟩) else some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
abbrev B := Q 1
abbrev P : List Bool := [false,false,false,true,true]
abbrev J : List Bool := [true,true,true,false,true]
abbrev K : List Bool := [true,true,false,true]
abbrev I : List Bool := [false,true,true]

def rep (w : List Bool) : Nat → List Bool → List Bool
  | 0,R => R
  | n+1,R => w++rep w n R

theorem repEnd (w : List Bool) (n : Nat) (R : List Bool) : rep w n (w++R)=rep w (n+1) R := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,ih]

inductive Digit where
  | hi | mid | lo

def digit (g : Bool) (d : Digit) : List Bool :=
  match g,d with
  | false,.hi => [true,true]
  | false,.mid => [false,false]
  | false,.lo => [true,false]
  | true,.hi => [true,true,true]
  | true,.mid => [true,false,true]
  | true,.lo => [true,false,false]

def enc (g : Bool) : List Digit → List Bool
  | [] => [true,false]
  | d::ds => digit g d++enc g ds

def nextTail : List Digit → List Digit
  | [] => [.hi]
  | .hi::ds => .mid::ds
  | .mid::ds => .lo::ds
  | .lo::ds => .hi::nextTail ds

def len (g : Bool) := if g then 3 else 2
def pushCost (g fast : Bool) := (if g then 1 else 0)+(if fast then 2 else 4)
def hiCost (fast : Bool) := if fast then 5 else 7
def midCost (g fast : Bool) := if g && fast then 7 else 9

theorem scan (g fast : Bool) (s : List Digit) (L : List Bool) : Reach (table g fast)
    (B (false::L) (enc g s)) (F L (true::enc g (nextTail s))) := by
  induction s generalizing L with
  | nil =>
    have h1 : run0 (table g fast) (pushCost g fast) (B (false::L) (enc g [])) = some (B (false::(U (len g)++L)) []) := by cases g <;> cases fast <;> rfl
    have h2 : run0 (table g fast) 9 (B (false::(U (len g)++L)) []) = some (F (U (len g)++L) [true,true,false]) := by cases g <;> cases fast <;> rfl
    have h3 : run0 (table g fast) (len g) (F (U (len g)++L) [true,true,false]) = some (F L (true::enc g (nextTail []))) := by cases g <;> cases fast <;> rfl
    exact ⟨_,join0 (join0 h1 h2) h3⟩
  | cons d ds ih =>
    cases d with
    | hi => exact ⟨hiCost fast,by cases g <;> cases fast <;> rfl⟩
    | mid => exact ⟨midCost g fast,by cases g <;> cases fast <;> rfl⟩
    | lo =>
      have h1 : run0 (table g fast) (pushCost g fast) (B (false::L) (enc g (.lo::ds))) = some (B (false::(U (len g)++L)) (enc g ds)) := by cases g <;> cases fast <;> rfl
      have h2 := ih (U (len g)++L)
      have h3 : run0 (table g fast) (len g) (F (U (len g)++L) (true::enc g (nextTail ds))) = some (F L (true::enc g (nextTail (.lo::ds)))) := by cases g <;> cases fast <;> rfl
      exact reachTrans ⟨_,h1⟩ (reachTrans h2 ⟨_,h3⟩)

def head : Digit → List Bool
  | .hi => [true,true]
  | .mid => [false,true]
  | .lo => [false,false]
abbrev Counter := Digit × List Digit

def bits (g : Bool) (c : Counter) := head c.1++enc g c.2

def next : Counter → Counter
  | (.hi,s) => (.mid,s)
  | (.mid,s) => (.lo,s)
  | (.lo,s) => (.hi,nextTail s)

theorem sub (g fast : Bool) (c : Counter) (L : List Bool) : Reach (table g fast)
    (B (false::L) (I++bits g c)) (F (K++L) (bits g (next c))) := by
  obtain ⟨d,s⟩ := c
  cases d with
  | hi => exact ⟨5,by cases g <;> cases fast <;> rfl⟩
  | mid => exact ⟨7,by cases g <;> cases fast <;> rfl⟩
  | lo =>
    have h1 : run0 (table g fast) 5 (B (false::L) (I++bits g (.lo,s))) = some (B (false::(J++L)) (enc g s)) := by cases g <;> cases fast <;> rfl
    have h2 := scan g fast s (J++L)
    have h3 : run0 (table g fast) 1 (F (J++L) (true::enc g (nextTail s))) = some (F (K++L) (bits g (next (.lo,s)))) := by cases g <;> cases fast <;> rfl
    exact reachTrans ⟨5,h1⟩ (reachTrans h2 ⟨1,h3⟩)

theorem pack (g fast : Bool) (n : Nat) (L R : List Bool) : Reach (table g fast)
    (B (false::L) (I++rep P n R)) (B (false::rep J n L) (I++R)) := by
  induction n generalizing L with
  | zero => exact ⟨0,by rfl⟩
  | succ n ih =>
    have h1 : run0 (table g fast) 5 (B (false::L) (I++rep P (n+1) R)) = some (B (false::(J++L)) (I++rep P n R)) := by cases g <;> cases fast <;> rfl
    have h2 := ih (J++L)
    rw [repEnd J n L] at h2
    exact reachTrans ⟨5,h1⟩ h2

theorem unpack (g fast : Bool) (n : Nat) (L R : List Bool) : Reach (table g fast)
    (F (K++rep J n L) R) (F (K++L) (rep P n R)) := by
  induction n generalizing R with
  | zero => exact ⟨0,by rfl⟩
  | succ n ih =>
    have h1 : run0 (table g fast) 5 (F (K++rep J (n+1) L) R) = some (F (K++rep J n L) (P++R)) := by cases g <;> cases fast <;> rfl
    have h2 := ih (P++R)
    rw [repEnd P n R] at h2
    exact reachTrans ⟨5,h1⟩ h2

def cfg (g : Bool) (n : Nat) (c : Counter) := F [] (rep P (n+1) (bits g c))

theorem advance (g fast : Bool) (n : Nat) (c : Counter) : ∃ t, 0<t ∧ run0 (table g fast) t (cfg g n c) = some (cfg g (n+1) (next (next c))) := by
  have h1 : run0 (table g fast) 16 (cfg g n c) = some (B (false::J) (I++rep P n (bits g c))) := by cases g <;> cases fast <;> rfl
  obtain ⟨a,ha⟩ := pack g fast n J (bits g c)
  have hJ : rep J n J = rep J (n+1) [] := repEnd J n []
  rw [hJ] at ha
  obtain ⟨b,hb⟩ := sub g fast c (rep J (n+1) [])
  obtain ⟨d,hd⟩ := unpack g fast (n+1) [] (bits g (next c))
  have h2 : run0 (table g fast) 5 (F K (rep P (n+1) (bits g (next c)))) = some (B [false,true] (I++rep P (n+1) (bits g (next c)))) := by cases g <;> cases fast <;> rfl
  obtain ⟨e,he⟩ := pack g fast (n+1) [true] (bits g (next c))
  obtain ⟨f,hf⟩ := sub g fast (next c) (rep J (n+1) [true])
  obtain ⟨h,hh⟩ := unpack g fast (n+1) [true] (bits g (next (next c)))
  have h3 : run0 (table g fast) 5 (F (K++[true]) (rep P (n+1) (bits g (next (next c))))) = some (cfg g (n+1) (next (next c))) := by cases g <;> cases fast <;> rfl
  exact ⟨_,by omega,join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 h1 ha) hb) hd) h2) he) hf) hh) h3⟩

def counters : Nat → Counter
  | 0 => (.hi,[])
  | n+1 => next (next (counters n))
def family (g : Bool) (n : Nat) := cfg g n (counters n)
theorem entry (g fast : Bool) : run0 (table g fast) 42 ⟨0,[],[]⟩ = some (family g 0) := by cases g <;> cases fast <;> rfl

theorem growth_exists (g fast : Bool) (n : Nat) : ∃ t, 0<t ∧ run0 (table g fast) t (family g n) = some (family g (n+1)) := advance g fast n (counters n)
noncomputable def cost (g fast : Bool) (n : Nat) : Nat := Classical.choose (growth_exists g fast n)
theorem never (g fast : Bool) (m : Machine) (hm : compatible (table g fast) m) : NeverHalts m :=
  never_of_growth (table g fast) (family g) 42 (cost g fast) (entry g fast) (fun n => (Classical.choose_spec (growth_exists g fast n)).1)
    (fun n => (Classical.choose_spec (growth_exists g fast n)).2) m hm
#print axioms never
namespace V1024
def table := BB6.Agent1Raw60LFPrefixCounter.table false false
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6.Agent1Raw60LFPrefixCounter.never false false m hm
end V1024
namespace V1036
def table := BB6.Agent1Raw60LFPrefixCounter.table false true
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6.Agent1Raw60LFPrefixCounter.never false true m hm
end V1036
namespace V1032
def table := BB6.Agent1Raw60LFPrefixCounter.table true false
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6.Agent1Raw60LFPrefixCounter.never true false m hm
end V1032
namespace V1035
def table := BB6.Agent1Raw60LFPrefixCounter.table true true
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6.Agent1Raw60LFPrefixCounter.never true true m hm
end V1035
end BB6.Agent1Raw60LFPrefixCounter
