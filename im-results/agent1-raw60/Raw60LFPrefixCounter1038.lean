import Raw60LFUnaryCore
namespace BB6.Agent1Raw60LFPrefixCounter1038
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1Raw60LFUnaryCore
set_option maxRecDepth 4000
set_option maxHeartbeats 4000000
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,3⟩)
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

def digit : Digit → List Bool
  | .hi => [true,true,true,true,true]
  | .mid => [true,true,true,false,true]
  | .lo => [true,true,true,false,false]

inductive Tail where
  | stop (b : Bool)
  | more (d : Digit) (s : Tail)

def enc : Tail → List Bool
  | .stop false => [false]
  | .stop true => [true,false]
  | .more d s => digit d++enc s

def nextTail : Tail → Tail
  | .stop false => .stop true
  | .stop true => .more .hi (.stop false)
  | .more .hi s => .more .mid s
  | .more .mid s => .more .lo s
  | .more .lo s => .more .hi (nextTail s)

theorem scan (s : Tail) (L : List Bool) : Reach table
    (B (false::L) (enc s)) (F L (true::enc (nextTail s))) := by
  induction s generalizing L with
  | stop b => cases b
              · exact ⟨9,by rfl⟩
              · exact ⟨19,by rfl⟩
  | more d s ih =>
    cases d with
    | hi => exact ⟨9,by rfl⟩
    | mid => exact ⟨11,by rfl⟩
    | lo =>
      have h1 : run0 table 5 (B (false::L) (enc (.more .lo s))) = some (B (false::(U 5++L)) (enc s)) := by rfl
      have h2 := ih (U 5++L)
      have h3 : run0 table 5 (F (U 5++L) (true::enc (nextTail s))) = some (F L (true::enc (nextTail (.more .lo s)))) := by rfl
      exact reachTrans ⟨5,h1⟩ (reachTrans h2 ⟨5,h3⟩)

def head : Digit → List Bool
  | .hi => [true,true]
  | .mid => [false,true]
  | .lo => [false,false]
abbrev Counter := Digit × Tail

def bits (c : Counter) := head c.1++enc c.2

def next : Counter → Counter
  | (.hi,s) => (.mid,s)
  | (.mid,s) => (.lo,s)
  | (.lo,s) => (.hi,nextTail s)

theorem sub (c : Counter) (L : List Bool) : Reach table
    (B (false::L) (I++bits c)) (F (K++L) (bits (next c))) := by
  obtain ⟨d,s⟩ := c
  cases d with
  | hi => exact ⟨5,by rfl⟩
  | mid => exact ⟨7,by rfl⟩
  | lo =>
    have h1 : run0 table 5 (B (false::L) (I++bits (.lo,s))) = some (B (false::(J++L)) (enc s)) := by rfl
    have h2 := scan s (J++L)
    have h3 : run0 table 1 (F (J++L) (true::enc (nextTail s))) = some (F (K++L) (bits (next (.lo,s)))) := by rfl
    exact reachTrans ⟨5,h1⟩ (reachTrans h2 ⟨1,h3⟩)

theorem pack (n : Nat) (L R : List Bool) : Reach table
    (B (false::L) (I++rep P n R)) (B (false::rep J n L) (I++R)) := by
  induction n generalizing L with
  | zero => exact ⟨0,by rfl⟩
  | succ n ih =>
    have h1 : run0 table 5 (B (false::L) (I++rep P (n+1) R)) = some (B (false::(J++L)) (I++rep P n R)) := by rfl
    have h2 := ih (J++L)
    rw [repEnd J n L] at h2
    exact reachTrans ⟨5,h1⟩ h2

theorem unpack (n : Nat) (L R : List Bool) : Reach table
    (F (K++rep J n L) R) (F (K++L) (rep P n R)) := by
  induction n generalizing R with
  | zero => exact ⟨0,by rfl⟩
  | succ n ih =>
    have h1 : run0 table 5 (F (K++rep J (n+1) L) R) = some (F (K++rep J n L) (P++R)) := by rfl
    have h2 := ih (P++R)
    rw [repEnd P n R] at h2
    exact reachTrans ⟨5,h1⟩ h2

def cfg (n : Nat) (c : Counter) := F [] (rep P (n+1) (bits c))

theorem advance (n : Nat) (c : Counter) : ∃ t, 0<t ∧ run0 table t (cfg n c) = some (cfg (n+1) (next (next c))) := by
  have h1 : run0 table 16 (cfg n c) = some (B (false::J) (I++rep P n (bits c))) := by rfl
  obtain ⟨a,ha⟩ := pack n J (bits c)
  have hJ : rep J n J = rep J (n+1) [] := repEnd J n []
  rw [hJ] at ha
  obtain ⟨b,hb⟩ := sub c (rep J (n+1) [])
  obtain ⟨d,hd⟩ := unpack (n+1) [] (bits (next c))
  have h2 : run0 table 5 (F K (rep P (n+1) (bits (next c)))) = some (B [false,true] (I++rep P (n+1) (bits (next c)))) := by rfl
  obtain ⟨e,he⟩ := pack (n+1) [true] (bits (next c))
  obtain ⟨f,hf⟩ := sub (next c) (rep J (n+1) [true])
  obtain ⟨h,hh⟩ := unpack (n+1) [true] (bits (next (next c)))
  have h3 : run0 table 5 (F (K++[true]) (rep P (n+1) (bits (next (next c))))) = some (cfg (n+1) (next (next c))) := by rfl
  exact ⟨_,by omega,join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 h1 ha) hb) hd) h2) he) hf) hh) h3⟩

def counters : Nat → Counter
  | 0 => (.hi,.stop true)
  | n+1 => next (next (counters n))
def family (n : Nat) := cfg n (counters n)
theorem entry : run0 table 42 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth_exists (n : Nat) : ∃ t, 0<t ∧ run0 table t (family n) = some (family (n+1)) := advance n (counters n)
noncomputable def cost (n : Nat) : Nat := Classical.choose (growth_exists n)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 42 (cost) (entry) (fun n => (Classical.choose_spec (growth_exists n)).1)
    (fun n => (Classical.choose_spec (growth_exists n)).2) m hm
#print axioms never
end BB6.Agent1Raw60LFPrefixCounter1038
