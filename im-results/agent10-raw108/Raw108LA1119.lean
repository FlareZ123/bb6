import SweepPumping
namespace BB6.Agent10Raw108LA1119
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,2⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem unaryP0 (n : Nat) (R : List Bool) : run0 table 3 ⟨2,[false] ++ R,[true,false,true,true] ++ rep [true] n⟩ = some ⟨2,[true,true,true,false] ++ R,[true] ++ rep [true] n⟩ := by rfl

theorem unaryL1 (L R : List Bool) : run0 table 1 ⟨2,[true] ++ L,[true] ++ [true] ++ R⟩ = some ⟨2,[true] ++ [false] ++ L,[true] ++ R⟩ := by rfl

theorem unaryP1 (n : Nat) (R : List Bool) : run0 table (1*n) ⟨2,[true,true,true,false] ++ R,[true] ++ rep [true] n⟩ = some ⟨2,[true] ++ rep [false] n ++ [true,true,false] ++ R,[true]⟩ := by
  simpa only [List.nil_append,List.append_nil,List.append_assoc,List.cons_append] using sweepR table 2 [true] [true] [true] [false] 1 unaryL1 n ([true,true,false] ++ R) ([])

theorem unaryP2 (n : Nat) (R : List Bool) : run0 table 3 ⟨2,[true] ++ rep [false] n ++ [true,true,false] ++ R,[true]⟩ = some ⟨3,[false,false,false,false] ++ rep [false] n ++ [true,true,false] ++ R,[]⟩ := by rfl

theorem unaryL3 (L R : List Bool) : run0 table 1 ⟨3,[false,false,false,false] ++ [false] ++ L,R⟩ = some ⟨3,[false,false,false,false] ++ L,[true] ++ R⟩ := by rfl

theorem unaryP3 (n : Nat) (R : List Bool) : run0 table (1*n) ⟨3,[false,false,false,false] ++ rep [false] n ++ [true,true,false] ++ R,[]⟩ = some ⟨3,[false,false,false,false,true,true,false] ++ R,rep [true] n⟩ := by
  simpa only [List.nil_append,List.append_nil,List.append_assoc,List.cons_append] using sweepL table 3 [false,false,false,false] [] [false] [true] 1 unaryL3 n ([true,true,false] ++ R) ([])

theorem unaryP4 (n : Nat) (R : List Bool) : run0 table 7 ⟨3,[false,false,false,false,true,true,false] ++ R,rep [true] n⟩ = some ⟨0,[true,false] ++ R,[false,true,true,true,true] ++ rep [true] n⟩ := by rfl

theorem unary (n : Nat) (R : List Bool) : run0 table (13+2*n) ⟨2,[false] ++ R,[true,false,true,true] ++ rep [true] n⟩ = some ⟨0,[true,false] ++ R,[false,true,true,true,true] ++ rep [true] n⟩ := by
  have H := (join0 (join0 (join0 (join0 (unaryP0 n R) (unaryP1 n R)) (unaryP2 n R)) (unaryP3 n R)) (unaryP4 n R))
  rw [show 3+1*n+3+1*n+7=13+2*n by omega] at H
  exact H
theorem emptyP0 (n : Nat) (R : List Bool) : run0 table 2 ⟨0,[],[false,true,true] ++ rep [true] n⟩ = some ⟨2,[true,true,true],[true] ++ rep [true] n⟩ := by rfl

theorem emptyL1 (L R : List Bool) : run0 table 1 ⟨2,[true] ++ L,[true] ++ [true] ++ R⟩ = some ⟨2,[true] ++ [false] ++ L,[true] ++ R⟩ := by rfl

theorem emptyP1 (n : Nat) (R : List Bool) : run0 table (1*n) ⟨2,[true,true,true],[true] ++ rep [true] n⟩ = some ⟨2,[true] ++ rep [false] n ++ [true,true],[true]⟩ := by
  simpa only [List.nil_append,List.append_nil,List.append_assoc,List.cons_append] using sweepR table 2 [true] [true] [true] [false] 1 emptyL1 n ([true,true]) ([])

theorem emptyP2 (n : Nat) (R : List Bool) : run0 table 3 ⟨2,[true] ++ rep [false] n ++ [true,true],[true]⟩ = some ⟨3,[false,false,false,false] ++ rep [false] n ++ [true,true],[]⟩ := by rfl

theorem emptyL3 (L R : List Bool) : run0 table 1 ⟨3,[false,false,false,false] ++ [false] ++ L,R⟩ = some ⟨3,[false,false,false,false] ++ L,[true] ++ R⟩ := by rfl

theorem emptyP3 (n : Nat) (R : List Bool) : run0 table (1*n) ⟨3,[false,false,false,false] ++ rep [false] n ++ [true,true],[]⟩ = some ⟨3,[false,false,false,false,true,true],rep [true] n⟩ := by
  simpa only [List.nil_append,List.append_nil,List.append_assoc,List.cons_append] using sweepL table 3 [false,false,false,false] [] [false] [true] 1 emptyL3 n ([true,true]) ([])

theorem emptyP4 (n : Nat) (R : List Bool) : run0 table 7 ⟨3,[false,false,false,false,true,true],rep [true] n⟩ = some ⟨0,[true],[false,true,true,true,true] ++ rep [true] n⟩ := by rfl

theorem empty (n : Nat) (R : List Bool) : run0 table (12+2*n) ⟨0,[],[false,true,true] ++ rep [true] n⟩ = some ⟨0,[true],[false,true,true,true,true] ++ rep [true] n⟩ := by
  have H := (join0 (join0 (join0 (join0 (emptyP0 n R) (emptyP1 n R)) (emptyP2 n R)) (emptyP3 n R)) (emptyP4 n R))
  rw [show 2+1*n+3+1*n+7=12+2*n by omega] at H
  exact H
abbrev P := [true,false,true,false]
abbrev Q := [false,true,true,false]
abbrev Z := [true,false,false,true]
abbrev O := [true,false,true,true]
def U (m : Nat) := [true,true] ++ rep [true] m
def right (k m : Nat) := [false] ++ rep P k ++ U m

theorem pairRotate (k : Nat) : [true,false] ++ rep P k = rep P k ++ [true,false] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rep,List.append_assoc]
    change P ++ ([true,false] ++ rep P k) = P ++ (rep P k ++ [true,false])
    rw [ih]
theorem encRotate (k : Nat) : [true,false] ++ rep Q k = rep Z k ++ [true,false] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rep, List.append_assoc]
    change Z ++ ([true,false] ++ rep Q k) = Z ++ (rep Z k ++ [true,false])
    rw [ih]
theorem unaryRep (m : Nat) : [false,true,true,true,true] ++ rep [true] m = right 0 (m+2) := by
  rw [show m+2=Nat.succ (Nat.succ m) by omega]
  rfl

theorem sweepPair (L R : List Bool) : run0 table 4 ⟨2,[false]++L,P++R⟩ = some ⟨2,[false]++Q++L,R⟩ := by rfl

theorem oddCore (k m : Nat) (L : List Bool) :
    run0 table (4*k+ (13+2*m)) ⟨2,false::L,[true,false]++rep P k++U m⟩ =
    some ⟨0,rep Z k++[true,false]++L,right 0 (m+2)⟩ := by
  have h1 := sweepR table 2 [false] [] P Q 4 sweepPair k L ([true,false]++U m)
  have h2 := unary m (rep Q k++L)
  have h := join0 h1 h2
  simp only [List.nil_append] at h
  rw [← List.append_assoc (rep P k),← pairRotate k,← List.append_assoc [true,false] (rep Q k) L,encRotate k,unaryRep m] at h
  simpa only [List.nil_append,List.append_assoc,List.cons_append] using h

inductive Term where
 | empty | one | mid
 deriving DecidableEq

def endWord : Term → List Bool
 | .empty => []
 | .one => [true]
 | .mid => [true,false,true]

def enc : List Bool → Term → List Bool
 | [], t => endWord t
 | false::bs,t => Z++enc bs t
 | true::bs,t => O++enc bs t

theorem enc_rep (k : Nat) (bs : List Bool) (t : Term) :
    enc (List.replicate k false ++ bs) t = rep Z k ++ enc bs t := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ,List.cons_append,enc,rep,ih,List.append_assoc]

structure Sec where
 bs : List Bool
 t : Term
 k : Nat
 m : Nat

def cfg (s : Sec) : Z0 := ⟨0,enc s.bs s.t,right s.k s.m⟩
def next : Sec → Sec
 | ⟨false::bs,t,k,m⟩ => ⟨List.replicate k false ++ true::bs,t,0,m+2⟩
 | ⟨true::bs,t,k,m⟩ => ⟨bs,t,k+1,m⟩
 | ⟨[],.one,k,m⟩ => ⟨List.replicate k false,.mid,0,m+2⟩
 | ⟨[],.mid,k,m⟩ => ⟨List.replicate (k+1) false,.empty,0,m+2⟩
 | ⟨[],.empty,0,m⟩ => ⟨[],.one,0,m+2⟩
 | ⟨[],.empty,k+1,m⟩ => ⟨List.replicate (k+1) false,.one,0,m+2⟩
def cost : Sec → Nat
 | ⟨false::_,_,k,m⟩ => 3+(4*k+(13+2*m))
 | ⟨true::_,_,_,_⟩ => 4
 | ⟨[],.one,k,m⟩ => 3+(4*k+(13+2*m))
 | ⟨[],.mid,k,m⟩ => 5+(4*k+(13+2*m))
 | ⟨[],.empty,0,m⟩ => 12+2*m
 | ⟨[],.empty,k+1,m⟩ => 3+(4*k+(13+2*m))

theorem zeroStep (k m : Nat) (L : List Bool) :
    run0 table 3 ⟨0,Z++L,right k m⟩ = some ⟨2,[false,true,true]++L,[true,false]++rep P k++U m⟩ := by rfl
theorem oneStep (k m : Nat) (L : List Bool) :
    run0 table 4 ⟨0,O++L,right k m⟩ = some ⟨0,L,right (k+1) m⟩ := by rfl
theorem endOne (k m : Nat) :
    run0 table 3 ⟨0,[true],right k m⟩ = some ⟨2,[false,true],[true,false]++rep P k++U m⟩ := by rfl
theorem endMid (k m : Nat) :
    run0 table 5 ⟨0,[true,false,true],right k m⟩ = some ⟨2,[false,false,true],[true,false]++rep P k++U m⟩ := by rfl
theorem endEmpty (k m : Nat) :
    run0 table 3 ⟨0,[],right (k+1) m⟩ = some ⟨2,[false,false,true,true],[true,false]++rep P k++U m⟩ := by rfl

theorem advance (s : Sec) : run0 table (cost s) (cfg s) = some (cfg (next s)) := by
  rcases s with ⟨bs,t,k,m⟩
  cases bs with
  | cons b bs =>
    cases b
    · have h := join0 (zeroStep k m (enc bs t)) (oddCore k m ([true,true]++enc bs t))
      simpa only [cfg,cost,next,enc,enc_rep,Z,O,List.append_assoc,List.cons_append,List.nil_append] using h
    · exact oneStep k m (enc bs t)
  | nil =>
    cases t with
    | one =>
      have h := join0 (endOne k m) (oddCore k m [true])
      have hr := enc_rep k [] Term.mid
      simp only [List.append_nil,enc,endWord] at hr
      simp only [cfg,cost,next,enc,endWord,hr]
      rw [List.append_assoc] at h; exact h
    | mid =>
      have h := join0 (endMid k m) (oddCore k m [false,true])
      have hr := enc_rep (k+1) [] Term.empty
      simp only [List.append_nil,enc,endWord] at hr
      rw [List.append_assoc,show [true,false]++[false,true]=Z by rfl,rep_snoc Z k] at h
      simp only [cfg,cost,next,enc,endWord,hr]; exact h
    | empty =>
      cases k with
      | zero =>
        have h := empty m []
        rw [unaryRep] at h
        exact h
      | succ k =>
        have h := join0 (endEmpty k m) (oddCore k m [false,true,true])
        have hr := enc_rep (k+1) [] Term.one
        simp only [List.append_nil,enc,endWord] at hr
        rw [List.append_assoc (rep Z k),show [true,false]++[false,true,true]=Z++[true] by rfl,← List.append_assoc,rep_snoc Z k] at h
        simp only [cfg,cost,next,enc,endWord,hr]; exact h

def orbit : Nat → Sec
 | 0 => ⟨[],.one,0,0⟩
 | n+1 => next (orbit n)
def family (n : Nat) := cfg (orbit n)
theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem growth (n : Nat) : run0 table (cost (orbit n)) (family n) = some (family (n+1)) := advance (orbit n)
theorem positive (s : Sec) : 0 < cost s := by
  rcases s with ⟨bs,t,k,m⟩
  cases bs with
  | cons b bs => cases b <;> simp [cost] <;> omega
  | nil => cases t <;> cases k <;> simp [cost] <;> omega
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (fun n => cost (orbit n)) entry (fun n => positive (orbit n)) growth m hm
#print axioms growth
#print axioms never
end BB6.Agent10Raw108LA1119
