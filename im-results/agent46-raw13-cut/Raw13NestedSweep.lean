import Raw13BinarySiblings

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13NestedSweep
open BB6Coverage BB6Coverage.Agent31Pump
open BB6Coverage.Agent31Pump.Auto (rep_add)

inductive Variant where | oneLE | oneRC
  deriving DecidableEq

def bCode : Variant → Nat
  | .oneLE => 18 | .oneRC => 11

def p (v : Variant) : PartialMachine :=
  FAR.fromCodes [7,14,11,bCode v,2,19,22,0,9,13,16,24]

def prefixCost : Variant → Nat
  | .oneLE => 9 | .oneRC => 5

def turn2Cost : Variant → Nat
  | .oneLE => 14 | .oneRC => 10

def ones (n : Nat) : List Bool := rep [true] n
def Q : List Bool := [true,true,true]
def pair : List Bool := [false,true]

theorem ones_add (a b : Nat) : ones (a+b) = ones a ++ ones b :=
  (rep_add [true] a b).symm

theorem ones_cons (n : Nat) : ones (n+1) = true::ones n := rfl

theorem ones_triple (k : Nat) : ones (3*k) = rep Q k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 3*(k+1)=3*k+3 by omega,ones_add,ih]
    exact rep_snoc Q k

theorem prefix (v : Variant) (L R : List Bool) :
    run0 (p v) (prefixCost v) ⟨4,false::L,[false,true,true]++R⟩ =
      some ⟨4,ones 4++L,R⟩ := by cases v <;> rfl

theorem prefixBlank (v : Variant) (R : List Bool) :
    run0 (p v) (prefixCost v) ⟨4,[],[false,true,true]++R⟩ =
      some ⟨4,ones 4,R⟩ := by cases v <;> rfl

theorem triple (v : Variant) (L R : List Bool) :
    run0 (p v) 5 ⟨4,[true]++L,[]++Q++R⟩ =
      some ⟨4,[true]++Q++L,[]++R⟩ := by cases v <;> rfl

theorem fill (v : Variant) (k a : Nat) (L R : List Bool) :
    run0 (p v) (5*k) ⟨4,ones (a+1)++L,ones (3*k)++R⟩ =
      some ⟨4,ones (3*k+a+1)++L,R⟩ := by
  have h := sweepR (p v) 4 [true] [] Q Q 5 (triple v) k (ones a++L) R
  rw [← ones_triple] at h
  simpa only [ones_cons,List.nil_append,List.singleton_append,List.cons_append,
    List.append_assoc,ones_add] using h

theorem drainOne (v : Variant) (L R : List Bool) :
    run0 (p v) 3 ⟨4,[]++[true]++L,[false]++R⟩ =
      some ⟨4,[]++L,[false]++[true]++R⟩ := by cases v <;> rfl

theorem drain (v : Variant) (n : Nat) (L R : List Bool) :
    run0 (p v) (3*n) ⟨4,ones n++L,false::R⟩ =
      some ⟨4,L,false::(ones n++R)⟩ := by
  simpa only [ones,List.nil_append,List.singleton_append,List.cons_append,List.append_assoc] using
    sweepL (p v) 4 [] [false] [true] [true] 3 (drainOne v) n L R

theorem drainFirst (v : Variant) (L : List Bool) :
    run0 (p v) 3 ⟨4,true::L,[]⟩ = some ⟨4,L,[false,true]⟩ := by cases v <;> rfl

theorem drainBlank (v : Variant) (n : Nat) (L : List Bool) :
    run0 (p v) (3*(n+1)) ⟨4,ones (n+1)++L,[]⟩ =
      some ⟨4,L,false::ones (n+1)⟩ := by
  have h := join0 (drainFirst v (ones n++L)) (drain v n L [true])
  simpa only [ones_cons,List.cons_append,show 3*(n+1)=3+3*n by omega,
    show ones n ++ [true] = ones (n+1) from rep_snoc [true] n] using h

def U (n : Nat) : Z0 := ⟨4,[],false::ones n⟩
def RPhase (k j : Nat) : Z0 :=
  ⟨4,[],false::(ones (3*k+2)++rep pair j++[true])⟩
def LPhase (k j : Nat) : Z0 :=
  ⟨4,ones (3*k+2)++rep pair j++[true,true],[]⟩

theorem rightPhase (v : Variant) (k j : Nat) :
    ∃ c, 0<c ∧ run0 (p v) c (RPhase k (j+1)) = some (RPhase (k+1) j) := by
  let R := rep pair j++[true]
  have h1 := prefixBlank v (ones (3*k)++pair++R)
  have h1' : run0 (p v) (prefixCost v) (RPhase k (j+1)) =
      some ⟨4,ones 4,ones (3*k)++pair++R⟩ := by
    simpa only [RPhase,R,rep, pair,show 3*k+2=2+3*k by omega,ones_add,
      show ones 2=[true,true] by rfl,List.append_assoc,List.cons_append,List.nil_append] using h1
  have h2 := fill v k 3 [] (pair++R)
  have h2' : run0 (p v) (5*k) ⟨4,ones 4,ones (3*k)++pair++R⟩ =
      some ⟨4,ones (3*k+4),pair++R⟩ := by
    simpa only [List.append_nil,show 3*k+3+1=3*k+4 by omega,List.append_assoc] using h2
  have h3 := drain v (3*k+4) [] (true::R)
  have h3' : run0 (p v) (3*(3*k+4)) ⟨4,ones (3*k+4),pair++R⟩ =
      some (RPhase (k+1) j) := by
    simpa only [RPhase,R,pair,List.append_nil,List.cons_append,List.nil_append,
      show 3*(k+1)+2=3*k+4+1 by omega,ones_add,show ones 1=[true] by rfl,List.append_assoc] using h3
  exact ⟨prefixCost v+5*k+3*(3*k+4),by omega,join0 (join0 h1' h2') h3'⟩

theorem leftPhase (v : Variant) (k j : Nat) :
    ∃ c, 0<c ∧ run0 (p v) c (LPhase k (j+1)) = some (LPhase (k+1) j) := by
  let L := rep pair j++[true,true]
  have h1 := drainBlank v (3*k+1) (pair++L)
  have h1' : run0 (p v) (3*(3*k+2)) (LPhase k (j+1)) =
      some ⟨4,pair++L,false::ones (3*k+2)⟩ := by
    simpa only [LPhase,L,rep,show 3*k+1+1=3*k+2 by omega,List.append_assoc] using h1
  have h2 := prefix v (true::L) (ones (3*k))
  have h2' : run0 (p v) (prefixCost v) ⟨4,pair++L,false::ones (3*k+2)⟩ =
      some ⟨4,ones 4++true::L,ones (3*k)⟩ := by
    simpa only [pair,List.cons_append,List.nil_append,show 3*k+2=2+3*k by omega,
      ones_add,show ones 2=[true,true] by rfl] using h2
  have h3 := fill v k 3 (true::L) []
  have h3' : run0 (p v) (5*k) ⟨4,ones 4++true::L,ones (3*k)⟩ =
      some (LPhase (k+1) j) := by
    simpa only [LPhase,L,List.append_nil,show 3*(k+1)+2=3*k+3+1+1 by omega,
      ones_add,show ones 1=[true] by rfl,List.append_assoc,List.cons_append,List.nil_append] using h3
  exact ⟨3*(3*k+2)+prefixCost v+5*k,by omega,join0 (join0 h1' h2') h3'⟩

theorem leftDone (v : Variant) (k : Nat) :
    run0 (p v) (3*(3*k+4)) (LPhase k 0) = some (U (3*k+4)) := by
  simpa only [LPhase,U,rep,List.nil_append,List.append_nil,show 3*k+3+1=3*k+4 by omega,
    show 3*k+4=3*k+2+2 by omega,ones_add,show ones 2=[true,true] by rfl] using
    drainBlank v (3*k+3) []

theorem turn1 (v : Variant) (L : List Bool) :
    run0 (p v) 5 ⟨4,ones 4++L,[true]⟩ =
      some ⟨0,ones 5++L,[true]⟩ := by cases v <;> rfl

theorem turn2 (v : Variant) (L : List Bool) :
    run0 (p v) (turn2Cost v) ⟨4,ones 4++L,[true,true]⟩ =
      some ⟨0,ones 8++L,[true]⟩ := by cases v <;> rfl

theorem pairL (v : Variant) (L R : List Bool) :
    run0 (p v) 2 ⟨0,[]++[true,true]++L,[]++R⟩ =
      some ⟨0,[]++L,[]++pair++R⟩ := by cases v <;> rfl

theorem ones_pair (j : Nat) : ones (2*j) = rep [true,true] j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show 2*(j+1)=2*j+2 by omega,ones_add,ih]
    exact rep_snoc [true,true] j

theorem ADrain (v : Variant) (j : Nat) (L : List Bool) :
    run0 (p v) (2*j) ⟨0,ones (2*j)++L,[true]⟩ =
      some ⟨0,L,rep pair j++[true]⟩ := by
  simpa only [ones_pair,List.nil_append] using
    sweepL (p v) 0 [] [] [true,true] pair 2 (pairL v) j L [true]

theorem oddEnd (v : Variant) (R : List Bool) :
    run0 (p v) 3 ⟨0,[true],R⟩ =
      some ⟨4,[],[false,true,true]++R⟩ := by cases v <;> rfl

theorem alternatingStart (v : Variant) (R : List Bool) :
    run0 (p v) 2 ⟨0,[],pair++R⟩ =
      some ⟨2,[true,true,true],R⟩ := by cases v <;> rfl

theorem alternatingPair (v : Variant) (L R : List Bool) :
    run0 (p v) 2 ⟨2,[true]++L,[]++pair++R⟩ =
      some ⟨2,[true]++pair++L,[]++R⟩ := by cases v <;> rfl

theorem alternatingEnd (v : Variant) (L : List Bool) :
    run0 (p v) 1 ⟨2,true::L,[true]⟩ =
      some ⟨4,true::true::L,[]⟩ := by cases v <;> rfl

theorem evenEnd (v : Variant) (j : Nat) :
    run0 (p v) (2+2*j+1) ⟨0,[],rep pair (j+1)++[true]⟩ =
      some (LPhase 0 j) := by
  have h1 := alternatingStart v (rep pair j++[true])
  have h2 := sweepR (p v) 2 [true] [] pair pair 2 (alternatingPair v) j [true,true] [true]
  have h2' : run0 (p v) (2*j) ⟨2,[true,true,true],rep pair j++[true]⟩ =
      some ⟨2,true::(rep pair j++[true,true]),[true]⟩ := by
    simpa only [List.nil_append,List.singleton_append,List.cons_append,List.append_assoc] using h2
  have h3 := alternatingEnd v (rep pair j++[true,true])
  simpa only [LPhase,rep,show 3*0+2=2 by rfl,show ones 2=[true,true] by rfl,
    List.append_assoc,List.cons_append,List.nil_append] using join0 (join0 h1 h2') h3

def Allowed (z : Z0) : Prop :=
  (∃ n, 2≤n ∧ z=U n) ∨ (∃ k j, z=RPhase k j) ∨ (∃ k j, z=LPhase k j)

theorem AProgress (v : Variant) (n : Nat) (hn : 2≤n) :
    ∃ c z, 0<c ∧ run0 (p v) c ⟨0,ones n,[true]⟩ = some z ∧ Allowed z := by
  by_cases h : n%2=0
  · let j := n/2-1
    have he : n=2*(j+1) := by dsimp [j]; omega
    have h1 := ADrain v (j+1) []
    have h2 := evenEnd v j
    have h1' : run0 (p v) (2*(j+1)) ⟨0,ones n,[true]⟩ =
        some ⟨0,[],rep pair (j+1)++[true]⟩ := by
      simpa only [he,List.append_nil] using h1
    exact ⟨2*(j+1)+(2+2*j+1),LPhase 0 j,by omega,join0 h1' h2,Or.inr (Or.inr ⟨0,j,rfl⟩)⟩
  · let j := n/2
    have he : n=2*j+1 := by dsimp [j]; omega
    have h1 := ADrain v j [true]
    have h1' : run0 (p v) (2*j) ⟨0,ones n,[true]⟩ =
        some ⟨0,[true],rep pair j++[true]⟩ := by simpa only [he,ones_add,show ones 1=[true] by rfl] using h1
    have h2 := oddEnd v (rep pair j++[true])
    refine ⟨2*j+3,RPhase 0 j,by omega,?_,Or.inr (Or.inl ⟨0,j,rfl⟩)⟩
    simpa only [RPhase,show 3*0+2=2 by rfl,show ones 2=[true,true] by rfl,
      List.cons_append,List.nil_append,List.append_assoc] using join0 h1' h2

theorem UProgress (v : Variant) (n : Nat) (hn : 2≤n) :
    ∃ c z, 0<c ∧ run0 (p v) c (U n) = some z ∧ Allowed z := by
  let k := (n-2)/3
  let r := (n-2)%3
  have he : n=3*k+2+r := by dsimp [k,r]; omega
  have hr : r<3 := by dsimp [r]; omega
  have h1 := prefixBlank v (ones (3*k)++ones r)
  have h1' : run0 (p v) (prefixCost v) (U n) =
      some ⟨4,ones 4,ones (3*k)++ones r⟩ := by
    simpa only [U,he,show 3*k+2+r=2+3*k+r by omega,ones_add,
      show ones 2=[true,true] by rfl,List.append_assoc,List.cons_append,List.nil_append] using h1
  have h2 := fill v k 3 [] (ones r)
  have h2' : run0 (p v) (5*k) ⟨4,ones 4,ones (3*k)++ones r⟩ =
      some ⟨4,ones (3*k+4),ones r⟩ := by simpa only [List.append_nil,show 3*k+3+1=3*k+4 by omega] using h2
  have h12 := join0 h1' h2'
  have hp : 0<prefixCost v := by cases v <;> decide
  have hs : r=0 ∨ r=1 ∨ r=2 := by omega
  rcases hs with h | h | h
  · refine ⟨prefixCost v+5*k,LPhase k 0,by omega,?_,Or.inr (Or.inr ⟨k,0,rfl⟩)⟩
    simpa only [h,show ones 0=[] by rfl,LPhase,rep,List.nil_append,List.append_nil,
      show 3*k+4=3*k+2+2 by omega,ones_add,show ones 2=[true,true] by rfl] using h12
  · have h3 := turn1 v (ones (3*k))
    have h3' : run0 (p v) 5 ⟨4,ones (3*k+4),ones r⟩ =
        some ⟨0,ones (3*k+5),[true]⟩ := by
      simpa only [h,show ones 1=[true] by rfl,show 3*k+4=4+3*k by omega,
        show 3*k+5=5+3*k by omega,ones_add] using h3
    obtain ⟨c,z,hc,hz,ha⟩ := AProgress v (3*k+5) (by omega)
    exact ⟨prefixCost v+5*k+5+c,z,by omega,join0 (join0 h12 h3') hz,ha⟩
  · have h3 := turn2 v (ones (3*k))
    have h3' : run0 (p v) (turn2Cost v) ⟨4,ones (3*k+4),ones r⟩ =
        some ⟨0,ones (3*k+8),[true]⟩ := by
      simpa only [h,show ones 2=[true,true] by rfl,show 3*k+4=4+3*k by omega,
        show 3*k+8=8+3*k by omega,ones_add] using h3
    obtain ⟨c,z,hc,hz,ha⟩ := AProgress v (3*k+8) (by omega)
    exact ⟨prefixCost v+5*k+turn2Cost v+c,z,by omega,join0 (join0 h12 h3') hz,ha⟩

theorem progress (v : Variant) (z : Z0) (h : Allowed z) :
    ∃ c z', 0<c ∧ run0 (p v) c z = some z' ∧ Allowed z' := by
  rcases h with ⟨n,hn,rfl⟩ | ⟨k,j,rfl⟩ | ⟨k,j,rfl⟩
  · exact UProgress v n hn
  · cases j with
    | zero =>
      have he : RPhase k 0 = U (3*k+3) := by
        simp only [RPhase,U,rep,List.nil_append,List.append_nil,
          show 3*k+3=3*k+2+1 by omega,ones_add,show ones 1=[true] by rfl]
      rw [he]
      exact UProgress v (3*k+3) (by omega)
    | succ j =>
      obtain ⟨c,hc,hr⟩ := rightPhase v k j
      exact ⟨c,RPhase (k+1) j,hc,hr,Or.inr (Or.inl ⟨k+1,j,rfl⟩)⟩
  · cases j with
    | zero => exact ⟨3*(3*k+4),U (3*k+4),by omega,leftDone v k,Or.inl ⟨3*k+4,by omega,rfl⟩⟩
    | succ j =>
      obtain ⟨c,hc,hr⟩ := leftPhase v k j
      exact ⟨c,LPhase (k+1) j,hc,hr,Or.inr (Or.inr ⟨k+1,j,rfl⟩)⟩

theorem first (v : Variant) : run0 (p v) 20 ⟨0,[],[]⟩ = some (U 4) := by
  cases v <;> decide

theorem never (v : Variant) (m : Machine) (hm : compatible (p v) m) : NeverHalts m :=
  BB6.Agent46Raw13BinarySiblings.never_of_return (p v) Allowed 20 (U 4)
    (first v) (Or.inl ⟨4,by omega,rfl⟩) (progress v) m hm

#print axioms rightPhase
#print axioms leftPhase
#print axioms progress
#print axioms never
end BB6.Agent46Raw13NestedSweep
