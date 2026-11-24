import Lean

namespace BB429Q0Macro.CrossGate

abbrev State := Int × Int

def bit (b : Bool) : Int := if b then 1 else 0

def len (q : Int) (d : Bool) : Int :=
  if q % 2 = 0 then (if d then 9 else 5) else (if d then 3 else 1)

def off (q : Int) (d : Bool) : Int :=
  if d then (if q % 2 = 0 then 12 else 4) else 0

def strip (a : Nat) (x : State) : Prop :=
  min x.1 0 - 2 ≤ 3*x.2 ∧ 3*x.2 ≤ max x.1 0 + (a:Int) + 2

instance (a : Nat) (x : State) : Decidable (strip a x) := by unfold strip; infer_instance

def parity (a : Nat) (x : State) (r : Bool) : Prop :=
  x.1 % 2 = 0 → ((a:Int)*bit r+x.2)%2=0

instance (a : Nat) (x : State) (r : Bool) : Decidable (parity a x r) := by unfold parity; infer_instance

def pairs : List (Bool × Bool) := [(false,false),(false,true),(true,false),(true,true)]

def Step (a : Nat) (x y : State) : Prop := ∃ r d : Bool,
  strip a x ∧ strip a y ∧ parity a x r ∧ y.1=x.1+len x.1 d ∧
    4*y.2=x.2+(a:Int)*bit r+bit d*x.1+off x.1 d

def forward (a : Nat) (x : State) : List State := pairs.filterMap fun (r,d) =>
  let n := x.2+(a:Int)*bit r+bit d*x.1+off x.1 d
  let y := (x.1+len x.1 d,n/4)
  if strip a x ∧ strip a y ∧ parity a x r ∧ n%4=0 then some y else none

def backward (a : Nat) (y : State) : List State := pairs.filterMap fun (r,d) =>
  let q := y.1-len (y.1+1) d
  let x := (q,4*y.2-(a:Int)*bit r-bit d*q-off q d)
  if strip a x ∧ strip a y ∧ parity a x r then some x else none

theorem mem_pairs (r d : Bool) : (r,d) ∈ pairs := by cases r <;> cases d <;> decide

theorem forward_complete {a : Nat} {x y : State} (h : Step a x y) : y ∈ forward a x := by
  obtain ⟨r,d,hx,hy,hp,hq,he⟩ := h
  unfold forward
  apply List.mem_filterMap.mpr
  refine ⟨(r,d),mem_pairs r d,?_⟩
  dsimp
  have hY : (x.1+len x.1 d,(x.2+(a:Int)*bit r+bit d*x.1+off x.1 d)/4)=y := by
    apply Prod.ext
    · exact hq.symm
    · dsimp; omega
  have hm : (x.2+(a:Int)*bit r+bit d*x.1+off x.1 d)%4=0 := by omega
  rw [hY]
  simp [hx,hy,hp,hm]

theorem len_odd (q : Int) (d : Bool) : len q d % 2=1 := by
  unfold len; split <;> cases d <;> decide

theorem len_eq_next {q Q : Int} {d : Bool} (h : Q=q+len q d) : len (Q+1) d = len q d := by
  have ho := len_odd q d
  have hp : (Q+1)%2=q%2 := by omega
  simp [len,hp]

theorem backward_complete {a : Nat} {x y : State} (h : Step a x y) : x ∈ backward a y := by
  obtain ⟨r,d,hx,hy,hp,hq,he⟩ := h
  unfold backward
  apply List.mem_filterMap.mpr
  refine ⟨(r,d),mem_pairs r d,?_⟩
  dsimp
  rw [len_eq_next hq]
  have hQ : y.1-len x.1 d=x.1 := by omega
  rw [hQ]
  have hE : 4*y.2-(a:Int)*bit r-bit d*x.1-off x.1 d=x.2 := by omega
  rw [hE]
  cases x
  simp_all

/-- Test two incoming and two outgoing edges, with the center the first
    nonnegative rank offset. The test allows independent input bits,
    so it is necessary even for arbitrarily long delayed histories. -/
def gateTest (a : Nat) (x : State) : Bool :=
  (backward a x).any (fun y => y.1 < 0 && !(backward a y).isEmpty) &&
  (forward a x).any (fun y => !(forward a y).isEmpty)

def gate (a : Nat) : List State := (List.range 9).flatMap fun (b : Nat) =>
  (List.range 5).filterMap fun (e : Nat) =>
    let x : State := ((b:Int),(e:Int))
    if gateTest a x then some x else none

def gate1 : List State := [(0,0),(1,0),(2,1),(3,0),(3,1),(5,2)]
def gate2 : List State := [(0,0),(1,0),(1,1),(3,0),(3,1),(7,3)]

theorem gate1_eq : gate 1=gate1 := by decide
theorem gate2_eq : gate 2=gate2 := by decide

theorem gateTest_complete {a : Nat} {x0 x1 x2 x3 x4 : State}
    (h0 : Step a x0 x1) (h1 : Step a x1 x2) (h2 : Step a x2 x3) (h3 : Step a x3 x4)
    (hc : x1.1<0) : gateTest a x2=true := by
  have b0 := backward_complete h0
  have b1 := backward_complete h1
  have f2 := forward_complete h2
  have f3 := forward_complete h3
  unfold gateTest
  simp only [Bool.and_eq_true, List.any_eq_true]
  constructor
  · refine ⟨x1,b1,?_⟩
    simp [hc]
    intro he
    simp [he] at b0
  · refine ⟨x3,f2,?_⟩
    simp
    intro he
    simp [he] at f3

/-- The all-scale central gate contains only six (rank,carry) pairs for
    each coefficient, rather than the full nine overshoot classes. -/
theorem central_gate {a : Nat} {x0 x1 x2 x3 x4 : State}
    (ha : a=1 ∨ a=2) (h0 : Step a x0 x1) (h1 : Step a x1 x2)
    (h2 : Step a x2 x3) (h3 : Step a x3 x4)
    (hc : x1.1<0) (hb : 0≤x2.1 ∧ x2.1<9) :
    (a=1 ∧ x2 ∈ gate1) ∨ (a=2 ∧ x2 ∈ gate2) := by
  have hs : strip a x2 := by obtain ⟨_,_,_,h,_,_,_⟩ := h1; exact h
  unfold strip at hs
  have he : 0≤x2.2 ∧ x2.2<5 := by
    rw [Int.min_eq_right hb.1,Int.max_eq_left hb.1] at hs
    rcases ha with h|h <;> simp [h] at hs <;> omega
  have ht := gateTest_complete h0 h1 h2 h3 hc
  have hmem : x2 ∈ gate a := by
    unfold gate
    apply List.mem_flatMap.mpr
    refine ⟨x2.1.toNat,by simp; omega,?_⟩
    apply List.mem_filterMap.mpr
    refine ⟨x2.2.toNat,by simp; omega,?_⟩
    have hpair : (((x2.1.toNat:Nat):Int),((x2.2.toNat:Nat):Int))=x2 := by
      apply Prod.ext <;> dsimp <;> omega
    dsimp
    rw [hpair]
    simp [ht]
  rcases ha with h|h
  · subst a; rw [gate1_eq] at hmem; exact Or.inl ⟨rfl,hmem⟩
  · subst a; rw [gate2_eq] at hmem; exact Or.inr ⟨rfl,hmem⟩

#print axioms gate1_eq
#print axioms gate2_eq
#print axioms central_gate
end BB429Q0Macro.CrossGate
