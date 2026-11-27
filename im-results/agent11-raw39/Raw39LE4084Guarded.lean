import Raw39LE4084Simplified
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39LE4084Guarded
open BB6Coverage BB6.Agent11Raw39LE4084Simplified

/-- Finite automata read a nearest-first stack from the far end. -/
def readD {n : Nat} (d : Fin n → Bool → Fin n) (q : Fin n) : List Bool → Fin n
  | [] => q
  | b::t => d (readD d q t) b

theorem readD_append {n : Nat} (d : Fin n → Bool → Fin n) (q : Fin n)
    (u v : List Bool) : readD d q (u ++ v) = readD d (readD d q v) u := by
  induction u with
  | nil => rfl
  | cons b t ih => simp only [List.cons_append, readD, ih]

def dL (q : Fin 9) (b : Bool) : Fin 9 :=
  match q.val,b with
  | 0,false => 0
  | 0,true => 1
  | 1,false => 2
  | 1,true => 3
  | 2,false => 4
  | 2,true => 5
  | 3,false => 6
  | 3,true => 3
  | 4,false => 4
  | 4,true => 4
  | 5,false => 7
  | 5,true => 3
  | 6,false => 7
  | 6,true => 1
  | 7,false => 4
  | 7,true => 8
  | 8,false => 4
  | 8,true => 3
  | _,_ => 0

def dR (q : Fin 11) (b : Bool) : Fin 11 :=
  match q.val,b with
  | 0,false => 0
  | 0,true => 1
  | 1,false => 0
  | 1,true => 2
  | 2,false => 3
  | 2,true => 4
  | 3,false => 5
  | 3,true => 6
  | 4,false => 7
  | 4,true => 4
  | 5,false => 5
  | 5,true => 8
  | 6,false => 0
  | 6,true => 9
  | 7,false => 5
  | 7,true => 10
  | 8,false => 5
  | 8,true => 4
  | 9,false => 7
  | 9,true => 4
  | 10,false => 5
  | 10,true => 4
  | _,_ => 0

def qL (L : List Bool) : Fin 9 := readD dL 0 L
def qR (R : List Bool) : Fin 11 := readD dR 0 R
def goodL (q : Fin 9) : Bool := q != 4
def goodR (q : Fin 11) : Bool := q == 0 || q == 1 || q == 2 || q == 3 || q == 9
def GoodL (L : List Bool) : Prop := goodL (qL L) = true
def GoodR (R : List Bool) : Prop := goodR (qR R) = true

theorem seedL (n : Nat) : qL (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change dL (qL (List.replicate n false)) false = 0
    rw [ih]
    rfl
theorem seedR (n : Nat) : qR (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change dR (qR (List.replicate n false)) false = 0
    rw [ih]
    rfl

theorem l0 (L : List Bool) (h : GoodL L) : GoodL L := by
  simp only [GoodL,qL,readD_append] at *
  exact (show ∀ q : Fin 9, goodL (readD dL q []) = true → goodL (readD dL q []) = true from by decide) (qL L) h
theorem r0 (R : List Bool) (ht : qR R ≠ 6) (h : GoodR ([false,false,false,false] ++ R)) : GoodR ([true,true,false,true] ++ R) := by
  simp only [GoodR,qR,readD_append] at *
  exact (show ∀ q : Fin 11, q ≠ 6 → goodR (readD dR q [false,false,false,false]) = true → goodR (readD dR q [true,true,false,true]) = true from by decide) (qR R) ht h

theorem l1 (L : List Bool) (h : GoodL L) : GoodL ([false,false,true,true] ++ L) := by
  simp only [GoodL,qL,readD_append] at *
  exact (show ∀ q : Fin 9, goodL (readD dL q []) = true → goodL (readD dL q [false,false,true,true]) = true from by decide) (qL L) h
theorem r1 (R : List Bool) (h : GoodR ([false,false,false,true] ++ R)) : GoodR R := by
  simp only [GoodR,qR,readD_append] at *
  exact (show ∀ q : Fin 11, goodR (readD dR q [false,false,false,true]) = true → goodR (readD dR q []) = true from by decide) (qR R) h

theorem l2 (L : List Bool) (h : GoodL L) : GoodL ([true,true,true,true] ++ L) := by
  simp only [GoodL,qL,readD_append] at *
  exact (show ∀ q : Fin 9, goodL (readD dL q []) = true → goodL (readD dL q [true,true,true,true]) = true from by decide) (qL L) h
theorem r2 (R : List Bool) (h : GoodR ([false,false,true,false,false] ++ R)) : GoodR ([false] ++ R) := by
  simp only [GoodR,qR,readD_append] at *
  exact (show ∀ q : Fin 11, goodR (readD dR q [false,false,true,false,false]) = true → goodR (readD dR q [false]) = true from by decide) (qR R) h

theorem l3 (L : List Bool) (h : GoodL L) : GoodL ([false,true,false,true,true] ++ L) := by
  simp only [GoodL,qL,readD_append] at *
  exact (show ∀ q : Fin 9, goodL (readD dL q []) = true → goodL (readD dL q [false,true,false,true,true]) = true from by decide) (qL L) h
theorem r3 (R : List Bool) (h : GoodR ([false,false,true,false,true] ++ R)) : GoodR R := by
  simp only [GoodR,qR,readD_append] at *
  exact (show ∀ q : Fin 11, goodR (readD dR q [false,false,true,false,true]) = true → goodR (readD dR q []) = true from by decide) (qR R) h

theorem l5 (L : List Bool) (h : GoodL L) : GoodL ([true,true] ++ L) := by
  simp only [GoodL,qL,readD_append] at *
  exact (show ∀ q : Fin 9, goodL (readD dL q []) = true → goodL (readD dL q [true,true]) = true from by decide) (qL L) h
theorem r5 (R : List Bool) (h : GoodR ([false,true] ++ R)) : GoodR R := by
  simp only [GoodR,qR,readD_append] at *
  exact (show ∀ q : Fin 11, goodR (readD dR q [false,true]) = true → goodR (readD dR q []) = true from by decide) (qR R) h

theorem l6 (L : List Bool) (h : GoodL ([false,false] ++ L)) : GoodL ([true,true] ++ L) := by
  simp only [GoodL,qL,readD_append] at *
  exact (show ∀ q : Fin 9, goodL (readD dL q [false,false]) = true → goodL (readD dL q [true,true]) = true from by decide) (qL L) h
theorem r6 (R : List Bool) (h : GoodR ([true] ++ R)) : GoodR ([false] ++ R) := by
  simp only [GoodR,qR,readD_append] at *
  exact (show ∀ q : Fin 11, goodR (readD dR q [true]) = true → goodR (readD dR q [false]) = true from by decide) (qR R) h

theorem l7 (L : List Bool) (h : GoodL ([false,true] ++ L)) : GoodL L := by
  simp only [GoodL,qL,readD_append] at *
  exact (show ∀ q : Fin 9, goodL (readD dL q [false,true]) = true → goodL (readD dL q []) = true from by decide) (qL L) h
theorem r7 (R : List Bool) (h : GoodR ([true] ++ R)) : GoodR ([true,true,false] ++ R) := by
  simp only [GoodR,qR,readD_append] at *
  exact (show ∀ q : Fin 11, goodR (readD dR q [true]) = true → goodR (readD dR q [true,true,false]) = true from by decide) (qR R) h

theorem l8 (L : List Bool) (h : GoodL ([true,false] ++ L)) : GoodL ([true,true,true] ++ L) := by
  simp only [GoodL,qL,readD_append] at *
  exact (show ∀ q : Fin 9, goodL (readD dL q [true,false]) = true → goodL (readD dL q [true,true,true]) = true from by decide) (qL L) h
theorem r8 (R : List Bool) (h : GoodR ([true,false] ++ R)) : GoodR ([false] ++ R) := by
  simp only [GoodR,qR,readD_append] at *
  exact (show ∀ q : Fin 11, goodR (readD dR q [true,false]) = true → goodR (readD dR q [false]) = true from by decide) (qR R) h

theorem l9 (L : List Bool) (h : GoodL ([true,false] ++ L)) : GoodL ([false,true,false,true] ++ L) := by
  simp only [GoodL,qL,readD_append] at *
  exact (show ∀ q : Fin 9, goodL (readD dL q [true,false]) = true → goodL (readD dL q [false,true,false,true]) = true from by decide) (qL L) h
theorem r9 (R : List Bool) (h : GoodR ([true,true] ++ R)) : GoodR R := by
  simp only [GoodR,qR,readD_append] at *
  exact (show ∀ q : Fin 11, goodR (readD dR q [true,true]) = true → goodR (readD dR q []) = true from by decide) (qR R) h

theorem l10 (L : List Bool) (h : GoodL ([true,true] ++ L)) : GoodL ([true] ++ L) := by
  simp only [GoodL,qL,readD_append] at *
  exact (show ∀ q : Fin 9, goodL (readD dL q [true,true]) = true → goodL (readD dL q [true]) = true from by decide) (qL L) h
theorem r10 (R : List Bool) (h : GoodR ([true] ++ R)) : GoodR ([true,false] ++ R) := by
  simp only [GoodR,qR,readD_append] at *
  exact (show ∀ q : Fin 11, goodR (readD dR q [true]) = true → goodR (readD dR q [true,false]) = true from by decide) (qR R) h

theorem rbad (R : List Bool) : ¬ GoodR ([false,false,true,true] ++ R) := by
  simp only [GoodR,qR,readD_append]
  exact (show ∀ q : Fin 11, ¬ goodR (readD dR q [false,false,true,true]) = true from by decide) (qR R)

/-- Only the bounce on 0000 requires a new safety premise. A candidate
    relation may ignore configurations outside the independently preserved
    left/right guards. -/
structure Guarded (K : List Bool → List Bool → Prop) : Prop where
  seed : ∀ n, K (List.replicate n false) (List.replicate n false)
  trigger : ∀ L R, K L ([false,false,false,false] ++ R) → GoodL L →
    GoodR ([false,false,false,false] ++ R) → qR R ≠ 6
  c0 : ∀ L R, K L ([false,false,false,false] ++ R) →
    GoodL L → GoodR ([false,false,false,false] ++ R) →
    K L ([true,true,false,true] ++ R)
  c1 : ∀ L R, K L ([false,false,false,true] ++ R) →
    GoodL L → GoodR ([false,false,false,true] ++ R) →
    K ([false,false,true,true] ++ L) R
  c2 : ∀ L R, K L ([false,false,true,false,false] ++ R) →
    GoodL L → GoodR ([false,false,true,false,false] ++ R) →
    K ([true,true,true,true] ++ L) ([false] ++ R)
  c3 : ∀ L R, K L ([false,false,true,false,true] ++ R) →
    GoodL L → GoodR ([false,false,true,false,true] ++ R) →
    K ([false,true,false,true,true] ++ L) R
  c5 : ∀ L R, K L ([false,true] ++ R) →
    GoodL L → GoodR ([false,true] ++ R) →
    K ([true,true] ++ L) R
  c6 : ∀ L R, K ([false,false] ++ L) ([true] ++ R) →
    GoodL ([false,false] ++ L) → GoodR ([true] ++ R) →
    K ([true,true] ++ L) ([false] ++ R)
  c7 : ∀ L R, K ([false,true] ++ L) ([true] ++ R) →
    GoodL ([false,true] ++ L) → GoodR ([true] ++ R) →
    K L ([true,true,false] ++ R)
  c8 : ∀ L R, K ([true,false] ++ L) ([true,false] ++ R) →
    GoodL ([true,false] ++ L) → GoodR ([true,false] ++ R) →
    K ([true,true,true] ++ L) ([false] ++ R)
  c9 : ∀ L R, K ([true,false] ++ L) ([true,true] ++ R) →
    GoodL ([true,false] ++ L) → GoodR ([true,true] ++ R) →
    K ([false,true,false,true] ++ L) R
  c10 : ∀ L R, K ([true,true] ++ L) ([true] ++ R) →
    GoodL ([true,true] ++ L) → GoodR ([true] ++ R) →
    K ([true] ++ L) ([true,false] ++ R)
theorem guarded_closed {K : List Bool → List Bool → Prop} (h : Guarded K) :
    Closed (fun L R => K L R ∧ GoodL L ∧ GoodR R) := by
  constructor
  · intro n
    refine ⟨h.seed n, ?_, ?_⟩
    · simp [GoodL, seedL, goodL]
    · simp [GoodR, seedR, goodR]
  · intro L R hh
    exact ⟨h.c0 L R hh.1 hh.2.1 hh.2.2, l0 L hh.2.1, r0 R (h.trigger L R hh.1 hh.2.1 hh.2.2) hh.2.2⟩
  · intro L R hh
    exact ⟨h.c1 L R hh.1 hh.2.1 hh.2.2, l1 L hh.2.1, r1 R hh.2.2⟩
  · intro L R hh
    exact ⟨h.c2 L R hh.1 hh.2.1 hh.2.2, l2 L hh.2.1, r2 R hh.2.2⟩
  · intro L R hh
    exact ⟨h.c3 L R hh.1 hh.2.1 hh.2.2, l3 L hh.2.1, r3 R hh.2.2⟩
  · intro L R hh
    exact rbad R hh.2.2
  · intro L R hh
    exact ⟨h.c5 L R hh.1 hh.2.1 hh.2.2, l5 L hh.2.1, r5 R hh.2.2⟩
  · intro L R hh
    exact ⟨h.c6 L R hh.1 hh.2.1 hh.2.2, l6 L hh.2.1, r6 R hh.2.2⟩
  · intro L R hh
    exact ⟨h.c7 L R hh.1 hh.2.1 hh.2.2, l7 L hh.2.1, r7 R hh.2.2⟩
  · intro L R hh
    exact ⟨h.c8 L R hh.1 hh.2.1 hh.2.2, l8 L hh.2.1, r8 R hh.2.2⟩
  · intro L R hh
    exact ⟨h.c9 L R hh.1 hh.2.1 hh.2.2, l9 L hh.2.1, r9 R hh.2.2⟩
  · intro L R hh
    exact ⟨h.c10 L R hh.1 hh.2.1 hh.2.2, l10 L hh.2.1, r10 R hh.2.2⟩
theorem never_of_guarded {K : List Bool → List Bool → Prop} (h : Guarded K)
    (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_closed (guarded_closed h) m hm

#print axioms never_of_guarded
