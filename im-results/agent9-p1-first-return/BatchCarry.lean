import Lean
namespace BB6.Agent9BatchCarry

/-- The non-boundary carry interval at clock q. -/
def Interior (q c : Nat) : Prop := 1 ≤ c ∧ c+3 ≤ q

def weightSum (q : Nat) : List Bool → Nat
  | [] => 0
  | b::bs => (if b then q else 0)+2*weightSum (q+1) bs

/-- A legal signed-carry edge stays in the strict interior. -/
def Edge (q c z : Nat) : Prop :=
  Interior q c ∧ Interior (q+1) z ∧ (2*z=c ∨ 2*z=c+q)

inductive Walk : Nat → Nat → Nat → Nat → Prop
  | nil (q c : Nat) (h : Interior q c) : Walk q c 0 c
  | cons (q c z k y : Nat) (h : Edge q c z)
      (tail : Walk (q+1) z k y) : Walk q c (k+1) y

/-- Every valid weighted word has a legal forward walk. -/
theorem walk_of_weight (q c : Nat) (xs : List Bool) (a : Nat)
    (hi : Interior q c) (he : c+weightSum q xs=2^xs.length*a) :
    Walk q c xs.length a := by
  induction xs generalizing q c with
  | nil =>
    simp [weightSum] at he
    subst a
    exact Walk.nil q c hi
  | cons b bs ih =>
    let v := if b then q else 0
    let z := (c+v)/2
    have hs : c+v+2*weightSum (q+1) bs=2*(2^bs.length*a) := by
      simp only [weightSum,List.length_cons,Nat.pow_succ] at he
      calc
        _ = c+((if b then q else 0)+2*weightSum (q+1) bs) := by simp [v,Nat.add_assoc]
        _ = (2^bs.length*2)*a := he
        _ = _ := by ac_rfl
    have hz : 2*z=c+v := by dsimp [z]; omega
    have he' : z+weightSum (q+1) bs=2^bs.length*a := by omega
    have hv : v=0 ∨ v=q := by cases b <;> simp [v]
    have hi' : Interior (q+1) z := by
      unfold Interior at hi ⊢
      rcases hv with h|h <;> omega
    have hEdge : Edge q c z := by
      refine ⟨hi,hi',?_⟩
      rcases hv with h|h <;> omega
    exact Walk.cons q c z bs.length a hEdge (ih (q+1) z hi' he')

/-- The converse also holds, with an exact weighted Boolean word. -/
theorem weight_of_walk {q c k a : Nat} (h : Walk q c k a) :
    ∃ xs : List Bool, xs.length=k ∧ c+weightSum q xs=2^k*a := by
  induction h with
  | nil q c hi => exact ⟨[],rfl,by simp [weightSum]⟩
  | cons q c z k y h tail ih =>
    obtain ⟨xs,hx,he⟩ := ih
    rcases h.2.2 with h0|h1
    · refine ⟨false::xs,by simp [hx],?_⟩
      simp [weightSum,Nat.pow_succ]
      calc
        _ = 2*(z+weightSum (q+1) xs) := by omega
        _ = _ := by rw [he]; ac_rfl
    · refine ⟨true::xs,by simp [hx],?_⟩
      simp [weightSum,Nat.pow_succ]
      calc
        _ = 2*(z+weightSum (q+1) xs) := by omega
        _ = _ := by rw [he]; ac_rfl

/-- At most one interior predecessor exists; the map is exact. -/
theorem edge_iff_parent (q c z : Nat) (hz : Interior (q+1) z) :
    Edge q c z ↔ Interior q c ∧ c=(2*z)%q := by
  unfold Edge
  constructor
  · rintro ⟨hc,_,he⟩
    refine ⟨hc,?_⟩
    have hlt : c<q := by unfold Interior at hc; omega
    rcases he with h|h
    · rw [h,Nat.mod_eq_of_lt hlt]
    · rw [h,Nat.add_mod_right,Nat.mod_eq_of_lt hlt]
  · rintro ⟨hc,rfl⟩
    refine ⟨hc,hz,?_⟩
    unfold Interior at hz
    by_cases h : 2*z<q
    · left; rw [Nat.mod_eq_of_lt h]
    · right
      rw [Nat.mod_eq_sub_mod (by omega : q≤2*z),Nat.mod_eq_of_lt (by omega : 2*z-q<q)]
      omega

/-- Merge two sorted lists, suppressing equal heads. Membership is preserved
    even for unsorted inputs and insufficient fuel. -/
def join : Nat → List Nat → List Nat → List Nat
  | 0, xs, ys => xs++ys
  | _+1, [], ys => ys
  | _+1, xs, [] => xs
  | k+1, a::as, b::bs =>
    if a=b then a::join k as bs
    else if a<b then a::join k as (b::bs)
    else b::join k (a::as) bs

theorem mem_join (x k : Nat) (as bs : List Nat) :
    x∈join k as bs ↔ x∈as ∨ x∈bs := by
  induction k generalizing as bs with
  | zero => simp [join]
  | succ k ih =>
    cases as with
    | nil => simp [join]
    | cons a as =>
      cases bs with
      | nil => simp [join]
      | cons b bs =>
        by_cases h : a=b
        · subst b; simp [join,ih,or_assoc,or_left_comm,or_comm]
        · by_cases hlt : a<b <;> simp [join,h,hlt,ih,or_assoc,or_left_comm,or_comm]

instance (q c : Nat) : Decidable (Interior q c) := by unfold Interior; infer_instance

/-- Split at the only modular wrap, then merge the two monotone images.
    This avoids quadratic duplicate removal or nonreducible sorting. -/
def branch (q : Nat) (low : Bool) (zs : List Nat) : List Nat :=
  (((zs.filter fun z => decide (2*z<q) == low).map fun z => (2*z)%q).filter
    fun c => decide (Interior q c))

def back (q : Nat) (zs : List Nat) : List Nat :=
  let a := branch q true zs
  let b := branch q false zs
  join (a.length+b.length) a b

theorem mem_branch (q c : Nat) (low : Bool) (zs : List Nat) :
    c∈branch q low zs ↔ (∃ z∈zs, decide (2*z<q)=low ∧ (2*z)%q=c) ∧ Interior q c := by
  simp only [branch,List.mem_filter,List.mem_map,decide_eq_true_eq,beq_iff_eq]
  constructor
  · rintro ⟨⟨z,⟨hz,hb⟩,he⟩,hc⟩; exact ⟨⟨z,hz,hb,he⟩,hc⟩
  · rintro ⟨⟨z,hz,hb,he⟩,hc⟩; exact ⟨⟨z,⟨hz,hb⟩,he⟩,hc⟩

theorem mem_back (q c : Nat) (zs : List Nat)
    (h : ∀ z∈zs, Interior (q+1) z) :
    c∈back q zs ↔ ∃ z∈zs, Edge q c z := by
  unfold back
  rw [mem_join,mem_branch,mem_branch]
  constructor
  · rintro (⟨⟨z,hz,_,rfl⟩,hc⟩|⟨⟨z,hz,_,rfl⟩,hc⟩) <;>
      exact ⟨z,hz,(edge_iff_parent q _ z (h z hz)).mpr ⟨hc,rfl⟩⟩
  · rintro ⟨z,hz,he⟩
    obtain ⟨hc,hp⟩ := (edge_iff_parent q c z (h z hz)).mp he
    cases hb : decide (2*z<q)
    · right; exact ⟨⟨z,hz,hb,hp.symm⟩,hc⟩
    · left; exact ⟨⟨z,hz,hb,hp.symm⟩,hc⟩

/-- All interior endpoints at the common final clock. -/
def terminal (q : Nat) : List Nat := List.range' 1 (q-3)

theorem mem_terminal (q c : Nat) : c∈terminal q ↔ Interior q c := by
  simp only [terminal,List.mem_range',Nat.one_mul,Interior]
  constructor
  · rintro ⟨i,hi,rfl⟩; omega
  · intro h; exact ⟨c-1,by omega,by omega⟩

/-- live q k comprises exactly the states with a k-edge continuation.
All starts at the same clock share the same backward computation. -/
def live (q : Nat) : Nat → List Nat
  | 0 => terminal q
  | k+1 => back q (live (q+1) k)

theorem mem_live (q c k : Nat) : c∈live q k ↔ ∃ y, Walk q c k y := by
  induction k generalizing q c with
  | zero =>
    rw [live,mem_terminal]
    constructor
    · intro hi; exact ⟨c,Walk.nil q c hi⟩
    · rintro ⟨y,h⟩; cases h; assumption
  | succ k ih =>
    rw [live,mem_back]
    · constructor
      · rintro ⟨z,hz,he⟩
        obtain ⟨y,hy⟩ := (ih (q+1) z).mp hz
        exact ⟨y,Walk.cons q c z k y he hy⟩
      · rintro ⟨y,h⟩
        cases h with
        | cons _ _ z _ _ he tail => exact ⟨z,(ih (q+1) z).mpr ⟨y,tail⟩,he⟩
    · intro z hz
      obtain ⟨y,hy⟩ := (ih (q+1) z).mp hz
      cases hy with
      | nil _ _ hi => exact hi
      | cons _ _ _ _ _ he _ => exact he.1

/-- The center birth at an even clock q represents index n=q-4. -/
def birth (q : Nat) (zs : List Nat) : List Nat :=
  if q%2=0 ∧ (q-2)/2 ∈ zs then [q-4] else []

/-- A single downward sweep collects all centers which still have
    descendants at the common terminal clock. -/
def sweep (q : Nat) (zs : List Nat) : Nat → List Nat
  | 0 => birth q zs
  | d+1 => birth q zs ++ sweep (q-1) (back (q-1) zs) d

theorem mem_birth (q n : Nat) (zs : List Nat) (hq : 4≤q) :
    n∈birth q zs ↔ n+4=q ∧ n%2=0 ∧ (n+2)/2∈zs := by
  unfold birth
  split <;> rename_i h
  · simp only [List.mem_singleton]
    constructor
    · intro he; subst n; exact ⟨by omega,by omega,by simpa [show q-4+2=q-2 by omega] using h.2⟩
    · intro he; omega
  · simp only [List.not_mem_nil,false_iff]
    rintro ⟨rfl,he,hm⟩
    exact h ⟨by omega,by simpa using hm⟩

/-- Membership in the sweep is equivalent to a surviving central birth.
    The proof maintains the common final clock q+k. -/
theorem mem_sweep (q d k n : Nat) (hq : d+4≤q) :
    n∈sweep q (live q k) d ↔
      q-d≤n+4 ∧ n+4≤q ∧ n%2=0 ∧
      (n+2)/2∈live (n+4) (q+k-(n+4)) := by
  induction d generalizing q k with
  | zero =>
    rw [sweep,mem_birth q n _ (by omega)]
    constructor
    · rintro ⟨rfl,hn,hm⟩
      exact ⟨by omega,by omega,hn,by simpa using hm⟩
    · rintro ⟨hlo,hhi,hn,hm⟩
      have hq : q=n+4 := by omega
      subst q
      exact ⟨rfl,hn,by simpa using hm⟩
  | succ d ih =>
    have hq1 : q-1+1=q := by omega
    have hback : back (q-1) (live q k)=live (q-1) (k+1) := by rw [live,hq1]
    rw [sweep,List.mem_append,mem_birth q n _ (by omega),hback,ih (q-1) (k+1) (by omega)]
    constructor
    · rintro (⟨rfl,hn,hm⟩|⟨hl,hh,hn,hm⟩)
      · exact ⟨by omega,by omega,hn,by simpa using hm⟩
      · exact ⟨by omega,by omega,hn,by simpa [show q-1+(k+1)=q+k by omega] using hm⟩
    · rintro ⟨hl,hh,hn,hm⟩
      by_cases h : n+4=q
      · left; subst q; exact ⟨rfl,hn,by simpa using hm⟩
      · right; exact ⟨by omega,by omega,hn,by simpa [show q-1+(k+1)=q+k by omega] using hm⟩

/-- A complete sweep down from F, retaining only births at or above L. -/
def batch (F L : Nat) : List Nat := sweep F (terminal F) (F-(L+4))

theorem mem_batch (F L n : Nat) (hL : L+4≤F) :
    n∈batch F L ↔ L≤n ∧ n+4≤F ∧ n%2=0 ∧
      (n+2)/2∈live (n+4) (F-(n+4)) := by
  unfold batch
  have h := mem_sweep F (F-(L+4)) 0 n (by omega)
  simp only [live,Nat.add_zero] at h
  rw [h]
  simp [show F-(F-(L+4))=L+4 by omega]

#print axioms walk_of_weight
#print axioms weight_of_walk
#print axioms edge_iff_parent
#print axioms mem_live
#print axioms mem_sweep
#print axioms mem_batch
end BB6.Agent9BatchCarry
