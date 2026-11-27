import AffineTable
namespace BB6.Agent9AffineResidue
open BB6.P1CarryExtinction

/-- Complement all selected bits after the compulsory initial bit. -/
def Twin (k : Nat) (p q : Node) : Prop :=
  p.r=q.r ∧ p.a+q.a=p.r+k+1 ∧ p.B+q.B=2^k ∧ p.B%2=1 ∧ q.B%2=1

theorem twin_advance (k : Nat) (p q : Node) (b : Bool) (hk : 0<k)
    (h : Twin k p q) : Twin (k+1) (advance k p b) (advance k q (!b)) := by
  rcases p with ⟨r,a,B⟩
  rcases q with ⟨s,c,D⟩
  rcases h with ⟨hr,ha,hB,ho,hd⟩
  change r=s at hr
  subst s
  change a+c=r+k+1 at ha
  change B+D=2^k at hB
  change B%2=1 at ho
  change D%2=1 at hd
  have hp : 2^k%2=0 := by
    cases k with
    | zero => omega
    | succ j => rw [Nat.pow_succ]; omega
  cases b <;> simp [Twin,advance,Nat.pow_succ]
  · have ht : (c+r+3+k)%2=a%2 := by omega
    rw [ht]
    rcases (show a%2=0 ∨ a%2=1 by omega) with hh|hh <;> simp [hh] <;> omega
  · have ht : (a+r+3+k)%2=c%2 := by omega
    rw [ht]
    rcases (show c%2=0 ∨ c%2=1 by omega) with hh|hh <;> simp [hh] <;> omega

/-- At depth d+2, retain only words with their second selected bit zero. -/
def halfNodes : Nat → List Node
  | 0 => [⟨2,1,1⟩]
  | d+1 => (halfNodes d).flatMap fun p => [advance (d+2) p false,advance (d+2) p true]

theorem halfNodes_subset (d : Nat) (p : Node) (hp : p∈halfNodes d) : p∈nodes (d+1) := by
  induction d generalizing p with
  | zero =>
    simp [halfNodes] at hp
    subst p
    decide
  | succ d ih =>
    simp only [halfNodes,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at hp
    obtain ⟨q,hq,rfl|rfl⟩ := hp <;> simp only [nodes,List.mem_flatMap]
    · exact ⟨q,ih q hq,by simp⟩
    · exact ⟨q,ih q hq,by simp⟩

theorem halfNodes_cover (d : Nat) (p : Node) (hp : p∈nodes (d+1)) :
    ∃ q∈halfNodes d, p=q ∨ Twin (d+2) p q := by
  induction d generalizing p with
  | zero =>
    have h : p=⟨2,1,1⟩ ∨ p=⟨2,4,3⟩ := by
      simpa [nodes,advance] using hp
    rcases h with rfl|rfl
    · exact ⟨_,by simp [halfNodes],Or.inl rfl⟩
    · exact ⟨_,by simp [halfNodes],Or.inr (by decide)⟩
  | succ d ih =>
    simp only [nodes,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at hp
    obtain ⟨p,hp,rfl|rfl⟩ := hp
    · obtain ⟨q,hq,rfl|ht⟩ := ih p hp
      · exact ⟨advance (d+2) q false,by simp [halfNodes,hq],Or.inl rfl⟩
      · refine ⟨advance (d+2) q true,by simp [halfNodes,hq],Or.inr ?_⟩
        exact twin_advance (d+2) p q false (by omega) ht
    · obtain ⟨q,hq,rfl|ht⟩ := ih p hp
      · exact ⟨advance (d+2) q true,by simp [halfNodes,hq],Or.inl rfl⟩
      · refine ⟨advance (d+2) q false,by simp [halfNodes,hq],Or.inr ?_⟩
        exact twin_advance (d+2) p q true (by omega) ht

theorem half_support (d r : Nat) :
    (∃ p∈nodes (d+1),p.r=r) ↔ ∃ p∈halfNodes d,p.r=r := by
  constructor
  · rintro ⟨p,hp,hr⟩
    obtain ⟨q,hq,he|ht⟩ := halfNodes_cover d p hp
    · exact ⟨q,hq,by simpa [he] using hr⟩
    · exact ⟨q,hq,ht.1.symm.trans hr⟩
  · rintro ⟨p,hp,hr⟩
    exact ⟨p,halfNodes_subset d p hp,hr⟩

theorem half_descend (k d : Nat) (hk : 2≤k) :
    descend k d (halfNodes (k-2))=halfNodes (k+d-2) := by
  induction d with
  | zero => simp [descend]
  | succ d ih =>
    rw [descend,ih,show k+(d+1)-2=(k+d-2)+1 by omega,halfNodes]
    rw [show k+d-2+2=k+d by omega]

def halfMask (k d r : Nat) : Nat :=
  pack k (descend k d ((halfNodes (k-2)).filter fun p=>p.r%2^k==r))

theorem halfMask_eq (k d r : Nat) (hk : 2≤k) : halfMask k d r=localMask k d r := by
  apply Nat.eq_of_testBit_eq
  intro j
  apply Bool.eq_iff_iff.mpr
  simp only [halfMask,localMask,pack_bit]
  constructor
  · rintro ⟨p,hp,hj⟩
    obtain ⟨hm,hr⟩ := (descend_filter k k d r _ (by omega) p).mp hp
    rw [half_descend k d hk] at hm
    have hf := halfNodes_subset (k+d-2) p hm
    refine ⟨p,(descend_filter k k d r _ (by omega) p).mpr ⟨?_,hr⟩,hj⟩
    rw [descend_nodes k d (by omega)]
    rwa [show k+d-1=k+d-2+1 by omega]
  · rintro ⟨p,hp,hj⟩
    obtain ⟨hm,hr⟩ := (descend_filter k k d r _ (by omega) p).mp hp
    rw [descend_nodes k d (by omega),show k+d-1=k+d-2+1 by omega] at hm
    obtain ⟨q,hq,he|ht⟩ := halfNodes_cover (k+d-2) p hm
    · subst p
      refine ⟨q,(descend_filter k k d r _ (by omega) q).mpr ⟨?_,hr⟩,hj⟩
      rwa [half_descend k d hk]
    · refine ⟨q,(descend_filter k k d r _ (by omega) q).mpr ⟨?_,?_⟩,?_⟩
      · rwa [half_descend k d hk]
      · rw [←ht.1]; exact hr
      · rw [←ht.1]; exact hj

def checkHalfRows (k d : Nat) (rows : List (Nat×Nat)) : Bool :=
  rows.all fun p=>halfMask k d p.1==p.2

theorem checkRows_half (k d : Nat) (hk : 2≤k) (rows : List (Nat×Nat)) :
    checkRows k d rows=checkHalfRows k d rows := by
  induction rows with
  | nil => rfl
  | cons p ps ih =>
    simp only [checkRows,checkHalfRows,List.all_cons] at *
    rw [halfMask_eq k d p.1 hk,ih]

#print axioms twin_advance
#print axioms halfNodes_cover
#print axioms halfMask_eq
#print axioms checkRows_half
end BB6.Agent9AffineResidue
