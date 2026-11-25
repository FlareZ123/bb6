import ShadowBits

namespace BB6.Agent19ShadowBits

def Good : Node → Prop
  | .c m x => 0<x ∧ x+211*(1+(m+1)%2)+422<base m
  | .p m x => 0<x ∧ x+844<base m

theorem child_good {n : Nat} {u v : Node} (hg : Good u) (hv : v∈child n u) : Good v := by
  cases u with
  | c m x =>
    by_cases h : num m x 1%2=0
    · simp [child,h] at hv
      rcases hv with rfl|⟨_,_,rfl⟩
      · simp [Good,base,num,nextM] at *
        omega
      · simp [Good,base] at *
        omega
    · simp [child,h] at hv
      rcases hv with rfl|⟨_,_,rfl⟩
      · simp [Good,base,num,nextM] at *
        omega
      · simp [Good,base] at *
        omega
  | p m x =>
    by_cases h : x%2=0
    · simp [child,h] at hv
      subst v
      simp [Good,base] at *
      omega
    · simp [child,h] at hv

/-- Every legal compact step has one of four arithmetic forms. -/
def Micro : Node → Node → Prop
  | .c m x, .c a b => a=m+4 ∧ 2*b=num m x 1
  | .c m x, .p a b => (a=m+7 ∧ 2*b=num m x 2) ∨ (a=m+6 ∧ 2*b=x)
  | .p m x, .c a b => a=m ∧ 2*b=x
  | .p _ _, .p _ _ => False

theorem child_micro {n : Nat} {u v : Node} (hv : v∈child n u) : Micro u v := by
  cases u with
  | c m x =>
    by_cases h : num m x 1%2=0
    · simp [child,h] at hv
      rcases hv with rfl|⟨_,_,rfl⟩
      · simp [Micro,nextM]; omega
      · simp [Micro]; omega
    · have hp := num_parity_flip m x
      simp [child,h] at hv
      rcases hv with rfl|⟨_,_,rfl⟩
      · simp [Micro,nextM]; omega
      · simp [Micro]; omega
  | p m x =>
    by_cases h : x%2=0
    · simp [child,h] at hv
      subst v
      simp [Micro]; omega
    · simp [child,h] at hv

theorem micro_parent_unique {u v z : Node}
    (gu : Good u) (gv : Good v)
    (hu : Micro u z) (hv : Micro v z) : u=v := by
  cases u <;> cases v <;> cases z <;>
    simp [Micro,Good,base,num,nextM] at * <;> omega

theorem child_parent_unique {n : Nat} {u v z : Node}
    (gu : Good u) (gv : Good v)
    (hu : z∈child n u) (hv : z∈child n v) : u=v :=
  micro_parent_unique gu gv (child_micro hu) (child_micro hv)

theorem child_nodup (n : Nat) (u : Node) : (child n u).Nodup := by
  cases u with
  | c m x =>
    by_cases h : num m x 1%2=0 <;>
      by_cases h' : n>0 ∧ x%2=0 <;>
      simp [child,h,h',nextM] <;> omega
  | p m x => by_cases h : x%2=0 <;> simp [child,h]

theorem frontier_good {m x : Nat} (g : Good (.c m x)) (n : Nat) :
    ∀ v ∈ frontier m x n, Good v := by
  induction n with
  | zero => simp [frontier,g]
  | succ n ih =>
    intro v hv
    obtain ⟨u,hu,hv⟩ := List.mem_flatMap.mp hv
    exact child_good (ih u hu) hv

theorem nodup_children (n : Nat) (l : List Node) (hn : l.Nodup)
    (hg : ∀ v∈l, Good v) : (l.flatMap (child n)).Nodup := by
  induction l with
  | nil => simp
  | cons u us ih =>
    have hnu := List.nodup_cons.mp hn
    have hgu := hg u (by simp)
    have hgs : ∀ v∈us, Good v := fun v hv => hg v (by simp [hv])
    rw [List.flatMap_cons,List.nodup_append]
    refine ⟨child_nodup n u,ih hnu.2 hgs,?_⟩
    intro a ha b hb hab
    subst b
    obtain ⟨v,hv,ha'⟩ := List.mem_flatMap.mp hb
    have he := child_parent_unique hgu (hgs v hv) ha ha'
    subst v
    exact hnu.1 hv

theorem frontier_nodup {m x : Nat} (g : Good (.c m x)) (n : Nat) :
    (frontier m x n).Nodup := by
  induction n with
  | zero => simp [frontier]
  | succ n ih => exact nodup_children n _ ih (frontier_good g n)

#print axioms child_good
#print axioms micro_parent_unique
#print axioms frontier_nodup

/-- The mass interval at bit layer n. Pending nodes include one extra
    bit of intended cost. -/
def MassBound (m0 n : Nat) : Node → Prop
  | .c m _ => m0+3*n≤m ∧ m≤m0+4*n
  | .p m _ => m0+3*(n+1)≤m ∧ m≤m0+4*(n+1)

theorem full_mass {m0 x0 n m x : Nat} (hf : Full m0 x0 n m x) :
    m0+3*n≤m ∧ m≤m0+4*n := by
  induction hf with
  | zero => omega
  | snoc hp he ih =>
    obtain ⟨hd,hm,_⟩ := he
    unfold nextM at hm
    omega

theorem valid_mass {m0 x0 n : Nat} {v : Node} (h : Valid m0 x0 n v) : MassBound m0 n v := by
  cases v with
  | c m x => exact full_mass h
  | p m z =>
    obtain ⟨p,a,b,d,hp,hd,hn,hm,_⟩ := h
    have hh := full_mass hp
    unfold nextM at hm
    simp [MassBound]
    omega

def grid (m n : Nat) : List Node :=
  (List.range (n+5)).flatMap fun i =>
    (List.range (base (m+4*(n+1)))).flatMap fun z =>
      [.c (m+3*n+i) z,.p (m+3*n+i) z]

theorem in_grid {m x n : Nat} {v : Node}
    (g : Good (.c m x)) (h : v∈frontier m x n) : v∈grid m n := by
  have hM := valid_mass ((valid_frontier _ _ _ _).mp h)
  have hG := frontier_good g n v h
  cases v with
  | c a b =>
    simp only [MassBound] at hM
    simp only [Good] at hG
    have hA : a=m+3*n+(a-(m+3*n)) := by omega
    have hI : a-(m+3*n)<n+5 := by omega
    have hB : b<base (m+4*(n+1)) := by unfold base at *; omega
    exact List.mem_flatMap.mpr ⟨_,List.mem_range.mpr hI,List.mem_flatMap.mpr
      ⟨_,List.mem_range.mpr hB,by rw [←hA]; simp⟩⟩
  | p a b =>
    simp only [MassBound] at hM
    simp only [Good] at hG
    have hA : a=m+3*n+(a-(m+3*n)) := by omega
    have hI : a-(m+3*n)<n+5 := by omega
    have hB : b<base (m+4*(n+1)) := by unfold base at *; omega
    exact List.mem_flatMap.mpr ⟨_,List.mem_range.mpr hI,List.mem_flatMap.mpr
      ⟨_,List.mem_range.mpr hB,by rw [←hA]; simp⟩⟩

theorem flatMap_const_len {α β : Type} (l : List α) (f : α → List β)
    (k : Nat) (h : ∀ a, (f a).length=k) :
    (l.flatMap f).length=l.length*k := by
  induction l with
  | nil => simp
  | cons a as ih => simp [List.flatMap_cons, h, ih, Nat.succ_mul, Nat.add_comm]

theorem grid_length (m n : Nat) :
    (grid m n).length=2*(n+5)*base (m+4*(n+1)) := by
  unfold grid
  rw [flatMap_const_len _ _ (base (m+4*(n+1))*2)]
  · simp [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]
  · intro i
    rw [flatMap_const_len _ _ 2]
    · simp
    · intro z; rfl

theorem frontier_width {m x : Nat} (g : Good (.c m x)) (n : Nat) :
    (frontier m x n).length≤2*(n+5)*base (m+4*(n+1)) := by
  rw [←grid_length]
  exact (frontier_nodup g n).length_le_of_subset (fun _ hv => in_grid g hv)

#print axioms full_mass
#print axioms frontier_width

end BB6.Agent19ShadowBits
