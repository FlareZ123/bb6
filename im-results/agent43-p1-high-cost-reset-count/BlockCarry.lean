import CarryCert
namespace BB6.Agent43Block
open BB6.Agent43CarryCert

/-- All weighted sums of h consecutive choices, without integrality pruning. -/
def offsets (Q j : Nat) : Nat → List Nat
  | 0 => [0]
  | h+1 => (offsets Q (j+1) h).flatMap fun s => [2*s, 2*s+(Q-j)]

theorem step_eqn {Q j c : Nat} {cs : List Nat} (hc : c ∈ step Q j cs) :
    ∃ p ∈ cs, 2*c=p ∨ 2*c=p+(Q-j) := by
  simp only [step, List.mem_flatMap, List.mem_append] at hc
  obtain ⟨p,hp,hc⟩ := hc
  refine ⟨p,hp,?_⟩
  rcases hc with h|h
  · by_cases he : p%2=0
    · simp [he] at h; omega
    · simp [he] at h
  · by_cases he : (p+(Q-j))%2=0
    · simp [he] at h; omega
    · simp [he] at h

theorem states_offset (Q j h : Nat) (cs : List Nat) (v : Nat)
    (hv : v ∈ states Q j cs h) :
    ∃ c ∈ cs, ∃ s ∈ offsets Q j h, 2^h*v=c+s := by
  induction h generalizing j cs with
  | zero => exact ⟨v,hv,0,by simp [offsets],by simp⟩
  | succ h ih =>
    obtain ⟨u,hu,s,hs,he⟩ := ih (j+1) (step Q j cs) hv
    obtain ⟨c,hc,hh⟩ := step_eqn hu
    have he2 : 2*(2^h*v)=2*u+2*s := by omega
    have he3 : 2^(h+1)*v=2*(2^h*v) := by rw [Nat.pow_succ]; ac_rfl
    rcases hh with hh|hh
    · refine ⟨c,hc,2*s,?_,by omega⟩
      exact List.mem_flatMap.mpr ⟨s,hs,by simp⟩
    · refine ⟨c,hc,2*s+(Q-j),?_,by omega⟩
      exact List.mem_flatMap.mpr ⟨s,hs,by simp⟩

/-- Residue-indexed binary trie. The input is consumed low bit first. -/
inductive Trie where
  | leaf (values : List Nat)
  | node (zero one : Trie)
  deriving Inhabited

def Trie.empty : Nat → Trie
  | 0 => .leaf []
  | h+1 => let t := Trie.empty h; .node t t

def Trie.get (t : Trie) (r : Nat) : List Nat :=
  match t with
  | .leaf xs => xs
  | .node a b => if r%2=0 then a.get (r/2) else b.get (r/2)

def Trie.insert (t : Trie) (r v : Nat) : Trie :=
  match t with
  | .leaf xs => .leaf (v::xs)
  | .node a b => if r%2=0 then .node (a.insert (r/2) v) b else .node a (b.insert (r/2) v)

theorem Trie.get_insert_same (t : Trie) (r v : Nat) : v ∈ (t.insert r v).get r := by
  induction t generalizing r with
  | leaf xs => simp [Trie.get,Trie.insert]
  | node a b ia ib =>
    by_cases h : r%2=0 <;> simp [Trie.get,Trie.insert,h,ia,ib]

theorem Trie.get_insert_mono (t : Trie) (r r' v x : Nat)
    (hx : x ∈ t.get r) : x ∈ (t.insert r' v).get r := by
  induction t generalizing r r' with
  | leaf xs => simp [Trie.get,Trie.insert] at *; exact Or.inr hx
  | node a b ia ib =>
    by_cases h : r%2=0 <;> by_cases h' : r'%2=0 <;>
      simp [Trie.get,Trie.insert,h,h'] at * <;> first | exact hx | apply ia; exact hx | apply ib; exact hx

def modulus (h : Nat) := 2^h

def residue (M s : Nat) := (M-s%M)%M

def delta (M s : Nat) := (s+M-1)/M

def build (M : Nat) (t : Trie) : List Nat → Trie
  | [] => t
  | s::ss => build M (t.insert (residue M s) (delta M s)) ss

theorem build_mono (M : Nat) (t : Trie) (ss : List Nat) (r x : Nat)
    (hx : x ∈ t.get r) : x ∈ (build M t ss).get r := by
  induction ss generalizing t with
  | nil => exact hx
  | cons s ss ih => exact ih _ (t.get_insert_mono r _ _ x hx)

theorem build_sound (M : Nat) (t : Trie) (ss : List Nat) (s : Nat) (hs : s∈ss) :
    delta M s ∈ (build M t ss).get (residue M s) := by
  induction ss generalizing t with
  | nil => simp at hs
  | cons a as ih =>
    simp only [List.mem_cons] at hs
    rcases hs with rfl|hs
    · exact build_mono M _ as _ _ (t.get_insert_same _ _)
    · exact ih _ hs

def table (Q j h : Nat) : Trie := build (modulus h) (Trie.empty h) (offsets Q j h)

def blockStep (Q j h : Nat) (cs : List Nat) : List Nat :=
  let M := modulus h
  let t := table Q j h
  cs.flatMap fun c => (t.get (c%M)).map fun d => c/M+d

theorem residue_delta {M c s v : Nat} (hM : 0<M) (he : M*v=c+s) :
    c%M=residue M s ∧ v=c/M+delta M s := by
  have hmod : (c+s)%M=0 := by rw [←he]; simp
  have hc := Nat.mod_add_div c M
  have hs := Nat.mod_add_div s M
  have hcm := Nat.mod_lt c hM
  have hsm := Nat.mod_lt s hM
  have hsum : (c%M+s%M)%M=0 := by rw [←Nat.add_mod]; exact hmod
  have hcases : c%M+s%M=0 ∨ c%M+s%M=M := by
    have hh := Nat.mod_add_div (c%M+s%M) M
    have hsmall : (c%M+s%M)/M<2 := (Nat.div_lt_iff_lt_mul hM).2 (by omega)
    have hh' : (c%M+s%M)/M=0 ∨ (c%M+s%M)/M=1 := Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp hsmall)
    rcases hh' with h|h <;> rw [h,hsum] at hh <;> simp at hh <;> omega
  have hD : delta M s=s/M+(if s%M=0 then 0 else 1) := by
    unfold delta
    have h1 : s+M-1 = (s%M+M-1)+M*(s/M) := by omega
    rw [h1,Nat.add_mul_div_left _ _ hM]
    by_cases h : s%M=0
    · simp [h,Nat.div_eq_of_lt (show M-1<M by omega)]
    · have h2 : (s%M+M-1)/M=1 := by
        apply Nat.div_eq_of_lt_le <;> omega
      rw [h2]; simp [h]; omega
  rcases hcases with h|h
  · have hc0 : c%M=0 := by omega
    have hs0 : s%M=0 := by omega
    refine ⟨by simp [residue,hc0,hs0],?_⟩
    rw [hD,hs0,ite_eq_left rfl,Nat.add_zero]
    apply Nat.eq_of_mul_eq_mul_left hM
    rw [Nat.mul_add]
    omega
  · have hs0 : s%M≠0 := by omega
    have hh : M-s%M<M := by omega
    refine ⟨by simp [residue,Nat.mod_eq_of_lt hh]; omega,?_⟩
    rw [hD,ite_eq_right hs0]
    apply Nat.eq_of_mul_eq_mul_left hM
    rw [Nat.mul_add,Nat.mul_add,Nat.mul_one]
    omega

theorem block_sound (Q j h : Nat) (cs : List Nat) (v : Nat)
    (hv : v ∈ states Q j cs h) : v ∈ blockStep Q j h cs := by
  obtain ⟨c,hc,s,hs,he⟩ := states_offset Q j h cs v hv
  obtain ⟨hr,hv'⟩ := residue_delta (M:=modulus h) (Nat.two_pow_pos h) he
  apply List.mem_flatMap.mpr
  refine ⟨c,hc,List.mem_map.mpr ⟨delta (modulus h) s,?_,hv'.symm⟩⟩
  rw [hr]
  exact build_sound _ _ _ _ hs

#print axioms block_sound
end BB6.Agent43Block
