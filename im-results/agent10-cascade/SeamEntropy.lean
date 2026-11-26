import SeamPrefix
namespace SeamMass
set_option maxHeartbeats 0

inductive PrefixState where
  | boundary | oneZero | manyZeros
  deriving DecidableEq
open PrefixState

def next : PrefixState → Bool → Option PrefixState
  | boundary, true => some boundary
  | boundary, false => some oneZero
  | oneZero, true => none
  | oneZero, false => some manyZeros
  | manyZeros, true => some boundary
  | manyZeros, false => some manyZeros

def follow (s : PrefixState) : List Bool → Option PrefixState
  | [] => some s
  | b::xs => (next s b).bind (fun t => follow t xs)

theorem follow_append (s : PrefixState) (xs ys : List Bool) :
    follow s (xs++ys) = (follow s xs).bind (fun t => follow t ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons b xs ih =>
    simp only [List.cons_append,follow]
    cases next s b with
    | none => rfl
    | some t => simpa using ih t

theorem follow_many_zeros (n : Nat) : follow manyZeros (List.replicate n false) = some manyZeros := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ,follow,next,Option.bind_some] using ih

theorem block_legal (j : Nat) (hpos : 0<j) (hforbid : j≠2) :
    follow boundary (List.replicate (j-1) false ++ [true]) = some boundary := by
  cases j with
  | zero => omega
  | succ j =>
    cases j with
    | zero => rfl
    | succ j =>
      cases j with
      | zero => omega
      | succ n =>
        have he : n+1+1+1-1=n+1+1 := by omega
        rw [he,List.replicate_succ,List.replicate_succ,follow_append]
        simp only [follow,next,Option.bind_some,follow_many_zeros]

theorem code_legal {s w} (hw : Path s w) : follow boundary (code w) = some boundary := by
  induction hw with
  | nil => rfl
  | @cons s t j a w he hA hw ih =>
    have hj := edge_j_pos he
    have h2 : j≠2 := fun h => exponent_two_forbidden a (h ▸ he.2.2.2.2)
    have hb := block_legal j hj h2
    have hc : code ((j,a)::w) = (List.replicate (j-1) false ++ [true]) ++ code w := by
      simp only [code,List.append_assoc,List.singleton_append]
    rw [hc,follow_append,hb]
    exact ih

theorem prefix_legal {s t : PrefixState} {xs : List Bool} (h : follow s xs = some t) (n : Nat) :
    ∃ u, follow s (xs.take n) = some u := by
  have he := follow_append s (xs.take n) (xs.drop n)
  rw [List.take_append_drop,h] at he
  cases hh : follow s (xs.take n) with
  | none => simp [hh] at he
  | some u => exact ⟨u,rfl⟩

def prefixes : Nat → PrefixState → List (List Bool)
  | 0,_ => [[]]
  | n+1,boundary => (prefixes n boundary).map (true::·) ++ (prefixes n oneZero).map (false::·)
  | n+1,oneZero => (prefixes n manyZeros).map (false::·)
  | n+1,manyZeros => (prefixes n manyZeros).map (false::·) ++ (prefixes n boundary).map (true::·)

theorem prefixes_complete {n : Nat} {s t : PrefixState} {xs : List Bool}
    (hl : xs.length=n) (hr : follow s xs=some t) : xs ∈ prefixes n s := by
  induction n generalizing s t xs with
  | zero =>
    have he : xs=[] := List.eq_nil_of_length_eq_zero hl
    subst xs; simp [prefixes]
  | succ n ih =>
    cases xs with
    | nil => simp at hl
    | cons b ys =>
      have hn : ys.length=n := by simpa using hl
      cases s <;> cases b <;> simp only [follow,next,Option.bind_some,Option.bind_none] at hr
      · exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨ys,ih hn hr,rfl⟩))
      · exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨ys,ih hn hr,rfl⟩))
      · exact List.mem_map.mpr ⟨ys,ih hn hr,rfl⟩
      · contradiction
      · exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨ys,ih hn hr,rfl⟩))
      · exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨ys,ih hn hr,rfl⟩))

theorem prefix_lengths (n : Nat) :
    (prefixes n boundary).length=(prefixCounts n).1 ∧
    (prefixes n oneZero).length=(prefixCounts n).2.1 ∧
    (prefixes n manyZeros).length=(prefixCounts n).2.2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rcases h : prefixCounts n with ⟨x,y,z⟩
    rw [h] at ih
    obtain ⟨hx,hy,hz⟩ := ih
    simp only [prefixes,prefixCounts,h,List.length_append,List.length_map]
    simp [hx,hy,hz]

/-- An ideal word together with its terminal state and exact exponent. -/
def IdealWord (A : Nat) := {p : State × List (Nat × Nat) // p.1.A=A ∧ Path p.1 p.2}

def encodePrefix (A B : Nat) (p : IdealWord A) : List Bool := (code p.val.2).take B

theorem encodePrefix_injective {A B : Nat} (hA : 0<A)
    (hlo : 2^B≤3^A) (hhi : 3^A<2^(B+1)) {p q : IdealWord A}
    (h : encodePrefix A B p=encodePrefix A B q) : p=q := by
  have e := prefix_injective p.property.2 q.property.2 (p.property.1.trans q.property.1.symm)
    (by rw [p.property.1]; exact hA) B
    (by rw [p.property.1]; exact hlo) (by rw [p.property.1]; exact hhi) h
  apply Subtype.ext
  exact Prod.ext e.1 e.2

theorem encodePrefix_mem {A B : Nat} (hA : 0<A) (hlo : 2^B≤3^A) (p : IdealWord A) :
    encodePrefix A B p ∈ prefixes B boundary := by
  have hpos : 0<p.val.1.A := by rw [p.property.1]; exact hA
  have hb := (path_budget p.property.2).2 hpos
  rw [p.property.1] at hb
  have hlen : B≤totalJ p.val.2 := by
    by_cases h : B≤totalJ p.val.2
    · exact h
    · have hm := Nat.pow_le_pow_right (by decide : 0<2) (by omega : totalJ p.val.2≤B)
      omega
  have hl : (encodePrefix A B p).length=B := by
    simp only [encodePrefix,List.length_take,code_length p.property.2]
    omega
  obtain ⟨u,hu⟩ := prefix_legal (code_legal p.property.2) B
  exact prefixes_complete hl hu

/-- Every finite list of distinct ideal words of exponent A satisfies the
    exact automaton counting bound. No enumeration assumptions are required. -/
theorem ideal_count {A B : Nat} (hA : 0<A) (hlo : 2^B≤3^A) (hhi : 3^A<2^(B+1))
    (xs : List (IdealWord A)) (hn : xs.Nodup) : xs.length≤(prefixCounts B).1 := by
  let f := encodePrefix A B
  have hnd : (xs.map f).Nodup := by
    apply List.Pairwise.map f _ hn
    intro p q hpq he
    exact hpq (encodePrefix_injective hA hlo hhi he)
  have hs : xs.map f ⊆ prefixes B boundary := by
    intro x hx
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hx
    exact encodePrefix_mem hA hlo p
  have hh := hnd.length_le_of_subset hs
  rw [List.length_map,(prefix_lengths B).1] at hh
  exact hh

/-- Kernel-certified exponential bound on the weighted ideal mass at each
    exponent; multiplication by 7*9^B clears the denominators. -/
theorem ideal_count_majorant {A B : Nat} (hA : 0<A) (hlo : 2^B≤3^A) (hhi : 3^A<2^(B+1))
    (xs : List (IdealWord A)) (hn : xs.Nodup) : 7*9^B*xs.length≤9*16^B :=
  Nat.le_trans (Nat.mul_le_mul_left (7*9^B) (ideal_count hA hlo hhi xs hn)) (prefix_majorant B).1

#print axioms code_legal
#print axioms encodePrefix_injective
#print axioms ideal_count
#print axioms ideal_count_majorant
end SeamMass
