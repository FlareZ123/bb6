import BB429InverseWordCount
import Lean.Elab.Tactic.Omega

namespace BB429InverseWord

/-- Any odd offset c gives an odd initial rank and an even starting phase. -/
def rayPhase (c:Nat) : Nat := if c%4=1 then 0 else 2

theorem rayPhase_even (c:Nat) : (rayPhase c)%2=0 := by
  unfold rayPhase
  split <;> decide

theorem ray_initial_phase (c a b:Nat) (hc:c%2=1)
    (hbal:b+c=2*a) :
    (2*a+b)%4=(3+rayPhase c)%4 := by
  unfold rayPhase
  by_cases h : c%4=1
  · simp [h]; omega
  · have hc3 : c%4=3 := by omega
    simp [h]; omega

/-- All high-depth inverse words on any fixed odd affine offset ray are regular. -/
theorem odd_ray_regular (c a b:Nat) (hc:c%2=1)
    (hbal:b+c=2*a) {ws:List Move} {x y:Nat}
    (h:HighChain a b ws x y) : Regular (rayPhase c) ws := by
  exact high_chain_regular (rayPhase c) a b
    (ray_initial_phase c a b hc hbal) h

theorem allWords_len_even (j k:Nat) (hj:j%2=0) :
    (allWords j k).length=2^(k/2) := by
  have hh := allWords_length_even (k/2) j hj
  rcases hh with ⟨he,ho⟩
  have hk : k = 2*(k/2) ∨ k = 2*(k/2)+1 := by omega
  rcases hk with h|h
  · rw [h]
    have hdiv : (2*(k/2))/2 = k/2 := by omega
    simpa [hdiv] using he
  · rw [h]
    have hdiv : (2*(k/2)+1)/2 = k/2 := by omega
    simpa [hdiv] using ho

/-- An integer first counter on an actual rooted odd ray. -/
def OddRayCandidate (c a:Nat) : Prop :=
  ∃ b, BB429NewResidue.Reach a b ∧ b+c=2*a

theorem odd_ray_has_word (c k a:Nat)
    (hc:c%2=1) (hr:OddRayCandidate c a)
    (ha:16*2^k≤a+3) :
    ∃ ws:List Move, ws.length=k ∧ Regular (rayPhase c) ws ∧
      ∃ b x y, BB429NewResidue.Reach a b ∧ b+c=2*a ∧
        HighChain a b ws x y := by
  obtain ⟨b,hr,hbal⟩ := hr
  obtain ⟨ws,x,y,hws,hchain⟩ := source_high_prefix k a b hr ha
  exact ⟨ws,hws,odd_ray_regular c a b hc hbal hchain,
    ⟨b,x,y,hr,hbal,hchain⟩⟩

noncomputable def chosenOddRayWord (c k a:Nat) : List Move := by
  classical
  exact if h : c%2=1 ∧ OddRayCandidate c a ∧ 16*2^k≤a+3 then
    Classical.choose (odd_ray_has_word c k a h.1 h.2.1 h.2.2)
  else []

theorem chosenOddRayWord_spec (c k a:Nat)
    (hc:c%2=1) (hr:OddRayCandidate c a) (ha:16*2^k≤a+3) :
    (chosenOddRayWord c k a).length=k ∧
    Regular (rayPhase c) (chosenOddRayWord c k a) ∧
    ∃ b x y, BB429NewResidue.Reach a b ∧ b+c=2*a ∧
      HighChain a b (chosenOddRayWord c k a) x y := by
  have hh : c%2=1 ∧ OddRayCandidate c a ∧ 16*2^k≤a+3 :=
    ⟨hc,hr,ha⟩
  unfold chosenOddRayWord
  simp only [dif_pos hh]
  exact Classical.choose_spec (odd_ray_has_word c k a hc hr ha)

/-- If two rooted ray points select the same inverse word, they have equal
first-counter residues modulo 2^k. -/
theorem chosenOddRayWord_mod (c k a a':Nat)
    (hc:c%2=1)
    (hr:OddRayCandidate c a) (hr':OddRayCandidate c a')
    (ha:16*2^k≤a+3) (ha':16*2^k≤a'+3)
    (hw:chosenOddRayWord c k a=chosenOddRayWord c k a') :
    a%(2^k)=a'%(2^k) := by
  obtain ⟨hlen,_,b,x,y,_,hbal,hchain⟩ :=
    chosenOddRayWord_spec c k a hc hr ha
  obtain ⟨hlen',_,b',x',y',_,hbal',hchain'⟩ :=
    chosenOddRayWord_spec c k a' hc hr' ha'
  have hc2 : HighChain a' b' (chosenOddRayWord c k a) x' y' := by
    rw [hw]; exact hchain'
  by_cases hh : a'≤a
  · have ht := original_same_word_unique c a b a' b' hbal hbal' hh hchain hc2
    exact congruence_of_dvd_sub (2^k) a a' hh (by simpa [hlen] using ht)
  · have hh' : a≤a' := by omega
    have ht := original_same_word_unique c a' b' a b hbal' hbal hh' hc2 hchain
    exact (congruence_of_dvd_sub (2^k) a' a hh' (by simpa [hlen] using ht)).symm

/-- The two components of the usual quotient-remainder decomposition uniquely
identify the nonnegative integer. -/
theorem divmod_unique (M a a':Nat)
    (hr:a%M=a'%M) (hd:a/M=a'/M) : a=a' := by
  calc
    a = a%M+M*(a/M) := (Nat.mod_add_div a M).symm
    _ = a'%M+M*(a'/M) := by rw [hr,hd]
    _ = a' := Nat.mod_add_div a' M

theorem chosenOddRayWord_quot_inj (c k a a':Nat)
    (hc:c%2=1)
    (hr:OddRayCandidate c a) (hr':OddRayCandidate c a')
    (ha:16*2^k≤a+3) (ha':16*2^k≤a'+3)
    (hw:chosenOddRayWord c k a=chosenOddRayWord c k a')
    (hq:a/(2^k)=a'/(2^k)) : a=a' := by
  exact divmod_unique (2^k) a a'
    (chosenOddRayWord_mod c k a a' hc hr hr' ha ha' hw) hq

/-- A rectangular list of all possible (inverse-word, integer quotient)
certificates has exactly the product count. -/
theorem rectangle_list_count {α:Type} (l:List α) (n:Nat) :
    (l.flatMap (fun ws => (List.range n).map (fun q => (ws,q)))).length
        = l.length*n := by
  induction l with
  | nil => simp
  | cons ws rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map,
        List.length_range, List.length_cons, ih]
      simp [Nat.add_mul, Nat.add_comm]

theorem rectangle_count (j k n:Nat) (hj:j%2=0) :
    ((allWords j k).flatMap (fun ws => (List.range n).map (fun q => (ws,q)))).length
        = n*2^(k/2) := by
  rw [rectangle_list_count, allWords_len_even j k hj]
  exact Nat.mul_comm _ _

/-- A genuine blank-root orbit meets any fixed odd-offset diagonal ray in
at most O(sqrt N) first-counter values within each dyadic shell. -/
theorem odd_ray_dyadic_shell_bound (c k:Nat) (hc:c%2=1)
    (l:List Nat) (hn:l.Nodup)
    (hl:∀a, a∈l → 16*2^k≤a ∧ a<32*2^k ∧ OddRayCandidate c a) :
    l.length ≤ 32*2^(k/2) := by
  classical
  let f : Nat → List Move × Nat := fun a => (chosenOddRayWord c k a, a/(2^k))
  have hinj : ∀ a, a∈l → ∀ a', a'∈l → f a=f a' → a=a' := by
    intro a ha a' ha' he
    obtain ⟨ha0,ha1,ha2⟩ := hl a ha
    obtain ⟨ha0',ha1',ha2'⟩ := hl a' ha'
    have hword : chosenOddRayWord c k a=chosenOddRayWord c k a' := by
      exact congrArg Prod.fst he
    have hquot : a/(2^k)=a'/(2^k) := by
      exact congrArg Prod.snd he
    exact chosenOddRayWord_quot_inj c k a a' hc ha2 ha2'
      (by omega) (by omega) hword hquot
  have hnodup : (l.map f).Nodup := nodup_map_inj_on l f hn hinj
  have hsub : (l.map f) ⊆
      (allWords (rayPhase c) k).flatMap
        (fun ws => (List.range 32).map (fun q => (ws,q))) := by
    intro z hz
    obtain ⟨a,ha,hz⟩ := List.mem_map.mp hz
    subst z
    obtain ⟨ha0,ha1,ha2⟩ := hl a ha
    obtain ⟨hwlen,hwreg,_⟩ :=
      chosenOddRayWord_spec c k a hc ha2 (by omega)
    apply List.mem_flatMap.mpr
    refine ⟨chosenOddRayWord c k a, ?_, ?_⟩
    · simpa [hwlen] using regular_mem_allWords (rayPhase c) hwreg
    · apply List.mem_map.mpr
      have hp : 0<2^k := Nat.two_pow_pos k
      have hq : a/(2^k)<32 :=
        (Nat.div_lt_iff_lt_mul hp).mpr (by simpa [Nat.mul_comm] using ha1)
      exact ⟨a/(2^k),List.mem_range.mpr hq,rfl⟩
  have hh := List.Nodup.length_le_of_subset hnodup hsub
  rw [List.length_map,rectangle_count (rayPhase c) k 32 (rayPhase_even c)] at hh
  exact hh

#print axioms odd_ray_dyadic_shell_bound
end BB429InverseWord
