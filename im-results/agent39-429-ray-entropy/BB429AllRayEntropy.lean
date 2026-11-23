import BB429OddRayEntropy
import Lean.Elab.Tactic.Omega

namespace BB429InverseWord

/-- The unique phase that realizes the initial rank on the ray b+c=2a,
for both odd and even c. -/
def anyRayPhase (c:Nat) : Nat := (5-c%4)%4

theorem any_ray_initial_phase (c a b:Nat) (hbal:b+c=2*a) :
    (2*a+b)%4=(3+anyRayPhase c)%4 := by
  unfold anyRayPhase
  have h : c%4=0 ∨ c%4=1 ∨ c%4=2 ∨ c%4=3 := by omega
  rcases h with h|h|h|h <;> omega

/-- At arbitrary initial rank parity, at most ceil(k/2) inverse letters have
more than one legal choice. -/
theorem allWords_universal_bound (j k:Nat) :
    (allWords j k).length ≤ 2*2^(k/2) := by
  by_cases hj:j%2=0
  · rw [allWords_len_even j k hj]
    omega
  · have hj1:j%2=1 := by omega
    cases k with
    | zero => simp [allWords]
    | succ k =>
        have hpe:(j+1)%2=0 := by omega
        have he:=allWords_len_even (j+1) k hpe
        rw [allWords_len_step,options_odd j hj1,he]
        have hdiv:k/2≤(k+1)/2 := by omega
        have hp:2^(k/2)≤2^((k+1)/2) := Nat.pow_le_pow_right (by decide) hdiv
        omega

def AnyRayCandidate (c a:Nat) : Prop :=
  ∃ b, BB429NewResidue.Reach a b ∧ b+c=2*a

noncomputable def chosenAnyRayWord (c k a:Nat) : List Move := by
  classical
  exact if h : AnyRayCandidate c a ∧ 16*2^k≤a+3 then
    Classical.choose (by
      obtain ⟨b,hr,hbal⟩ := h.1
      obtain ⟨ws,x,y,hws,hchain⟩ := source_high_prefix k a b hr h.2
      exact ⟨ws,hws,high_chain_regular (anyRayPhase c) a b
        (any_ray_initial_phase c a b hbal) hchain,
        ⟨b,x,y,hr,hbal,hchain⟩⟩ :
      ∃ ws:List Move, ws.length=k ∧ Regular (anyRayPhase c) ws ∧
        ∃ b x y, BB429NewResidue.Reach a b ∧ b+c=2*a ∧
          HighChain a b ws x y)
  else []

theorem chosenAnyRayWord_spec (c k a:Nat)
    (hr:AnyRayCandidate c a) (ha:16*2^k≤a+3) :
    (chosenAnyRayWord c k a).length=k ∧
    Regular (anyRayPhase c) (chosenAnyRayWord c k a) ∧
    ∃ b x y, BB429NewResidue.Reach a b ∧ b+c=2*a ∧
      HighChain a b (chosenAnyRayWord c k a) x y := by
  have hh : AnyRayCandidate c a ∧ 16*2^k≤a+3 := ⟨hr,ha⟩
  unfold chosenAnyRayWord
  simp only [dif_pos hh]
  exact Classical.choose_spec (by
      obtain ⟨b,hr,hbal⟩ := hr
      obtain ⟨ws,x,y,hws,hchain⟩ := source_high_prefix k a b hr ha
      exact ⟨ws,hws,high_chain_regular (anyRayPhase c) a b
        (any_ray_initial_phase c a b hbal) hchain,
        ⟨b,x,y,hr,hbal,hchain⟩⟩ :
      ∃ ws:List Move, ws.length=k ∧ Regular (anyRayPhase c) ws ∧
        ∃ b x y, BB429NewResidue.Reach a b ∧ b+c=2*a ∧
          HighChain a b ws x y)

/-- Source-path uniqueness along any fixed offset and length, regardless of
whether c is odd or even. -/
theorem anyRayWord_quot_inj (c k a a':Nat)
    (hr:AnyRayCandidate c a) (hr':AnyRayCandidate c a')
    (ha:16*2^k≤a+3) (ha':16*2^k≤a'+3)
    (hw:chosenAnyRayWord c k a=chosenAnyRayWord c k a')
    (hq:a/(2^k)=a'/(2^k)) : a=a' := by
  obtain ⟨hlen,_,b,x,y,_,hbal,hchain⟩ := chosenAnyRayWord_spec c k a hr ha
  obtain ⟨hlen',_,b',x',y',_,hbal',hchain'⟩ := chosenAnyRayWord_spec c k a' hr' ha'
  have hc2 : HighChain a' b' (chosenAnyRayWord c k a) x' y' := by
    rw [hw]; exact hchain'
  have hmod : a%(2^k)=a'%(2^k) := by
    by_cases hh:a'≤a
    · have ht := original_same_word_unique c a b a' b' hbal hbal' hh hchain hc2
      exact congruence_of_dvd_sub (2^k) a a' hh (by simpa [hlen] using ht)
    · have hh':a≤a' := by omega
      have ht := original_same_word_unique c a' b' a b hbal' hbal hh' hc2 hchain
      exact (congruence_of_dvd_sub (2^k) a' a hh' (by simpa [hlen] using ht)).symm
  exact divmod_unique (2^k) a a' hmod hq

/-- Uniform original-source dyadic-shell square-root bound on every
fixed affine diagonal ray, *including* even offsets c. -/
theorem any_ray_dyadic_shell_bound (c k:Nat)
    (l:List Nat) (hn:l.Nodup)
    (hl:∀a, a∈l → 16*2^k≤a ∧ a<32*2^k ∧ AnyRayCandidate c a) :
    l.length ≤ 64*2^(k/2) := by
  classical
  let f : Nat → List Move × Nat := fun a => (chosenAnyRayWord c k a, a/(2^k))
  have hinj : ∀ a, a∈l → ∀ a', a'∈l → f a=f a' → a=a' := by
    intro a ha a' ha' he
    obtain ⟨ha0,ha1,ha2⟩ := hl a ha
    obtain ⟨ha0',ha1',ha2'⟩ := hl a' ha'
    have hword : chosenAnyRayWord c k a=chosenAnyRayWord c k a' :=
      congrArg Prod.fst he
    have hquot : a/(2^k)=a'/(2^k) := congrArg Prod.snd he
    exact anyRayWord_quot_inj c k a a' ha2 ha2'
      (by omega) (by omega) hword hquot
  have hnodup : (l.map f).Nodup := nodup_map_inj_on l f hn hinj
  have hsub : (l.map f) ⊆
      (allWords (anyRayPhase c) k).flatMap
        (fun ws => (List.range 32).map (fun q => (ws,q))) := by
    intro z hz
    obtain ⟨a,ha,hz⟩ := List.mem_map.mp hz
    subst z
    obtain ⟨ha0,ha1,ha2⟩ := hl a ha
    obtain ⟨hwlen,hwreg,_⟩ :=
      chosenAnyRayWord_spec c k a ha2 (by omega)
    apply List.mem_flatMap.mpr
    refine ⟨chosenAnyRayWord c k a, ?_, ?_⟩
    · simpa [hwlen] using regular_mem_allWords (anyRayPhase c) hwreg
    · apply List.mem_map.mpr
      have hp : 0<2^k := Nat.two_pow_pos k
      have hq : a/(2^k)<32 :=
        (Nat.div_lt_iff_lt_mul hp).mpr (by simpa [Nat.mul_comm] using ha1)
      exact ⟨a/(2^k),List.mem_range.mpr hq,rfl⟩
  have hh := List.Nodup.length_le_of_subset hnodup hsub
  rw [List.length_map, rectangle_list_count] at hh
  have hb := allWords_universal_bound (anyRayPhase c) k
  omega

#print axioms any_ray_dyadic_shell_bound
end BB429InverseWord
