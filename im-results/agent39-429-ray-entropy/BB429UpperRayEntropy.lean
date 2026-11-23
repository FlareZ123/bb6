import BB429AllRayGlobal
import Lean.Elab.Tactic.Omega

namespace BB429InverseWord

theorem twin_balanced_invariant (a b a' b' : Nat)
    (hbal0 : 2*a+b+4*a' = 2*a'+b'+4*a)
    {ws : List Move} {x y x' y' : Nat}
    (h : Twin a b a' b' ws x y x' y') :
    ∃ M : Nat,
      M%2=1 ∧
      2^(ws.length)*x + M*a' = 2^(ws.length)*x' + M*a ∧
      2*x+y+4*a' = 2*x'+y'+4*a := by
  induction h with
  | nil =>
      refine ⟨1, by decide, ?_, ?_⟩
      · simp [Nat.add_comm]
      · exact hbal0
  | @snoc ws x y x' y' u v u' v' m hp he he' ih =>
      obtain ⟨M, hodd, hfirst, hbal⟩ := ih
      have hnewR : 2*u+v+4*a' = 2*u'+v'+4*a := by
        have hc := legit_cost m x y u v he
        have hc' := legit_cost m x' y' u' v' he'
        omega
      have hlen : (ws ++ [m]).length = ws.length+1 := by simp
      cases m with
      | F =>
          refine ⟨M, hodd, ?_, hnewR⟩
          rw [hlen]
          exact pair_F ws.length M x x' u u' a a' he.1.1 he'.1.1 hfirst
      | S =>
          let P := 2^(ws.length+1)
          have hP : P%2=0 := by
            dsimp [P]
            rw [Nat.pow_succ]
            omega
          have hmodd : (M+P)%2=1 := by omega
          refine ⟨M+P, hmodd, ?_, hnewR⟩
          rw [hlen]
          exact pair_nonF ws.length M x y x' y' u u' a a' 26
            hbal he.1.1 he'.1.1 hfirst
      | E =>
          let P := 2^(ws.length+1)
          have hP : P%2=0 := by
            dsimp [P]
            rw [Nat.pow_succ]
            omega
          have hmodd : (M+P)%2=1 := by omega
          refine ⟨M+P, hmodd, ?_, hnewR⟩
          rw [hlen]
          exact pair_nonF ws.length M x y x' y' u u' a a' 14
            hbal he.1.1 he'.1.1 hfirst

theorem twin_balanced_residue_unique (a b a' b' : Nat)
    (hbal: 2*a+b+4*a' = 2*a'+b'+4*a)
    (haa': a'≤a)
    {ws:List Move} {x y x' y':Nat}
    (ht: Twin a b a' b' ws x y x' y') :
    2^(ws.length) ∣ a-a' := by
  obtain ⟨M,hodd,hfirst,_⟩ := twin_balanced_invariant a b a' b' hbal ht
  exact paired_linear_congruence ws.length M a a' x x' hodd haa' hfirst

/-- Companion of the original ray result for the upper-side b=2a+c. -/
theorem upper_same_word_unique (c a b a' b' : Nat)
    (hb:b=2*a+c) (hb':b'=2*a'+c)
    (haa':a'≤a)
    {ws:List Move} {x y x' y':Nat}
    (h1:HighChain a b ws x y)
    (h2:HighChain a' b' ws x' y') :
    2^(ws.length) ∣ a-a' := by
  have hbal : 2*a+b+4*a' = 2*a'+b'+4*a := by omega
  have ht := twin_of_two_high_chains a b a' b' (Twin.nil) h1 h2
  exact twin_balanced_residue_unique a b a' b' hbal haa' ht

/-- The unique phase that realizes the initial rank on the ray b+c=2a,
for both odd and even c. -/
def upperRayPhase (c:Nat) : Nat := (c%4+1)%4

theorem upper_ray_initial_phase (c a b:Nat) (hbal:b=2*a+c) :
    (2*a+b)%4=(3+upperRayPhase c)%4 := by
  unfold upperRayPhase
  have h : c%4=0 ∨ c%4=1 ∨ c%4=2 ∨ c%4=3 := by omega
  rcases h with h|h|h|h <;> omega

def UpperRayCandidate (c a:Nat) : Prop :=
  ∃ b, BB429NewResidue.Reach a b ∧ b=2*a+c

noncomputable def chosenUpperRayWord (c k a:Nat) : List Move := by
  classical
  exact if h : UpperRayCandidate c a ∧ 16*2^k≤a+3 then
    Classical.choose (by
      obtain ⟨b,hr,hbal⟩ := h.1
      obtain ⟨ws,x,y,hws,hchain⟩ := source_high_prefix k a b hr h.2
      exact ⟨ws,hws,high_chain_regular (upperRayPhase c) a b
        (upper_ray_initial_phase c a b hbal) hchain,
        ⟨b,x,y,hr,hbal,hchain⟩⟩ :
      ∃ ws:List Move, ws.length=k ∧ Regular (upperRayPhase c) ws ∧
        ∃ b x y, BB429NewResidue.Reach a b ∧ b=2*a+c ∧
          HighChain a b ws x y)
  else []

theorem chosenUpperRayWord_spec (c k a:Nat)
    (hr:UpperRayCandidate c a) (ha:16*2^k≤a+3) :
    (chosenUpperRayWord c k a).length=k ∧
    Regular (upperRayPhase c) (chosenUpperRayWord c k a) ∧
    ∃ b x y, BB429NewResidue.Reach a b ∧ b=2*a+c ∧
      HighChain a b (chosenUpperRayWord c k a) x y := by
  have hh : UpperRayCandidate c a ∧ 16*2^k≤a+3 := ⟨hr,ha⟩
  unfold chosenUpperRayWord
  simp only [dif_pos hh]
  exact Classical.choose_spec (by
      obtain ⟨b,hr,hbal⟩ := hr
      obtain ⟨ws,x,y,hws,hchain⟩ := source_high_prefix k a b hr ha
      exact ⟨ws,hws,high_chain_regular (upperRayPhase c) a b
        (upper_ray_initial_phase c a b hbal) hchain,
        ⟨b,x,y,hr,hbal,hchain⟩⟩ :
      ∃ ws:List Move, ws.length=k ∧ Regular (upperRayPhase c) ws ∧
        ∃ b x y, BB429NewResidue.Reach a b ∧ b=2*a+c ∧
          HighChain a b ws x y)

/-- Source-path uniqueness along any fixed offset and length, regardless of
whether c is odd or even. -/
theorem upperRayWord_quot_inj (c k a a':Nat)
    (hr:UpperRayCandidate c a) (hr':UpperRayCandidate c a')
    (ha:16*2^k≤a+3) (ha':16*2^k≤a'+3)
    (hw:chosenUpperRayWord c k a=chosenUpperRayWord c k a')
    (hq:a/(2^k)=a'/(2^k)) : a=a' := by
  obtain ⟨hlen,_,b,x,y,_,hbal,hchain⟩ := chosenUpperRayWord_spec c k a hr ha
  obtain ⟨hlen',_,b',x',y',_,hbal',hchain'⟩ := chosenUpperRayWord_spec c k a' hr' ha'
  have hc2 : HighChain a' b' (chosenUpperRayWord c k a) x' y' := by
    rw [hw]; exact hchain'
  have hmod : a%(2^k)=a'%(2^k) := by
    by_cases hh:a'≤a
    · have ht := upper_same_word_unique c a b a' b' hbal hbal' hh hchain hc2
      exact congruence_of_dvd_sub (2^k) a a' hh (by simpa [hlen] using ht)
    · have hh':a≤a' := by omega
      have ht := upper_same_word_unique c a' b' a b hbal' hbal hh' hc2 hchain
      exact (congruence_of_dvd_sub (2^k) a' a hh' (by simpa [hlen] using ht)).symm
  exact divmod_unique (2^k) a a' hmod hq

/-- Uniform original-source dyadic-shell square-root bound on every
fixed affine diagonal ray, *including* even offsets c. -/
theorem upper_ray_dyadic_shell_bound (c k:Nat)
    (l:List Nat) (hn:l.Nodup)
    (hl:∀a, a∈l → 16*2^k≤a ∧ a<32*2^k ∧ UpperRayCandidate c a) :
    l.length ≤ 64*2^(k/2) := by
  classical
  let f : Nat → List Move × Nat := fun a => (chosenUpperRayWord c k a, a/(2^k))
  have hinj : ∀ a, a∈l → ∀ a', a'∈l → f a=f a' → a=a' := by
    intro a ha a' ha' he
    obtain ⟨ha0,ha1,ha2⟩ := hl a ha
    obtain ⟨ha0',ha1',ha2'⟩ := hl a' ha'
    have hword : chosenUpperRayWord c k a=chosenUpperRayWord c k a' :=
      congrArg Prod.fst he
    have hquot : a/(2^k)=a'/(2^k) := congrArg Prod.snd he
    exact upperRayWord_quot_inj c k a a' ha2 ha2'
      (by omega) (by omega) hword hquot
  have hnodup : (l.map f).Nodup := nodup_map_inj_on l f hn hinj
  have hsub : (l.map f) ⊆
      (allWords (upperRayPhase c) k).flatMap
        (fun ws => (List.range 32).map (fun q => (ws,q))) := by
    intro z hz
    obtain ⟨a,ha,hz⟩ := List.mem_map.mp hz
    subst z
    obtain ⟨ha0,ha1,ha2⟩ := hl a ha
    obtain ⟨hwlen,hwreg,_⟩ :=
      chosenUpperRayWord_spec c k a ha2 (by omega)
    apply List.mem_flatMap.mpr
    refine ⟨chosenUpperRayWord c k a, ?_, ?_⟩
    · simpa [hwlen] using regular_mem_allWords (upperRayPhase c) hwreg
    · apply List.mem_map.mpr
      have hp : 0<2^k := Nat.two_pow_pos k
      have hq : a/(2^k)<32 :=
        (Nat.div_lt_iff_lt_mul hp).mpr (by simpa [Nat.mul_comm] using ha1)
      exact ⟨a/(2^k),List.mem_range.mpr hq,rfl⟩
  have hh := List.Nodup.length_le_of_subset hnodup hsub
  rw [List.length_map, rectangle_list_count] at hh
  have hb := allWords_universal_bound (upperRayPhase c) k
  omega

/-- Uniform O(sqrt N) bound for the intersection of the original blank-root
accelerator with any fixed (even or odd) nonnegative-offset diagonal ray,
with a globally bounded first counter rather than one isolated shell. -/
theorem upper_ray_global_dyadic_bound (c m:Nat)
    (l:List Nat) (hn:l.Nodup)
    (hl:∀a, a∈l → a<32*4^m ∧ UpperRayCandidate c a) :
    l.length ≤ 256*2^m := by
  induction m generalizing l with
  | zero =>
      have hsub:l ⊆ List.range 32 := by
        intro a ha
        have hh := (hl a ha).1
        simp at hh
        exact List.mem_range.mpr hh
      have hh:=List.Nodup.length_le_of_subset hn hsub
      simp at hh ⊢
      omega
  | succ m ih =>
      let cut1 := 32*4^m
      let cut2 := 64*4^m
      let lo := l.filter (fun a => decide (a<cut1))
      let rest := l.filter (fun a => decide (cut1≤a))
      let mid := rest.filter (fun a => decide (a<cut2))
      let hi := rest.filter (fun a => decide (cut2≤a))
      have hsize1 : l.length = lo.length+rest.length :=
        filter_cut_partition l cut1
      have hsize2 : rest.length = mid.length+hi.length :=
        filter_cut_partition rest cut2
      have hnlo : lo.Nodup := (List.filter_sublist).nodup hn
      have hnrest : rest.Nodup := (List.filter_sublist).nodup hn
      have hnmid : mid.Nodup := (List.filter_sublist).nodup hnrest
      have hnhi : hi.Nodup := (List.filter_sublist).nodup hnrest
      have hlo (a:Nat) (ha:a∈lo) : a∈l ∧ a<cut1 := by
        simp only [lo,List.mem_filter] at ha
        exact ⟨ha.1,(decide_eq_true_eq.mp ha.2)⟩
      have hrest (a:Nat) (ha:a∈rest) : a∈l ∧ cut1≤a := by
        simp only [rest,List.mem_filter] at ha
        exact ⟨ha.1,(decide_eq_true_eq.mp ha.2)⟩
      have hmid (a:Nat) (ha:a∈mid) : a∈l ∧ cut1≤a ∧ a<cut2 := by
        simp only [mid,List.mem_filter] at ha
        have hh:=hrest a ha.1
        exact ⟨hh.1,hh.2,decide_eq_true_eq.mp ha.2⟩
      have hhi (a:Nat) (ha:a∈hi) : a∈l ∧ cut2≤a := by
        simp only [hi,List.mem_filter] at ha
        have hh:=hrest a ha.1
        exact ⟨hh.1,decide_eq_true_eq.mp ha.2⟩
      have hlow : lo.length ≤256*2^m := by
        apply ih lo hnlo
        intro a ha
        obtain ⟨hal,hlt⟩:=hlo a ha
        exact ⟨hlt,(hl a hal).2⟩
      have hpow := two_shell_powers m
      have hlim := next_global_limit m
      have hmiddle : mid.length≤64*2^((2*m+1)/2) := by
        apply upper_ray_dyadic_shell_bound c (2*m+1) mid hnmid
        intro a ha
        obtain ⟨hal,ha0,ha1⟩ := hmid a ha
        refine ⟨?_,?_,(hl a hal).2⟩
        · rw [hpow.1]; exact ha0
        · rw [hpow.2.1]; exact ha1
      have hhigh : hi.length≤64*2^((2*m+2)/2) := by
        apply upper_ray_dyadic_shell_bound c (2*m+2) hi hnhi
        intro a ha
        obtain ⟨hal,ha0⟩ := hhi a ha
        refine ⟨?_,?_,(hl a hal).2⟩
        · rw [hpow.2.2.1]; exact ha0
        · rw [hpow.2.2.2]; simpa only [hlim] using (hl a hal).1
      have hm1:(2*m+1)/2=m := by omega
      have hm2:(2*m+2)/2=m+1 := by omega
      rw [hm1] at hmiddle
      rw [hm2, Nat.pow_succ] at hhigh
      rw [Nat.pow_succ]
      omega

#print axioms upper_ray_global_dyadic_bound
#print axioms upper_ray_dyadic_shell_bound
end BB429InverseWord
