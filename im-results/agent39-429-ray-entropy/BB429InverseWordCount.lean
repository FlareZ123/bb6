import BB429InverseWordLang
import Lean.Elab.Tactic.Omega

namespace BB429InverseWord

theorem allWords_len0 (k:Nat) : (allWords 0 k).length = 2^(k/2) := by
  have hh := allWords_length_even (k/2) 0 (by decide)
  rcases hh with ⟨he,ho⟩
  have hk : k = 2*(k/2) ∨ k = 2*(k/2)+1 := by omega
  rcases hk with h|h
  · rw [h]
    have hdiv : (2*(k/2))/2 = k/2 := by omega
    simpa [hdiv] using he
  · rw [h]
    have hdiv : (2*(k/2)+1)/2 = k/2 := by omega
    simpa [hdiv] using ho

theorem nodup_map_inj_on {α β : Type} (l:List α) (f:α→β)
    (h:l.Nodup)
    (hinj:∀ a∈l,∀ b∈l, f a = f b → a=b) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a as ih =>
      obtain ⟨hnot,hnodup⟩ := List.nodup_cons.mp h
      apply List.nodup_cons.mpr
      constructor
      · intro hm
        obtain ⟨b,hb,heq⟩ := List.mem_map.mp hm
        have hab : a = b := hinj a (by simp) b (by simp [hb]) heq.symm
        exact hnot (hab ▸ hb)
      · apply ih hnodup
        intro x hx y hy hxy
        exact hinj x (by simp [hx]) y (by simp [hy]) hxy

/-- An arbitrary finite set of distinct legal parameters injects into the
exact length-k regular inverse-word list if each parameter selects a unique
word. This is the reusable nontrivial finite pigeonhole bridge. -/
theorem abstract_cardinality_bound (k:Nat) (l:List Nat) (f:Nat→List Move)
    (huniq:l.Nodup)
    (hlegal:∀ u∈l, Regular 0 (f u) ∧ (f u).length=k)
    (hinj:∀ u∈l,∀ v∈l, f u=f v → u=v) :
    l.length ≤ 2^(k/2) := by
  have hn : (l.map f).Nodup := nodup_map_inj_on l f huniq hinj
  have hsub : (l.map f) ⊆ allWords 0 k := by
    intro w hw
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hw
    obtain ⟨hr,hlen⟩ := hlegal u hu
    simpa [hlen] using regular_mem_allWords 0 hr
  have hh := List.Nodup.length_le_of_subset hn hsub
  rw [List.length_map,allWords_len0] at hh
  exact hh

/-- Exponential q0 seed growth dominates its affine correction uniformly. -/
theorem q0_linear_below_power (u:Nat) : 24*u+19 ≤ 2^(23+32*u) := by
  induction u with
  | zero => decide
  | succ u ih =>
      have hh : 23+32*(u+1)=(23+32*u)+32 := by omega
      have he : 2^(23+32*(u+1)) = (2^(23+32*u))*4294967296 := by
        rw [hh, Nat.pow_add]
      have hp : 0<2^(23+32*u) := Nat.two_pow_pos _
      rw [he]
      omega

/-- A parameter at least k gives a source-reachable first counter high enough
for k genuine inverse steps, provided it satisfies the exact q0 equation. -/
theorem q0_high (k u a : Nat)
    (huk:k≤u)
    (heq:a+24*u+19=13*2^(23+32*u)) :
    16*2^k ≤ a+3 := by
  have hb : 24*u+19 ≤ 2^(23+32*u) := q0_linear_below_power u
  have hk : k+1≤23+32*u := by omega
  have hpow : 2^(k+1) ≤2^(23+32*u) := Nat.pow_le_pow_right (by decide) hk
  have h2 : 2^(k+1) = 2*2^k := by rw [Nat.pow_succ]; omega
  omega

/-- Equality of first-counter residues and two q0 power equations transfers to
the linear parameter correction 24u, without any subtraction underflow. -/
theorem affine_correction_mod (M u v a a' : Nat)
    (h1 : M ∣ a+24*u+19)
    (h2 : M ∣ a'+24*v+19)
    (hm : a%M=a'%M) : (24*u)%M=(24*v)%M := by
  obtain ⟨p,hp⟩ := h1
  obtain ⟨q,hq⟩ := h2
  obtain ⟨r,s,hr⟩ := Nat.mod_eq_mod_iff.mp hm
  apply Nat.mod_eq_mod_iff.mpr
  refine ⟨q+s,p+r,?_⟩
  simp only [Nat.add_mul, Nat.mul_comm M] at *
  omega

/-- Cancel a multiplicative factor coprime to the modulus, using no
nonstandard number-theory library. -/
theorem coprime_mod_cancel (M c x y : Nat) (hc:M.Coprime c)
    (hm:(c*x)%M=(c*y)%M) : x%M=y%M := by
  by_cases hxy : y≤x
  · obtain ⟨r,s,heq⟩ := Nat.mod_eq_mod_iff.mp hm
    have hcmp : c*y≤c*x := Nat.mul_le_mul_left c hxy
    have hsub : c*x-c*y = s*M-r*M := by omega
    have hdvd : M ∣ c*(x-y) := by
      rw [Nat.mul_sub_left_distrib, hsub]
      exact Nat.dvd_sub (⟨s,Nat.mul_comm s M⟩) (⟨r,Nat.mul_comm r M⟩)
    obtain ⟨t,ht⟩ := hc.dvd_of_dvd_mul_left hdvd
    have heqxy : x=y+M*t := by omega
    rw [heqxy]
    simp [Nat.add_mod, Nat.mul_mod]
  · have hyx : x≤y := by omega
    obtain ⟨r,s,heq⟩ := Nat.mod_eq_mod_iff.mp hm.symm
    have hcmp : c*x≤c*y := Nat.mul_le_mul_left c hyx
    have hsub : c*y-c*x = s*M-r*M := by omega
    have hdvd : M ∣ c*(y-x) := by
      rw [Nat.mul_sub_left_distrib, hsub]
      exact Nat.dvd_sub (⟨s,Nat.mul_comm s M⟩) (⟨r,Nat.mul_comm r M⟩)
    obtain ⟨t,ht⟩ := hc.dvd_of_dvd_mul_left hdvd
    have heqxy : y=x+M*t := by omega
    rw [heqxy]
    simp [Nat.add_mod, Nat.mul_mod]

/-- The factor 8 in 24 cancels three binary modulus bits. -/
theorem reduce_mod24_pow2 (k u v : Nat) (hk:3≤k)
    (hm:(24*u)%(2^k)=(24*v)%(2^k)) :
    (3*u)%(2^(k-3))=(3*v)%(2^(k-3)) := by
  have hpow : 2^k=8*2^(k-3) := by
    calc
      2^k = 2^(3+(k-3)) := by congr 1; omega
      _ = 2^3*2^(k-3) := Nat.pow_add _ _ _
      _ = 8*2^(k-3) := by simp
  obtain ⟨r,s,heq⟩ := Nat.mod_eq_mod_iff.mp hm
  apply Nat.mod_eq_mod_iff.mpr
  refine ⟨r,s,?_⟩
  have he : 8*(3*u+r*2^(k-3)) = 8*(3*v+s*2^(k-3)) := by
    calc
      8*(3*u+r*2^(k-3)) = 24*u + r*(2^k) := by
        rw [hpow]
        simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]
      _ = 24*v + s*(2^k) := heq
      _ = 8*(3*v+s*2^(k-3)) := by
        rw [hpow]
        simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]
  omega

/-- Consequently the 24-linear parameter correction is injective below one
period 2^(k-3) whenever its values agree modulo 2^k. -/
theorem residue24_inj (k u v X:Nat) (hk:3≤k) (hX:X≤2^(k-3))
    (hu:u<X) (hv:v<X)
    (hm:(24*u)%(2^k)=(24*v)%(2^k)) : u=v := by
  have h3 : Nat.Coprime (2^(k-3)) 3 :=
    ((odd_coprime_two 3 (by decide)).pow_left (k-3))
  have hh := coprime_mod_cancel (2^(k-3)) 3 u v h3 (reduce_mod24_pow2 k u v hk hm)
  by_cases huv : u≤v
  · have he : v%(2^(k-3))=v := Nat.mod_eq_of_lt (by omega)
    have he' : u%(2^(k-3))=u := Nat.mod_eq_of_lt (by omega)
    omega
  · have he : v%(2^(k-3))=v := Nat.mod_eq_of_lt (by omega)
    have he' : u%(2^(k-3))=u := Nat.mod_eq_of_lt (by omega)
    omega

/-- Translate divisibility of a nonnegative difference to residue equality. -/
theorem congruence_of_dvd_sub (M a a' : Nat) (haa:a'≤a)
    (hdiv:M∣a-a') : a%M=a'%M := by
  obtain ⟨t,ht⟩ := hdiv
  have he:a=a'+M*t := by omega
  rw [he]
  simp [Nat.add_mod]

/-- Every exponent at least k makes the affine q0 seed equation zero mod 2^k. -/
theorem q0_power_divisibility (k u a:Nat) (hku:k≤23+32*u)
    (heq:a+24*u+19=13*2^(23+32*u)) :
    2^k ∣ a+24*u+19 := by
  have hp : 2^k ∣ 2^(23+32*u) := Nat.pow_dvd_pow 2 hku
  obtain ⟨t,ht⟩ := hp
  refine ⟨13*t,?_⟩
  calc
    a+24*u+19 = 13*2^(23+32*u) := heq
    _ = 13*(2^k*t) := by rw [ht]
    _ = 2^k*(13*t) := by ac_rfl

/-- Two high q0 source paths using exactly the same length-k inverse labels
have identical parameter values inside a shorter-than-period interval. -/
theorem q0_same_word_inj
    (k X u v a b a' b' : Nat)
    (hk:3≤k) (hX:X≤2^(k-3))
    (huk:k≤u) (hvk:k≤v)
    (huX:u<X) (hvX:v<X)
    (hbal:b+13=2*a) (hbal':b'+13=2*a')
    (heq:a+24*u+19=13*2^(23+32*u))
    (heq':a'+24*v+19=13*2^(23+32*v))
    {ws : List Move} {x y x' y' : Nat}
    (hws:ws.length=k)
    (h1:HighChain a b ws x y)
    (h2:HighChain a' b' ws x' y') : u=v := by
  have hmod : a%(2^k)=a'%(2^k) := by
    by_cases haa:a'≤a
    · have ht : 2^ws.length ∣ a-a' :=
        original_same_word_unique 13 a b a' b' hbal hbal' haa h1 h2
      exact congruence_of_dvd_sub (2^k) a a' haa (by simpa [hws] using ht)
    · have haa':a≤a' := by omega
      have ht : 2^ws.length ∣ a'-a :=
        original_same_word_unique 13 a' b' a b hbal' hbal haa' h2 h1
      exact (congruence_of_dvd_sub (2^k) a' a haa' (by simpa [hws] using ht)).symm
  have hu0 : 2^k ∣ a+24*u+19 :=
    q0_power_divisibility k u a (by omega) heq
  have hv0 : 2^k ∣ a'+24*v+19 :=
    q0_power_divisibility k v a' (by omega) heq'
  have hm := affine_correction_mod (2^k) u v a a' hu0 hv0 hmod
  exact residue24_inj k u v X hk hX huX hvX hm

/-- Source-connected q0 parameter candidate. The exponential affine equation
is written without truncated Nat subtraction. -/
def Q0Candidate (u:Nat) : Prop :=
  ∃ a b, BB429NewResidue.Reach a b ∧ b+13=2*a ∧
    a+24*u+19=13*2^(23+32*u)

/-- Each sufficiently large genuine candidate possesses an exact regular
high-output reverse word; all existential details remain inside Prop. -/
theorem q0_has_word (k u:Nat) (hku:k≤u) (h:Q0Candidate u) :
    ∃ ws:List Move, ws.length=k ∧ Regular 0 ws ∧
      ∃ a b x y,
        BB429NewResidue.Reach a b ∧ b+13=2*a ∧
        a+24*u+19=13*2^(23+32*u) ∧
        HighChain a b ws x y := by
  obtain ⟨a,b,hr,hbal,heq⟩ := h
  obtain ⟨ws,x,y,hlen,hchain⟩ := source_high_prefix k a b hr (q0_high k u a hku heq)
  exact ⟨ws, hlen, root_ray_regular a b hbal hchain,
    ⟨a,b,x,y,hr,hbal,heq,hchain⟩⟩

noncomputable def chosenQ0Word (k u:Nat) : List Move := by
  classical
  exact if h : k≤u ∧ Q0Candidate u then
    Classical.choose (q0_has_word k u h.1 h.2)
  else []

theorem chosenQ0Word_spec (k u:Nat) (hku:k≤u) (h:Q0Candidate u) :
    (chosenQ0Word k u).length=k ∧ Regular 0 (chosenQ0Word k u) ∧
      ∃ a b x y,
        BB429NewResidue.Reach a b ∧ b+13=2*a ∧
        a+24*u+19=13*2^(23+32*u) ∧
        HighChain a b (chosenQ0Word k u) x y := by
  have hh : k≤u ∧ Q0Candidate u := ⟨hku,h⟩
  unfold chosenQ0Word
  simp only [dif_pos hh]
  exact Classical.choose_spec (q0_has_word k u hku h)

/-- If two candidates below X select the same inverse word, they are equal. -/
theorem chosenQ0Word_inj (k X u v:Nat)
    (hk:3≤k) (hX:X≤2^(k-3))
    (hku:k≤u) (hkv:k≤v) (huX:u<X) (hvX:v<X)
    (hu:Q0Candidate u) (hv:Q0Candidate v)
    (hword:chosenQ0Word k u = chosenQ0Word k v) : u=v := by
  obtain ⟨hkl,hr, a,b,x,y,hrun,hbal,heq,hchain⟩ := chosenQ0Word_spec k u hku hu
  obtain ⟨hkl',hr',a',b',x',y',hrun',hbal',heq',hchain'⟩ := chosenQ0Word_spec k v hkv hv
  have hchainv : HighChain a' b' (chosenQ0Word k u) x' y' := by
    rw [hword]
    exact hchain'
  exact q0_same_word_inj k X u v a b a' b' hk hX hku hkv huX hvX
    hbal hbal' heq heq' hkl hchain hchainv

theorem filter_cut_partition (l:List Nat) (k:Nat) :
    l.length = (l.filter (fun u => decide (u<k))).length +
      (l.filter (fun u => decide (k≤u))).length := by
  induction l with
  | nil => simp
  | cons a as ih =>
      by_cases h : a<k
      · have hn : ¬ k≤a := by omega
        simp [h, hn]
        omega
      · have hp : k≤a := by omega
        simp [h, hp]
        omega

/-- At most k exceptional short-parameter candidates and at most 2^(k/2)
long candidates can occur in any finite list below 2^(k-3). -/
theorem q0_candidate_cardinality_bound (X k:Nat)
    (hk:3≤k) (hX:X≤2^(k-3))
    (l:List Nat) (hn:l.Nodup)
    (hl:∀u, u∈l → u<X ∧ Q0Candidate u) :
    l.length ≤ k + 2^(k/2) := by
  classical
  let small := l.filter (fun u => decide (u<k))
  let large := l.filter (fun u => decide (k≤u))
  have hsplit : l.length = small.length+large.length :=
    filter_cut_partition l k
  have hns : small.Nodup := (List.filter_sublist).nodup hn
  have hnl : large.Nodup := (List.filter_sublist).nodup hn
  have hs : small.length ≤ k := by
    have hss : ∀ u, u∈small → u ∈ List.range k := by
      intro u hu
      simp only [small, List.mem_filter] at hu
      exact List.mem_range.mpr ((decide_eq_true_eq.mp hu.2))
    have h := hns.length_le_of_subset hss
    simpa only [List.length_range] using h
  have hm (u:Nat) (hu:u∈large) : u∈l ∧ k≤u := by
    simp only [large, List.mem_filter] at hu
    exact ⟨hu.1,(decide_eq_true_eq.mp hu.2)⟩
  have hlegal : ∀ u, u∈large →
      Regular 0 (chosenQ0Word k u) ∧ (chosenQ0Word k u).length=k := by
    intro u hu
    obtain ⟨hul,hku⟩ := hm u hu
    obtain ⟨_,hreg,_⟩ := chosenQ0Word_spec k u hku (hl u hul).2
    obtain ⟨hlen,_,_⟩ := chosenQ0Word_spec k u hku (hl u hul).2
    exact ⟨hreg,hlen⟩
  have hinj : ∀ u, u∈large → ∀ v, v∈large →
      chosenQ0Word k u = chosenQ0Word k v → u=v := by
    intro u hu v hv he
    obtain ⟨hlu,hku⟩ := hm u hu
    obtain ⟨hlv,hkv⟩ := hm v hv
    obtain ⟨huX,hup⟩ := hl u hlu
    obtain ⟨hvX,hvp⟩ := hl v hlv
    exact chosenQ0Word_inj k X u v hk hX hku hkv huX hvX hup hvp he
  have hb : large.length ≤ 2^(k/2) :=
    abstract_cardinality_bound k large (chosenQ0Word k) hnl hlegal hinj
  omega

#print axioms q0_candidate_cardinality_bound
#print axioms chosenQ0Word_inj
#print axioms q0_same_word_inj
#print axioms reduce_mod24_pow2
#print axioms residue24_inj
#print axioms coprime_mod_cancel
#print axioms affine_correction_mod
#print axioms q0_linear_below_power
#print axioms q0_high
#print axioms allWords_len0
#print axioms abstract_cardinality_bound
end BB429InverseWord
