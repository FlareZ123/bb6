import BatchCarry
namespace BB6.Agent9BatchCarry

/-- Reconstruct the unique ancestor at clock q of a terminal carry k
clocks later. Legality is certified separately by Walk. -/
def rewind (q : Nat) : Nat → Nat → Nat
  | 0, z => z
  | k+1, z => (2*rewind (q+1) k z)%q

theorem walk_rewind {q c k z : Nat} (h : Walk q c k z) : rewind q k z=c := by
  induction h with
  | nil q c _ => rfl
  | cons q c z k y he _ ih =>
    rw [rewind,ih,← (edge_iff_parent q c z he.2.1).mp he |>.2]

theorem walk_end {q c k z : Nat} (h : Walk q c k z) : Interior (q+k) z := by
  induction h with
  | nil q c hi => simpa using hi
  | cons q c z k y he _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih

theorem walk_split {q c k z : Nat} (h : Walk q c k z) (a : Nat) (ha : a≤k) :
    ∃ y, Walk q c a y ∧ Walk (q+a) y (k-a) z := by
  induction h generalizing a with
  | nil q c hi =>
    have ha' : a=0 := by omega
    subst a
    exact ⟨c,Walk.nil q c hi,by simpa using Walk.nil q c hi⟩
  | cons q c z k y he tail ih =>
    cases a with
    | zero => exact ⟨c,Walk.nil q c he.1,by simpa using Walk.cons q c z k y he tail⟩
    | succ a =>
      obtain ⟨w,h1,h2⟩ := ih a (by omega)
      exact ⟨w,Walk.cons q c z a w he h1,by simpa [show q+1+a=q+(a+1) by omega] using h2⟩

def center (q : Nat) : Nat := (q-2)/2

/-- A center at an even clock is a genuine birth of the strict-interior
forest. It has no legal predecessor at the preceding clock. -/
theorem center_no_parent (q c : Nat) (hq : 4≤q) (he : q%2=0) :
    ¬ Edge (q-1) c (center q) := by
  intro h
  have hp := (edge_iff_parent (q-1) c (center q) h.2.1).mp h
  have hcenter : 2*center q=q-2 := by unfold center; omega
  rw [hcenter,Nat.mod_eq_of_lt (by omega : q-2<q-1)] at hp
  unfold Interior at hp
  omega

/-- Distinct even-clock central births cannot share a terminal carry. -/
theorem center_disjoint (q p F z : Nat) (hq : 4≤q) (hp : 4≤p)
    (heq : q%2=0) (hep : p%2=0) (hqF : q≤F) (hpF : p≤F)
    (h₁ : Walk q (center q) (F-q) z) (h₂ : Walk p (center p) (F-p) z) : q=p := by
  have no_earlier (a b : Nat) (ha : 4≤a) (hb : 4≤b) (heb : b%2=0)
      (hab : a<b) (hbF : b≤F)
      (hA : Walk a (center a) (F-a) z) (hB : Walk b (center b) (F-b) z) : False := by
    obtain ⟨y,hy,hs⟩ := walk_split hA (b-a-1) (by omega)
    have hclock : a+(b-a-1)=b-1 := by omega
    have hlen : F-a-(b-a-1)=F-b+1 := by omega
    rw [hclock,hlen] at hs
    cases hs with
    | cons _ _ v _ _ hedge tail =>
      have htail : Walk b v (F-b) z := by simpa [show b-1+1=b by omega] using tail
      have hv : v=center b := (walk_rewind htail).symm.trans (walk_rewind hB)
      subst v
      exact center_no_parent b y hb heb hedge
  rcases Nat.lt_trichotomy q p with hlt|he|hgt
  · exact False.elim (no_earlier q p hq hp hep hlt hpF h₁ h₂)
  · exact he
  · exact False.elim (no_earlier p q hp hq heq hgt hqF h₂ h₁)

/-- All Boolean words of a specified length, without multiplicity. -/
def words : Nat → List (List Bool)
  | 0 => [[]]
  | k+1 => (words k).map (false::·) ++ (words k).map (true::·)

theorem mem_words (k : Nat) (xs : List Bool) : xs∈words k ↔ xs.length=k := by
  induction k generalizing xs with
  | zero => simp [words]
  | succ k ih =>
    cases xs with
    | nil => simp [words]
    | cons b bs => cases b <;> simp [words,ih]

theorem words_nodup (k : Nat) : (words k).Nodup := by
  induction k with
  | zero => simp [words]
  | succ k ih =>
    rw [List.nodup_iff_pairwise_ne] at ih
    rw [words,List.nodup_append]
    refine ⟨?_,?_,?_⟩
    · change List.Pairwise (· ≠ ·) ((words k).map (false::·))
      rw [List.pairwise_map]; simpa using ih
    · change List.Pairwise (· ≠ ·) ((words k).map (true::·))
      rw [List.pairwise_map]; simpa using ih
    · rintro _ h _ h'
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp h
      obtain ⟨y,_,rfl⟩ := List.mem_map.mp h'
      simp

def validWords (q c k : Nat) : List (List Bool) :=
  (words k).filter fun xs => decide ((c+weightSum q xs)%2^k=0)

def endOf (q c : Nat) (xs : List Bool) : Nat :=
  (c+weightSum q xs)/2^xs.length

theorem valid_end_walk (q c k : Nat) (hi : Interior q c) (xs : List Bool)
    (hx : xs∈validWords q c k) : Walk q c k (endOf q c xs) := by
  obtain ⟨hm,hdiv⟩ := List.mem_filter.mp hx
  have hlen := (mem_words k xs).mp hm
  have hzero : (c+weightSum q xs)%2^k=0 := of_decide_eq_true hdiv
  have h := Nat.mod_add_div (c+weightSum q xs) (2^k)
  rw [hzero,Nat.zero_add] at h
  unfold endOf
  rw [hlen]
  exact hlen ▸ walk_of_weight q c xs _ hi (by rw [hlen]; exact h.symm)

/-- A terminal endpoint determines the entire weighted word, not just its
start. This uses the exact reverse map, not a bound on the word size. -/
theorem weight_word_unique (q c z : Nat) (xs ys : List Bool) (hi : Interior q c)
    (hlen : xs.length=ys.length)
    (hx : c+weightSum q xs=2^xs.length*z)
    (hy : c+weightSum q ys=2^ys.length*z) : xs=ys := by
  induction xs generalizing q c ys with
  | nil => exact (List.length_eq_zero_iff.mp hlen.symm).symm
  | cons b bs ih =>
    cases ys with
    | nil => simp at hlen
    | cons a as =>
      have hlen' : bs.length=as.length := by simpa using hlen
      let v := (c+(if b then q else 0))/2
      let w := (c+(if a then q else 0))/2
      have hv : 2*v=c+(if b then q else 0) := by
        simp only [weightSum,List.length_cons,Nat.pow_succ] at hx
        have he : (2^bs.length*2)*z=2*(2^bs.length*z) := by ac_rfl
        rw [he] at hx
        dsimp [v]; omega
      have hw : 2*w=c+(if a then q else 0) := by
        simp only [weightSum,List.length_cons,Nat.pow_succ] at hy
        have he : (2^as.length*2)*z=2*(2^as.length*z) := by ac_rfl
        rw [he] at hy
        dsimp [w]; omega
      have hiv : Interior (q+1) v := by
        unfold Interior at hi ⊢; cases b <;> simp at hv <;> omega
      have hiw : Interior (q+1) w := by
        unfold Interior at hi ⊢; cases a <;> simp at hw <;> omega
      have hvx : v+weightSum (q+1) bs=2^bs.length*z := by
        simp only [weightSum,List.length_cons,Nat.pow_succ] at hx
        have he : (2^bs.length*2)*z=2*(2^bs.length*z) := by ac_rfl
        rw [he] at hx; omega
      have hwy : w+weightSum (q+1) as=2^as.length*z := by
        simp only [weightSum,List.length_cons,Nat.pow_succ] at hy
        have he : (2^as.length*2)*z=2*(2^as.length*z) := by ac_rfl
        rw [he] at hy; omega
      have hr₁ := walk_rewind (walk_of_weight (q+1) v bs z hiv hvx)
      have hr₂ := walk_rewind (walk_of_weight (q+1) w as z hiw hwy)
      rw [hlen'] at hr₁
      have heq : v=w := hr₁.symm.trans hr₂
      have hab : b=a := by
        unfold Interior at hi
        rw [heq] at hv
        cases b <;> cases a <;> simp_all <;> omega
      subst a
      rw [← heq] at hwy
      rw [ih (q+1) v as hiv hlen' hvx hwy]

def endpoints (q c k : Nat) : List Nat := (validWords q c k).map (endOf q c)

theorem mem_endpoints (q c k z : Nat) (hi : Interior q c) :
    z∈endpoints q c k ↔ Walk q c k z := by
  constructor
  · intro hm
    obtain ⟨xs,hx,rfl⟩ := List.mem_map.mp hm
    exact valid_end_walk q c k hi xs hx
  · intro hw
    obtain ⟨xs,hx,he⟩ := weight_of_walk hw
    apply List.mem_map.mpr
    refine ⟨xs,?_ ,?_⟩
    · apply List.mem_filter.mpr
      refine ⟨(mem_words k xs).mpr hx,?_⟩
      simp [he]
    · unfold endOf
      rw [hx,he,Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]

theorem endpoints_nodup (q c k : Nat) (hi : Interior q c) : (endpoints q c k).Nodup := by
  unfold endpoints validWords
  change List.Pairwise (· ≠ ·) _
  rw [List.pairwise_map,List.pairwise_filter]
  have hn : (words k).Pairwise (· ≠ ·) := words_nodup k
  apply hn.imp_of_mem
  intro xs ys hxs hys hne hx hy he
  have hlenx := (mem_words k xs).mp hxs
  have hleny := (mem_words k ys).mp hys
  have hxm : (c+weightSum q xs)%2^k=0 := of_decide_eq_true hx
  have hym : (c+weightSum q ys)%2^k=0 := of_decide_eq_true hy
  have hxe := Nat.mod_add_div (c+weightSum q xs) (2^k)
  have hye := Nat.mod_add_div (c+weightSum q ys) (2^k)
  rw [hxm,Nat.zero_add] at hxe
  rw [hym,Nat.zero_add] at hye
  have h1 : c+weightSum q xs=2^xs.length*endOf q c xs := by
    unfold endOf; rw [hlenx]; exact hxe.symm
  have h2 : c+weightSum q ys=2^ys.length*endOf q c xs := by
    rw [he]; unfold endOf; rw [hleny]; exact hye.symm
  exact hne (weight_word_unique q c (endOf q c xs) xs ys hi (by omega) h1 h2)

def centerEnds (F n : Nat) : List Nat := endpoints (n+4) (center (n+4)) (F-(n+4))

def packedEnds (F : Nat) (ns : List Nat) : List Nat := ns.flatMap (centerEnds F)

theorem center_interior (n : Nat) : Interior (n+4) (center (n+4)) := by
  unfold Interior center; omega

theorem centerEnds_nodup (F n : Nat) : (centerEnds F n).Nodup :=
  endpoints_nodup _ _ _ (center_interior n)

theorem centerEnds_mem (F n z : Nat) : z∈centerEnds F n ↔
    Walk (n+4) (center (n+4)) (F-(n+4)) z :=
  mem_endpoints _ _ _ _ (center_interior n)

theorem packedEnds_nodup (F : Nat) (ns : List Nat) (hn : ns.Nodup)
    (h : ∀ n∈ns, n+4≤F ∧ n%2=0) : (packedEnds F ns).Nodup := by
  induction ns with
  | nil => simp [packedEnds]
  | cons n ns ih =>
    obtain ⟨hnot,hnd⟩ := List.nodup_cons.mp hn
    have hN := h n (by simp)
    have htail : ∀ m∈ns, m+4≤F ∧ m%2=0 := by
      intro m hm; exact h m (by simp [hm])
    unfold packedEnds at *
    rw [List.flatMap_cons,List.nodup_append]
    refine ⟨centerEnds_nodup F n,ih hnd htail,?_⟩
    intro z hz w hw he
    subst w
    obtain ⟨m,hm,hmz⟩ := List.mem_flatMap.mp hw
    have hM := htail m hm
    have heq := center_disjoint (n+4) (m+4) F z (by omega) (by omega)
      (by omega) (by omega) hN.1 hM.1 ((centerEnds_mem F n z).mp hz) ((centerEnds_mem F m z).mp hmz)
    have hnm : n=m := by omega
    exact hnot (hnm ▸ hm)

/-- Exact endpoint packing: total word multiplicity over arbitrary distinct
central births with the same final clock cannot exceed the number of
terminal interior states. No probabilistic hypothesis or periodic averaging. -/
theorem packedEnds_bound (F : Nat) (ns : List Nat) (hn : ns.Nodup)
    (h : ∀ n∈ns, n+4≤F ∧ n%2=0) :
    (ns.map (fun n => (centerEnds F n).length)).sum≤F-3 := by
  have hnd := packedEnds_nodup F ns hn h
  have hsub : packedEnds F ns ⊆ terminal F := by
    intro z hz
    obtain ⟨n,hn,hz⟩ := List.mem_flatMap.mp hz
    have hc := (h n hn).1
    have hwalk := (centerEnds_mem F n z).mp hz
    have he := walk_end hwalk
    rw [show n+4+(F-(n+4))=F by omega] at he
    exact (mem_terminal F z).mpr he
  have hlen := hnd.length_le_of_subset hsub
  simpa [packedEnds,List.length_flatMap,terminal] using hlen

#print axioms center_no_parent
#print axioms center_disjoint
#print axioms weight_word_unique
#print axioms packedEnds_bound
end BB6.Agent9BatchCarry
