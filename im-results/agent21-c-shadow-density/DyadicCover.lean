import DyadicReach
namespace BB6.Agent21Dyadic

theorem open_congr (s z s' z' : Int) (n : Nat) (hs : P (n+1)∣s'-s) (hz : P n∣z'-z)
    (ho : OpenAt s z n) : OpenAt s' z' n := by
  obtain ⟨q,hq⟩ := hs
  have he : s'-s=2*(P n*q) := by rw [hq,P_add]; change (P n*2)*q=2*(P n*q); ac_rfl
  have htrans (w : List Nat) (h : P n∣z+acc s w) : P n∣z'+acc s' w := by
    have hacc := acc_translate s (s'-s) w (by omega)
    rw [show s+(s'-s)=s' by omega,show (s'-s)/2=P n*q by omega] at hacc
    have hd : P n∣(P n*q)*coeff w := by rw [Int.mul_assoc]; exact Int.dvd_mul_right _ _
    have ht := Int.dvd_add (Int.dvd_add h hz) hd
    rwa [show z+acc s w+(z'-z)+P n*q*coeff w=z'+acc s' w by omega] at ht
  rcases ho with ⟨w,hp,hc,hh⟩|⟨w,r,hr,hp,hc,hh⟩
  · exact Or.inl ⟨w,hp,hc,htrans w hh⟩
  · exact Or.inr ⟨w,r,hr,hp,hc,htrans _ hh⟩

theorem open_weight (a : Affine) (s : Cylinder a) (ho : OpenAt (mass a s.b) (norm a s.b) s.n) :
    0<weight s.pop := by
  rcases ho with ⟨w,hp,hc,hd⟩|⟨w,r,hr,hp,hc,hd⟩
  · have hm : w.reverse∈s.pop.c := by
      apply (s.valid.1 _).mpr
      simpa [Cspec,rpos,rcost,rnum,numer] using And.intro hp (And.intro hc hd)
    have hl := List.length_pos_of_mem hm
    unfold weight; omega
  · have hm : (w++[r]).reverse∈s.pop.p := by
      apply (s.valid.2 _).mpr
      refine ⟨⟨r,w.reverse,by simp,hr⟩,?_,?_,?_⟩
      · simpa [rpos] using hp
      · simpa [rcost] using hc
      · simpa [rnum,numer] using hd
    have hl := List.length_pos_of_mem hm
    unfold weight; omega

def leaves {α : Type} (f : α→Bool→α) : Nat→α→List α
  | 0,s => [s]
  | n+1,s => leaves f n (f s false)++leaves f n (f s true)

theorem leaf_count {α : Type} (f : α→Bool→α) (v : α→Nat) (n : Nat) (s : α) :
    ((leaves f n s).filter (fun q=>0<v q)).length=FiniteTree.count f (FiniteTree.live v) n s := by
  induction n generalizing s with
  | zero => simp [leaves,FiniteTree.count,FiniteTree.live]; split <;> simp_all
  | succ n ih => simp [leaves,FiniteTree.count,ih]

theorem run_mem_leaves {α : Type} (f : α→Bool→α) (s : α) (bits : List Bool) :
    runBits f s bits∈leaves f bits.length s := by
  induction bits generalizing s with
  | nil => simp [runBits,leaves]
  | cons e bits ih =>
    cases e <;> simp only [runBits, List.length_cons,leaves,List.mem_append]
    · exact Or.inl (ih _)
    · exact Or.inr (ih _)

theorem affine_mod_open (a : Affine) (h : Admissible a) (t : Int) (n : Nat)
    (ho : OpenAt (mass a t) (norm a t) n) : OpenAt (mass a (t%P n)) (norm a (t%P n)) n := by
  apply open_congr _ _ _ _ n _ _ ho
  · have he := Int.emod_add_mul_ediv t (P n)
    have hσ : 2∣a.sigma := Int.dvd_of_emod_eq_zero (h.1)
    obtain ⟨q,hq⟩ := hσ
    refine ⟨-(q*(t/P n)),?_⟩
    unfold mass
    rw [show a.s+a.sigma*(t%P n)-(a.s+a.sigma*t)=a.sigma*(t%P n-t) by rw [Int.mul_sub]; omega,
      show t%P n-t= -(P n*(t/P n)) by omega,hq,P_add]
    change 2*q* -(P n*(t/P n))=(P n*2)* -(q*(t/P n))
    simp only [Int.mul_neg]; congr 1; ac_rfl
  · have he := Int.emod_add_mul_ediv t (P n)
    refine ⟨-(a.lam*(t/P n)),?_⟩
    unfold norm
    rw [show a.z+a.lam*(t%P n)-(a.z+a.lam*t)=a.lam*(t%P n-t) by rw [Int.mul_sub]; omega,
      show t%P n-t= -(P n*(t/P n)) by omega]
    simp only [Int.mul_neg]; congr 1; ac_rfl

/-- The open cylinders are contained in a uniformly sparse list of residues. -/
theorem sparse_cover (d : Nat) (hd : 0<d) : ∃ n, ∀ (a : Affine), Admissible a →
    ∃ R : List Int, d*R.length≤2^n ∧ ∀ t : Int, OpenAt (mass a t) (norm a t) n → t%P n∈R := by
  obtain ⟨n,hn⟩ := affine_extinction_uniform d hd
  refine ⟨n,?_⟩
  intro a h
  let L := (leaves (next a h) n (root a)).filter (fun s=>0<weight s.pop)
  refine ⟨L.map (fun s=>s.b),?_,?_⟩
  · simpa [L,List.length_map,leaf_count] using hn a h
  · intro t ho
    let b := t%P n
    have hlo : 0≤b := Int.emod_nonneg _ (P_ne _)
    have hhi : b<P n := Int.emod_lt_of_pos _ (P_pos _)
    obtain ⟨bits,hbl,hdepth,hprefix⟩ := chooseBits a h (root a) n b hlo hhi
    let s := runBits (next a h) (root a) bits
    have hsn : s.n=n := by simpa [s,root] using hdepth
    have hsb : s.b=b := by simpa [s,root,P] using hprefix
    have hsopen : OpenAt (mass a s.b) (norm a s.b) s.n := by rw [hsn,hsb]; exact affine_mod_open a h t n ho
    have hweight := open_weight a s hsopen
    have hmem : s∈leaves (next a h) n (root a) := by rw [←hbl]; exact run_mem_leaves _ _ _
    have hL : s∈L := by simp [L,hmem,hweight]
    exact List.mem_map.mpr ⟨s,hL,hsb⟩

#print axioms sparse_cover
end BB6.Agent21Dyadic
