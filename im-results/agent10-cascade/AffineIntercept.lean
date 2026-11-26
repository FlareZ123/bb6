import SeamEntropy
namespace AffineIntercept
set_option maxHeartbeats 0

structure State where
  A : Nat
  J : Nat
  d : Nat
  deriving DecidableEq

def root : State := ⟨0,0,0⟩
def Edge (s t : State) (j a : Nat) : Prop :=
  0<j ∧ s.J=t.J+j ∧ s.A=t.A+a ∧ s.d=2^j*t.d+3^s.A ∧
  (0<t.J → SeamMass.Admissible j a)

inductive Path : State → List (Nat × Nat) → Prop
  | nil : Path root []
  | cons : Edge s t j a → Path t w → Path s ((j,a)::w)

theorem pow3_odd (n : Nat) : 3^n%2=1 := by
  induction n with
  | zero => decide
  | succ n ih => simp [Nat.pow_succ,Nat.mul_mod,ih]

theorem pow2_even {n : Nat} (hn : 0<n) : 2^n%2=0 := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  simp [Nat.pow_succ]

theorem nonempty_shape {s w} (h : Path s w) (hw : w≠[]) : 0<s.J ∧ s.d%2=1 := by
  cases h with
  | nil => contradiction
  | cons he _ =>
    obtain ⟨hj,hJ,_,hd,_⟩ := he
    refine ⟨by omega,?_⟩
    rw [hd]
    simp [Nat.add_mod,Nat.mul_mod,pow2_even hj,pow3_odd]

theorem empty_iff {s w} (h : Path s w) : w=[] ↔ s.d=0 := by
  constructor
  · intro hw
    subst w
    cases h
    rfl
  · intro hd
    by_cases hn : w=[]
    · exact hn
    · have hodd := (nonempty_shape h hn).2
      omega

theorem path_unique {s w v} (hw : Path s w) (hv : Path s v) : w=v := by
  induction hw generalizing v with
  | nil => exact ((empty_iff hv).2 (by rfl)).symm
  | @cons s t j a w he hw ih =>
    cases hv with
    | nil => have h1:=he.1; have h2:=he.2.1; simp [root] at h2; omega
    | @cons _ u k b v ge hv =>
      obtain ⟨hj,hJ,hA,hd,had⟩ := he
      obtain ⟨hk,hK,hB,heq,hbd⟩ := ge
      have eq : 2^j*t.d=2^k*u.d := by omega
      by_cases hw0 : w=[]
      · subst w
        cases hw
        have hzero : u.d=0 := by
          simp [root] at eq
          have hp := Nat.two_pow_pos k
          exact (Nat.mul_eq_zero.mp eq.symm).resolve_left (by omega)
        have hv0 := (empty_iff hv).2 hzero
        subst v
        cases hv
        simp [root] at hJ hA hK hB
        congr 2 <;> omega
      · have hto := nonempty_shape hw hw0
        have hv0 : v≠[] := by
          intro h
          have hzero := (empty_iff hv).1 h
          rw [hzero,Nat.mul_zero] at eq
          have hpos := Nat.mul_pos (Nat.two_pow_pos j) (by omega : 0<t.d)
          omega
        have huo := nonempty_shape hv hv0
        have hjk := SeamMass.odd_pow_two_unique hto.2 huo.2 eq
        subst k
        have hab := SeamMass.exponent_unique (had hto.1) (hbd huo.1)
        subst b
        have hd' := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos j) eq
        have ht : t=u := by cases t; cases u; simp_all
        subst u
        rw [ih hv]

def paddedPrefix (B : Nat) (w : List (Nat × Nat)) : List Bool :=
  (SeamMass.code w.dropLast ++ List.replicate B false).take B

theorem prefix_length (B : Nat) (w : List (Nat × Nat)) : (paddedPrefix B w).length=B := by
  simp [paddedPrefix,List.length_take]

theorem prefix_single (B j a : Nat) : paddedPrefix B [(j,a)]=List.replicate B false := by
  simp [paddedPrefix,SeamMass.code,List.take_replicate]

theorem prefix_cons {B j a : Nat} {w : List (Nat × Nat)} (hw : w≠[]) :
    paddedPrefix B ((j,a)::w) = ((List.replicate (j-1) false ++ [true]) ++
      (SeamMass.code w.dropLast ++ List.replicate B false)).take B := by
  cases w with
  | nil => contradiction
  | cons x xs => simp [paddedPrefix,List.dropLast_cons_cons,SeamMass.code,List.append_assoc]

theorem prefix_one {B j a : Nat} {w} (hw : w≠[]) (hj : 0<j) (hB : j≤B) :
    (paddedPrefix B ((j,a)::w))[j-1]?=some true := by
  rw [prefix_cons hw]
  simp [List.getElem?_take,List.getElem?_append,show j-1<B by omega]

theorem prefix_zero {B j a i : Nat} {w} (hw : w≠[]) (hi : i<j-1) (hB : i<B) :
    (paddedPrefix B ((j,a)::w))[i]?=some false := by
  rw [prefix_cons hw]
  simp [List.getElem?_take,List.getElem?_append,hi,hB,List.getElem?_replicate]

theorem prefix_drop {B j a : Nat} {w} (hw : w≠[]) (hj : 0<j) :
    (paddedPrefix B ((j,a)::w)).drop j = paddedPrefix (B-j) w := by
  rw [prefix_cons hw,List.drop_take]
  have hlen : (List.replicate (j-1) false ++ [true]).length=j := by simp; omega
  have hd : ((List.replicate (j-1) false ++ [true]) ++
      (SeamMass.code w.dropLast ++ List.replicate B false)).drop j =
      SeamMass.code w.dropLast ++ List.replicate B false := by
    exact (congrArg (fun n => ((List.replicate (j-1) false ++ [true]) ++
      (SeamMass.code w.dropLast ++ List.replicate B false)).drop n) hlen).symm.trans List.drop_left
  rw [hd]
  unfold paddedPrefix
  simp only [List.take_append,List.take_replicate]
  congr 2
  omega

/-- A completed noninitial code block in a shared paddedPrefix determines the same
    exponent on the other path, which cannot end at its initial edge. -/
theorem prefix_head {B j a k b : Nat} {w v : List (Nat × Nat)}
    (hw : w≠[]) (hj : 0<j) (hk : 0<k) (hjB : j≤B)
    (he : paddedPrefix B ((j,a)::w)=paddedPrefix B ((k,b)::v)) : v≠[] ∧ j=k := by
  have hv : v≠[] := by
    intro h
    subst v
    have hh := congrArg (fun x : List Bool => x[j-1]?) he
    rw [prefix_one hw hj hjB,prefix_single] at hh
    simp [List.getElem?_replicate,show j-1<B by omega] at hh
  refine ⟨hv,?_⟩
  rcases Nat.lt_trichotomy j k with hlt|heq|hgt
  · have hg := congrArg (fun x : List Bool => x[j-1]?) he
    rw [prefix_one hw hj hjB,prefix_zero hv (by omega : j-1<k-1) (by omega : j-1<B)] at hg
    contradiction
  · exact heq
  · have hg := congrArg (fun x : List Bool => x[k-1]?) he
    rw [prefix_one hv hk (by omega : k≤B),prefix_zero hw (by omega : k-1<j-1) (by omega : k-1<B)] at hg
    contradiction

theorem no_complete_block {s t : State} {j a B : Nat} {w}
    (he : Edge s t j a) (hw : Path t w) (h : w=[] ∨ B<j) :
    s.d%2^(B+1)=3^s.A%2^(B+1) := by
  obtain ⟨_,_,_,hd,_⟩ := he
  rcases h with h|h
  · have ht := (empty_iff hw).1 h
    rw [hd,ht,Nat.mul_zero,Nat.zero_add]
  · have hdiv : 2^(B+1) ∣ 2^j*t.d := Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) (Nat.dvd_mul_right _ _)
    rw [hd,Nat.add_mod,Nat.mod_eq_zero_of_dvd hdiv,Nat.zero_add,Nat.mod_mod]

/-- Padded prefixes determine the affine intercept modulo 2^(B+1). The
    initial edge is coded by an infinite zero tail, since its prior d is zero. -/
theorem prefix_mod {s t w v} (hw : Path s w) (hv : Path t v)
    (hn : w≠[]) (hm : v≠[]) (hA : s.A=t.A) (B : Nat)
    (he : paddedPrefix B w=paddedPrefix B v) : s.d%2^(B+1)=t.d%2^(B+1) := by
  induction hw generalizing t v B with
  | nil => contradiction
  | @cons s u j a w hsu hw ih =>
    cases hv with
    | nil => contradiction
    | @cons t z k b v htz hv =>
      have hj:=hsu.1
      have hk:=htz.1
      by_cases h : w≠[] ∧ j≤B
      · obtain ⟨hv',hjk⟩ := prefix_head h.1 hj hk h.2 he
        subst k
        have hu := (nonempty_shape hw h.1).1
        have hz := (nonempty_shape hv hv').1
        have hab := SeamMass.exponent_unique (hsu.2.2.2.2 hu) (htz.2.2.2.2 hz)
        subst b
        have h1:=hsu.2.2.1
        have h2:=htz.2.2.1
        have hAz : u.A=z.A := by omega
        have htail := congrArg (List.drop j) he
        rw [prefix_drop h.1 hj,prefix_drop hv' hj] at htail
        have hh := ih hv h.1 hv' hAz (B-j) htail
        have ep : B+1=j+(B-j+1) := by omega
        have hd1:=hsu.2.2.2.1
        have hd2:=htz.2.2.2.1
        have hmul : (2^j*u.d)%2^(B+1)=(2^j*z.d)%2^(B+1) := by
          rw [ep,Nat.pow_add,Nat.mul_mod_mul_left,Nat.mul_mod_mul_left,hh]
        rw [hd1,hd2,hA,Nat.add_mod (2^j*u.d),Nat.add_mod (2^j*z.d),hmul]
      · have h1 : w=[] ∨ B<j := by
          by_cases hz : w=[]
          · exact Or.inl hz
          · exact Or.inr (by by_cases hle : j≤B; exact False.elim (h ⟨hz,hle⟩); omega)
        have h2 : v=[] ∨ B<k := by
          by_cases hz : v=[]
          · exact Or.inl hz
          · by_cases hkB : k≤B
            · obtain ⟨hw',heq⟩ := prefix_head hz hk hj hkB he.symm
              exact False.elim (h ⟨hw',by omega⟩)
            · exact Or.inr (by omega)
        rw [no_complete_block hsu hw h1,no_complete_block htz hv h2,hA]

theorem code_dropLast_legal {s w} (h : Path s w) :
    SeamMass.follow .boundary (SeamMass.code w.dropLast)=some .boundary := by
  induction h with
  | nil => rfl
  | @cons s t j a w he hw ih =>
    by_cases h : w=[]
    · subst w; rfl
    · have hpos := (nonempty_shape hw h).1
      have had:=he.2.2.2.2 hpos
      have h2 : j≠2 := by intro e; exact SeamMass.exponent_two_forbidden a (e ▸ had)
      have hj:=he.1
      cases w with
      | nil => contradiction
      | cons x xs =>
        rw [List.dropLast_cons_cons]
        have hc : SeamMass.code ((j,a)::(x::xs).dropLast)=
            (List.replicate (j-1) false ++ [true])++SeamMass.code (x::xs).dropLast := by
          simp [SeamMass.code,List.append_assoc]
        rw [hc,SeamMass.follow_append,SeamMass.block_legal j hj h2]
        exact ih

theorem prefix_mem {s w} (h : Path s w) (B : Nat) : paddedPrefix B w ∈ SeamMass.prefixes B .boundary := by
  have hf : ∃ u, SeamMass.follow .boundary (List.replicate B false)=some u := by
    cases B with
    | zero => exact ⟨.boundary,rfl⟩
    | succ n =>
      cases n with
      | zero => exact ⟨.oneZero,rfl⟩
      | succ m =>
        refine ⟨.manyZeros,?_⟩
        simp only [List.replicate_succ,SeamMass.follow,SeamMass.next,Option.bind_some]
        exact SeamMass.follow_many_zeros m
  obtain ⟨u,hu⟩:=hf
  have hg : SeamMass.follow .boundary (SeamMass.code w.dropLast++List.replicate B false)=some u := by
    rw [SeamMass.follow_append,code_dropLast_legal h]
    exact hu
  obtain ⟨v,hv⟩ := SeamMass.prefix_legal hg B
  exact SeamMass.prefixes_complete (prefix_length B w) hv

#print axioms path_unique
#print axioms prefix_mod
#print axioms prefix_mem

/-- Any interval of 2^(B+1) consecutive integer intercepts contains at most
    one representative of each residue. -/
theorem interval_mod_unique {p q L B : Nat}
    (hp : L≤p ∧ p<L+2^(B+1)) (hq : L≤q ∧ q<L+2^(B+1))
    (hm : p%2^(B+1)=q%2^(B+1)) : p=q := by
  have he : ((p-L)+L)%2^(B+1)=((q-L)+L)%2^(B+1) := by
    rwa [Nat.sub_add_cancel hp.1,Nat.sub_add_cancel hq.1]
  have h := SeamMass.add_mod_cancel he
  rw [Nat.mod_eq_of_lt (by omega : p-L<2^(B+1)),Nat.mod_eq_of_lt (by omega : q-L<2^(B+1))] at h
  omega

def Slice (A J L B : Nat) := {p : State × List (Nat × Nat) //
  Path p.1 p.2 ∧ p.2≠[] ∧ p.1.A=A ∧ p.1.J=J ∧ L≤p.1.d ∧ p.1.d<L+2^(B+1)}

theorem slice_injective {A J L B : Nat} {x y : Slice A J L B}
    (h : paddedPrefix B x.val.2=paddedPrefix B y.val.2) : x=y := by
  obtain ⟨hx,hxn,hxA,hxJ,hxlo,hxhi⟩:=x.property
  obtain ⟨hy,hyn,hyA,hyJ,hylo,hyhi⟩:=y.property
  have hdmod := prefix_mod hx hy hxn hyn (hxA.trans hyA.symm) B h
  have hd := interval_mod_unique ⟨hxlo,hxhi⟩ ⟨hylo,hyhi⟩ hdmod
  have he : x.val.1=y.val.1 := by
    have hA : x.val.1.A=y.val.1.A := hxA.trans hyA.symm
    have hJ : x.val.1.J=y.val.1.J := hxJ.trans hyJ.symm
    cases ex : x.val.1
    cases ey : y.val.1
    rw [ex,ey] at hA hJ hd
    simp_all
  apply Subtype.ext
  exact Prod.ext he (path_unique (he ▸ hx) hy)

/-- Uniform entropy bound at fixed cumulative A and J for every interval of
    2^(B+1) intercepts, with no dyadic-seed restriction. -/
theorem interval_word_count {A J L B : Nat} (xs : List (Slice A J L B)) (hn : xs.Nodup) :
    xs.length≤(SeamMass.prefixCounts B).1 := by
  let f : Slice A J L B → List Bool := fun x => paddedPrefix B x.val.2
  have hm : (xs.map f).Nodup := by
    apply List.Pairwise.map f _ hn
    intro x y hne he
    exact hne (slice_injective he)
  have hs : xs.map f ⊆ SeamMass.prefixes B .boundary := by
    intro x hx
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hx
    exact prefix_mem p.property.1 B
  have h := hm.length_le_of_subset hs
  rw [List.length_map,(SeamMass.prefix_lengths B).1] at h
  exact h

theorem interval_word_majorant {A J L B : Nat} (xs : List (Slice A J L B)) (hn : xs.Nodup) :
    7*9^B*xs.length≤9*16^B :=
  Nat.le_trans (Nat.mul_le_mul_left (7*9^B) (interval_word_count xs hn)) (SeamMass.prefix_majorant B).1

#print axioms slice_injective
#print axioms interval_word_count
#print axioms interval_word_majorant
end AffineIntercept
