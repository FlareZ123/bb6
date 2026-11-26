import NeedleBatchCore

namespace NeedleAllOrderGrowth
open NeedleTerminalExtension NeedleBatch

 theorem edge_strict {v x y : Nat} (h : Edge v x y) : x<y := by
  obtain ⟨q,hx,hy⟩ := h
  omega

 theorem path_mono {w x y} (h : Path w x y) : x≤y := by
  induction h with
  | nil => omega
  | cons he hp ih => have := edge_strict he; omega

 theorem coeff_odd (w : List Nat) : coeffA w % 2=1 := by
  induction w with
  | nil => decide
  | cons v w ih => simp [coeffA,Nat.mul_mod,ih,den_odd]

 theorem cylinder {w x y x' y'} (h : Path w x y) (h' : Path w x' y')
    (hx : x<x') (hpos : 1≤x) : 2^weight w ∣ x'-x := by
  have h1 := path_affine h
  have h2 := path_affine h'
  have hd1 : 2^weight w ∣ 2^weight w*(y'-1)-2^weight w*(y-1) :=
    Nat.dvd_sub (Nat.dvd_mul_right _ _) (Nat.dvd_mul_right _ _)
  rw [h2,h1,Nat.add_sub_add_right,←Nat.mul_sub_left_distrib] at hd1
  have he : x'-1-(x-1)=x'-x := by omega
  rw [he] at hd1
  have hc : (coeffA w).Coprime 2 := by
    unfold Nat.Coprime
    rw [Nat.gcd_comm,Nat.gcd_rec,coeff_odd]
    decide
  exact (hc.symm.pow_left _).dvd_of_dvd_mul_left hd1

 theorem path_gain_product {w x y} (h : Path w x y) (b G : Nat)
    (hx : b≤x) (hy : y≤b+G) : b^w.length≤G^w.length*2^weight w := by
  induction h with
  | nil => simp [weight]
  | @cons v w x z y he hp ih =>
    have hle := path_mono hp
    have hlt := edge_strict he
    have hz : b≤z := by omega
    have hrest := ih hz hy
    have hsingle : b≤G*2^(v+1) := by
      obtain ⟨q,hxq,hzq⟩ := he
      have hq : 2*q+3≤G := by omega
      have hh : x≤2^v*G := by rw [hxq]; exact Nat.mul_le_mul_left _ hq
      have hd : 2^v*G≤G*2^(v+1) := by rw [Nat.pow_succ]; grind
      omega
    simp only [List.length_cons,weight,Nat.pow_succ G,Nat.pow_succ b,Nat.pow_add]
    calc
      b^w.length*b ≤ (G^w.length*2^weight w)*(G*2^(v+1)) := Nat.mul_le_mul hrest hsingle
      _ = G^w.length*G*(2^(v+1)*2^weight w) := by ac_rfl

 def word (v : Nat→Nat) (i : Nat) : Nat→List Nat
  | 0 => []
  | t+1 => v i :: word v (i+1) t

 theorem word_len (v : Nat→Nat) (i t : Nat) : (word v i t).length=t := by
  induction t generalizing i with
  | zero => rfl
  | succ t ih => simp [word,ih]

 theorem word_path (v b : Nat→Nat) (i t : Nat)
    (h : ∀ j, j<t → Edge (v (i+j)) (b (i+j)) (b (i+j+1))) :
    Path (word v i t) (b i) (b (i+t)) := by
  induction t generalizing i with
  | zero => simpa [word] using Path.nil (b i)
  | succ t ih =>
    have h0 := h 0 (by omega)
    simp at h0
    have hr := ih (i+1) (by
      intro j hj
      have hh := h (j+1) (by omega)
      simpa [Nat.add_assoc,Nat.add_comm 1 j] using hh)
    have he : i+1+t=i+(t+1) := by omega
    rw [he] at hr
    exact Path.cons h0 hr

 def encode (M : Nat) : List Nat→Nat
  | [] => 0
  | x::w => x+M*encode M w

 theorem encode_bound (M : Nat) (w : List Nat) (_hM : 0<M)
    (h : ∀ x∈w, x<M) : encode M w<M^w.length := by
  induction w with
  | nil => simp [encode]
  | cons x w ih =>
    have hx := h x (by simp)
    have hw := ih (by intro y hy; exact h y (by simp [hy]))
    simp only [encode,List.length_cons,Nat.pow_succ]
    have hh := Nat.mul_le_mul_left M (show encode M w+1≤M^w.length by omega)
    rw [Nat.mul_add,Nat.mul_one] at hh
    rw [Nat.mul_comm (M^w.length) M]
    omega

 theorem encode_injective (M : Nat) (w z : List Nat) (hM : 0<M)
    (hlen : w.length=z.length) (hw : ∀ x∈w, x<M) (hz : ∀ x∈z, x<M)
    (he : encode M w=encode M z) : w=z := by
  induction w generalizing z with
  | nil => cases z <;> simp_all
  | cons x w ih =>
    cases z with
    | nil => simp at hlen
    | cons y z =>
      have hx := hw x (by simp)
      have hy := hz y (by simp)
      have he' := congrArg (·%M) he
      simp [encode,Nat.add_mod,Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hy] at he'
      subst y
      simp only [encode,Nat.add_left_cancel_iff] at he
      have hr := Nat.eq_of_mul_eq_mul_left hM he
      have hlen' : w.length=z.length := by simpa using hlen
      have h := ih z hlen' (by intro a ha; exact hw a (by simp [ha]))
        (by intro a ha; exact hz a (by simp [ha])) hr
      rw [h]

 theorem word_bound (v : Nat→Nat) (i t M : Nat) (h : ∀ j, j<t → v (i+j)<M) :
    ∀ x∈word v i t, x<M := by
  induction t generalizing i with
  | zero => simp [word]
  | succ t ih =>
    intro x hx
    simp only [word,List.mem_cons] at hx
    rcases hx with rfl | hx
    · simpa using h 0 (by omega)
    · apply ih (i+1) _ x hx
      intro j hj
      have hh := h (j+1) (by omega)
      simpa [Nat.add_assoc,Nat.add_comm 1 j] using hh

 theorem bounded_collision (M : Nat) (f : Nat→Nat) (h : ∀ i, i≤M → f i<M) :
    ∃ i j, i<j ∧ j≤M ∧ f i=f j := by
  classical
  apply Classical.byContradiction
  intro hn
  let l := (List.range (M+1)).map f
  have hn' : ∀ i j, i∈List.range (M+1) → j∈List.range (M+1) → i≠j → f i≠f j := by
    intro i j hi hj hne
    rw [List.mem_range] at hi hj
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · intro he; exact hn ⟨i,j,hlt,by omega,he⟩
    · intro he; exact hn ⟨j,i,hgt,by omega,he.symm⟩
  have hp : l.Nodup := by
    unfold l
    rw [List.nodup_iff_pairwise_ne,List.pairwise_map]
    apply List.Pairwise.imp_of_mem (l:=List.range (M+1)) (R:=fun x y : Nat => x≠y)
    · intro a b ha hb hne; exact hn' a b ha hb hne
    · exact List.nodup_range
  have hs : l⊆List.range M := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    exact List.mem_range.mpr (h i (by have := List.mem_range.mp hi; omega))
  have hl := hp.length_le_of_subset hs
  simp [l] at hl
  omega

 theorem trace_mono (v b : Nat→Nat) (N : Nat)
    (h : ∀ i, i<N → Edge (v i) (b i) (b (i+1)))
    {i j : Nat} (hij : i≤j) (hj : j≤N) : b i≤b j := by
  induction j with
  | zero =>
    have hi : i=0 := by omega
    simp [hi]
  | succ j ih =>
    by_cases he : i=j+1
    · simp [he]
    · have hprev := ih (by omega) (by omega)
      have hstep := edge_strict (h j (by omega))
      omega

 theorem trace_strict (v b : Nat→Nat) (N : Nat)
    (h : ∀ i, i<N → Edge (v i) (b i) (b (i+1)))
    {i j : Nat} (hij : i<j) (hj : j≤N) : b i<b j := by
  have h1 := edge_strict (h i (by omega))
  have h2 := trace_mono v b N h (show i+1≤j by omega) hj
  omega

 def blockLength (M t : Nat) : Nat := M^t+t

 /-- Every sufficiently long block in a bounded valuation alphabet has a
     repeated word, hence a gain of order b^(t/(t+1)). -/
 theorem all_order_gain (v b : Nat→Nat) (M t : Nat) (hM : 0<M) (hb : 0<b 0)
    (h : ∀ i, i<blockLength M t → Edge (v i) (b i) (b (i+1)))
    (hv : ∀ i, i<blockLength M t → v i<M) :
    (b 0)^t ≤ (b (blockLength M t)-b 0)^(t+1) := by
  let N := blockLength M t
  let G := b N-b 0
  have hN : N=M^t+t := rfl
  have hB (i : Nat) (hi : i≤M^t) : ∀ x∈word v i t, x<M := by
    apply word_bound
    intro j hj
    exact hv _ (by omega)
  obtain ⟨i,j,hij,hj,he⟩ := bounded_collision (M^t) (fun i => encode M (word v i t))
    (fun i hi => by simpa [word_len] using encode_bound M (word v i t) hM (hB i hi))
  have hw := encode_injective M (word v i t) (word v j t) hM (by simp [word_len])
    (hB i (by omega)) (hB j hj) he
  have hp : Path (word v i t) (b i) (b (i+t)) := word_path v b i t (fun k hk => h _ (by omega))
  have hq : Path (word v i t) (b j) (b (j+t)) := by
    rw [hw]
    exact word_path v b j t (fun k hk => h _ (by omega))
  have hbi : b 0≤b i := trace_mono v b N h (by omega) (by omega)
  have hbj : b i<b j := trace_strict v b N h hij (by omega)
  have hdvd := cylinder hp hq hbj (by omega)
  have hdiv := Nat.le_of_dvd (show 0<b j-b i by omega) hdvd
  have hjle : b j≤b N := trace_mono v b N h (by omega) (by omega)
  have hpow : 2^weight (word v i t)≤G := by dsimp [G]; omega
  have hile : b (i+t)≤b N := trace_mono v b N h (by omega) (by omega)
  have hgain := path_gain_product hp (b 0) G hbi (by dsimp [G]; omega)
  rw [word_len] at hgain
  change (b 0)^t≤G^(t+1)
  rw [Nat.pow_succ]
  exact Nat.le_trans hgain (Nat.mul_le_mul_left _ hpow)

 theorem gain_fraction (b G R t : Nat) (_hb : 0<b)
    (hg : b^t≤G^(t+1)) (hR : b≤R^(t+1)) : b≤R*G := by
  by_cases h : b≤R*G
  · exact h
  · have ht : 0<t+1 := by omega
    have hlt : (R*G)^(t+1)<b^(t+1) := Nat.pow_lt_pow_left (by omega) (by omega)
    rw [Nat.mul_pow] at hlt
    have hmul := Nat.mul_le_mul hR hg
    rw [Nat.mul_comm b (b^t),←Nat.pow_succ] at hmul
    change b^(t+1)≤R^(t+1)*G^(t+1) at hmul
    omega

 theorem valuation_bound {v x y L : Nat} (he : Edge v x y) (hx : x<2^L) : v<L := by
  obtain ⟨q,hq,hy⟩ := he
  have hb : 2^v≤x := by rw [hq]; have hh:=Nat.mul_le_mul_left (2^v) (show 1≤2*q+3 by omega); simpa using hh
  by_cases h : v<L
  · exact h
  · have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (show L≤v by omega)
    omega

 def fuel (L r t : Nat) : Nat := blockLength L t * 2^r * L

 /-- A finite positive path bounded above by 2^L cannot have this length.
     Choose r=ceil(L/(t+1)) and optimize t for subexponential target fuel. -/
 theorem no_long_bounded_path (v b : Nat→Nat) (L r t : Nat)
    (hL : 0<L) (hr : L≤r*(t+1)) (hb : 0<b 0)
    (h : ∀ i, i<fuel L r t → Edge (v i) (b i) (b (i+1)))
    (hbound : b (fuel L r t)<2^L) : False := by
  let B := blockLength L t
  let R := 2^r
  let N := fuel L r t
  have hN : N=B*R*L := rfl
  change b N<2^L at hbound
  have hRpos : 0<R := Nat.two_pow_pos _
  have hBpos : 0<B := by
    have hh : 0<L^t := Nat.pow_pos hL
    dsimp [B,blockLength]; omega
  have hPow : 2^L≤R^(t+1) := by
    dsimp [R]; rw [←Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) hr
  have hAll (i : Nat) (hi : i≤N) : b i<2^L := by
    have hm := trace_mono v b N h (show i≤N by exact hi) (by omega : N≤N)
    omega
  have hGain (i : Nat) (hi : i+B≤N) : b i≤R*(b (i+B)-b i) := by
    have hsub : ∀ j, j<B → Edge (v (i+j)) (b (i+j)) (b (i+(j+1))) := by
      intro j hj
      have hh := h (i+j) (by omega)
      simpa [Nat.add_assoc] using hh
    have hv : ∀ j, j<B → v (i+j)<L := by
      intro j hj
      exact valuation_bound (hsub j hj) (hAll _ (by omega))
    have hbpos : 0<b i := by
      have hh:=trace_mono v b N h (Nat.zero_le i) (by omega : i≤N)
      omega
    have hg := all_order_gain (fun j=>v (i+j)) (fun j=>b (i+j)) L t hL
      (by simpa using hbpos) hsub hv
    simp only [Nat.add_zero] at hg
    exact gain_fraction (b i) (b (i+B)-b i) R t hbpos hg (Nat.le_trans (Nat.le_of_lt (hAll i (by omega))) hPow)
  have hLinear (i k : Nat) (hi : i+B*k≤N) :
      R*b i+k*b i≤R*b (i+B*k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have he : i+B*(k+1)=i+B*k+B := by rw [Nat.mul_succ]; omega
      rw [he] at hi ⊢
      have hprev := ih (by omega)
      have hgm := hGain (i+B*k) hi
      have hm := trace_mono v b N h (show i≤i+B*k by omega) (by omega : i+B*k≤N)
      have hm2 := trace_mono v b N h (show i+B*k≤i+B*k+B by omega) hi
      have heq : R*(b (i+B*k+B)-b (i+B*k)) = R*b (i+B*k+B)-R*b (i+B*k) := Nat.mul_sub_left_distrib ..
      rw [heq] at hgm
      have hmul := Nat.mul_le_mul_left R hm2
      rw [Nat.succ_mul]
      omega
  have hDouble (i : Nat) (hi : i+B*R≤N) : 2*b i≤b (i+B*R) := by
    have hh:=hLinear i R hi
    have hEq : R*(2*b i)=R*b i+R*b i := by grind
    apply Nat.le_of_mul_le_mul_left (c:=R) _ hRpos
    omega
  have hGrow (k : Nat) (hk : k≤L) : 2^k≤b (B*R*k) := by
    induction k with
    | zero => simp; omega
    | succ k ih =>
      have hprev:=ih (by omega)
      have hidx : B*R*(k+1)=B*R*k+B*R := Nat.mul_succ ..
      have hle : B*R*(k+1)≤N := by rw [hN]; exact Nat.mul_le_mul_left _ hk
      have hh:=hDouble (B*R*k) (by rw [←hidx]; exact hle)
      rw [hidx,Nat.pow_succ]
      omega
  have hh:=hGrow L (Nat.le_refl _)
  rw [←hN] at hh
  omega

def targetBits (d : Nat) : Nat := (d+2).log2+1

def ceilRatio (L t : Nat) : Nat := (L+t)/(t+1)

theorem ceilRatio_bound (L t : Nat) : L≤ceilRatio L t*(t+1) := by
  have h1 := Nat.div_add_mod (L+t) (t+1)
  have h2 := Nat.mod_lt (L+t) (show 0<t+1 by omega)
  rw [Nat.mul_comm (t+1)] at h1
  unfold ceilRatio
  omega

def orderFor (L : Nat) : Nat := (L/(L.log2+1)).sqrt

def targetFuel (d : Nat) : Nat :=
  let L := targetBits d
  let t := orderFor L
  fuel L (ceilRatio L t) t

 theorem prefix_target_fuel (v b : Nat→Nat) (d n : Nat)
    (hb : 0<b 0) (h : ∀ i, i<n → Edge (v i) (b i) (b (i+1)))
    (ht : b n=d+2) : n<targetFuel d := by
  by_cases hn : n<targetFuel d
  · exact hn
  · have hle : targetFuel d≤n := by omega
    have hlt : d+2<2^targetBits d := ((Nat.log2_eq_iff (show d+2≠0 by omega)).mp rfl).2
    have hmon := trace_mono v b n h hle (Nat.le_refl n)
    rw [ht] at hmon
    have hF : b (targetFuel d)<2^targetBits d := by omega
    exact False.elim (no_long_bounded_path v b (targetBits d) (ceilRatio (targetBits d) (orderFor (targetBits d)))
      (orderFor (targetBits d)) (by simp [targetBits]) (ceilRatio_bound _ _) hb
      (fun i hi=>h i (by change i<targetFuel d at hi; omega)) hF)

#print axioms prefix_target_fuel
#print axioms all_order_gain
#print axioms no_long_bounded_path
end NeedleAllOrderGrowth
