import Lean
namespace BB6.Agent43CarryAperiodic

private theorem zero_of_halves (f : Nat → Int) (h : ∀ j, 2*f (j+1)=f j) : ∀ j, f j=0 := by
  have aux : ∀ n j, (f j).natAbs=n → f j=0 := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro j hn
      by_cases hz : n=0
      · exact Int.natAbs_eq_zero.mp (hn.trans hz)
      · have hh := congrArg Int.natAbs (h j)
        simp only [Int.natAbs_mul] at hh
        change 2*(f (j+1)).natAbs=(f j).natAbs at hh
        have hl : (f (j+1)).natAbs<n := by omega
        have he := ih _ hl (j+1) rfl
        have hh' := h j
        rw [he] at hh'
        omega
  intro j
  exact aux _ j rfl

private theorem periodic_many (f : Nat → Int) (p : Nat) (h : ∀ j, f (j+p)=f j)
    (j k : Nat) : f (j+k*p)=f j := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul,←Nat.add_assoc,h,ih]

private theorem nonneg_periodic (d : Nat → Int) (p : Nat) (hp : 0<p)
    (hperiod : ∀ j, d (j+p)=d j) (hstep : ∀ j, d j≤2*d (j+1)) : ∀ j, 0≤d j := by
  intro j
  by_cases hn : 0≤d j
  · exact hn
  · have ha : ∀ k, d j≤d (j+k) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have hh := hstep (j+k)
        rw [Nat.add_assoc] at hh
        omega
    have h1 := ha (p-1)
    have h2 := hstep (j+(p-1))
    rw [show j+(p-1)+1=j+p by omega,hperiod] at h2
    omega

private theorem zero_tail (d : Nat → Int) (p : Nat) (hp : 0<p)
    (hperiod : ∀ j, d (j+p)=d j) (hstep : ∀ j, d j≤2*d (j+1))
    (hnonneg : ∀ j, 0≤d j) (j : Nat) (hz : d j=0) : ∀ k, d (j+k)=0 := by
  intro k
  by_cases he : d (j+k)=0
  · exact he
  · have hh : 0<d (j+k) := by have := hnonneg (j+k); omega
    have hpos : ∀ a, 0<d (j+k+a) := by
      intro a
      induction a with
      | zero => simpa using hh
      | succ a ih =>
        have h := hstep (j+k+a)
        rw [show j+k+a+1=j+k+(a+1) by omega] at h
        omega
    have hmul : k≤k*p := Nat.le_mul_of_pos_right k hp
    have hbig := hpos (k*p-k)
    rw [show j+k+(k*p-k)=j+k*p by omega,periodic_many d p hperiod j k,hz] at hbig
    omega

private theorem collision (d : Nat → Int) (p : Nat) (hp : 0<p)
    (hb : ∀ j, 0<d j ∧ d j<(p:Int)) :
    ∃ i j, i<j ∧ j<p ∧ d i=d j := by
  by_cases h : ∃ i j, i<j ∧ j<p ∧ d i=d j
  · exact h
  · exfalso
    let f : Nat → Nat := fun i => (d i).toNat
    have hnd : ((List.range p).map f).Nodup := by
      rw [List.nodup_iff_pairwise_ne,List.pairwise_map,List.pairwise_iff_getElem]
      intro i j hi hj hij
      simp only [List.getElem_range]
      intro he
      have hdi := Int.toNat_of_nonneg (show 0≤d i by have := (hb i).1; omega)
      have hdj := Int.toNat_of_nonneg (show 0≤d j by have := (hb j).1; omega)
      have he' : d i=d j := by
        change (d i).toNat=(d j).toNat at he
        omega
      exact h ⟨i,j,hij,by simpa using hj,he'⟩
    have hsub : (List.range p).map f ⊆ List.range' 1 (p-1) := by
      intro a ha
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
      have hi := hb i
      have hcast := Int.toNat_of_nonneg (show 0≤d i by omega)
      have hf : 0<f i ∧ f i<p := by dsimp [f]; omega
      apply List.mem_range'.2
      exact ⟨f i-1,by omega,by omega⟩
    have hlen := hnd.length_le_of_subset hsub
    simp only [List.length_map,List.length_range,List.length_range'] at hlen
    omega

/-- An infinite bounded modular carry path cannot have a periodic bit word.
    The two outer boundaries are essential: they support constant bits. -/
theorem no_period (q : Int) (c x : Nat → Int)
    (hc : ∀ j, 1≤c j ∧ c j≤q+(j:Int)-3)
    (hx : ∀ j, x j=0 ∨ x j=1)
    (hs : ∀ j, 2*c (j+1)=c j+(q+(j:Int))*x j)
    (p : Nat) (hp : 0<p) (hperiod : ∀ j, x (j+p)=x j) : False := by
  induction p using Nat.strongRecOn with
  | ind p ih =>
    let d : Nat → Int := fun j => c (j+p)-c j
    have hd : ∀ j, 2*d (j+1)=d j+(p:Int)*x j := by
      intro j
      have h1 := hs j
      have h2 := hs (j+p)
      rw [hperiod] at h2
      dsimp [d]
      rw [show j+1+p=j+p+1 by omega]
      rcases hx j with h|h <;> rw [h] at h1 h2 ⊢ <;> simp at h1 h2 ⊢ <;> omega
    have hdperiod : ∀ j, d (j+p)=d j := by
      let e : Nat → Int := fun j => d (j+p)-d j
      have he : ∀ j, 2*e (j+1)=e j := by
        intro j
        have h1 := hd j
        have h2 := hd (j+p)
        rw [hperiod] at h2
        dsimp [e]
        rw [show j+1+p=j+p+1 by omega]
        omega
      intro j
      have hz := zero_of_halves e he j
      dsimp [e] at hz
      omega
    have hdstep : ∀ j, d j≤2*d (j+1) := by
      intro j
      have h := hd j
      rcases hx j with hh|hh <;> rw [hh] at h <;> simp at h <;> omega
    have hnonneg := nonneg_periodic d p hp hdperiod hdstep
    let u : Nat → Int := fun j => (p:Int)-d j
    have huperiod : ∀ j, u (j+p)=u j := by intro j; simp only [u,hdperiod]
    have hustep : ∀ j, u j≤2*u (j+1) := by
      intro j
      have h := hd j
      dsimp [u]
      rcases hx j with hh|hh <;> rw [hh] at h <;> simp at h <;> omega
    have hunonneg := nonneg_periodic u p hp huperiod hustep
    have hb : ∀ j, 0<d j ∧ d j<(p:Int) := by
      intro j
      constructor
      · by_cases h : 0<d j
        · exact h
        · have hn := hnonneg j
          have hz : d j=0 := by omega
          have ht := zero_tail d p hp hdperiod hdstep hnonneg j hz
          have hbits : ∀ k, x (j+k)=0 := by
            intro k
            have hh := hd (j+k)
            rw [ht k,Nat.add_assoc,ht (k+1)] at hh
            rcases hx (j+k) with h0|h1
            · exact h0
            · rw [h1,Int.mul_one] at hh; omega
          let g : Nat → Int := fun k => c (j+k)
          have hg : ∀ k, 2*g (k+1)=g k := by
            intro k
            have hh := hs (j+k)
            rw [hbits k,Int.mul_zero,Int.add_zero] at hh
            simpa [g,Nat.add_assoc] using hh
          have he := zero_of_halves g hg 0
          have hpos := (hc j).1
          simp [g] at he
          omega
      · by_cases h : d j<(p:Int)
        · exact h
        · have hu := hunonneg j
          have hz : u j=0 := by dsimp [u] at *; omega
          have ht := zero_tail u p hp huperiod hustep hunonneg j hz
          have ht' : ∀ k, d (j+k)=(p:Int) := by intro k; have hh:=ht k; dsimp [u] at hh; omega
          have hbits : ∀ k, x (j+k)=1 := by
            intro k
            have hh := hd (j+k)
            rw [ht' k,Nat.add_assoc,ht' (k+1)] at hh
            rcases hx (j+k) with h0|h1
            · rw [h0,Int.mul_zero] at hh; omega
            · exact h1
          let g : Nat → Int := fun k => q+((j+k:Nat):Int)-2-c (j+k)
          have hg : ∀ k, 2*g (k+1)=g k := by
            intro k
            have hh := hs (j+k)
            rw [hbits k,Int.mul_one] at hh
            dsimp [g]
            rw [←Nat.add_assoc]
            omega
          have he := zero_of_halves g hg 0
          have hpos := (hc j).2
          simp [g] at he
          omega
    obtain ⟨i,j,hij,hjp,he⟩ := collision d p hp hb
    let a := j-i
    have ha : 0<a := by dsimp [a]; omega
    have hap : a<p := by dsimp [a]; omega
    have hia : i+a=j := by dsimp [a]; omega
    have hback : ∀ t, d (t+1)=d (t+a+1) → d t=d (t+a) := by
      intro t he'
      have h1 := hd t
      have h2 := hd (t+a)
      have ht := hb t
      have hta := hb (t+a)
      rw [←he'] at h2
      rcases hx t with h0|h0 <;> rcases hx (t+a) with h1'|h1' <;>
        rw [h0] at h1 <;> rw [h1'] at h2 <;> simp at h1 h2 <;> omega
    have hbackmany : ∀ k t, d (t+k)=d (t+k+a) → d t=d (t+a) := by
      intro k
      induction k with
      | zero => intro t he'; simpa using he'
      | succ k ih' =>
        intro t he'
        have hh : d (t+k+1)=d (t+k+a+1) := by
          rw [show t+k+1=t+(k+1) by omega,show t+k+a+1=t+(k+1)+a by omega]
          exact he'
        exact ih' t (hback (t+k) hh)
    have hnew : ∀ t, d (t+a)=d t := by
      intro t
      have ht : t≤i+t*p := by have := Nat.le_mul_of_pos_right t hp; omega
      have hh : d (i+t*p)=d (i+t*p+a) := by
        rw [periodic_many d p hdperiod i t,show i+t*p+a=j+t*p by omega,periodic_many d p hdperiod j t]
        exact he
      have hh' : d (t+(i+t*p-t))=d (t+(i+t*p-t)+a) := by simpa only [show t+(i+t*p-t)=i+t*p by omega] using hh
      exact (hbackmany (i+t*p-t) t hh').symm
    have hxp : ∀ t, x (t+a)=x t := by
      intro t
      have h1 := hd t
      have h2 := hd (t+a)
      rw [show t+a+1=t+1+a by omega,hnew (t+1),hnew t] at h2
      rcases hx t with h0|h0 <;> rcases hx (t+a) with h1'|h1' <;>
        rw [h0] at h1 ⊢ <;> rw [h1'] at h2 ⊢ <;> simp at h1 h2 ⊢ <;> omega
    exact ih a hap ha hxp

/-- Even an eventually periodic tail is impossible; shift the clock. -/
theorem no_eventual_period (q : Int) (c x : Nat → Int)
    (hc : ∀ j, 1≤c j ∧ c j≤q+(j:Int)-3)
    (hx : ∀ j, x j=0 ∨ x j=1)
    (hs : ∀ j, 2*c (j+1)=c j+(q+(j:Int))*x j)
    (J p : Nat) (hp : 0<p) (hperiod : ∀ j, x (J+j+p)=x (J+j)) : False := by
  apply no_period (q+(J:Int)) (fun j => c (J+j)) (fun j => x (J+j))
  · intro j; have h := hc (J+j); omega
  · intro j; exact hx (J+j)
  · intro j; have h := hs (J+j); simpa only [Nat.add_assoc,Int.natCast_add,Int.add_assoc] using h
  · exact hp
  · intro j; simpa only [←Nat.add_assoc] using hperiod j

#print axioms no_period
#print axioms no_eventual_period
end BB6.Agent43CarryAperiodic

namespace BB6.Agent43CarryAperiodic

private theorem finite_halving (f : Nat → Int) (L : Nat)
    (hs : ∀ j<L, 2*f (j+1)=f j) (hb : (f 0).natAbs<2^L) : f 0=0 := by
  have he : ∀ j≤L, (f 0).natAbs=2^j*(f j).natAbs := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      have h := congrArg Int.natAbs (hs j (by omega))
      simp only [Int.natAbs_mul] at h
      change 2*(f (j+1)).natAbs=(f j).natAbs at h
      rw [ih (by omega),←h,Nat.pow_succ,Nat.mul_assoc]
  have h := he L (by omega)
  have hz : (f L).natAbs=0 := by
    by_cases hh : (f L).natAbs=0
    · exact hh
    · have hm := Nat.mul_le_mul_left (2^L) (show 1≤(f L).natAbs by omega)
      simp at hm
      omega
  rw [hz,Nat.mul_zero] at h
  exact Int.natAbs_eq_zero.mp h

private theorem mod_div_succ (t p : Nat) (hp : 0<p) :
    ((t%p+1<p) ∧ (t+1)%p=t%p+1 ∧ (t+1)/p=t/p) ∨
    (t%p+1=p ∧ (t+1)%p=0 ∧ (t+1)/p=t/p+1) := by
  have he := Nat.mod_add_div t p
  have he' := Nat.mod_add_div (t+1) p
  have hr := Nat.mod_lt t hp
  have hr' := Nat.mod_lt (t+1) hp
  by_cases h : t%p+1<p
  · left
    have hdiv : (t+1)/p=t/p := by
      apply (Nat.div_eq_iff hp).2
      rw [Nat.mul_comm (t/p) p]
      omega
    rw [hdiv] at he'
    exact ⟨h,by omega,hdiv⟩
  · right
    have hdiv : (t+1)/p=t/p+1 := by
      apply (Nat.div_eq_iff hp).2
      rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm (t/p) p]
      omega
    rw [hdiv,Nat.mul_add,Nat.mul_one] at he'
    exact ⟨by omega,by omega,hdiv⟩

/-- A long enough repeated finite word has an infinite affine-periodic
    continuation if its second block difference has already vanished. -/
private theorem affine_periodic_extension (q : Int) (c d x : Nat → Int)
    (p : Nat) (hp : 0<p)
    (hc : ∀ j<p, 1≤c j ∧ c j≤q+(j:Int)-3)
    (hx : ∀ j<p, x j=0 ∨ x j=1)
    (hs : ∀ j<p, 2*c (j+1)=c j+(q+(j:Int))*x j)
    (hd : ∀ j<p, 2*d (j+1)=d j+(p:Int)*x j)
    (hcp : c p=c 0+d 0) (hdp : d p=d 0) : False := by
  let D : Nat → Int := fun t => d (t%p)
  let X : Nat → Int := fun t => x (t%p)
  let C : Nat → Int := fun t => c (t%p)+((t/p:Nat):Int)*D t
  have hDp : ∀ t, D (t+p)=D t := by intro t; simp [D,Nat.add_mod_right]
  have hXp : ∀ t, X (t+p)=X t := by intro t; simp [X,Nat.add_mod_right]
  have hX : ∀ t, X t=0 ∨ X t=1 := by intro t; exact hx _ (Nat.mod_lt _ hp)
  have hDs : ∀ t, 2*D (t+1)=D t+(p:Int)*X t := by
    intro t
    have h := hd (t%p) (Nat.mod_lt _ hp)
    rcases mod_div_succ t p hp with ⟨_,hm,_⟩|⟨he,hm,_⟩
    · simpa only [D,X,hm] using h
    · rw [he,hdp] at h
      simpa only [D,X,hm] using h
  have hDstep : ∀ t, D t≤2*D (t+1) := by
    intro t; have h:=hDs t
    rcases hX t with hh|hh <;> rw [hh] at h <;> simp at h <;> omega
  have hDnonneg := nonneg_periodic D p hp hDp hDstep
  let U : Nat → Int := fun t => (p:Int)-D t
  have hUp : ∀ t, U (t+p)=U t := by intro t; simp only [U,hDp]
  have hUstep : ∀ t, U t≤2*U (t+1) := by
    intro t; have h:=hDs t
    dsimp [U]
    rcases hX t with hh|hh <;> rw [hh] at h <;> simp at h <;> omega
  have hUnonneg := nonneg_periodic U p hp hUp hUstep
  have hC : ∀ t, 1≤C t ∧ C t≤q+(t:Int)-3 := by
    intro t
    have hh := hc (t%p) (Nat.mod_lt _ hp)
    have h1 := hDnonneg t
    have h2 := hUnonneg t
    dsimp [U] at h2
    have hmul := Int.mul_nonneg (Int.natCast_nonneg (t/p)) h1
    have hmul2 := Int.mul_le_mul_of_nonneg_left (show D t≤(p:Int) by omega) (Int.natCast_nonneg (t/p))
    have he := congrArg (fun a : Nat => (a:Int)) (Nat.mod_add_div t p)
    simp only [Int.natCast_add,Int.natCast_mul] at he
    rw [Int.mul_comm (p:Int) ((t/p:Nat):Int)] at he
    constructor
    · exact Int.le_trans hh.1 (Int.le_add_of_nonneg_right hmul)
    · calc
        C t=c (t%p)+((t/p:Nat):Int)*D t := rfl
        _≤(q+((t%p:Nat):Int)-3)+((t/p:Nat):Int)*(p:Int) := Int.add_le_add hh.2 hmul2
        _=q+(t:Int)-3 := by rw [←he]; omega
  have hCs : ∀ t, 2*C (t+1)=C t+(q+(t:Int))*X t := by
    intro t
    let r:=t%p
    let k:=t/p
    have hr : r<p := Nat.mod_lt _ hp
    have hcstep := hs r hr
    have hdstep := hd r hr
    have hnext : C (t+1)=c (r+1)+(k:Int)*d (r+1) := by
      rcases mod_div_succ t p hp with ⟨_,hm,hk⟩|⟨he,hm,hk⟩
      · simp only [C,D,hm,hk,r,k]
      · have he' : r+1=p := he
        rw [he',hdp,hcp]
        simp only [C,D,hm,hk,Int.natCast_add,Int.natCast_one]
        dsimp [k]
        rw [Int.add_mul]
        simp only [Int.one_mul]
        omega
    have he := congrArg (fun a : Nat => (a:Int)) (Nat.mod_add_div t p)
    simp only [Int.natCast_add,Int.natCast_mul] at he
    change (r:Int)+(p:Int)*(k:Int)=(t:Int) at he
    rw [hnext]
    change 2*(c (r+1)+(k:Int)*d (r+1)) = c r+(k:Int)*d r+(q+(t:Int))*x r
    have hm := congrArg (fun z : Int => (k:Int)*z) hdstep
    rw [Int.mul_add] at hm
    have hprod : (k:Int)*(2*d (r+1))=2*((k:Int)*d (r+1)) := by ac_rfl
    rw [hprod] at hm
    rw [Int.mul_add]
    rcases hx r hr with h0|h1
    · rw [h0] at hcstep hm ⊢
      simp only [Int.mul_zero,Int.add_zero] at hcstep hm ⊢
      omega
    · rw [h1] at hcstep hm ⊢
      simp only [Int.mul_one] at hcstep hm ⊢
      rw [Int.mul_comm (k:Int) (p:Int)] at hm
      omega
  exact no_period q C X hC hX hCs p hp hXp

/-- Quantitative form: a p-periodic legal carry word of length 2p+L is
    impossible as soon as 2^L > 2(q+p). No unknown large-index constant. -/
theorem no_long_period (q p L : Nat) (c x : Nat → Int) (hp : 0<p)
    (hc : ∀ j≤2*p+L, 1≤c j ∧ c j≤(q:Int)+(j:Int)-3)
    (hx : ∀ j<2*p+L, x j=0 ∨ x j=1)
    (hs : ∀ j<2*p+L, 2*c (j+1)=c j+((q:Int)+(j:Int))*x j)
    (hperiod : ∀ j, j+p<2*p+L → x (j+p)=x j)
    (hscale : 2*(q+p)<2^L) : False := by
  let d : Nat → Int := fun j => c (j+p)-c j
  have hd : ∀ j<p+L, 2*d (j+1)=d j+(p:Int)*x j := by
    intro j hj
    have h1 := hs j (by omega)
    have h2 := hs (j+p) (by omega)
    rw [hperiod j (by omega)] at h2
    dsimp [d]
    rw [show j+1+p=j+p+1 by omega]
    rcases hx j (by omega) with h0|h1' <;> (first | rw [h0] at h1 h2 ⊢ | rw [h1'] at h1 h2 ⊢) <;> simp at h1 h2 ⊢ <;> omega
  let e : Nat → Int := fun j => d (j+p)-d j
  have he : ∀ j<L, 2*e (j+1)=e j := by
    intro j hj
    have h1 := hd j (by omega)
    have h2 := hd (j+p) (by omega)
    rw [hperiod j (by omega)] at h2
    dsimp [e]
    rw [show j+1+p=j+p+1 by omega]
    omega
  have hbound : (e 0).natAbs<2^L := by
    have h0 := hc 0 (by omega)
    have h1 := hc p (by omega)
    have h2 := hc (2*p) (by omega)
    have he' : e 0=c (2*p)-2*c p+c 0 := by simp only [e,d,Nat.zero_add,show p+p=2*p by omega]; omega
    by_cases hz : 0≤e 0
    · have ha := Int.natAbs_of_nonneg hz
      omega
    · have ha := Int.natAbs_of_nonneg (show 0≤ -e 0 by omega)
      simp only [Int.natAbs_neg] at ha
      omega
  have he0 := finite_halving e L he hbound
  have hdp : d p=d 0 := by simp only [e,Nat.zero_add] at he0; omega
  apply affine_periodic_extension (q:Int) c d x p hp
  · intro j hj; exact hc j (by omega)
  · intro j hj; exact hx j (by omega)
  · intro j hj; exact hs j (by omega)
  · intro j hj; exact hd j (by omega)
  · simp only [d,Nat.zero_add]; omega
  · exact hdp

#print axioms no_long_period
end BB6.Agent43CarryAperiodic
