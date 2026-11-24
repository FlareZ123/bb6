import P1CarryExact

/-! Finite dyadic conservation and extinction bounds for the critical carry words.
    All counts retain the multiplicity of Boolean words. -/
namespace BB6.P1CarryExtinction
open BB6.P1CarryExact

/-- Sum a natural-valued function over all Boolean lists of length k. -/
def wordSum : Nat → (List Bool → Nat) → Nat
  | 0, f => f []
  | k+1, f => wordSum k (fun xs => f (false::xs)) + wordSum k (fun xs => f (true::xs))

theorem wordSum_congr (k : Nat) (f g : List Bool → Nat)
    (h : ∀ xs, xs.length=k → f xs=g xs) : wordSum k f=wordSum k g := by
  induction k generalizing f g with
  | zero => exact h [] rfl
  | succ k ih =>
    simp only [wordSum]
    rw [ih _ _ (fun xs hx => h _ (by simp [hx])),
        ih _ _ (fun xs hx => h _ (by simp [hx]))]

theorem wordSum_add (k : Nat) (f g : List Bool → Nat) :
    wordSum k (fun xs => f xs+g xs)=wordSum k f+wordSum k g := by
  induction k generalizing f g with
  | zero => rfl
  | succ k ih =>
    simp only [wordSum]
    rw [ih,ih]
    omega

theorem wordSum_mul (k a : Nat) (f : List Bool → Nat) :
    wordSum k (fun xs => a*f xs)=a*wordSum k f := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih => simp only [wordSum,ih,Nat.mul_add]

theorem wordSum_snoc (k : Nat) (f : List Bool → Nat) :
    wordSum (k+1) f=wordSum k (fun xs => f (xs++[false])+f (xs++[true])) := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
    change wordSum (k+1) (fun xs => f (false::xs)) +
      wordSum (k+1) (fun xs => f (true::xs)) =
      wordSum k (fun xs => f ((false::xs)++[false])+f ((false::xs)++[true])) +
      wordSum k (fun xs => f ((true::xs)++[false])+f ((true::xs)++[true]))
    rw [ih,ih]
    rfl

theorem wordSum_pos_iff (k : Nat) (f : List Bool → Nat) :
    0<wordSum k f ↔ ∃ xs, xs.length=k ∧ 0<f xs := by
  induction k generalizing f with
  | zero =>
    constructor
    · intro h; exact ⟨[],rfl,h⟩
    · rintro ⟨xs,hx,h⟩
      have : xs=[] := List.length_eq_zero_iff.mp hx
      simpa [this,wordSum] using h
  | succ k ih =>
    simp only [wordSum]
    constructor
    · intro h
      by_cases h0 : 0<wordSum k (fun xs => f (false::xs))
      · obtain ⟨xs,hx,hp⟩ := (ih _).mp h0
        exact ⟨false::xs,by simp [hx],hp⟩
      · have h1 : 0<wordSum k (fun xs => f (true::xs)) := by omega
        obtain ⟨xs,hx,hp⟩ := (ih _).mp h1
        exact ⟨true::xs,by simp [hx],hp⟩
    · rintro ⟨xs,hx,hp⟩
      cases xs with
      | nil => simp at hx
      | cons b xs =>
        have hx' : xs.length=k := by simp at hx; omega
        cases b with
        | false =>
          have h0 := (ih (fun xs => f (false::xs))).mpr ⟨xs,hx',hp⟩
          omega
        | true =>
          have h1 := (ih (fun xs => f (true::xs))).mpr ⟨xs,hx',hp⟩
          omega

def ind (p : Prop) [Decidable p] : Nat := if p then 1 else 0

def weight (n j : Nat) : Nat := (n+3+j)*2^j

def absSum (n j : Nat) : List Bool → Nat
  | [] => 0
  | b::bs => (if b then weight n j else 0)+absSum n (j+1) bs

def bitMass (j : Nat) : List Bool → Nat
  | [] => 0
  | b::bs => (if b then 2^j else 0)+bitMass (j+1) bs

def expr (n : Nat) (xs : List Bool) : Nat := n+3+absSum n 1 xs

theorem absSum_eq (n j : Nat) (xs : List Bool) :
    absSum n j xs=2^j*weightedTail n j xs := by
  induction xs generalizing j with
  | nil => simp [absSum,weightedTail]
  | cons b bs ih =>
    cases b <;> simp [absSum,weightedTail,weight,ih,Nat.pow_succ,Nat.mul_add,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]

theorem expr_eq (n : Nat) (xs : List Bool) :
    expr n xs=n+3+2*weightedTail n 1 xs := by
  simp [expr,absSum_eq]

theorem absSum_shift (n p j : Nat) (xs : List Bool) :
    absSum (n+p) j xs=absSum n j xs+p*bitMass j xs := by
  induction xs generalizing j with
  | nil => simp [absSum,bitMass]
  | cons b bs ih =>
    have hW : weight (n+p) j = weight n j+p*2^j := by
      simp [weight,Nat.add_mul]; omega
    cases b <;> simp [absSum,bitMass,ih,hW,Nat.mul_add] <;> omega

theorem expr_shift (n p : Nat) (xs : List Bool) :
    expr (n+p) xs=expr n xs+p*(1+bitMass 1 xs) := by
  simp [expr,absSum_shift,Nat.mul_add]; omega

theorem bitMass_even (j : Nat) (xs : List Bool) : bitMass (j+1) xs % 2=0 := by
  induction xs generalizing j with
  | nil => simp [bitMass]
  | cons b bs ih =>
    have h := ih (j+1)
    cases b <;> simp [bitMass,Nat.pow_succ,Nat.add_mod,h]

theorem expr_snoc (n : Nat) (xs : List Bool) (b : Bool) :
    expr n (xs++[b])=expr n xs+(if b then weight n (1+xs.length) else 0) := by
  have hh (j : Nat) (ys : List Bool) :
      absSum n j (ys++[b])=absSum n j ys+(if b then weight n (j+ys.length) else 0) := by
    induction ys generalizing j with
    | nil => simp [absSum]
    | cons a as ih =>
      simp only [List.cons_append,absSum,ih,List.length_cons]
      have he : j+1+as.length=j+(as.length+1) := by omega
      rw [he]; omega
  simp only [expr,hh]
  omega

/-- Width at cost K: prefix words with a compulsory leading one. -/
def width (K n : Nat) : Nat :=
  wordSum (K-1) (fun xs => ind (expr n xs % 2^K=1))

theorem width_pos_iff (K n : Nat) (hK : 0<K) :
    0<width K n ↔ ∃ xs, xs.length+1=K ∧ expr n xs % 2^K=1 := by
  rw [width,wordSum_pos_iff]
  constructor
  · rintro ⟨xs,hx,h⟩
    refine ⟨xs,by omega,?_⟩
    by_cases hc : expr n xs % 2^K=1
    · exact hc
    · simp [ind,hc] at h
  · rintro ⟨xs,hx,h⟩
    exact ⟨xs,by omega,by simp [ind,h]⟩

theorem width_period (K n a : Nat) : width K (n+2^K*a)=width K n := by
  apply wordSum_congr
  intro xs _
  rw [expr_shift]
  have he : 2^K*a*(1+bitMass 1 xs)=2^K*(a*(1+bitMass 1 xs)) := by ac_rfl
  rw [he,Nat.add_mul_mod_self_left]

theorem width_one (n : Nat) : width 1 n = ind (n%2=0) := by
  have he : (n+3)%2=1 ↔ n%2=0 := by omega
  simp [width,wordSum,expr,absSum,ind,he]

/-- Exactly one high parameter bit makes a fixed extension valid, if the
    old low bits are valid. -/
theorem indicator_flip (M a S : Nat) (hM : 1<M) (hS : S%2=1) :
    ind (a%(2*M)=1)+ind ((a+M*S)%(2*M)=1)=ind (a%M=1) := by
  let r := a%(2*M)
  have hr : r<2*M := Nat.mod_lt _ (by omega)
  have hsmall : r%M=a%M := Nat.mod_mod_of_dvd a ⟨2,by ac_rfl⟩
  have hs : S=2*(S/2)+1 := by omega
  have hp : M*S=M+(2*M)*(S/2) := by
    calc
      M*S = M*(2*(S/2)+1) := congrArg (fun x => M*x) hs
      _ = M+(2*M)*(S/2) := by rw [Nat.mul_add,Nat.mul_one]; ac_rfl
  have hshift : (a+M*S)%(2*M)=(r+M)%(2*M) := by
    rw [hp,← Nat.add_assoc,Nat.add_mul_mod_self_left,Nat.mod_add_mod]
  change ind (r=1)+ind ((a+M*S)%(2*M)=1)=ind (a%M=1)
  rw [hshift,← hsmall]
  by_cases hlt : r<M
  · rw [Nat.mod_eq_of_lt hlt,Nat.mod_eq_of_lt (by omega : r+M<2*M)]
    have hne : r+M≠1 := by omega
    simp [ind,hne]
  · have hge : M≤r := by omega
    rw [Nat.mod_eq_sub_mod hge,Nat.mod_eq_of_lt (by omega : r-M<M)]
    rw [Nat.mod_eq_sub_mod (by omega : 2*M≤r+M),Nat.mod_eq_of_lt (by omega : r+M-2*M<2*M)]
    have hne : r≠1 := by omega
    have he : r+M-2*M=r-M := by omega
    simp [ind,hne,he]

/-- Exact dyadic martingale law. No independence assumption is used. -/
theorem width_conservation (K n : Nat) (hK : 0<K) :
    width (K+1) n+width (K+1) (n+2^K)=2*width K n := by
  have hlen : K+1-1=(K-1)+1 := by omega
  unfold width
  rw [hlen,wordSum_snoc,wordSum_snoc,← wordSum_add,← wordSum_mul]
  apply wordSum_congr
  intro xs hx
  have hP : 1<2^K := by
    have := Nat.pow_lt_pow_right (show 1<2 by decide) hK
    simpa using this
  have hf (b : Bool) :
      ind (expr n (xs++[b])%2^(K+1)=1)+
      ind (expr (n+2^K) (xs++[b])%2^(K+1)=1)=ind (expr n xs%2^K=1) := by
    rw [expr_shift,Nat.pow_succ]
    have hS : (1+bitMass 1 (xs++[b]))%2=1 := by
      have h := bitMass_even 0 (xs++[b])
      change bitMass 1 (xs++[b])%2=0 at h
      omega
    have he : 2^K*2=2*2^K := by ac_rfl
    rw [he,indicator_flip (2^K) _ _ hP hS,expr_snoc]
    have hi : 1+xs.length=K := by omega
    rw [hi]
    cases b <;> simp [weight,Nat.add_mul_mod_self_right]
  have h0 := hf false
  have h1 := hf true
  omega

#print axioms width_pos_iff
#print axioms width_period
#print axioms width_conservation

/-- Count arbitrary remaining suffixes modulo M, from accumulated sum a. -/
def suffixCount (n j k M a : Nat) : Nat :=
  wordSum k (fun xs => ind ((a+absSum n j xs)%M=1))

theorem suffixCount_step (n j k M a : Nat) :
    suffixCount n j (k+1) M a =
      suffixCount n (j+1) k M a + suffixCount n (j+1) k M (a+weight n j) := by
  simp [suffixCount,wordSum,absSum,Nat.add_assoc]

theorem suffixCount_period (n j k M a t : Nat) :
    suffixCount n j k M (a+M*t)=suffixCount n j k M a := by
  apply wordSum_congr
  intro xs _
  have he : a+M*t+absSum n j xs = a+absSum n j xs+M*t := by ac_rfl
  rw [he,Nat.add_mul_mod_self_left]

/-- Number of freely togglable positions among j,...,j+k-1. -/
def freeCount (n M j : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => ind (M ∣ weight n j)+freeCount n M (j+1) k

/-- Toggling each zero-weight bit gives a factor of two in multiplicity. -/
theorem suffixCount_free_dvd (n j k M a : Nat) :
    2^freeCount n M j k ∣ suffixCount n j k M a := by
  induction k generalizing j a with
  | zero => simp [freeCount]
  | succ k ih =>
    rw [suffixCount_step,freeCount]
    by_cases h : M ∣ weight n j
    · simp only [ind,if_pos h]
      obtain ⟨t,ht⟩ := h
      rw [ht,suffixCount_period]
      have hdiv := ih (j+1) a
      obtain ⟨u,hu⟩ := hdiv
      rw [hu]
      refine ⟨u,?_⟩
      rw [Nat.add_comm 1,Nat.pow_succ]
      rw [Nat.mul_assoc,← Nat.mul_add]
      congr 1
      omega
    · simp only [ind,if_neg h,Nat.zero_add]
      exact Nat.dvd_add (ih _ _) (ih _ _)

theorem width_free_dvd (K n : Nat) :
    2^freeCount n (2^K) 1 (K-1) ∣ width K n :=
  suffixCount_free_dvd n 1 (K-1) (2^K) (n+3)

theorem freeCount_extend_left (n M j l k : Nat) :
    freeCount n M (j+l) k ≤ freeCount n M j (l+k) := by
  induction l generalizing j with
  | zero => simp
  | succ l ih =>
    have h : l+1+k=l+k+1 := by omega
    rw [h,freeCount]
    have he : j+(l+1)=j+1+l := by omega
    rw [he]
    have hp := ih (j+1)
    omega

/-- Growing chain of distances from the terminal bit. Earlier distances are
    congruent to later ones modulo their respective powers of two. -/
def dist : Nat → Nat
  | 0 => 1
  | k+1 => dist k+2^(dist k)

theorem dist_pos (k : Nat) : 0<dist k := by
  cases k with
  | zero => decide
  | succ k => rw [dist]; have := Nat.two_pow_pos (dist k); omega

theorem dist_step_gt (k : Nat) : dist k < dist (k+1) := by
  simp [dist,Nat.two_pow_pos]

theorem weight_dvd_of_distance (n K r : Nat) (hr : r≤K)
    (h : 2^r ∣ n+K+3-r) : 2^K ∣ weight n (K-r) := by
  obtain ⟨a,ha⟩ := h
  have he : n+3+(K-r)=n+K+3-r := by omega
  have hp : 2^K=2^r*2^(K-r) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  unfold weight
  rw [he,ha,hp]
  exact ⟨a,by ac_rfl⟩

/-- A congruence at the largest chain distance guarantees all k+1 free bits.
    The suffix begins at index K-dist k and has length dist k. -/
theorem dist_free_count (n K k : Nat) (hK : dist k<K)
    (h : 2^(dist k) ∣ n+K+3-dist k) :
    k+1 ≤ freeCount n (2^K) (K-dist k) (dist k) := by
  induction k with
  | zero =>
    have hh : 2^K ∣ weight n (K-1) := weight_dvd_of_distance n K 1 (by simp [dist] at hK; omega) h
    simp [dist,freeCount,ind,hh]
  | succ k ih =>
    have hgt := dist_step_gt k
    have hK' : dist k<K := by omega
    have hP : 2^(dist k) ∣ 2^(dist (k+1)) := Nat.pow_dvd_pow 2 (by omega)
    have hdiv := Nat.dvd_trans hP h
    have hdiff : n+K+3-dist k = (n+K+3-dist (k+1))+2^(dist k) := by
      have he : dist (k+1)=dist k+2^(dist k) := rfl
      omega
    have hprev : 2^(dist k) ∣ n+K+3-dist k := by
      rw [hdiff]
      exact Nat.dvd_add hdiv (Nat.dvd_refl _)
    have hp := ih hK' hprev
    have hfree : 2^K ∣ weight n (K-dist (k+1)) :=
      weight_dvd_of_distance n K _ (by omega) h
    have hidx : K-dist (k+1)+1+(dist (k+1)-dist k-1)=K-dist k := by omega
    have hlen : dist (k+1)-dist k-1+dist k=dist (k+1)-1 := by omega
    have hext := freeCount_extend_left n (2^K) (K-dist (k+1)+1)
      (dist (k+1)-dist k-1) (dist k)
    rw [hidx,hlen] at hext
    have hlen' : dist (k+1)=dist (k+1)-1+1 := by omega
    -- The recursive suffix has at least k+1 free positions, plus the new head.
    have hhead : freeCount n (2^K) (K-dist (k+1)) (dist (k+1)) =
        1+freeCount n (2^K) (K-dist (k+1)+1) (dist (k+1)-1) := by
      calc
        _ = freeCount n (2^K) (K-dist (k+1)) (dist (k+1)-1+1) :=
          congrArg (freeCount n (2^K) (K-dist (k+1))) hlen'
        _ = _ := by rw [freeCount]; simp [ind,hfree]
    omega

/-- Every parameter has a checkpoint of width divisible by 2^(k+1), within
    the same finite horizon dist(k+1)+1. -/
theorem free_checkpoint (n k : Nat) :
    ∃ K, 0<K ∧ K≤dist (k+1)+1 ∧ 2^(k+1) ∣ width K n := by
  let r := dist k
  let P := 2^r
  let K := r+1+(P-(n+4)%P)
  have hP : 0<P := Nat.two_pow_pos _
  have hrem : (n+4)%P<P := Nat.mod_lt _ hP
  have hK : r<K := by dsimp [K]; omega
  have hcap : K≤dist (k+1)+1 := by
    dsimp [K,P,r]
    simp only [dist]
    omega
  have hmod : P ∣ n+K+3-r := by
    refine ⟨(n+4)/P+1,?_⟩
    have he := Nat.mod_add_div (n+4) P
    rw [Nat.mul_add,Nat.mul_one]
    dsimp [K]
    omega
  have hf := dist_free_count n K k hK hmod
  change k+1≤freeCount n (2^K) (K-r) r at hf
  have hext := freeCount_extend_left n (2^K) 1 (K-r-1) r
  have hi : 1+(K-r-1)=K-r := by omega
  have hl : K-r-1+r=K-1 := by omega
  rw [hi,hl] at hext
  have hpow : 2^(k+1) ∣ 2^freeCount n (2^K) 1 (K-1) := Nat.pow_dvd_pow 2 (by omega)
  exact ⟨K,by omega,hcap,Nat.dvd_trans hpow (width_free_dvd K n)⟩

#print axioms suffixCount_free_dvd
#print axioms free_checkpoint

theorem width_pos_earlier (n K d : Nat) (hK : 0<K)
    (h : 0<width (K+d) n) : 0<width K n := by
  induction d with
  | zero => simpa using h
  | succ d ih =>
    have he := width_conservation (K+d) n (by omega)
    have hp : 0<width (K+d) n := by
      change 0<width (K+d+1) n at h
      omega
    exact ih hp

/-- The residues in a dyadic cylinder, enumerated in binary tree order. -/
def leaves (K n : Nat) : Nat → List Nat
  | 0 => [n]
  | d+1 => leaves (K+1) n d ++ leaves (K+1) (n+2^K) d

theorem leaves_length (K n d : Nat) : (leaves K n d).length=2^d := by
  induction d generalizing K n with
  | zero => rfl
  | succ d ih => simp [leaves,ih,Nat.pow_succ,Nat.mul_two]

theorem leaves_mem_iff (K n d a : Nat) :
    a∈leaves K n d ↔ ∃ t<2^d, a=n+2^K*t := by
  induction d generalizing K n with
  | zero =>
    simp [leaves]
  | succ d ih =>
    simp only [leaves,List.mem_append,ih,Nat.pow_succ]
    constructor
    · rintro (⟨t,ht,ha⟩ | ⟨t,ht,ha⟩)
      · refine ⟨2*t,by omega,?_⟩
        rw [ha]; congr 1; ac_rfl
      · refine ⟨2*t+1,by omega,?_⟩
        rw [ha,Nat.mul_add,Nat.mul_one]
        have he : 2^K*2*t=2^K*(2*t) := by ac_rfl
        rw [he]; omega
    · rintro ⟨t,ht,ha⟩
      have ht' : t/2<2^d := by omega
      by_cases hEven : t%2=0
      · left
        refine ⟨t/2,ht',?_⟩
        have he : t=2*(t/2) := by omega
        calc
          a = n+2^K*t := ha
          _ = n+2^K*(2*(t/2)) := by rw [← he]
          _ = _ := by ac_rfl
      · right
        refine ⟨t/2,ht',?_⟩
        have he : t=2*(t/2)+1 := by omega
        calc
          a = n+2^K*t := ha
          _ = n+2^K*(2*(t/2)+1) := congrArg (fun x => n+2^K*x) he
          _ = _ := by rw [Nat.mul_add,Nat.mul_one]; ac_rfl

/-- Number of positive-width leaves in a dyadic cylinder. -/
def liveCount (K n d : Nat) : Nat :=
  (leaves K n d).countP (fun a => decide (0<width (K+d) a))

theorem liveCount_le (K n d : Nat) : liveCount K n d ≤ 2^d := by
  unfold liveCount
  rw [← leaves_length K n d]
  exact List.countP_le_length

theorem liveCount_step (K n d : Nat) : liveCount K n (d+1) =
    liveCount (K+1) n d+liveCount (K+1) (n+2^K) d := by
  have he : K+(d+1)=K+1+d := by omega
  simp only [liveCount,leaves,List.countP_append,he]

/-- Finite first-hit inequality on the dyadic tree.  If every live final
    leaf hits threshold B at some intermediate level, its mass is at most
    the initial width budget divided by B. -/
theorem live_budget (B K n d : Nat) (hK : 0<K)
    (hhit : ∀ a∈leaves K n d, 0<width (K+d) a →
      ∃ j, K≤j ∧ j≤K+d ∧ B≤width j a) :
    B*liveCount K n d≤2^d*width K n := by
  induction d generalizing K n with
  | zero =>
    by_cases h : 0<width K n
    · obtain ⟨j,hj,hj',hB⟩ := hhit n (by simp [leaves]) (by simpa using h)
      have he : j=K := by omega
      subst j
      simpa [liveCount,leaves,h] using hB
    · simp [liveCount,leaves,h]
  | succ d ih =>
    by_cases hB : B≤width K n
    · have h1 := Nat.mul_le_mul_left B (liveCount_le K n (d+1))
      have h2 := Nat.mul_le_mul_left (2^(d+1)) hB
      rw [Nat.mul_comm B (2^(d+1))] at h1
      exact Nat.le_trans h1 h2
    · have hh (r : Nat) (hr : ∀ a∈leaves (K+1) r d, a∈leaves K n (d+1)) :
          ∀ a∈leaves (K+1) r d, 0<width (K+1+d) a →
            ∃ j, K+1≤j ∧ j≤K+1+d ∧ B≤width j a := by
        intro a ha hw
        have ha' := hr a ha
        have he : K+(d+1)=K+1+d := by omega
        obtain ⟨j,hj,hj',hW⟩ := hhit a ha' (by simpa only [he] using hw)
        have hjK : K<j := by
          by_cases hj0 : j=K
          · subst j
            obtain ⟨t,_,hat⟩ := (leaves_mem_iff K n (d+1) a).mp ha'
            rw [hat,width_period] at hW
            omega
          · omega
        exact ⟨j,by omega,by omega,hW⟩
      have h0 := ih (K+1) n (by omega) (hh n (by
        intro a ha; simp [leaves,ha]))
      have h1 := ih (K+1) (n+2^K) (by omega) (hh (n+2^K) (by
        intro a ha; simp [leaves,ha]))
      have hsum := Nat.add_le_add h0 h1
      rw [← Nat.mul_add,← Nat.mul_add,width_conservation K n hK] at hsum
      rw [liveCount_step,Nat.pow_succ,Nat.mul_assoc]
      exact hsum

/-- Universal finite density bound: at horizon M>=dist(k+1)+1,
    at most 2^M / 2^(k+2) parameter residues still admit a carry word.
    The left side is a count in the even and odd dyadic cylinders. -/
theorem survival_bound (k M : Nat) (hM : dist (k+1)+1≤M) :
    2^(k+1)*(liveCount 1 0 (M-1)+liveCount 1 1 (M-1))≤2^(M-1) := by
  have hMpos : 0<M := by omega
  have hhit (r : Nat) : ∀ a∈leaves 1 r (M-1), 0<width (1+(M-1)) a →
      ∃ j, 1≤j ∧ j≤1+(M-1) ∧ 2^(k+1)≤width j a := by
    intro a _ ha
    obtain ⟨j,hj,hjM,hdiv⟩ := free_checkpoint a k
    have hj' : j≤1+(M-1) := by omega
    have hsum : j+((1+(M-1))-j)=1+(M-1) := by omega
    have hW : 0<width j a := width_pos_earlier a j ((1+(M-1))-j) hj (by rwa [hsum])
    obtain ⟨t,ht⟩ := hdiv
    have htpos : 0<t := by
      by_cases hz : t=0
      · simp [hz] at ht; omega
      · omega
    have hWge : 2^(k+1)≤width j a := by
      rw [ht]
      exact Nat.le_mul_of_pos_right _ htpos
    exact ⟨j,by omega,hj',hWge⟩
  have h0 := live_budget (2^(k+1)) 1 0 (M-1) (by omega) (hhit 0)
  have h1 := live_budget (2^(k+1)) 1 1 (M-1) (by omega) (hhit 1)
  rw [width_one] at h0 h1
  simp [ind] at h0 h1
  rw [Nat.mul_add]
  omega

/-- With a positive prefix at every length, the width cannot be bounded. -/
theorem infinite_survival_unbounded (n B : Nat)
    (h : ∀ K, 0<K → 0<width K n) : ∃ K, 0<K ∧ B≤width K n := by
  obtain ⟨K,hK,_,hdiv⟩ := free_checkpoint n B
  obtain ⟨t,ht⟩ := hdiv
  have hw := h K hK
  have htpos : 0<t := by
    by_cases hz : t=0
    · simp [hz] at ht; omega
    · omega
  have hp (a : Nat) : a≤2^(a+1) := by
    induction a with
    | zero => omega
    | succ a ih =>
      have hpos := Nat.two_pow_pos (a+1)
      change a+1≤2^(a+1+1)
      rw [Nat.pow_succ]
      omega
  have hpow := hp B
  refine ⟨K,hK,Nat.le_trans hpow ?_⟩
  rw [ht]
  exact Nat.le_mul_of_pos_right _ htpos

#print axioms leaves_mem_iff
#print axioms live_budget
#print axioms survival_bound
#print axioms infinite_survival_unbounded
end BB6.P1CarryExtinction
