import BatchPacking
import BatchCarrySource
namespace BB6.Agent9BatchCarry
open BB6.P1CarryExact BB6.P1CarryExtinction

theorem wordSum_eq_sum (k : Nat) (f : List Bool → Nat) :
    wordSum k f = ((words k).map f).sum := by
  induction k generalizing f with
  | zero => simp [wordSum,words]
  | succ k ih =>
    simp [wordSum,words,ih,List.map_map,Function.comp_def]

theorem sum_ind_eq_length_filter {α : Type} (l : List α) (p : α → Bool) :
    (l.map fun x => if p x then 1 else 0).sum=(l.filter p).length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    cases h : p x <;> simp [h,ih,Nat.add_comm]

theorem expr_center (n : Nat) (xs : List Bool) (he : n%2=0) :
    expr n xs=1+2*(center (n+4)+weightSum (n+4) xs) := by
  rw [expr_eq,show n+4=n+3+1 by omega,weightSum_eq]
  unfold center
  omega

theorem one_add_two_mod (a M : Nat) (hM : 0<M) :
    (1+2*a)%(2*M)=1+2*(a%M) := by
  have h := Nat.mod_add_div a M
  have hrem := Nat.mod_lt a hM
  have he : 1+2*a = 1+2*(a%M)+(2*M)*(a/M) := by
    calc
      _ = 1+2*(a%M+M*(a/M)) := by rw [h]
      _ = _ := by rw [Nat.mul_add]; ac_rfl
  rw [he,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (by omega)]

theorem expr_mod_iff (n K : Nat) (xs : List Bool) (he : n%2=0) (hK : 0<K) :
    expr n xs%2^K=1 ↔ (center (n+4)+weightSum (n+4) xs)%2^(K-1)=0 := by
  rw [expr_center n xs he]
  have hp : 2^K=2*2^(K-1) := by
    have h : K=K-1+1 := by omega
    calc
      _ = 2^(K-1+1) := congrArg (fun t => 2^t) h
      _ = _ := by rw [Nat.pow_succ,Nat.mul_comm]
  rw [hp,one_add_two_mod _ _ (Nat.two_pow_pos _)]
  omega

/-- The actual source word count is exactly the number of distinct terminal
carries of the central birth, for any positive horizon. -/
theorem centerEnds_length (F n : Nat) (hF : n+4≤F) (he : n%2=0) :
    (centerEnds F n).length=width (F-(n+3)) n := by
  let K := F-(n+3)
  have hK : 0<K := by dsimp [K]; omega
  have hlen : F-(n+4)=K-1 := by dsimp [K]; omega
  unfold centerEnds endpoints validWords width
  rw [List.length_map,hlen]
  rw [wordSum_eq_sum]
  have hf : (words (K-1)).map (fun xs => ind (expr n xs%2^K=1)) =
      (words (K-1)).map (fun xs => if decide ((center (n+4)+weightSum (n+4) xs)%2^(K-1)=0) then 1 else 0) := by
    apply List.map_congr_left
    intro xs _
    simp [ind,expr_mod_iff n K xs he hK]
  change (List.filter _ _).length=((words (K-1)).map _).sum
  rw [hf,sum_ind_eq_length_filter]

/-- A single terminal clock bounds the total source width of arbitrary
nonrepeated even critical indices, even though their horizons differ. -/
theorem width_packing (F : Nat) (ns : List Nat) (hn : ns.Nodup)
    (h : ∀ n∈ns, n+4≤F ∧ n%2=0) :
    (ns.map (fun n => width (F-(n+3)) n)).sum≤F-3 := by
  have hmap : ns.map (fun n => (centerEnds F n).length)=ns.map (fun n => width (F-(n+3)) n) := by
    apply List.map_congr_left
    intro n hn
    exact centerEnds_length F n (h n hn).1 (h n hn).2
  rw [← hmap]
  exact packedEnds_bound F ns hn h

/-- The reflected suffix exchanges the two first-bit sectors exactly. -/
theorem weightSum_compl (q : Nat) (xs : List Bool) (hq : 2≤q) :
    weightSum q xs+weightSum q (xs.map (!·))+(q-2)=(q+xs.length-2)*2^xs.length := by
  induction xs generalizing q with
  | nil => simp [weightSum]
  | cons b bs ih =>
    have h := ih (q+1) (by omega)
    have hcoeff : q+1+bs.length-2=q+(bs.length+1)-2 := by omega
    rw [hcoeff] at h
    simp only [List.map_cons,List.length_cons,weightSum,Nat.pow_succ]
    have hmul : (q+(bs.length+1)-2)*(2^bs.length*2)=2*((q+(bs.length+1)-2)*2^bs.length) := by ac_rfl
    rw [hmul]
    cases b <;> simp <;> omega

theorem compl_valid (n K : Nat) (xs : List Bool) (he : n%2=0) (hK : 0<K)
    (hl : xs.length=K-1) : expr n (xs.map (!·))%2^K=1 ↔ expr n xs%2^K=1 := by
  rw [expr_mod_iff n K _ he hK,expr_mod_iff n K _ he hK]
  let a := center (n+4)+weightSum (n+4) xs
  let b := center (n+4)+weightSum (n+4) (xs.map (!·))
  let M := 2^(K-1)
  have hc : 2*center (n+4)=n+4-2 := by unfold center; omega
  have hs := weightSum_compl (n+4) xs (by omega)
  rw [hl] at hs
  have hsum : a+b=(n+4+(K-1)-2)*M := by dsimp [a,b,M]; omega
  have hmod : (a+b)%M=0 := by rw [hsum]; simp
  rw [Nat.add_mod] at hmod
  have hM : 0<M := Nat.two_pow_pos _
  have ha := Nat.mod_lt a hM
  have hb := Nat.mod_lt b hM
  change b%M=0 ↔ a%M=0
  constructor <;> intro hz
  · rw [hz,Nat.add_zero,Nat.mod_eq_of_lt ha] at hmod; exact hmod
  · rw [hz,Nat.zero_add,Nat.mod_eq_of_lt hb] at hmod; exact hmod

theorem wordSum_compl (k : Nat) (f : List Bool → Nat) :
    wordSum k (fun xs => f (xs.map (!·)))=wordSum k f := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
    simp only [wordSum,List.map_cons,Bool.not_false,Bool.not_true]
    rw [ih (fun xs => f (true::xs)),ih (fun xs => f (false::xs)),Nat.add_comm]

/-- Complement symmetry doubles the free-bit factor, provided at least one
suffix bit precedes the freely togglable suffix. -/
theorem width_half (n K : Nat) (he : n%2=0) (hK : 2≤K) :
    width K n = 2*suffixCount n 2 (K-2) (2^K) (n+3) := by
  have hlen : K-1=K-2+1 := by omega
  unfold width
  rw [hlen,wordSum]
  have heq : wordSum (K-2) (fun xs => ind (expr n (true::xs)%2^K=1))=
      wordSum (K-2) (fun xs => ind (expr n (false::xs)%2^K=1)) := by
    rw [←wordSum_compl (K-2) (fun xs => ind (expr n (true::xs)%2^K=1))]
    apply wordSum_congr
    intro xs hxs
    have hh := compl_valid n K (false::xs) he (by omega) (by simp [hxs]; omega)
    simp only [List.map_cons,Bool.not_false] at hh
    simp [hh]
  rw [heq]
  have hfalse : wordSum (K-2) (fun xs => ind (expr n (false::xs)%2^K=1))=
      suffixCount n 2 (K-2) (2^K) (n+3) := by
    unfold suffixCount
    apply wordSum_congr
    intro xs _
    simp [expr,absSum]
  rw [hfalse]
  omega

theorem common_free_factor (F n k : Nat) (he : n%2=0)
    (hK : dist k+2≤F-(n+3)) (hF : 2^(dist k)∣F-dist k) :
    2^(k+2) ∣ width (F-(n+3)) n := by
  let K := F-(n+3)
  have hK' : dist k+2≤K := hK
  have hk : dist k<K := by omega
  have hclock : n+K+3=F := by dsimp [K]; omega
  have hdiv : 2^(dist k) ∣ n+K+3-dist k := by rw [hclock]; exact hF
  have hfree := dist_free_count n K k hk hdiv
  have hext := freeCount_extend_left n (2^K) 2 (K-dist k-2) (dist k)
  rw [show 2+(K-dist k-2)=K-dist k by omega,show K-dist k-2+dist k=K-2 by omega] at hext
  have hpow : 2^(k+1)∣2^freeCount n (2^K) 2 (K-2) := Nat.pow_dvd_pow 2 (by omega)
  have hd := Nat.dvd_trans hpow (suffixCount_free_dvd n 2 (K-2) (2^K) (n+3))
  obtain ⟨a,ha⟩ := hd
  change 2^(k+2)∣width K n
  rw [width_half n K he (by omega),ha,Nat.pow_succ]
  exact ⟨a,by ac_rfl⟩

theorem sum_map_lower (ns : List Nat) (f : Nat → Nat) (B : Nat)
    (h : ∀ n∈ns, B≤f n) : B*ns.length≤(ns.map f).sum := by
  induction ns with
  | nil => simp
  | cons n ns ih =>
    have hn := h n (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp [Nat.mul_add]
    omega

/-- Non-asymptotic packing bound on surviving even indices at a common clock.
This uses only the free-bit distance congruence at F, not a 2^K-periodic
parameter enumeration. -/
theorem common_survivor_bound (F k : Nat) (ns : List Nat) (hn : ns.Nodup)
    (hF : 2^(dist k)∣F-dist k)
    (h : ∀ n∈ns, n%2=0 ∧ dist k+2≤F-(n+3) ∧ 0<width (F-(n+3)) n) :
    2^(k+2)*ns.length≤F-3 := by
  have hp := width_packing F ns hn (fun n hn => ⟨by have := (h n hn).2.1; omega,(h n hn).1⟩)
  apply Nat.le_trans _ hp
  apply sum_map_lower
  intro n hm
  obtain ⟨he,hK,hw⟩ := h n hm
  obtain ⟨a,ha⟩ := common_free_factor F n k he hK hF
  have ha' : 0<a := by
    by_cases hzero : a=0
    · simp [hzero] at ha; omega
    · omega
  rw [ha]
  exact Nat.le_mul_of_pos_right _ ha'

/-- The same finite bound applies to a list of genuinely blank-reachable
critical reset indices; the source bridge excludes zero width. -/
theorem common_reachable_bound (F k : Nat) (ns : List Nat) (hn : ns.Nodup)
    (hF : 2^(dist k)∣F-dist k)
    (h : ∀ n∈ns, 14≤n ∧ n%2=0 ∧ dist k+2≤F-(n+3) ∧ F≤2*n+3 ∧
      BB6.Agent1.Reach 2 (14*2^n-2*n-10)) : 2^(k+2)*ns.length≤F-3 := by
  apply common_survivor_bound F k ns hn hF
  intro n hm
  obtain ⟨hn,he,hK,hcap,hr⟩ := h n hm
  refine ⟨he,hK,?_⟩
  by_cases hz : width (F-(n+3)) n=0
  · exact False.elim (critical_reset_no_reach_of_empty_full n (F-(n+3)) (by omega) hn (by omega) hz hr)
  · omega

/-- Select one terminal clock close to the upper source-permitted clock.
The interval length loses only dist(k)+2^dist(k)+1, not a full 2^K
period of the old dyadic width estimate. -/
theorem exists_packing_clock (L R k : Nat)
    (h : R+dist k+2^(dist k)+1≤2*L) :
    ∃ F, R+dist k+5≤F ∧ F≤2*L+3 ∧ 2^(dist k)∣F-dist k := by
  let r := dist k
  let M := 2^r
  let U := 2*L+3
  let F := U-((U-r)%M)
  have hM : 0<M := Nat.two_pow_pos _
  have hrem := Nat.mod_lt (U-r) hM
  have hmod := Nat.mod_add_div (U-r) M
  change R+r+M+1≤2*L at h
  refine ⟨F,?_,?_,?_⟩
  · dsimp [F,U]; dsimp [U] at hrem; omega
  · dsimp [F,U]; omega
  · refine ⟨(U-r)/M,?_⟩
    change F-r=M*((U-r)/M)
    dsimp [F]
    omega

/-- Explicit local count for even indices surviving all n modular bits.
This is uniform in the interval's size and location and requires no
residue period of length 2^n. -/
theorem local_n_horizon_bound (L R k : Nat) (ns : List Nat) (hn : ns.Nodup)
    (hspan : R+dist k+2^(dist k)+1≤2*L)
    (h : ∀ n∈ns, L≤n ∧ n≤R ∧ n%2=0 ∧ 0<width n n) :
    2^(k+2)*ns.length≤2*L := by
  obtain ⟨F,hlo,hhi,hdiv⟩ := exists_packing_clock L R k hspan
  have hpack := common_survivor_bound F k ns hn hdiv (by
    intro n hm
    obtain ⟨hnl,hnr,he,hw⟩ := h n hm
    let K := F-(n+3)
    have hk : dist k+2≤K := by dsimp [K]; omega
    have hcap : K≤n := by dsimp [K]; omega
    have hsum : K+(n-K)=n := by omega
    exact ⟨he,hk,width_pos_earlier n K (n-K) (by omega) (by rwa [hsum])⟩)
  omega

/-- A concrete usable shell: the three free distances 1,3,11 plus
complement symmetry force 16 endpoints per surviving critical index. -/
theorem local_n_horizon_bound16 (L R : Nat) (ns : List Nat) (hn : ns.Nodup)
    (hspan : R+2060≤2*L)
    (h : ∀ n∈ns, L≤n ∧ n≤R ∧ n%2=0 ∧ 0<width n n) :
    16*ns.length≤2*L := by
  exact local_n_horizon_bound L R 2 ns hn (by change R+11+2048+1≤2*L; omega) h

#print axioms centerEnds_length
#print axioms width_packing
#print axioms width_half
#print axioms common_free_factor
#print axioms common_survivor_bound
#print axioms common_reachable_bound
#print axioms exists_packing_clock
#print axioms local_n_horizon_bound
#print axioms local_n_horizon_bound16
end BB6.Agent9BatchCarry
