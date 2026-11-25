import Lean

namespace BB6.Agent19ShadowBits

set_option maxHeartbeats 400000

def base (m : Nat) := 211*(m/2)+108
def nextM (m d : Nat) := m+3*d+1
def num (m x d : Nat) := x+base m+211*(nextM m d%2)

/-- Exact same positive-cost edge as Agent19Scalar.Step, in divisibility form. -/
def Edge (m x d m' x' : Nat) : Prop :=
  0<d ∧ m'=nextM m d ∧ 2^d*x'=num m x d

theorem edge_parity {m x d m' x' : Nat} (h : Edge m x d m' x') :
    m'%2=(x+base m)%2 := by
  obtain ⟨hd,rfl,he⟩ := h
  have he' := congrArg (·%2) he
  have hd' : d=d-1+1 := by omega
  have hp : (2:Nat)^d%2=0 := by
    conv => lhs; rw [hd',Nat.pow_succ]
    simp
  rw [Nat.mul_mod,hp,Nat.zero_mul,Nat.zero_mod] at he'
  unfold num at he'
  omega

inductive Full (m0 x0 : Nat) : Nat → Nat → Nat → Prop where
  | zero : Full m0 x0 0 m0 x0
  | snoc {p m x d m' x'} :
      Full m0 x0 p m x → Edge m x d m' x' → Full m0 x0 (p+d) m' x'

/-- An unfinished last gap: all but its final bit has been consumed. -/
def Pending (m0 x0 n m z : Nat) : Prop :=
  ∃ p a b d, Full m0 x0 p a b ∧ 2≤d ∧ p+d=n+1 ∧
    m=nextM a d ∧ 2^(d-1)*z=num a b d

theorem num_extend (m x d : Nat) : num m x (d+2)=num m x d := by
  unfold num nextM
  omega

theorem full_succ_iff (m0 x0 n m x : Nat) :
    Full m0 x0 (n+1) m x ↔
      (∃ a b, Full m0 x0 n a b ∧ m=nextM a 1 ∧ 2*x=num a b 1) ∨
      Pending m0 x0 n m (2*x) := by
  constructor
  · intro h
    generalize hk : n+1=k at h
    cases h with
    | zero => omega
    | snoc h0 he =>
      obtain ⟨hd,hm,heq⟩ := he
      rename_i p a b d
      by_cases hd1 : d=1
      · subst d
        left
        exact ⟨a,b,show Full m0 x0 n a b from (show p=n by omega) ▸ h0,hm,by simpa using heq⟩
      · right
        refine ⟨p,a,b,d,h0,by omega,by omega,hm,?_⟩
        have hd' : d=d-1+1 := by omega
        rw [←Nat.mul_assoc,←Nat.pow_succ]
        exact (show d=(d-1).succ by omega) ▸ heq
  · rintro (⟨a,b,h0,hm,hq⟩|⟨p,a,b,d,h0,hd,hp,hm,hq⟩)
    · exact Full.snoc h0 ⟨by decide,hm,by simpa using hq⟩
    · rw [←hp]
      apply Full.snoc h0
      refine ⟨by omega,hm,?_⟩
      have hd' : d=d-1+1 := by omega
      rw [←Nat.mul_assoc,←Nat.pow_succ] at hq
      exact (show (d-1).succ=d by omega) ▸ hq

theorem pending_succ_iff (m0 x0 n m z : Nat) :
    Pending m0 x0 (n+1) m z ↔
      (∃ a b, Full m0 x0 n a b ∧ m=nextM a 2 ∧ 2*z=num a b 2) ∨
      (0<n ∧ ∃ a, Full m0 x0 n a (2*z) ∧ m=a+6) := by
  constructor
  · rintro ⟨p,a,b,d,h0,hd,hp,hm,hq⟩
    by_cases h2 : d=2
    · subst d
      left
      have hpn : p=n := by omega
      exact ⟨a,b,hpn ▸ h0,hm,by simpa using hq⟩
    · right
      have hdm : d=d-2+2 := by omega
      have hm' : m=nextM a (d-2)+6 := by unfold nextM at *; omega
      have hn : p+(d-2)=n := by omega
      refine ⟨by omega,nextM a (d-2),?_,hm'⟩
      rw [←hn]
      apply Full.snoc h0
      refine ⟨by omega,rfl,?_⟩
      have hpow : d-1=(d-2)+1 := by omega
      rw [hpow,Nat.pow_succ,Nat.mul_assoc] at hq
      rwa [←num_extend a b (d-2),←hdm]
  · rintro (⟨a,b,h0,hm,hq⟩|⟨hn,a,h0,hm⟩)
    · exact ⟨n,a,b,2,h0,by decide,by omega,hm,by simpa using hq⟩
    · cases h0 with
      | zero => omega
      | snoc hpre he =>
        rename_i p a' b d
        obtain ⟨hd,ha,hq⟩ := he
        refine ⟨p,a',b,d+2,hpre,by omega,by omega,?_,?_⟩
        · unfold nextM at *; omega
        · rw [num_extend,show d+2-1=d+1 by omega,Nat.pow_succ,Nat.mul_assoc]
          exact hq

inductive Node where
  | c : Nat → Nat → Node
  | p : Nat → Nat → Node
  deriving DecidableEq, Repr

def Valid (m0 x0 n : Nat) : Node → Prop
  | .c m x => Full m0 x0 n m x
  | .p m x => Pending m0 x0 n m x

def child (n : Nat) : Node → List Node
  | .c m x =>
      (if num m x 1%2=0 then [.c (nextM m 1) (num m x 1/2)]
        else [.p (nextM m 2) (num m x 2/2)]) ++
      (if n>0 && x%2=0 then [.p (m+6) (x/2)] else [])
  | .p m z => if z%2=0 then [.c m (z/2)] else []

theorem num_parity_flip (m x : Nat) : num m x 1%2+num m x 2%2=1 := by
  unfold num nextM
  omega

theorem valid_child_iff (m0 x0 n : Nat) (v : Node) :
    Valid m0 x0 (n+1) v ↔ ∃ u, Valid m0 x0 n u ∧ v∈child n u := by
  cases v with
  | c m x =>
    rw [Valid,full_succ_iff]
    constructor
    · rintro (⟨a,b,h0,hm,hq⟩|hp)
      · refine ⟨.c a b,h0,?_⟩
        have h : num a b 1%2=0 := by omega
        simp [child,h,hm]
        omega
      · refine ⟨.p m (2*x),hp,?_⟩
        simp [child]
    · rintro ⟨u,hu,hv⟩
      cases u with
      | c a b =>
        by_cases he : num a b 1%2=0
        · left
          have hv' : m=nextM a 1 ∧ x=num a b 1/2 := by
            simp [child,he] at hv
            exact hv
          exact ⟨a,b,hu,hv'.1,by omega⟩
        · simp [child,he] at hv
      | p a b =>
        by_cases he : b%2=0
        · right
          simp [child,he] at hv
          obtain ⟨hm,hx⟩ := hv
          have hb : b=2*x := by omega
          simpa [Valid,←hm,←hb] using hu
        · simp [child,he] at hv
  | p m z =>
    rw [Valid,pending_succ_iff]
    constructor
    · rintro (⟨a,b,h0,hm,hq⟩|⟨hn,a,h0,hm⟩)
      · refine ⟨.c a b,h0,?_⟩
        have h : num a b 2%2=0 := by omega
        have h1 : ¬num a b 1%2=0 := by have := num_parity_flip a b; omega
        simp [child,h1,hm]
        left; omega
      · refine ⟨.c a (2*z),h0,?_⟩
        simp [child,hn,hm]
    · rintro ⟨u,hu,hv⟩
      cases u with
      | p a b =>
        by_cases he : b%2=0 <;> simp [child,he] at hv
      | c a b =>
        by_cases he : num a b 1%2=0
        · simp [child,he] at hv
          right
          obtain ⟨⟨hn,hb⟩,hm,hz⟩ := hv
          refine ⟨hn,a,?_,hm⟩
          have hb' : b=2*z := by omega
          simpa [Valid,←hb'] using hu
        · simp [child,he] at hv
          rcases hv with ⟨hm,hz⟩|⟨⟨hn,hb⟩,hm,hz⟩
          · left
            have h2 : num a b 2%2=0 := by have := num_parity_flip a b; omega
            exact ⟨a,b,hu,hm,by omega⟩
          · right
            refine ⟨hn,a,?_,hm⟩
            have hb' : b=2*z := by omega
            simpa [Valid,←hb'] using hu

def frontier (m x : Nat) : Nat → List Node
  | 0 => [.c m x]
  | n+1 => (frontier m x n).flatMap (child n)

theorem valid_frontier (m x n : Nat) (v : Node) :
    v ∈ frontier m x n ↔ Valid m x n v := by
  induction n generalizing v with
  | zero =>
    cases v with
    | c a b =>
      simp only [frontier,List.mem_singleton,Node.c.injEq,Valid]
      constructor
      · rintro ⟨rfl,rfl⟩
        exact Full.zero
      · intro h
        generalize hk : 0=k at h
        cases h with
        | zero => exact ⟨rfl,rfl⟩
        | snoc h0 he =>
          have := he.1
          omega
    | p a b =>
      simp only [frontier,List.mem_singleton,reduceCtorEq,Valid,false_iff]
      rintro ⟨p,c,d,e,h0,he,hp,hm,hq⟩
      omega
  | succ n ih =>
    simp only [frontier,List.mem_flatMap,valid_child_iff]
    constructor
    · rintro ⟨u,hu,hv⟩
      exact ⟨u,(ih u).mp hu,hv⟩
    · rintro ⟨u,hu,hv⟩
      exact ⟨u,(ih u).mpr hu,hv⟩

#print axioms edge_parity
#print axioms full_succ_iff
#print axioms pending_succ_iff
#print axioms valid_child_iff
#print axioms valid_frontier


/-- A whole word of ordinary costs, without storing intermediate states. -/
def Positive (w : List Nat) : Prop := ∀ d∈w, 0<d
def drift (w : List Nat) : Nat := 3*w.sum+w.length
def acc (m : Nat) : List Nat → Nat
  | [] => 0
  | d::w => base m+211*(nextM m d%2)+2^d*acc (nextM m d) w

theorem acc_append (m : Nat) (w v : List Nat) :
    acc m (w++v)=acc m w+2^w.sum*acc (m+drift w) v := by
  induction w generalizing m with
  | nil => simp [acc,drift]
  | cons d w ih =>
    simp only [List.cons_append,acc,List.sum_cons,Nat.pow_add,ih,Nat.mul_add,Nat.mul_assoc]
    have he : m+drift (d::w)=nextM m d+drift w := by
      simp [drift,nextM,List.sum_cons,Nat.mul_add]
      omega
    rw [he]
    omega

theorem Full.prepend {m0 x0 m1 x1 d p m x : Nat}
    (he : Edge m0 x0 d m1 x1) (h : Full m1 x1 p m x) :
    Full m0 x0 (d+p) m x := by
  induction h with
  | zero => simpa using (Full.snoc (d:=d) Full.zero he)
  | @snoc q a b r a' b' h0 he' ih =>
    rw [←Nat.add_assoc]
    exact Full.snoc ih he'

theorem full_of_word (w : List Nat) (m x : Nat) (hp : Positive w)
    (h : 2^w.sum ∣ x+acc m w) :
    ∃ z, Full m x w.sum (m+drift w) z ∧ 2^w.sum*z=x+acc m w := by
  induction w generalizing m x with
  | nil => exact ⟨x,by simp [drift]; exact Full.zero,by simp [acc]⟩
  | cons d w ih =>
    have hd : 0<d := hp d (by simp)
    have hw : Positive w := fun r hr => hp r (by simp [hr])
    let q := num m x d
    have hsum : x+acc m (d::w)=q+2^d*acc (nextM m d) w := by
      simp [q,num,acc]; omega
    rw [hsum,List.sum_cons,Nat.pow_add] at h
    have hq : 2^d∣q := by
      apply (Nat.dvd_add_iff_left (Nat.dvd_mul_right (2^d) (acc (nextM m d) w))).mpr
      exact Nat.dvd_trans (Nat.dvd_mul_right _ _) h
    obtain ⟨y,hy⟩ := hq
    have hdv : 2^w.sum∣y+acc (nextM m d) w := by
      rw [hy,←Nat.mul_add] at h
      exact (Nat.mul_dvd_mul_iff_left (Nat.two_pow_pos d)).mp h
    obtain ⟨z,hf,he⟩ := ih (nextM m d) y hw hdv
    have hm : m+drift (d::w)=nextM m d+drift w := by
      simp [drift,nextM,Nat.mul_add]; omega
    refine ⟨z,?_,?_⟩
    · rw [hm,List.sum_cons]
      exact Full.prepend ⟨hd,rfl,hy.symm⟩ hf
    · rw [hsum,List.sum_cons,Nat.pow_add,Nat.mul_assoc,he,Nat.mul_add,hy]

def Open (m x n : Nat) : Prop :=
  (∃ w : List Nat, Positive w ∧ w.sum=n ∧ 2^n∣x+acc m w) ∨
  (∃ w : List Nat, ∃ d : Nat, 2≤d ∧ Positive (w++[d]) ∧
    (w++[d]).sum=n+1 ∧ 2^n∣x+acc m (w++[d]))

theorem open_frontier (m x n : Nat) (h : Open m x n) :
    ∃ v, v∈frontier m x n := by
  rcases h with ⟨w,hp,hn,hd⟩|⟨w,d,h2,hp,hn,hd⟩
  · rw [←hn] at hd ⊢
    obtain ⟨z,hf,he⟩ := full_of_word w m x hp hd
    exact ⟨.c (m+drift w) z,(valid_frontier _ _ _ _).mpr hf⟩
  · have hw : Positive w := fun r hr => hp r (by simp [hr])
    have hcost : w.sum+(d-1)=n := by simp [List.sum_append] at hn; omega
    have hacc : x+acc m (w++[d])=x+acc m w+2^w.sum*(base (m+drift w)+211*(nextM (m+drift w) d%2)) := by
      rw [acc_append]; simp [acc]; omega
    rw [hacc,←hcost,Nat.pow_add] at hd
    have hpre : 2^w.sum∣x+acc m w := by
      apply (Nat.dvd_add_iff_left (Nat.dvd_mul_right _ _)).mpr
      exact Nat.dvd_trans (Nat.dvd_mul_right _ _) hd
    obtain ⟨z,hf,he⟩ := full_of_word w m x hw hpre
    rw [←he,←Nat.mul_add] at hd
    have hd' := (Nat.mul_dvd_mul_iff_left (Nat.two_pow_pos w.sum)).mp hd
    obtain ⟨y,hy⟩ := hd'
    refine ⟨.p (nextM (m+drift w) d) y,(valid_frontier _ _ _ _).mpr ?_⟩
    exact ⟨w.sum,m+drift w,z,d,hf,h2,by omega,rfl,by unfold num; omega⟩

/-- Signed coordinates used by the original-source inverse reachability lemma. -/
def P (n : Nat) : Int := 2^n
def shift (r : Nat) : Int := 3*(r:Int)+1
def signedOffset (S : Int) (r : Nat) : Int := (S+S%2)/2+1-(S+shift r)%2
def signedAcc (S : Int) : List Nat → Int
  | [] => 0
  | r::w => signedOffset S r+P r*signedAcc (S+shift r) w
def mask : List Nat → Int
  | [] => 0
  | r::w => 1+P r*mask w

theorem signed_offset_scale (m r q : Nat) (S k : Int)
    (hS : 211*S=5+211*(m:Int)+P (q+1)*k) :
    211*signedOffset S r=(base m:Int)+211*((nextM m r%2:Nat):Int)+P q*k := by
  have hpow : P (q+1)*k=2*(P q*k) := by
    unfold P
    rw [Int.pow_succ]
    ac_rfl
  rw [hpow] at hS
  have hp : S%2=((m+1)%2:Nat) := by omega
  have hp' : (S+shift r)%2=((nextM m r+1)%2:Nat) := by
    unfold shift nextM
    omega
  have hbase : 2*(base m:Int)=5+211*(m:Int)+211*((m+1)%2:Nat) := by
    unfold base
    simp
    omega
  have heven : 2*((S+S%2)/2)=S+S%2 := by omega
  have hhalf : 2*(211*((S+S%2)/2))=211*S+211*(S%2) := by
    rw [Int.mul_left_comm 2 211,heven,Int.mul_add]
  have hscale : 211*((S+S%2)/2)=(base m:Int)+P q*k := by
    have he : 2*(211*((S+S%2)/2))=2*((base m:Int)+P q*k) := by
      rw [hhalf,hS,hp,Int.mul_add,hbase]
      ac_rfl
    clear hS hp hp' hbase heven hhalf hpow
    omega
  have hflip (t : Nat) : (↑((t+1)%2):Int)=1-(↑(t%2):Int) := by
    omega
  unfold signedOffset
  rw [hp',hflip,Int.mul_sub,Int.mul_add,hscale]
  clear hS hp hp' hbase heven hhalf hpow hscale hflip
  omega

theorem signed_acc_scale (w : List Nat) (m q : Nat) (S k : Int)
    (hS : 211*S=5+211*(m:Int)+P (q+1)*k) :
    211*signedAcc S w=(acc m w:Int)+P q*k*mask w := by
  induction w generalizing m S with
  | nil => simp [signedAcc,acc,mask]
  | cons r w ih =>
    have hS' : 211*(S+shift r)=5+211*(nextM m r:Int)+P (q+1)*k := by
      unfold shift nextM
      simp only [Int.natCast_add,Int.natCast_mul]
      omega
    have hs := signed_offset_scale m r q S k hS
    have ht := ih (nextM m r) (S+shift r) hS'
    simp only [signedAcc,acc,mask,Int.natCast_add,Int.natCast_mul,Int.natCast_pow]
    rw [Int.mul_add,Int.mul_left_comm 211 (P r),hs,ht,Int.mul_add,Int.mul_add,Int.mul_one]
    unfold P
    simp
    ac_rfl

theorem signed_word_transfer (m x q : Nat) (S Z k l : Int) (w : List Nat)
    (hS : 211*S=5+211*(m:Int)+P (q+1)*k)
    (hZ : 211*Z=(x:Int)+P q*l)
    (hd : P q∣Z+signedAcc S w) :
    2^q∣x+acc m w := by
  have hs := signed_acc_scale w m q S k hS
  obtain ⟨v,hv⟩ := hd
  have he : (x+acc m w:Int)=P q*(211*v-l-k*mask w) := by
    have hmul := congrArg (fun t : Int => 211*t) hv
    rw [Int.mul_add,hZ,hs] at hmul
    calc
      _ = 211*(P q*v)-P q*l-P q*k*mask w := by
        clear hS hZ hs hv
        omega
      _ = _ := by
        rw [Int.mul_sub,Int.mul_sub]
        congr 1
        congr 1
        · ac_rfl
        · exact Int.mul_assoc _ _ _
  have hdi : P q∣(x+acc m w:Int) := ⟨_,he⟩
  unfold P at hdi
  exact_mod_cast hdi

def SignedOpen (S Z : Int) (n : Nat) : Prop :=
  (∃ w : List Nat, Positive w ∧ w.sum=n ∧ P n∣Z+signedAcc S w) ∨
  (∃ w : List Nat, ∃ d : Nat, 2≤d ∧ Positive (w++[d]) ∧
    (w++[d]).sum=n+1 ∧ P n∣Z+signedAcc S (w++[d]))

theorem signed_open_frontier (m x n : Nat) (S Z k l : Int)
    (hS : 211*S=5+211*(m:Int)+P (n+1)*k)
    (hZ : 211*Z=(x:Int)+P n*l)
    (ho : SignedOpen S Z n) : ∃ v, v∈frontier m x n := by
  apply open_frontier
  rcases ho with ⟨w,hp,hn,hd⟩|⟨w,d,h2,hp,hn,hd⟩
  · exact Or.inl ⟨w,hp,hn,signed_word_transfer m x n S Z k l w hS hZ hd⟩
  · exact Or.inr ⟨w,d,h2,hp,hn,signed_word_transfer m x n S Z k l (w++[d]) hS hZ hd⟩

#print axioms full_of_word
#print axioms open_frontier
#print axioms signed_offset_scale
#print axioms signed_acc_scale
#print axioms signed_word_transfer
#print axioms signed_open_frontier


end BB6.Agent19ShadowBits
