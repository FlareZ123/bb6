import F421SecondaryFar

namespace F421SecondaryLifetimes
open F421TertiaryGuard
open BB6Coverage.Agent41F421.EpochWords

/-- An arbitrary-length far prefix with full secondary-cycle P budgets. -/
def protectP (k B : Nat) : List PC → Prop
  | [] => True
  | c::cs => 2*B*k+3≤c.p ∧ protectP k (2*B) cs

/-- Exact position-dependent P update with unchanged Q coordinates. -/
def decAt (k B : Nat) : List PC → List PC
  | [] => []
  | c::cs => ⟨c.p-2*B*k,c.q⟩::decAt k (2*B) cs

theorem decAtZero (B : Nat) (ps : List PC) : decAt 0 B ps=ps := by
  induction ps generalizing B with
  | nil => rfl
  | cons c ps ih => simp only [decAt,Nat.mul_zero,Nat.sub_zero,ih]

theorem decAtLength (k B : Nat) (ps : List PC) : (decAt k B ps).length=ps.length := by
  induction ps generalizing B with
  | nil => rfl
  | cons c ps ih => simp [decAt,ih]

theorem trimQAppend (B : Nat) (ps tail : List PC) :
    trimQ B (ps++tail)=trimQ B ps++trimQ (B*2^ps.length) tail := by
  induction ps generalizing B with
  | nil => simp [trimQ]
  | cons c ps ih =>
    simp only [List.cons_append,trimQ,List.length_cons,List.cons.injEq,eq_self_iff_true,true_and]
    rw [ih]
    congr 1
    simp only [Nat.pow_succ]
    ac_rfl

def drainPrefix (B : Nat) : List PC → List PC
  | [] => []
  | c::cs => ⟨c.p-2*B,c.q+B⟩::drainPrefix (2*B) cs

theorem drainPrefixLength (B : Nat) (ps : List PC) :
    (drainPrefix B ps).length=ps.length := by
  induction ps generalizing B with
  | nil => rfl
  | cons c ps ih => simp [drainPrefix,ih]

theorem trimPrefix (B : Nat) (ps : List PC) :
    trimQ B (drainPrefix B ps) = decAt 1 B ps := by
  induction ps generalizing B with
  | nil => rfl
  | cons c ps ih =>
    simp only [drainPrefix,trimQ,decAt,Nat.mul_one]
    rw [show c.q+B-B=c.q by omega]
    exact congrArg (List.cons ⟨c.p-2*B,c.q⟩) (ih (2*B))

/-- Original source drain, including all terminal deletions in the arbitrary
    suffix, has an exact untouched-Q protected prefix. -/
theorem drainAProtectP (B : Nat) (ps tail : List PC)
    (hB : 0<B) (hp : protectP 1 B ps) :
    let (as,H,r) := drain (B*2^ps.length-1) 0 (dec tail)
    drain (B-1) 0 (dec (ps++tail)) =
      ((drainPrefix B ps)++as,H,r) := by
  induction ps generalizing B with
  | nil =>
    rcases he : drain (B-1) 0 (dec tail) with ⟨as,H,r⟩
    simp [drainPrefix,he]
  | cons c ps ih =>
    have hq : 2*B+3≤c.p := by simpa [protectP] using hp.1
    have ht : protectP 1 (2*B) ps := hp.2
    have hB' : 0<2*B := by omega
    have hcap : 2*(B-1)+1=2*B-1 := by omega
    have hnot : ¬c.p-1≤2*(B-1)+1 := by omega
    rcases he : drain ((2*B)*2^ps.length-1) 0 (dec tail) with ⟨as,H,r⟩
    have h := ih (2*B) hB' ht
    rw [he] at h
    simp only [dec,List.map_append,List.map_cons,drain,ite_eq_right hnot,
      List.length_cons,Nat.pow_succ,drainPrefix,List.cons_append]
    have hpar : B*2^(ps.length+1)=(2*B)*2^ps.length := by rw [Nat.pow_succ]; ac_rfl
    rw [show B*(2^ps.length*2)=(2*B)*2^ps.length by ac_rfl]
    simp only [hcap]
    simp only [Nat.add_zero]
    have hmap : List.map (fun c : PC => ⟨c.p-1,c.q⟩) ps ++
        List.map (fun c : PC => ⟨c.p-1,c.q⟩) tail = dec (ps++tail) := by
      simp [dec,List.map_append]
    rw [hmap]
    change ({ p := c.p-1-(2*B-1), q := c.q+(B-1)+1 } ::
      (drain (2*B-1) 0 (dec (ps++tail))).1,
      (drain (2*B-1) 0 (dec (ps++tail))).2.1,
      (drain (2*B-1) 0 (dec (ps++tail))).2.2) = _
    have h' : drain (2*B-1) 0 (dec (ps++tail)) =
        (drainPrefix (2*B) ps++as,H,r) := by simpa using h
    rw [h']
    have he' : drain (2*B*2^ps.length-1) 0
       (List.map (fun c : PC => ⟨c.p-1,c.q⟩) tail)=(as,H,r) := by simpa only [dec] using he
    rw [he']
    simp only [Prod.fst,Prod.snd]
    have hpEq : c.p-1-(2*B-1)=c.p-2*B := by omega
    have hqEq : c.q+(B-1)+1=c.q+B := by omega
    rw [hpEq,hqEq]

/-- One whole original-source secondary cycle preserves any protected prefix. -/
theorem sourceProtectPOne (b : Nat) (ps tail : List PC) (hp : protectP 1 1 ps) :
    ∃ a' b' rest, sNext b (ps++tail) =
      (a',b',decAt 1 1 ps++rest) := by
  have h := drainAProtectP 1 ps tail (by decide) hp
  rcases he : drain (2^ps.length-1) 0 (dec tail) with ⟨as,H,r⟩
  simp only [Nat.one_mul] at h
  rw [he] at h
  simp only [Nat.sub_self] at h
  refine ⟨4*2^((drainPrefix 1 ps).length+as.length)-1,
     6*2^((drainPrefix 1 ps).length+as.length)-1,
     trimQ (2^ps.length) as++[⟨4*2^(ps++tail).length,
       b+1+H+r-2^((drainPrefix 1 ps).length+as.length)⟩],?_⟩
  unfold sNext
  have hd : drain 0 0 (dec (ps++tail)) =
      (drainPrefix 1 ps++as,H,r) := by
    simpa only [Nat.one_mul,Nat.sub_self,Nat.zero_add] using h
  rw [hd]
  simp only [Prod.fst,Prod.snd,trimQAppend,List.length_append,drainPrefixLength]
  rw [trimPrefix 1 ps]
  simp only [Nat.one_mul,Nat.pow_zero,Nat.mul_one,Nat.add_zero]
  simp only [List.append_assoc]

theorem protectPDecrease (k B : Nat) (ps : List PC)
    (hp : protectP (k+1) B ps) : protectP 1 B ps := by
  induction ps generalizing B with
  | nil => trivial
  | cons c ps ih =>
    have hcb : 2*B*(k+1)+3≤c.p := hp.1
    refine ⟨?_,ih (2*B) hp.2⟩
    have hmul : 2*B*(k+1)=2*B*k+2*B := by rw [Nat.mul_succ]
    rw [hmul] at hcb
    change 2*B*1+3≤c.p
    omega

theorem protectPStep (k B : Nat) (ps : List PC)
    (hp : protectP (k+1) B ps) :
    protectP k B (decAt 1 B ps) := by
  induction ps generalizing B with
  | nil => trivial
  | cons c ps ih =>
    have hcb : 2*B*(k+1)+3≤c.p := hp.1
    change 2*B*k+3≤c.p-2*B*1 ∧ protectP k (2*B) (decAt 1 (2*B) ps)
    constructor
    · have hmul : 2*B*(k+1)=2*B*k+2*B := by rw [Nat.mul_succ]
      rw [hmul] at hcb
      omega
    · exact ih (2*B) hp.2

theorem decAtCompose (k B : Nat) (ps : List PC)
    (hp : protectP (k+1) B ps) :
    decAt k B (decAt 1 B ps)=decAt (k+1) B ps := by
  induction ps generalizing B with
  | nil => rfl
  | cons c ps ih =>
    have hcb : 2*B*(k+1)+3≤c.p := hp.1
    simp only [decAt]
    rw [ih (2*B) hp.2]
    have hmul : 2*B*(k+1)=2*B*k+2*B := by rw [Nat.mul_succ]
    rw [hmul] at hcb ⊢
    have hP : c.p - 2*B*1 - 2*B*k = c.p - (2*B*k+2*B) := by omega
    simp only [hP]

/-- The exact source primary-state invariant for arbitrary protected far
    suffix width, independent of all Q values and tail deletion patterns. -/
theorem sourceProtectedIter (k a b : Nat) (ps tail : List PC)
    (hp : protectP k 1 ps) :
    ∃ a' b' rest, sIter k (a,b,ps++tail) =
      (a',b',decAt k 1 ps++rest) := by
  induction k generalizing a b ps tail with
  | zero =>
    refine ⟨a,b,tail,?_⟩
    simp [sIter,decAtZero]
  | succ k ih =>
    have h1 : protectP 1 1 ps := protectPDecrease k 1 ps hp
    obtain ⟨a1,b1,tail1,he⟩ := sourceProtectPOne b ps tail h1
    have hstep : protectP k 1 (decAt 1 1 ps) := protectPStep k 1 ps hp
    obtain ⟨a2,b2,tail2,ht⟩ := ih a1 b1 (decAt 1 1 ps) tail1 hstep
    refine ⟨a2,b2,tail2,?_⟩
    simp only [sIter]
    rw [he,ht,decAtCompose k 1 ps hp]

#print axioms drainAProtectP
#print axioms sourceProtectPOne
#print axioms decAtCompose
#print axioms sourceProtectedIter
end F421SecondaryLifetimes
