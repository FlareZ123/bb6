import BitEventWord
namespace BB6.Agent12BitEventSummary
open BB6.Agent12WordBlock BB6.Agent12StreakWord BB6.Agent12BitPlanes BB6.Agent12BitEventWord

theorem bit_le_one (q j : Nat) : bit q j≤1 := by unfold bit; cases q.testBit j <;> decide

theorem bit_xor (x y j : Nat) : bit (x^^^y) j=(bit x j+bit y j)%2 := by
  unfold bit
  simp only [Nat.testBit_xor]
  cases x.testBit j <;> cases y.testBit j <;> decide

theorem value_mod_two (ps : List Nat) (j : Nat) : value ps j%2=bit (ps.headD 0) j := by
  cases ps with
  | nil => simp [value,bit]
  | cons p ps => simp only [value,List.headD_cons]; have h:=bit_le_one p j; omega

def massAt (m N : Nat) (counts : List Nat) (j : Nat) : Nat := m+3*(N-j)+value counts j

def parityMask (m N : Nat) (counts indices : List Nat) : Nat :=
  (counts.headD 0 ^^^ indices.headD 0 ^^^ (if (m+N)%2=1 then 2^N-1 else 0)) &&& (2^N-1)

theorem bit_full (N j : Nat) (hj : j<N) : bit (2^N-1) j=1 := by simp [bit,hj]

theorem parityMask_sound (m N : Nat) (counts indices : List Nat) (hi : indexCheck N indices) (j : Nat) (hj : j<N) :
    bit (parityMask m N counts indices) j=massAt m N counts j%2 := by
  simp only [parityMask,bit_and,bit_xor,bit_full N j hj,Nat.mul_one,←value_mod_two]
  rw [index_sound N indices hi j hj]
  have h : bit (if (m+N)%2=1 then 2^N-1 else 0) j=(m+N)%2 := by
    by_cases hm : (m+N)%2=1
    · simp [hm,bit_full N j hj]
    · have hm0 : (m+N)%2=0 := by omega
      simp [hm0,bit]
  rw [h]
  unfold massAt
  omega

/-- At boundary j, p records the parity of the most recent event; bit N
    is the initial parity. Check the entire recurrence with three masks. -/
def parityCheck (m N q p : Nat) (counts indices : List Nat) : Prop :=
  p = (((p>>>1)&&&((2^N-1)^^^q)) ||| (parityMask m N counts indices&&&q)) |||
    (if m%2=1 then 2^N else 0)

theorem parityCheck_top (m N q p : Nat) (counts indices : List Nat) (hq : q<2^N)
    (h : parityCheck m N q p counts indices) : bit p N=m%2 := by
  have he:=congrArg (fun x=>x.testBit N) h
  change p.testBit N=(((p>>>1)&&&((2^N-1)^^^q)) ||| (parityMask m N counts indices&&&q) ||| (if m%2=1 then 2^N else 0)).testBit N at he
  simp only [Nat.testBit_or,Nat.testBit_and,Nat.testBit_xor,Nat.testBit_two_pow_sub_one,Nat.lt_irrefl,decide_false,Nat.testBit_lt_two_pow hq,Bool.false_xor,Bool.and_false,Bool.false_or] at he
  by_cases hm : m%2=1
  · simp [hm] at he; simp [bit,he,hm]
  · have hm0 : m%2=0 := by omega
    simp [hm0] at he; simp [bit,he,hm0]

theorem parityCheck_step (m N q p : Nat) (counts indices : List Nat) (hi : indexCheck N indices)
    (h : parityCheck m N q p counts indices) (j : Nat) (hj : j<N) :
    bit p j=if q.testBit j then massAt m N counts j%2 else bit p (j+1) := by
  have he:=congrArg (fun x=>x.testBit j) h
  change p.testBit j=(((p>>>1)&&&((2^N-1)^^^q)) ||| (parityMask m N counts indices&&&q) ||| (if m%2=1 then 2^N else 0)).testBit j at he
  have hs : (if m%2=1 then 2^N else 0).testBit j=false := by split <;> simp [Nat.testBit_two_pow,show N≠j by omega]
  simp only [Nat.testBit_or,Nat.testBit_and,Nat.testBit_xor,Nat.testBit_two_pow_sub_one,hj,decide_true,Nat.testBit_shiftRight,hs,Bool.or_false] at he
  cases hb:q.testBit j
  · simp [hb] at he
    simp [hb,bit,he,Nat.add_comm]
  · simp [hb] at he
    simpa [hb,bit,he] using parityMask_sound m N counts indices hi j hj

theorem massAt_step (m N q : Nat) (counts : List Nat) (hc : countCheck N q counts) (j : Nat) (hj : j<N) :
    massAt m N counts j=massAt m N counts (j+1)+3+bit q j := by
  have he:=count_rec N q counts hc j
  unfold massAt
  omega

def correction (m N q p : Nat) (counts : List Nat) (j : Nat) : Int :=
  (bit q j:Int)*((m:Int)+3*(N:Int)-3*(j:Int)+(value counts j:Int)-2+2*(bit p (j+1):Int)-(bit p j:Int))

def iwsum : Nat → (Nat→Int) → Int
  | 0,_ => 0
  | n+1,f => iwsum n f+(2:Int)^n*f n

theorem iwsum_congr (n : Nat) (f g : Nat→Int) (h : ∀j<n,f j=g j) : iwsum n f=iwsum n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iwsum]; rw [ih (fun i hi=>h i (by omega)),h n (by omega)]

theorem iwsum_add (n : Nat) (f g : Nat→Int) : iwsum n (fun i=>f i+g i)=iwsum n f+iwsum n g := by
  induction n with
  | zero => simp [iwsum]
  | succ n ih => simp only [iwsum,ih,Int.mul_add]; omega

theorem iwsum_sub (n : Nat) (f g : Nat→Int) : iwsum n (fun i=>f i-g i)=iwsum n f-iwsum n g := by
  induction n with
  | zero => simp [iwsum]
  | succ n ih => simp only [iwsum,ih,Int.mul_sub]; omega

theorem iwsum_mul (n : Nat) (c : Int) (f : Nat→Int) : iwsum n (fun i=>c*f i)=c*iwsum n f := by
  induction n with
  | zero => simp [iwsum]
  | succ n ih => simp only [iwsum,ih,Int.mul_add]; rw [←Int.mul_assoc,Int.mul_comm ((2:Int)^n) c,Int.mul_assoc]

theorem iwsum_cast (n : Nat) (f : Nat→Nat) : iwsum n (fun j=>(f j:Int))=(wsum n f:Int) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iwsum,wsum,ih]; push_cast; rfl

theorem iwsum_bit (N q : Nat) (hq : q<2^N) : iwsum N (fun j=>(bit q j:Int))=(q:Int) := by
  rw [iwsum_cast,wsum_bit,Nat.mod_eq_of_lt hq]

theorem iwsum_plane (N q : Nat) (ps : List Nat) : iwsum N (fun j=>(bit q j:Int)*(value ps j:Int))=(weightedPlanes N q ps:Int) := by
  rw [weightedPlanes_sound,←iwsum_cast]; congr 1

theorem iwsum_mask (N q p : Nat) (hq : q<2^N) : iwsum N (fun j=>(bit q j:Int)*(bit p j:Int))=((p&&&q):Int) := by
  rw [←iwsum_bit N (p&&&q) (Nat.and_lt_two_pow p hq)]; congr 1; funext j; rw [bit_and]; push_cast; ac_rfl

/-- Evaluate all correction terms from O(log N) masks. -/
def correctionFast (m N q p : Nat) (counts indices : List Nat) : Int :=
  ((m:Int)+3*(N:Int)-2)*(q:Int)-3*(weightedPlanes N q indices:Int)+(weightedPlanes N q counts:Int)+2*((p>>>1)&&&q:Nat)-(p&&&q:Nat)

theorem correctionFast_sound (m N q p : Nat) (counts indices : List Nat) (hi : indexCheck N indices) (hq : q<2^N) :
    iwsum N (correction m N q p counts)=correctionFast m N q p counts indices := by
  let f : Nat→Int := fun j => ((m:Int)+3*(N:Int)-2)*(bit q j:Int)-3*((bit q j:Int)*(value indices j:Int))+(bit q j:Int)*(value counts j:Int)+2*((bit q j:Int)*(bit (p>>>1) j:Int))-(bit q j:Int)*(bit p j:Int)
  have hf : iwsum N (correction m N q p counts)=iwsum N f := by
    apply iwsum_congr
    intro j hj
    have hv:=index_sound N indices hi j hj
    have hb : bit (p>>>1) j=bit p (j+1) := by simp [bit,Nat.add_comm]
    dsimp [correction,f]; rw [hv,hb]; grind
  rw [hf]
  dsimp [f,correctionFast]
  rw [iwsum_sub,iwsum_add,iwsum_add,iwsum_sub,iwsum_mul,iwsum_mul,iwsum_mul,iwsum_bit N q hq,iwsum_plane,iwsum_plane,iwsum_mask N q (p>>>1) hq,iwsum_mask N q p hq]

/-- The symbolic walk agrees with the packed closed form for any suffix.
    The proof is induction on the mathematical bit length, not evaluation. -/
theorem walk_summary (m N q p : Nat) (counts indices : List Nat) (hc : countCheck N q counts)
    (hi : indexCheck N indices) (hp : parityCheck m N q p counts indices)
    (k : Nat) (hk : k≤N) (s : BitState) (hm : s.m=massAt m N counts k) (ho : s.o=(bit p k:Int)) :
    walk q k s=⟨(2:Int)^k*s.b-iwsum k (correction m N q p counts),massAt m N counts 0,(bit p 0:Int)⟩ := by
  induction k generalizing s with
  | zero => cases s; simp [walk,iwsum] at hm ho ⊢; exact ⟨hm,ho⟩
  | succ k ih =>
    have hj : k<N := by omega
    have hmass:=massAt_step m N q counts hc k hj
    have hpar:=parityCheck_step m N q p counts indices hi hp k hj
    let t := tick (q.testBit k) s
    have hT : t.m=massAt m N counts k ∧ t.o=(bit p k:Int) ∧ t.b=2*s.b-correction m N q p counts k := by
      cases hb:q.testBit k
      · have hc0 : bit q k=0 := by simp [bit,hb]
        simp only [hb,Bool.false_eq_true,ite_false] at hpar
        simp only [t,tick,hb,Bool.toNat_false,Nat.add_zero,Bool.false_eq_true,ite_false,correction,hc0,Int.natCast_zero,Int.zero_mul,Int.sub_zero]
        exact ⟨by omega,by rw [hpar,ho],trivial⟩
      · have hc1 : bit q k=1 := by simp [bit,hb]
        simp only [hb,ite_true] at hpar
        have hM : s.m+3+1=massAt m N counts k := by omega
        have hp' : ((s.m+3+1:Nat):Int)%2=(bit p k:Int) := by rw [hM,hpar]; omega
        have hcor : ((massAt m N counts k:Nat):Int)=(m:Int)+3*(N:Int)-3*(k:Int)+(value counts k:Int) := by unfold massAt; omega
        simp only [t,tick,hb,Bool.toNat_true,ite_true,correction,hc1,Int.natCast_one,Int.one_mul,hM,hp']
        refine ⟨trivial,by omega,?_⟩
        rw [hcor,ho]; omega
    rw [walk,ih (by omega) t hT.1 hT.2.1]
    simp only [hT.2.2,Int.pow_succ,iwsum]
    congr 1 <;> grind

def fastEndpoint (s : State) (N q p : Nat) (counts indices : List Nat) : State :=
  let m := massAt s.m N counts 0
  ⟨(2:Int)^N*(s.a+2+parity s)-correctionFast s.m N q p counts indices-2-(m:Int)%2,m⟩

theorem fastEndpoint_sound (s : State) (N q p : Nat) (counts indices : List Nat)
    (hN : 0<N) (hq : q<2^N) (hclose : q.testBit 0=true)
    (hc : countCheck N q counts) (hi : indexCheck N indices) (hp : parityCheck s.m N q p counts indices) :
    run (word q 0 N) s=fastEndpoint s N q p counts indices := by
  have htop : (lift s).m=massAt s.m N counts N := by simp [lift,massAt,count_top N q counts hc]
  have hpar : (lift s).o=(bit p N:Int) := by rw [parityCheck_top s.m N q p counts indices hq hp]; simp [lift,parity]
  have hw:=walk_summary s.m N q p counts indices hc hi hp N (by omega) (lift s) htop hpar
  have he:=walk_word q N 0 s (by simp) (fun _=>hclose)
  rw [idle_zero,hw,correctionFast_sound s.m N q p counts indices hi hq] at he
  have hm := congrArg BitState.m he
  have hb := congrArg BitState.b he
  simp only [lift] at hm hb
  simp only [fastEndpoint]
  cases hrun : run (word q 0 N) s with
  | mk a m =>
    simp only [hrun] at hm hb
    simp only [State.mk.injEq]
    refine ⟨?_,hm.symm⟩
    unfold parity at hb ⊢
    simp only [State.m] at hm hb
    rw [←hm] at hb
    omega

#print axioms parityCheck_step
#print axioms correctionFast_sound
#print axioms walk_summary
#print axioms fastEndpoint_sound
end BB6.Agent12BitEventSummary
