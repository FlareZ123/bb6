import LaneWord
namespace BB6.Agent12LaneCertificate
open BB6.Agent12WordBlock BB6.Agent12BitEventWord BB6.Agent12BitPlanes BB6.Agent12PlaneOps BB6.Agent12BitEventSummary BB6.Agent12LaneWord

structure Trace where
  bs : List Nat
  ms : List Nat
  p : Nat
  counts : List Nat
  deriving Repr

def lane (v : Trace) (j : Nat) : BitState := ⟨(value v.bs j : Int), value v.ms j, (bit v.p j : Int)⟩

def inputs (q N : Nat) := ((q ||| 2^N) >>> 1) <<< 1

def directInputs (q N : Nat) := inputs q N &&& (q <<< 1)
def bounceInputs (q N : Nat) := inputs q N &&& ((2^(N+1)-1) ^^^ (q <<< 1))

theorem inputs_bit (q N j : Nat) (hj:0<j) (he:j=N ∨ q.testBit j=true) : (inputs q N).testBit j=true := by
  simp only [inputs,Nat.testBit_shiftLeft,Nat.testBit_shiftRight,Nat.testBit_or,Nat.testBit_two_pow]
  have h : 1+(j-1)=j := by omega
  rw [h]
  simp [show 1≤j by omega]
  rcases he with h|h <;> simp [h]

theorem directInputs_bit (q N j : Nat) (hj:0<j) (he:j=N ∨ q.testBit j=true) (hd:q.testBit (j-1)=true) : (directInputs q N).testBit j=true := by
  simp [directInputs,Nat.testBit_and,inputs_bit q N j hj he,Nat.testBit_shiftLeft,show 1≤j by omega,hd]

theorem bounceInputs_bit (q N j : Nat) (hj:0<j) (hN:j≤N) (he:j=N ∨ q.testBit j=true) (hd:q.testBit (j-1)=false) : (bounceInputs q N).testBit j=true := by
  simp [bounceInputs,Nat.testBit_and,inputs_bit q N j hj he,Nat.testBit_xor,Nat.testBit_two_pow_sub_one,Nat.testBit_shiftLeft,show 1≤j by omega,show j<N+1 by omega,hd]

def full (N : Nat) := 2^(N+1)-1

def branchRhs (N : Nat) (v : Trace) : List Nat := addP (addP v.ms [0,0,full N]) (mul2 [v.p])

/-- Every condition is an equality or inequality on bitplanes, not a loop
    over the N bit positions. Lists of planes have logarithmic length when
    the trace counters are bounded by a polynomial in N. -/
def checked (s t : State) (N q K : Nat) (v : Trace) : Prop :=
  0<N ∧ q<2^N ∧ q.testBit 0=true ∧
  lane v N=lift s ∧ lane v 0=lift t ∧
  countCheckB N q v.counts=true ∧ value v.counts 0=K ∧
  equalOn (2^N-1) v.ms (addP (addP (shiftP v.ms) [2^N-1,2^N-1]) [q]) ∧
  equalOn q [v.p] [v.ms.headD 0] ∧
  equalOn ((2^N-1)^^^q) [v.p] [v.p>>>1] ∧
  equalOn (2^N-1) (addP (addP v.bs (maskP q v.ms)) (mul2 [q&&&(v.p>>>1)]))
      (addP (addP (mul2 (shiftP v.bs)) (mul2 [q])) [q&&&v.p]) ∧
  leOn (inputs q N) (addP [0,0,full N] [v.p]) v.bs ∧
  leOn (inputs q N) v.bs (addP v.ms [v.p]) ∧
  equalOn (inputs q N) [v.bs.headD 0] [] ∧
  leOn (directInputs q N) (branchRhs N v) (mul2 v.bs) ∧
  leOn (bounceInputs q N) (addP (mul2 v.bs) [full N]) (branchRhs N v) ∧
  leOn q (addP [0,full N] [v.p]) v.bs ∧
  leOn q (addP v.bs [0,full N,full N,full N]) (addP v.ms [v.p])

instance (s t : State) (N q K : Nat) (v : Trace) : Decidable (checked s t N q K v) := by
  unfold checked; infer_instance

theorem bit_full (N j : Nat) (h:j≤N) : bit (full N) j=1 := by simp [full,bit,Nat.testBit_two_pow_sub_one,show j<N+1 by omega]

theorem bit_bounded (N j : Nat) (h:j<N) : bit (2^N-1) j=1 := by simp [bit,Nat.testBit_two_pow_sub_one,h]

theorem bit_shr (p j : Nat) : bit (p>>>1) j=bit p (j+1) := by simp [bit,Nat.testBit_shiftRight,Nat.add_comm]

theorem spec_of_checked (s t : State) (N q K : Nat) (v : Trace) (h:checked s t N q K v) : LaneSpec q N (lane v) := by
  obtain ⟨hN,hq,hclose,hs,ht,hc,hK,hm,hpe,hpn,hb,hi1,hi2,hi3,hid,hib,ho1,ho2⟩:=h
  refine ⟨?_,?_,?_,hclose⟩
  · intro j hj
    have hf : (2^N-1).testBit j=true := by simp [Nat.testBit_two_pow_sub_one,hj]
    have hmass:=equalOn_sound _ _ _ hm j hf
    have hB:=equalOn_sound _ _ _ hb j hf
    simp only [addP_sound,value_shiftP,value_mul2,value_maskP,value,bit_bounded N j hj,bit_and,bit_shr] at hmass hB
    cases he:q.testBit j
    · have hn : ((2^N-1)^^^q).testBit j=true := by simp [Nat.testBit_xor,hf,he]
      have hp:=equalOn_sound _ _ _ hpn j hn
      simp only [value,bit_shr] at hp
      simp only [bit,he,Bool.toNat_false,Nat.zero_mul,Nat.mul_zero,Nat.add_zero] at hmass hB
      simp only [lane,tick,he,Bool.false_eq_true,ite_false,Bool.toNat_false,BitState.mk.injEq]
      refine ⟨by omega,by omega,by omega⟩
    · have hp:=equalOn_sound _ _ _ hpe j he
      simp only [value] at hp
      have hpar:=value_mod_two v.ms j
      have hq1:bit q j=1 := by simp [bit,he]
      simp only [hq1,Nat.one_mul,Nat.mul_one] at hmass hB
      simp only [lane,tick,he,ite_true,Bool.toNat_true,BitState.mk.injEq]
      refine ⟨?_,by omega,?_⟩ <;> omega
  · intro j hj hN' he
    have hmask:=inputs_bit q N j hj he
    have hf:=bit_full N j hN'
    have h1:=leOn_sound _ _ _ hi1 j hmask
    have h2:=leOn_sound _ _ _ hi2 j hmask
    have h3:=equalOn_sound _ _ _ hi3 j hmask
    simp only [value,Nat.mul_zero,Nat.add_zero] at h3
    have hpar:=value_mod_two v.bs j
    simp only [addP_sound,value,hf] at h1 h2
    have hzero:bit 0 j=0 := by simp [bit]
    simp only [hzero,Nat.zero_add,Nat.mul_zero,Nat.add_zero] at h1 h2
    unfold inputOK lane
    dsimp
    refine ⟨by omega,by omega,by omega,?_⟩
    cases hd:q.testBit (j-1)
    · have hh:=leOn_sound _ _ _ hib j (bounceInputs_bit q N j hj hN' he hd)
      simp only [branchRhs,addP_sound,value_mul2,value,hf,hzero,Nat.zero_add,Nat.mul_zero,Nat.add_zero] at hh
      simp only [hd,Bool.false_eq_true,ite_false]; omega
    · have hh:=leOn_sound _ _ _ hid j (directInputs_bit q N j hj he hd)
      simp only [branchRhs,addP_sound,value_mul2,value,hf,hzero,Nat.zero_add,Nat.mul_zero,Nat.add_zero] at hh
      simp only [hd,ite_true]; omega
  · intro j hj he
    have hf:=bit_full N j (by omega)
    have h1:=leOn_sound _ _ _ ho1 j he
    have h2:=leOn_sound _ _ _ ho2 j he
    have hzero:bit 0 j=0 := by simp [bit]
    simp only [addP_sound,value,hf,hzero,Nat.zero_add,Nat.mul_zero,Nat.add_zero] at h1 h2
    unfold outputOK lane
    dsimp
    exact ⟨by omega,by omega⟩

theorem lane_certificate (next : Nat×Nat→Option (Nat×Nat)) (law : EdgeLaw next)
    (s t : State) (N q K : Nat) (v : Trace) (h:checked s t N q K v) :
    runNext next K (some (decode s))=some (decode t) := by
  have spec := spec_of_checked s t N q K v h
  obtain ⟨hN,hq,hclose,hs,ht,hc,hK,_⟩:=h
  have hc' := countCheckB_sound N q v.counts hc
  have hcnt:=word_count q N 0 v.counts N (by omega) hc'
  rw [count_top N q v.counts hc',Nat.add_zero,hK] at hcnt
  have hw:=lane_word next law q N (lane v) spec N 0 s (by omega) (by simpa using hs)
      (Or.inl (by omega)) (by simpa [idle_zero] using hs) (by omega) (by simp)
  have he : run (word q 0 N) s=t := by
    rw [ht] at hw
    have hM:=congrArg BitState.m hw.2
    have hB:=congrArg BitState.b hw.2
    simp only [lift] at hM hB
    have hA : t.a=(run (word q 0 N) s).a := by unfold parity at hB; omega
    have hEq : ∀ u w : State, u.a=w.a → u.m=w.m → u=w := by
      intro u w ha hm; cases u; cases w; simp_all
    exact hEq _ _ hA.symm hM.symm
  rw [hcnt,he] at hw
  exact hw.1

#print axioms spec_of_checked
#print axioms lane_certificate
end BB6.Agent12LaneCertificate
