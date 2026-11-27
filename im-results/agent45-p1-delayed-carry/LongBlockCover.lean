import LongBlockWitness
import ReverseLagBlocks
import BitSpread
import BatchCarryChunks
import PairCarryCore
import PackedMidpoint

namespace BB6.Agent45LongBlock
open BB6.Agent45ReverseBlock
open BB6.Agent45.DelayedCarry
open BB6.Agent28BitSpread
open BB6.Agent28BitCarry (laneMask)
open BB6.Agent9PairCarry (spreadWith)
open BB6.Agent9BatchCarry (packList packList_sound)
open BB6.Agent9PackedMidpoint (targetWord_fixed MidpointLive)
open BB6.Agent43PackedRecover (recoverFast recoverFast_exact)

theorem digits_append (xs ys : List Nat) : digits (xs++ys) = digits xs + 2^xs.length*digits ys := by
  induction xs with
  | nil => simp [digits]
  | cons x xs ih =>
    simp only [List.cons_append,List.length_cons,digits,ih,Nat.pow_succ,Nat.mul_add]
    ac_rfl

theorem targetWord_append (n s B k j : Nat) :
    targetWord n s B (k+j) = targetWord n s B k ++ targetWord n (s+k) B j := by
  induction j with
  | zero => simp [targetWord]
  | succ j ih => simp [targetWord,ih,Nat.add_assoc,List.append_assoc]

def targetDigits (n s B k : Nat) := (quotient n s B)%2^k

theorem digits_targetWord (n s B k : Nat) : digits (targetWord n s B k)=targetDigits n s B k := by
  induction k with
  | zero => simp [targetWord,digits,targetDigits,Nat.mod_one]
  | succ k ih =>
    rw [targetWord,digits_append,ih,targetWord_length]
    have hdiv : quotient n (s+k) B = quotient n s B /2^k := by
      unfold quotient
      rw [Nat.pow_add,Nat.div_div_eq_div_mul]
    simp only [digits,Nat.mul_zero,Nat.zero_add,target_eq,targetDigits,hdiv,Nat.pow_succ]
    rw [Nat.mod_mul]

def spreadPlan2 (L : Nat) : Nat → List (Nat×Nat)
  | 0 => []
  | k+1 => (2^k,laneMask (2^k) (L-k))::spreadPlan2 L k

theorem spread_plan_eq (L k x : Nat) :
    spreadWith (spreadPlan2 L k) x = spreadFrom L k x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    simp only [spreadWith,spreadPlan2,List.foldl_cons,spreadFrom,spreadStep]
    exact ih _

def packedBack (plan : List (Nat×Nat)) (q y bits : Nat) : Nat :=
  let u := spreadWith plan bits <<< y
  (u ||| (u >>> q)) &&& (2^q-1)

theorem packedBack_sound (L q y bits z c : Nat)
    (hcap : z<2^L) (hb : bits.testBit z=true)
    (hw : Walk (q+1) z [y] c) :
    (packedBack (spreadPlan2 L L) q y bits).testBit c=true := by
  obtain ⟨B,hB,he⟩ := eq_of_walk hw
  have hr := walk_bound hw
  simp only [List.length_cons,List.length_nil,Nat.zero_add,Nat.add_sub_cancel] at hr hB he
  have hstep : 2*z+y=c+q*B := by
    rcases (show B=0 ∨ B=1 by omega) with h|h <;> simp [h,digits,corr,Nat.add_comm] at he ⊢ <;> omega
  have hbound : 2*z+y<2*q := by
    rcases (show B=0 ∨ B=1 by omega) with h|h <;> simp [h] at hstep <;> omega
  have hmod : (2*z+y)%q=c := by
    rw [hstep,Nat.mul_comm q B,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hr]
  unfold packedBack
  rw [spread_plan_eq]
  change (reverseStep L q y bits).testBit c=true
  rw [←hmod]
  exact reverseStep_sound L q y bits z (by omega) hcap hbound hb

def rewindTarget (plan : List (Nat×Nat)) (n s B : Nat) : Nat → Nat → Nat
  | 0,bits => bits
  | d+1,bits => rewindTarget plan n s B d (packedBack plan (n+s+d+3) (target n (s+d) B) bits)

theorem rewindTarget_sound (L n s B d bits z c : Nat)
    (hcap : n+s+d+3≤2^L) (hb : bits.testBit z=true)
    (hw : Walk (n+s+d+3) z (targetWord n s B d) c) :
    (rewindTarget (spreadPlan2 L L) n s B d bits).testBit c=true := by
  induction d generalizing bits z c with
  | zero =>
    change Walk (n+s+0+3) z [] c at hw
    cases hw
    exact hb
  | succ d ih =>
    change Walk (n+s+(d+1)+3) z (targetWord n s B d ++ [target n (s+d) B]) c at hw
    obtain ⟨a,ht,hp⟩ := walk_split _ _ _ _ _ hw
    have ht' : Walk (n+s+d+3+1) z [target n (s+d) B] a := by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht
    have hzc := start_bound ht'
    have hp' : Walk (n+s+d+3) a (targetWord n s B d) c := by
      simpa [show n+s+(d+1)+3-1=n+s+d+3 by omega] using hp
    exact ih _ _ _ (by omega) (packedBack_sound L _ _ _ z a (by omega) hb ht') hp'

def LiveBits (n B s k bits : Nat) : Prop :=
  ∀ z c, Walk (n+s+k+3) z (targetWord n s B k) c → bits.testBit c=true

def LiveList (n B s k : Nat) (xs : List Nat) : Prop :=
  ∀ z c, Walk (n+s+k+3) z (targetWord n s B k) c → c∈xs

theorem live_bits_init (n B s : Nat) : LiveBits n B s 0 (2^(n+s+3)-1) := by
  intro z c hw
  have hb := walk_bound hw
  rw [Nat.testBit_two_pow_sub_one]
  apply decide_eq_true
  simpa using hb

theorem live_bits_extend (L n B s j d bits out : Nat)
    (hcap : n+s+j+3≤2^L)
    (hOld : LiveBits n B (s+j) d bits)
    (hcalc : rewindTarget (spreadPlan2 L L) n s B j bits=out) :
    LiveBits n B s (j+d) out := by
  intro z c hw
  rw [targetWord_append] at hw
  obtain ⟨a,ht,hp⟩ := walk_split _ _ _ _ _ hw
  have ht' : Walk (n+(s+j)+d+3) z (targetWord n (s+j) B d) a := by simpa [Nat.add_assoc] using ht
  have hp' : Walk (n+s+j+3) a (targetWord n s B j) c := by
    simpa [show n+s+(j+d)+3-d=n+s+j+3 by omega] using hp
  rw [←hcalc]
  exact rewindTarget_sound L n s B j bits a c hcap (hOld z a ht') hp'

theorem live_bits_to_list (n B s k bits : Nat) (xs : List Nat)
    (hOld : LiveBits n B s k bits) (he : bits=packList xs) : LiveList n B s k xs := by
  intro z c hw
  apply (packList_sound xs c).mp
  rw [←he]
  exact hOld z c hw

theorem live_list_extend (L n B s j d : Nat)
    (old new : List Nat) (rows : List WitnessRow)
    (hL : j≤2^L) (hOld : LiveList n B (s+j) d old)
    (hrows : rows.map Prod.fst=old)
    (hcheck : rows.all (rowCheck L (n+s+j+3) j (targetDigits n s B j))=true)
    (hout : packList (rowsOut (n+s+j+3) j rows)=packList new) :
    LiveList n B s (j+d) new := by
  intro z c hw
  rw [targetWord_append] at hw
  obtain ⟨a,ht,hp⟩ := walk_split _ _ _ _ _ hw
  have ht' : Walk (n+(s+j)+d+3) z (targetWord n (s+j) B d) a := by simpa [Nat.add_assoc] using ht
  have hp' : Walk (n+s+j+3) a (targetWord n s B j) c := by
    simpa [show n+s+(j+d)+3-d=n+s+j+3 by omega] using hp
  have ha := hOld z a ht'
  rw [←hrows] at ha
  have hm := rows_cover L (n+s+j+3) (targetWord n s B j) rows
    (by simpa using hL) (by simpa [digits_targetWord] using hcheck) a c ha hp'
  have hb := (packList_sound _ c).mpr hm
  rw [targetWord_length,hout] at hb
  exact (packList_sound new c).mp hb

def recoverFull (n s h : Nat) (ps : List Prefix) (mids : Nat → List Nat) : List Prefix :=
  ps.flatMap fun p => (mids p.1).filterMap fun c =>
    let R := recoverFast n p.1 s h c
    if R.2=p.2 then some (R.1,c) else none

theorem midpoint_recovered (n s h B a C c D d : Nat) (ps : List Prefix)
    (mids : Nat → List Nat) (hhn : h≤n) (hp : (B,a)∈ps)
    (ht : Trace n s B a) (he : Extend n s B a h C c)
    (hsuf : Extend n (s+h) C c (n-h) D d)
    (hLive : MidpointLive n s h ps mids) : (C,c)∈recoverFull n s h ps mids := by
  have ht' := extend_trace n s B a h C c ht he
  obtain ⟨R,hR⟩ := extend_mod n s B a h C c he
  have hsame : targetWord n (s+h) C (n-h)=targetWord n (s+h) B (n-h) := by
    rw [hR]
    exact targetWord_fixed n s h B R (n-h) (by omega)
  have hw := extend_to_walk n (s+h) C c (n-h) D d ht' (by omega) hsuf
  rw [hsame] at hw
  have hc := hLive B a hp d c hw
  have hr := recoverFast_exact n s B a h C c ht he hhn
  unfold recoverFull
  apply List.mem_flatMap.mpr
  refine ⟨(B,a),hp,?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨c,hc,?_⟩
  simp [hr]

theorem covered_next_midpoint (n s h : Nat) (ps qs : List Prefix)
    (mids : Nat → List Nat) (hs : 1≤s) (hhn : h≤n)
    (hOld : Covered n s ps) (hLive : MidpointLive n s h ps mids)
    (hrec : recoverFull n s h ps mids=qs) : Covered n (s+h) qs := by
  intro B a C c ht he
  obtain ⟨D,d,hpre,hExt⟩ := trace_split n (s+h) B a s ht hs (by omega)
  have hExt' : Extend n s D d h B a := by simpa using hExt
  have hfull := extend_append n s D d h B a n C c hExt' he
  obtain ⟨E,e,hshort⟩ := extend_prefix n s D d (h+n) C c n hfull (by omega)
  have hp := hOld D d E e hpre hshort
  obtain ⟨F,f,hsuf⟩ := extend_prefix n (s+h) B a n C c (n-h) he (by omega)
  rw [←hrec]
  exact midpoint_recovered n s h D d B a F f ps mids hhn hp hpre hExt' hsuf hLive

theorem covered_empty_midpoint (n s h : Nat) (ps : List Prefix)
    (mids : Nat → List Nat) (hhn : h≤n)
    (hOld : Covered n s ps) (hLive : MidpointLive n s h ps mids)
    (hrec : recoverFull n s h ps mids=[]) : Covered n s [] := by
  intro B a C c ht he
  obtain ⟨D,d,hpre,hsuf⟩ := BB6.Agent45.DelayedCarry.extend_split n s B a n C c h he hhn
  have hp := hOld B a C c ht he
  have hm := midpoint_recovered n s h B a D d C c ps mids hhn hp ht hpre hsuf hLive
  rw [hrec] at hm
  exact False.elim (List.not_mem_nil hm)


/-- Append the high bit to a wrap word, with exact correction. -/
theorem corr_snoc (k R x : Nat) (hR : R<2^k) (hx : x≤1) :
    corr (k+1) (R+2^k*x)=corr k R+R+2^k*x := by
  induction k generalizing R with
  | zero =>
    have hr : R=0 := by simp at hR; omega
    subst R
    rcases (show x=0 ∨ x=1 by omega) with h|h <;> simp [h,corr]
  | succ k ih =>
    have hdiv : (R+2^(k+1)*x)/2=R/2+2^k*x := by
      rw [Nat.pow_succ]
      have he : 2^k*2*x=2*(2^k*x) := by ac_rfl
      rw [he,Nat.mul_comm 2 (2^k*x),Nat.add_mul_div_right _ _ (by decide)]
    have hmod : (R+2^(k+1)*x)%2=R%2 := by
      rw [Nat.pow_succ]
      have he : 2^k*2*x=(2^k*x)*2 := by ac_rfl
      rw [he,Nat.add_mul_mod_self_right]
    have hR' : R/2<2^k := by rw [Nat.pow_succ] at hR; omega
    rw [corr,hdiv,hmod,ih (R/2) hR']
    change 2*(corr k (R/2)+R/2+2^k*x)+(k+2)*(R%2) = (2*corr k (R/2)+(k+1)*(R%2))+R+2^(k+1)*x
    simp only [Nat.pow_succ,Nat.add_mul]
    have hmul : 2^k*2*x=2*(2^k*x) := by ac_rfl
    rw [hmul]
    omega

/-- The authentic appended low word is exactly the long reverse wrap word. -/
theorem extend_word_eq (n s B a k C c : Nat)
    (ht : Trace n s B a) (he : Extend n s B a k C c) (hk : k≤n) :
    ∃ R, R<2^k ∧ C=B+2^s*R ∧
      2^k*c+digits (targetWord n s B k)+corr k R=(n+s+k+3)*R+a := by
  induction he with
  | nil => exact ⟨0,by simp,by simp,by simp [digits,targetWord,corr]⟩
  | step k C c x d h hx he ih =>
    obtain ⟨R,hR,hC,hEq⟩ := ih (by omega)
    have htarget := target_prefix n s (s+k) B R (by omega)
    rw [hC,htarget] at he
    refine ⟨R+2^k*x,?_,?_,?_⟩
    · rw [Nat.pow_succ]
      rcases (show x=0 ∨ x=1 by omega) with h|h <;> simp [h] <;> omega
    · rw [hC,Nat.pow_add,Nat.mul_add]; ac_rfl
    · rw [targetWord,digits_append,targetWord_length,corr_snoc k R x hR hx]
      simp only [digits,Nat.mul_zero,Nat.zero_add,Nat.pow_succ]
      have hp : 2^k*2*d=2^k*(2*d) := by ac_rfl
      have he' := congrArg (2^k*·) he
      rw [Nat.mul_add,Nat.mul_add] at he'
      have hcomm : 2^k*(x*(n+(s+k)+3))=(n+s+k+3)*(2^k*x) := by
        rw [show n+(s+k)+3=n+s+k+3 by omega]; ac_rfl
      rw [hcomm] at he'
      rw [hp]
      have hsum : (n+s+(k+1)+3)*(R+2^k*x) =
          (n+s+k+3)*R+R+(n+s+k+3)*(2^k*x)+2^k*x := by
        rw [show n+s+(k+1)+3=n+s+k+3+1 by omega,Nat.add_mul,Nat.mul_add,Nat.one_mul]
        ac_rfl
      rw [hsum]
      omega

def recoverRows (s : Nat) (ps : List Prefix) (rows : Nat → List WitnessRow) : List Prefix :=
  ps.flatMap fun p => (rows p.1).filterMap fun row =>
    if row.2.2=p.2 then some (p.1+2^s*row.2.1,row.1) else none

def MidpointRows (L n s h : Nat) (ps : List Prefix) (rows : Nat → List WitnessRow) : Prop :=
  MidpointLive n s h ps (fun B => (rows B).map Prod.fst) ∧
  ∀ B a, (B,a)∈ps → (rows B).all (rowCheck L (n+s+h+3) h (targetDigits n s B h))=true

theorem midpoint_rows_recovered (L n s h B a C c D d : Nat) (ps : List Prefix)
    (rows : Nat → List WitnessRow) (hhn : h≤n) (hL : h≤2^L) (hp : (B,a)∈ps)
    (ht : Trace n s B a) (he : Extend n s B a h C c)
    (hsuf : Extend n (s+h) C c (n-h) D d)
    (hLive : MidpointRows L n s h ps rows) : (C,c)∈recoverRows s ps rows := by
  have ht' := extend_trace n s B a h C c ht he
  obtain ⟨R,hR,hC,hEq⟩ := extend_word_eq n s B a h C c ht he hhn
  have hsame : targetWord n (s+h) C (n-h)=targetWord n (s+h) B (n-h) := by
    rw [hC]
    exact targetWord_fixed n s h B R (n-h) (by omega)
  have hw := extend_to_walk n (s+h) C c (n-h) D d ht' (by omega) hsuf
  rw [hsame] at hw
  have hc := hLive.1 B a hp d c hw
  obtain ⟨row,hrow,hz⟩ := List.mem_map.mp hc
  have hcheck := List.all_eq_true.mp (hLive.2 B a hp) row hrow
  unfold rowCheck at hcheck
  rw [hz,←digits_targetWord] at hcheck
  have ha := (trace_bounds n s B a ht).2.2.2
  obtain ⟨hout,hword⟩ := witness_word_sound L (n+s+h+3) h
    (2^h*c+digits (targetWord n s B h)) row.2.1 row.2.2 R a hL hR (by omega) hEq hcheck
  unfold recoverRows
  apply List.mem_flatMap.mpr
  refine ⟨(B,a),hp,?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨row,hrow,?_⟩
  simp [hout,hword,hz,hC]

theorem covered_next_rows (L n s h : Nat) (ps qs : List Prefix)
    (rows : Nat → List WitnessRow) (hs : 1≤s) (hhn : h≤n) (hL : h≤2^L)
    (hOld : Covered n s ps) (hLive : MidpointRows L n s h ps rows)
    (hrec : recoverRows s ps rows=qs) : Covered n (s+h) qs := by
  intro B a C c ht he
  obtain ⟨D,d,hpre,hExt⟩ := trace_split n (s+h) B a s ht hs (by omega)
  have hExt' : Extend n s D d h B a := by simpa using hExt
  have hfull := extend_append n s D d h B a n C c hExt' he
  obtain ⟨E,e,hshort⟩ := extend_prefix n s D d (h+n) C c n hfull (by omega)
  have hp := hOld D d E e hpre hshort
  obtain ⟨F,f,hsuf⟩ := extend_prefix n (s+h) B a n C c (n-h) he (by omega)
  rw [←hrec]
  exact midpoint_rows_recovered L n s h D d B a F f ps rows hhn hL hp hpre hExt' hsuf hLive

theorem covered_empty_rows (L n s h : Nat) (ps : List Prefix)
    (rows : Nat → List WitnessRow) (hhn : h≤n) (hL : h≤2^L)
    (hOld : Covered n s ps) (hLive : MidpointRows L n s h ps rows)
    (hrec : recoverRows s ps rows=[]) : Covered n s [] := by
  intro B a C c ht he
  obtain ⟨D,d,hpre,hsuf⟩ := BB6.Agent45.DelayedCarry.extend_split n s B a n C c h he hhn
  have hp := hOld B a C c ht he
  have hm := midpoint_rows_recovered L n s h B a D d C c ps rows hhn hL hp ht hpre hsuf hLive
  rw [hrec] at hm
  exact False.elim (List.not_mem_nil hm)

#print axioms extend_word_eq
#print axioms midpoint_rows_recovered
#print axioms covered_next_rows
#print axioms covered_empty_rows

#print axioms digits_targetWord
#print axioms packedBack_sound
#print axioms rewindTarget_sound
#print axioms live_bits_extend
#print axioms live_bits_to_list
#print axioms live_list_extend
#print axioms covered_next_midpoint
#print axioms covered_empty_midpoint
end BB6.Agent45LongBlock
