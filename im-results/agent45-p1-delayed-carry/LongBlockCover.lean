import LongBlockWitness
import ReverseLagBlocks
import BitSpread
import BatchCarryChunks
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
  cases hw with
  | step ys a yy b r hp hy hbb ha hr he =>
    cases hp
    simp only [List.length_nil,Nat.zero_add,Nat.add_sub_cancel] at ha hr he
    have hbound : 2*z+y<2*q := by
      rcases (show b=0 ∨ b=1 by omega) with h|h <;> simp [h] at he <;> omega
    have hmod : (2*z+y)%q=c := by
      rw [he,Nat.add_mod]
      simp [Nat.mod_eq_of_lt hr]
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

#print axioms digits_targetWord
#print axioms packedBack_sound
#print axioms rewindTarget_sound
#print axioms live_bits_extend
#print axioms live_bits_to_list
#print axioms live_list_extend
#print axioms covered_next_midpoint
#print axioms covered_empty_midpoint
end BB6.Agent45LongBlock
