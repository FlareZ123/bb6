import F418SignedQueue

namespace BB6.Agent32F418.ReturnBounds.Prefix

def nPowerSum (hs : List Nat) : Nat := (hs.map fun h => 2^h).sum

theorem powerSum_cast (hs : List Nat) : powerSum hs = (nPowerSum hs:Int) := by
  induction hs with
  | nil => rfl
  | cons a as ih =>
    simp only [powerSum,nPowerSum,List.map_cons,List.sum_cons] at ih ⊢
    rw [ih,Int.natCast_add,Int.natCast_pow]
    rfl

theorem nPowerSum_shift (L : Nat) (hs : List Nat) (h : ∀ i ∈ hs, L≤i) :
    nPowerSum hs = 2^L*nPowerSum (shiftQueue L hs) := by
  apply Int.ofNat_inj.mp
  have h' := powerSum_shift L hs h
  rw [powerSum_cast,powerSum_cast] at h'
  rw [Int.natCast_mul,Int.natCast_pow]
  exact h'

theorem nPowerSum_bits {hs : List Nat} (hp : hs.Pairwise (· < ·)) (i : Nat) :
    (nPowerSum hs).testBit i = decide (i ∈ hs) := by
  induction hs with
  | nil => simp [nPowerSum]
  | cons a as ih =>
    obtain ⟨ha,has⟩ := List.pairwise_cons.mp hp
    have hfact := nPowerSum_shift (a+1) as (by intro j hj; have hh := ha j hj; omega)
    have hsmall : 2^a < 2^(a+1) := Nat.pow_lt_pow_right (by decide) (by omega)
    have he : nPowerSum (a::as)=2^(a+1)*nPowerSum (shiftQueue (a+1) as)+2^a := by
      simp only [nPowerSum,List.map_cons,List.sum_cons] at hfact ⊢
      rw [hfact]; omega
    rw [he,Nat.testBit_two_pow_mul_add _ hsmall]
    by_cases h : i<a+1
    · have hn : i ∉ as := by intro hi; have hh:=ha i hi; omega
      simp [h,Nat.testBit_two_pow,hn,eq_comm]
    · have hne : i≠a := by omega
      have ht : (nPowerSum as).testBit i = (nPowerSum (shiftQueue (a+1) as)).testBit (i-(a+1)) := by
        rw [hfact,Nat.mul_comm,Nat.testBit_mul_two_pow]
        simp [show a+1≤i by omega]
      rw [if_neg h,←ht,ih has]
      simp [hne]

theorem nPowerSum_lt {hs : List Nat} {L : Nat} (hp : hs.Pairwise (· < ·))
    (h : ∀ i ∈ hs, i<L) : nPowerSum hs<2^L := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [nPowerSum_bits hp]
  simp only [decide_eq_false_iff_not]
  intro hm
  have hh := h i hm
  omega

def lowQueue (L : Nat) (hs : List Nat) := hs.filter (· < L)
def highQueue (L : Nat) (hs : List Nat) := hs.filter (L ≤ ·)

theorem powerSum_partition (L : Nat) (hs : List Nat) :
    powerSum hs=powerSum (lowQueue L hs)+powerSum (highQueue L hs) := by
  induction hs with
  | nil => rfl
  | cons a as ih =>
    by_cases h : a<L
    · simp [lowQueue,highQueue,List.filter_cons,h,show ¬L≤a by omega,powerSum] at ih ⊢
      omega
    · simp [lowQueue,highQueue,List.filter_cons,h,show L≤a by omega,powerSum] at ih ⊢
      omega

def updateOffset (b : Prefix) (x : Int) (hs : List Nat) :=
  (x+powerSum (lowQueue b.L hs))/(2:Int)^b.L-(b.C:Int)

def updateQueue (b : Prefix) (W : Nat) (hs : List Nat) :=
  shiftQueue b.L (highQueue b.L hs)++[W+b.E]

theorem queue_return_split {b : Prefix} {Q W : Nat} {x : Int} {hs : List Nat}
    (hw : b.value Q<2^W) (hN : (b.value Q:Int)=x+powerSum hs) :
    (b.next Q W:Int)=updateOffset b x hs+powerSum (updateQueue b W hs) := by
  rw [powerSum_partition b.L hs,←Int.add_assoc] at hN
  exact queue_return hw hN (by
    intro i hi
    exact of_decide_eq_true (List.mem_filter.mp hi).2)

def Spaced (hs : List Nat) := hs.Pairwise (fun a b => a+4≤b)

theorem spaced_strict {hs : List Nat} (h : Spaced hs) : hs.Pairwise (· < ·) :=
  h.imp (by intro a b hab; omega)

theorem queue_spaced_update {hs : List Nat} {b : Prefix} {W : Nat}
    (hsp : Spaced hs) (hw : ∀ i ∈ hs, i<W) :
    Spaced (updateQueue b W hs) ∧ ∀ i ∈ updateQueue b W hs, i<W+b.E+1 := by
  have hf : Spaced (highQueue b.L hs) := hsp.filter _
  have hshift : Spaced (shiftQueue b.L (highQueue b.L hs)) := by
    unfold Spaced shiftQueue
    rw [List.pairwise_map]
    apply hf.imp_of_mem
    intro a c ha hc hgap
    have hal : b.L≤a := of_decide_eq_true (List.mem_filter.mp ha).2
    have hcl : b.L≤c := of_decide_eq_true (List.mem_filter.mp hc).2
    omega
  have hbound : ∀ i ∈ shiftQueue b.L (highQueue b.L hs), i+b.L<W := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    have hlj : b.L≤j := of_decide_eq_true (List.mem_filter.mp hj).2
    have hjw := hw j (List.mem_filter.mp hj).1
    omega
  have hL : 0<b.L := by simp [L]
  have hE : 2≤b.E := by simp [E]
  constructor
  · unfold Spaced updateQueue
    rw [List.pairwise_append]
    refine ⟨hshift,by simp,?_⟩
    intro a ha c hc
    simp only [List.mem_singleton] at hc
    subst c
    have h := hbound a ha
    omega
  · intro i hi
    simp only [updateQueue,List.mem_append,List.mem_singleton] at hi
    rcases hi with hi | rfl
    · have h := hbound i hi; omega
    · omega

theorem lowQueue_bounds {hs : List Nat} (hsp : Spaced hs) (L : Nat) :
    0≤powerSum (lowQueue L hs) ∧ powerSum (lowQueue L hs)<(2:Int)^L := by
  rw [powerSum_cast]
  constructor
  · exact Int.natCast_nonneg _
  · have h := nPowerSum_lt ((spaced_strict hsp).filter _) (L:=L)
        (by intro i hi; exact of_decide_eq_true (List.mem_filter.mp hi).2)
    have hc : ((2^L:Nat):Int)=(2:Int)^L := by simp [Int.natCast_pow]
    rw [←hc]
    exact Int.ofNat_lt.mpr h

#print axioms nPowerSum_bits
#print axioms queue_return_split
#print axioms queue_spaced_update

end BB6.Agent32F418.ReturnBounds.Prefix
