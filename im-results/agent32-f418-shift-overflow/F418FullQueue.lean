import F418FullReturn
import F418QueueHistory
import F418SparseGate

namespace BB6.Agent32F418.RecoveryCore
open Arithmetic EventSystem State ReturnBounds
namespace Word

/-- A recoverable gate forgets the old queue, leaving exactly two deferred powers. -/
def resetQueue (b : Word) (W : Nat) (p : Prefix) : List Nat := [W+b.U-p.L,b.outW W p-1]

def resetOffset (b : Word) (p : Prefix) : Int :=
  -(b.D:Int)/(2:Int)^p.L-((2^(b.e+3)-3:Nat):Int)*(2:Int)^(b.f+p.E)-(p.C0:Int)

theorem Q_width (b : Word) (W : Nat) : b.Q W<2^(W+b.U) := by
  have hd := b.D_pos
  have hp := Nat.two_pow_pos (W+b.U)
  unfold Q; omega

theorem n4_affine (b : Word) (W : Nat) :
    b.n4 W=2^(W+b.E+b.f+2)+(2^(b.e+3)-3)*2^b.f := by
  unfold n4
  rw [Prefix.reset0_affine (b.e+1),←Nat.pow_add]
  simp only [show b.e+1+2=b.e+3 by omega]
  congr 1

theorem recover_reg0 (b : Word) (W : Nat) (p : Prefix) (R : Nat)
    (hw : b.value<2^W) (he : b.e%2=1) (hq : b.Q W=p.value R) :
    iterate (b.steps+2+p.steps) (Prefix.pure b.value W)=
      some (reg0 R (b.n4 W*2^p.E+p.C0) (b.outW W p)) := by
  rw [iterate_add,recover_to_phase0 b W hw he,hq]
  simp only [Option.bind_some,Prefix.episode0_exact,outW]

theorem R_signed (b : Word) (W : Nat) (p : Prefix) (R : Nat)
    (hw : b.value<2^W) (hq : b.Q W=p.value R) :
    (R:Int)=(2:Int)^(W+b.U-p.L)+(-(b.D:Int))/(2:Int)^p.L := by
  have hL : p.L≤W+b.U := (Prefix.width_tail (hq ▸ b.Q_width W)).1
  have hD : b.D≤2^(W+b.U) := by
    exact Nat.le_trans b.D_bounds (Nat.pow_le_pow_right (by decide) (by have := width hw; omega))
  have h : (R:Int)=(b.Q W:Int)/(2:Int)^p.L := by
    have hcast : ((2^p.L:Nat):Int)=(2:Int)^p.L := by simp [Int.natCast_pow]
    rw [hq,←hcast,←Int.natCast_ediv,Prefix.value_div_length]
  rw [h,Q,Int.natCast_sub hD,Int.natCast_pow]
  change ((2:Int)^(W+b.U)-(b.D:Int))/(2:Int)^p.L=_
  have hp : (2:Int)^(W+b.U)=(2:Int)^(W+b.U-p.L)*(2:Int)^p.L := by
    rw [←Int.pow_add,show W+b.U-p.L+p.L=W+b.U by omega]
  rw [hp,Int.sub_eq_add_neg,Int.add_comm,Int.mul_comm ((2:Int)^(W+b.U-p.L)),Int.add_mul_ediv_left _ _ (Int.pow_ne_zero (by decide))]
  ac_rfl

theorem resetOffset_neg (b : Word) (p : Prefix) : b.resetOffset p<0 := by
  have hD : 0<(b.D:Int) := Int.ofNat_lt.mpr b.D_pos
  have hd : 0<(2:Int)^p.L := Int.pow_pos (by decide)
  have hq : -(b.D:Int)/(2:Int)^p.L<0 := by
    apply (Int.ediv_lt_iff_lt_mul hd).mpr
    simp; omega
  have hK : 0≤((2^(b.e+3)-3:Nat):Int)*(2:Int)^(b.f+p.E) :=
    Int.mul_nonneg (Int.natCast_nonneg _) (Int.le_of_lt (Int.pow_pos (by decide)))
  have hC := Int.natCast_nonneg p.C0
  unfold resetOffset; omega

theorem resetQueue_spaced (b : Word) (W : Nat) (p : Prefix) :
    Prefix.Spaced (b.resetQueue W p) ∧ ∀ i∈b.resetQueue W p, i<b.outW W p := by
  have hU := b.U_ge
  have he : b.E=b.e+b.U+1 := rfl
  have hp : 2≤p.E := by simp [Prefix.E]
  have hL : 0<p.L := by simp [Prefix.L]
  have hf : 2≤b.f := by unfold f; omega
  unfold resetQueue Prefix.Spaced outW w4
  simp
  omega

theorem reset_sound {b : Word} {W : Nat} {p : Prefix} {R : Nat}
    (hpath : PurePath b.value W) (he : b.e%2=1) (hq : b.Q W=p.value R) :
    (b.outN W p R:Int)=b.resetOffset p+Prefix.powerSum (b.resetQueue W p) := by
  have hwidth := (purePath_safe hpath).2
  have hreg := b.recover_reg0 W p R hwidth he hq
  have hs := reaches_safe (reaches_trans (purePath_reaches hpath) (reaches_iff.mpr ⟨_,hreg⟩))
  have hright : b.n4 W*2^p.E+p.C0 < 2^(b.outW W p) := hs.1.2.2
  have hR := b.R_signed W p R hwidth hq
  have hW : b.outW W p=W+b.E+b.f+3+p.E := rfl
  have hpow : 2^(b.outW W p)=2*2^(b.outW W p-1) := by
    have he : 0<b.outW W p := by rw [hW]; omega
    calc
      2^(b.outW W p)=2^((b.outW W p-1)+1) := by congr 1 <;> omega
      _=2*2^(b.outW W p-1) := by rw [Nat.pow_succ,Nat.mul_comm]
  have hn4 : b.n4 W*2^p.E = 2^(b.outW W p-1)+(2^(b.e+3)-3)*2^(b.f+p.E) := by
    rw [n4_affine,Nat.add_mul,←Nat.pow_add,Nat.mul_assoc,←Nat.pow_add]
    congr 2
    omega
  have hgap : gap (b.n4 W*2^p.E+p.C0) (b.outW W p)=
      2^(b.outW W p-1)-((2^(b.e+3)-3)*2^(b.f+p.E)+p.C0) := by
    unfold gap
    rw [hpow,hn4]
    omega
  have hcor : (2^(b.e+3)-3)*2^(b.f+p.E)+p.C0 ≤ 2^(b.outW W p-1) := by
    rw [hpow,hn4] at hright
    omega
  unfold outN
  rw [hgap,Int.natCast_add,Int.natCast_sub hcor,Int.natCast_add,Int.natCast_mul,Int.natCast_pow,hR]
  simp [resetOffset,resetQueue,Prefix.powerSum,Int.natCast_pow]
  omega

end Word

/-- A signed sparse representation of every checkpoint, not just the pre-recovery segment. -/
def QueueRep (N W : Nat) (x : Int) (hs : List Nat) : Prop :=
  (N:Int)=x+Prefix.powerSum hs ∧ Prefix.Spaced hs ∧ ∀ i∈hs,i<W

/-- Exact history, counting normal and recovered returns rather than choosing an arbitrary representation. -/
inductive FullQueuePath : Nat → Nat → Int → List Nat → Nat → Nat → Prop where
  | seed : FullQueuePath 268311341 29 268311341 [] 0 0
  | normal {b : Prefix} {Q W : Nat} {x : Int} {hs : List Nat} {t r : Nat} :
      FullQueuePath (b.value Q) W x hs t r →
      FullQueuePath (b.next Q W) (W+b.E+1) (Prefix.updateOffset b x hs)
        (Prefix.updateQueue b W hs) (t+1) r
  | recover {b : Word} {W : Nat} {p : Prefix} {R : Nat} {x : Int} {hs : List Nat} {t r : Nat} :
      FullQueuePath b.value W x hs t r → b.e%2=1 → b.Q W=p.value R →
      FullQueuePath (b.outN W p R) (b.outW W p) (b.resetOffset p) (b.resetQueue W p) (t+1) (r+1)

theorem fullQueue_pure {N W : Nat} {x : Int} {hs : List Nat} {t r : Nat}
    (h : FullQueuePath N W x hs t r) : PurePath N W := by
  induction h with
  | seed => exact PurePath.seed
  | normal _ ih => exact PurePath.normal ih
  | recover _ he hq ih => exact PurePath.recover ih he hq

theorem purePath_queue {N W : Nat} (h : PurePath N W) : ∃ x hs t r, FullQueuePath N W x hs t r := by
  induction h with
  | seed => exact ⟨_,_,_,_,FullQueuePath.seed⟩
  | normal _ ih =>
    obtain ⟨x,hs,t,r,h⟩ := ih
    exact ⟨_,_,_,_,FullQueuePath.normal h⟩
  | recover _ he hq ih =>
    obtain ⟨x,hs,t,r,h⟩ := ih
    exact ⟨_,_,_,_,FullQueuePath.recover h he hq⟩

theorem fullQueue_sound {N W : Nat} {x : Int} {hs : List Nat} {t r : Nat}
    (h : FullQueuePath N W x hs t r) : QueueRep N W x hs := by
  induction h with
  | seed => simp [QueueRep,Prefix.powerSum,Prefix.Spaced]
  | @normal b Q W x hs t r h ih =>
    obtain ⟨he,hsp,hw⟩ := ih
    exact ⟨Prefix.queue_return_split (purePath_safe (fullQueue_pure h)).2 he,Prefix.queue_spaced_update hsp hw⟩
  | @recover b W p R x hs t r h he hq ih =>
    exact ⟨b.reset_sound (fullQueue_pure h) he hq,b.resetQueue_spaced W p⟩

/-- If a representation is already negative, all later normal updates retain this sign. -/
theorem normal_preserves_negative {p : Prefix} {x : Int} {hs : List Nat}
    (hx : x<0) (hsp : Prefix.Spaced hs) : Prefix.updateOffset p x hs<0 := by
  have hl := (Prefix.lowQueue_bounds hsp p.L).2
  have hpow : 0<(2:Int)^p.L := Int.pow_pos (by decide)
  have hq : (x+Prefix.powerSum (Prefix.lowQueue p.L hs))/(2:Int)^p.L<1 := by
    apply (Int.ediv_lt_iff_lt_mul hpow).mpr
    simp; omega
  have hc := Prefix.C_ge_three p
  unfold Prefix.updateOffset; omega

theorem fullQueue_upper {N W : Nat} {x : Int} {hs : List Nat} {t r : Nat}
    (h : FullQueuePath N W x hs t r) : x≤(2:Int)^(29-t) := by
  induction h with
  | seed => decide
  | @normal b Q W x hs t r h ih =>
    have hu := Prefix.offset_upper_step (b:=b) (fullQueue_sound h).2.1 ih
    omega
  | @recover b W p R x hs t r h he hq ih =>
    have hx := b.resetOffset_neg p
    have hp : 0<(2:Int)^(29-(t+1)) := Int.pow_pos (by decide)
    omega

theorem fullQueue_negative {N W : Nat} {x : Int} {hs : List Nat} {t r : Nat}
    (h : FullQueuePath N W x hs t r) (ht : 29≤t ∨ 0<r) : x<0 := by
  induction h with
  | seed => omega
  | @normal b Q W x hs t r h ih =>
    rcases ht with ht | hr
    · have hu := Prefix.offset_upper_step (b:=b) (fullQueue_sound h).2.1 (fullQueue_upper h)
      simp [show 29-(t+1)=0 by omega] at hu
      omega
    · exact normal_preserves_negative (ih (Or.inr hr)) (fullQueue_sound h).2.1
  | recover _ _ _ _ => exact Word.resetOffset_neg _ _

/-- Direct application of the exact gate theorem to the signed representation. -/
theorem signed_gate {N W : Nat} {x : Int} {hs : List Nat}
    (h : QueueRep N W x hs) (hx : x<0) :
    ∃ pre a post r,
      hs=pre++a::post ∧ SparseGate.mass pre<(-x).toNat ∧
      (-x).toNat≤SparseGate.mass pre+2^a ∧ r=SparseGate.mass pre+2^a-(-x).toNat ∧
      r<2^a ∧ N=r+SparseGate.mass post ∧
      (Prefix.NoEven N ↔ Prefix.NoEven r ∧ ∀ i∈post, i%2=1) ∧
      15*(-x).toNat<16*2^a ∧
      (Prefix.NoEven N → (if a%2=0 then 2^a else 2^(a+1))+2≤3*(-x).toNat) := by
  obtain ⟨hN,hsp,_⟩ := h
  let d := (-x).toNat
  have hd : (d:Int)=-x := Int.toNat_of_nonneg (by omega)
  have hdpos : 0<d := by omega
  have hmass : Prefix.powerSum hs=(SparseGate.mass hs:Int) := Prefix.powerSum_cast hs
  have hle : d≤SparseGate.mass hs := by
    apply Int.ofNat_le.mp
    rw [hd,←hmass]
    have := Int.natCast_nonneg N
    omega
  have hvalue : N=SparseGate.mass hs-d := by
    apply Int.ofNat_inj.mp
    rw [Int.natCast_sub hle,←hmass,hd]
    omega
  rw [hvalue]
  exact SparseGate.gate_exact hsp hdpos hle

/-- Excess debt above the stable p=0 debt 7. It measures current debt, not the historical maximum p. -/
def excess (x : Int) : Int := max 0 (-x-7)

theorem excess_nonneg (x : Int) : 0≤excess x := by unfold excess; omega

theorem excess_lower (x : Int) : -7-excess x≤x := by unfold excess; omega

theorem excess_pzero {p : Prefix} {x : Int} {hs : List Nat} (hsp : Prefix.Spaced hs) (hp : p.p=0) :
    excess (Prefix.updateOffset p x hs)≤excess x/2 := by
  have hcase : p=Prefix.last 0 := by
    cases p with
    | last r => simp [Prefix.p] at hp; subst r; rfl
    | more r t => simp [Prefix.p] at hp
  subst p
  have hlow := (Prefix.lowQueue_bounds hsp 1).1
  have hx := excess_lower x
  have hu := excess_nonneg x
  change 0≤Prefix.powerSum (Prefix.lowQueue (Prefix.last 0).L hs) at hlow
  unfold Prefix.updateOffset excess
  change max 0 (-((x+Prefix.powerSum (Prefix.lowQueue (Prefix.last 0).L hs))/2-3)-7)≤max 0 (-x-7)/2
  unfold excess at hx hu
  omega

theorem excess_ppos {p : Prefix} {x : Int} {hs : List Nat} (hsp : Prefix.Spaced hs) (hp : 0<p.p) :
    excess (Prefix.updateOffset p x hs)≤excess x/(2:Int)^p.L+(p.C:Int) := by
  let B : Int := (2:Int)^p.L
  have hB : 8≤B := by
    have hL : 3≤p.L := by simp [Prefix.L]; omega
    have h := Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide : 0<2) hL)
    simpa [B,Int.natCast_pow] using h
  have hlow := (Prefix.lowQueue_bounds hsp p.L).1
  have hx := excess_lower x
  have hu := excess_nonneg x
  have hq : 0≤excess x/B := Int.ediv_nonneg hu (by omega)
  have hrem := Int.emod_lt_of_pos (excess x) (by omega : 0<B)
  have hdiv := Int.emod_add_mul_ediv (excess x) B
  have hrem0 := Int.emod_nonneg (excess x) (by omega : B≠0)
  have hB2 : 2*B≥B+7 := by omega
  have hmul : (- (excess x/B)-2)*B ≤ x+Prefix.powerSum (Prefix.lowQueue p.L hs) := by
    rw [Int.sub_mul,Int.neg_mul,Int.mul_comm (excess x/B) B]
    omega
  have hfloor : - (excess x/B)-2≤(x+Prefix.powerSum (Prefix.lowQueue p.L hs))/B :=
    (Int.le_ediv_iff_mul_le (by omega : 0<B)).mpr hmul
  have hc := Int.natCast_nonneg p.C
  unfold Prefix.updateOffset excess
  change max 0 (-((x+Prefix.powerSum (Prefix.lowQueue p.L hs))/B-(p.C:Int))-7)≤excess x/B+(p.C:Int)
  omega

/-- Current-debt bit envelope: zero-prefix returns contract it by one bit. -/
def debtWidth (p : Prefix) (B : Nat) : Nat :=
  if p.p=0 then B-1 else max (B-p.L) (7*p.p+2)+1

theorem debtWidth_step {p : Prefix} {x : Int} {hs : List Nat} {B : Nat}
    (hsp : Prefix.Spaced hs) (hB : excess x<(2:Int)^B) :
    excess (Prefix.updateOffset p x hs)<(2:Int)^(debtWidth p B) := by
  by_cases hp : p.p=0
  · have h := excess_pzero (x:=x) hsp hp
    simp only [debtWidth,if_pos hp]
    by_cases hb : B=0
    · subst B
      simp at hB ⊢
      have h0 := excess_nonneg x
      omega
    · have he : (2:Int)^B=2*(2:Int)^(B-1) := by
        calc
          (2:Int)^B=2^((B-1)+1) := by congr 1 <;> omega
          _=2*2^(B-1) := by rw [Int.pow_succ,Int.mul_comm]
      rw [he] at hB
      omega
  · have h := excess_ppos (x:=x) hsp (by omega : 0<p.p)
    let M := max (B-p.L) (7*p.p+2)
    have hpow : (2:Int)^B≤(2:Int)^(B-p.L)*(2:Int)^p.L := by
      rw [←Int.pow_add]
      exact Prefix.intPow_mono (by omega)
    have hpD : 0<(2:Int)^p.L := Int.pow_pos (by decide)
    have hdiv : excess x/(2:Int)^p.L<(2:Int)^(B-p.L) :=
      (Int.ediv_lt_iff_lt_mul hpD).mpr (by omega)
    have hC : (p.C:Int)<(2:Int)^(7*p.p+2) := by
      have h' := Prefix.correction_upper p
      have hcast : ((2^(p.E+2*p.p):Nat):Int)=(2:Int)^(7*p.p+2) := by
        simp [Int.natCast_pow,Prefix.E]; congr 1 <;> omega
      rw [←hcast]
      exact Int.ofNat_lt.mpr h'
    have hl := Prefix.intPow_mono (Nat.le_max_left (B-p.L) (7*p.p+2))
    have hr := Prefix.intPow_mono (Nat.le_max_right (B-p.L) (7*p.p+2))
    simp only [debtWidth,if_neg hp,Int.pow_succ]
    omega

/-- A surviving even power above the current bit envelope excludes the gate.
    The bound shrinks on zero-prefix runs and never refers to a historic record p. -/
theorem even_above_debtWidth {N W : Nat} {x : Int} {hs : List Nat} {B i : Nat}
    (h : QueueRep N W x hs) (hx : x<0) (hB : 3≤B) (hu : excess x<(2:Int)^B)
    (hn : Prefix.NoEven N) (hi : i%2=0) (hhigh : B+3≤i) : i∉hs := by
  obtain ⟨pre,a,post,r,hlist,_,_,_,_,_,hiff,_,hbound⟩ := signed_gate h hx
  have hg := hbound hn
  have hpow : 2^a+2≤3*(-x).toNat := by
    by_cases ha : a%2=0
    · simpa [ha] using hg
    · have hm := Nat.pow_le_pow_right (by decide : 0<2) (show a≤a+1 by omega)
      simp [ha] at hg
      omega
  have hd : (((-x).toNat):Int)=-x := Int.toNat_of_nonneg (by omega)
  have hD : ((2^B:Nat):Int)=(2:Int)^B := by simp [Int.natCast_pow]
  have hsmall : (-x).toNat<2^B+7 := by
    apply Int.ofNat_lt.mp
    rw [Int.natCast_add,hd,hD]
    have hh := excess_lower x
    omega
  have hlarge : 8≤2^B := by exact Nat.pow_le_pow_right (by decide : 0<2) hB
  have hb : 2^a<2^(B+3) := by rw [Nat.pow_add]; change 2^a<2^B*8; omega
  have ha := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp hb
  have hpost := (hiff.mp hn).2
  have hsp : Prefix.Spaced (pre++a::post) := hlist ▸ h.2.1
  obtain ⟨_,_,hc⟩ := List.pairwise_append.mp hsp
  rw [hlist]
  intro hm
  rcases List.mem_append.mp hm with hm | hm
  · have hg := hc i hm a (by simp)
    omega
  · rcases List.mem_cons.mp hm with hia | hm
    · omega
    · have hh := hpost i hm
      omega

#print axioms Word.reset_sound
#print axioms purePath_queue
#print axioms fullQueue_sound
#print axioms fullQueue_negative
#print axioms signed_gate
#print axioms excess_pzero
#print axioms excess_ppos
#print axioms debtWidth_step
#print axioms even_above_debtWidth

end BB6.Agent32F418.RecoveryCore
