import LagChecker
import LagCert
namespace BB6.Agent9CompactState
open BB6.Agent45.DelayedCarry

/-- Projection of the delayed carry path to a fixed-width queue. -/
inductive QExtend (n s Q a : Nat) : Nat → Nat → Nat → Prop
  | nil : QExtend n s Q a 0 Q a
  | step (k R c x d : Nat) (h : QExtend n s Q a k R c) (hx : x≤1)
      (he : 2*d+R%2 = c+x*(n+(s+k)+3)) :
      QExtend n s Q a (k+1) ((R+total n*x)/2) d

theorem project (n s B a k C c : Nat) (he : Extend n s B a k C c) :
    QExtend n s (quotient n s B) a k (quotient n (s+k) C) c := by
  induction he with
  | nil => simpa using (QExtend.nil : QExtend n s (quotient n s B) a 0 (quotient n s B) a)
  | step k C c x d he hx hh ih =>
    rw [show s+(k+1)=s+k+1 by omega,quotient_step]
    exact QExtend.step k (quotient n (s+k) C) c x d ih hx (by rw [target_eq] at hh; exact hh)

theorem lift (n s B a k R c : Nat) (he : QExtend n s (quotient n s B) a k R c) :
    ∃ C, Extend n s B a k C c ∧ quotient n (s+k) C=R := by
  induction he with
  | nil => exact ⟨B,Extend.nil,by simp⟩
  | step k R c x d he hx hh ih =>
    obtain ⟨C,hC,hQ⟩ := ih
    refine ⟨C+2^(s+k)*x,Extend.step k C c x d hC hx (by rw [target_eq,hQ]; exact hh),?_⟩
    rw [show s+(k+1)=s+k+1 by omega,quotient_step,hQ]

theorem future_equiv (n s B D a k Q c : Nat) (h : quotient n s B = quotient n s D) :
    (∃ C, Extend n s B a k C c ∧ quotient n (s+k) C=Q) ↔
    (∃ E, Extend n s D a k E c ∧ quotient n (s+k) E=Q) := by
  constructor
  · rintro ⟨C,hC,rfl⟩
    apply lift
    rw [←h]
    exact project _ _ _ _ _ _ _ hC
  · rintro ⟨E,hE,rfl⟩
    apply lift
    rw [h]
    exact project _ _ _ _ _ _ _ hE

theorem quotient_lt (n s B : Nat) (hB : B<2^s) : quotient n s B<total n := by
  unfold quotient
  apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos s)).2
  exact Nat.mul_lt_mul_of_pos_left hB (by unfold total; exact Nat.mul_pos (by decide) (Nat.two_pow_pos _))

theorem quotient_word (n s h B x : Nat) :
    quotient n (s+h) (B+2^s*x)=(quotient n s B+total n*x)/2^h := by
  unfold quotient
  rw [Nat.pow_add,←Nat.div_div_eq_div_mul]
  have he : total n*(B+2^s*x)=total n*B+2^s*(total n*x) := by
    rw [Nat.mul_add]; congr 1; ac_rfl
  rw [he,Nat.add_mul_div_left _ _ (Nat.two_pow_pos s)]

theorem fixed_target (n s j B : Nat) : target n (s+j) B=(quotient n s B/2^j)%2 := by
  rw [target_eq]
  unfold quotient
  rw [Nat.pow_add,←Nat.div_div_eq_div_mul]

/-- Top L bits of 7B modulo 2^s are present in the quotient queue. -/
def top (n L Q : Nat) : Nat := (Q/2^(n-L))%2^L

theorem top_eq (n L s B : Nat) (hL : L≤n) (hs : L≤s) :
    top n L (quotient n s B) = (7*B/2^(s-L))%2^L := by
  unfold top quotient total
  rw [Nat.div_div_eq_div_mul,←Nat.pow_add]
  have he : s+(n-L)=n+(s-L) := by omega
  rw [he,Nat.pow_add]
  have h : 7*2^n*B=2^n*(7*B) := by ac_rfl
  rw [h,Nat.mul_div_mul_left _ _ (Nat.two_pow_pos n)]

/-- Nonconstant high bits certify distance from both edges of the dyadic cell. -/
theorem top_resMin (n L s B : Nat) (hL : L≤n) (hs : L≤s)
    (hlo : 0<top n L (quotient n s B)) (hhi : top n L (quotient n s B)+1<2^L) :
    2^(s-L)≤resMin s B := by
  rw [top_eq n L s B hL hs] at hlo hhi
  let D := 2^(s-L)
  let T := (7*B/D)%2^L
  have hd : 0<D := Nat.two_pow_pos _
  change 0<T at hlo
  change T+1<2^L at hhi
  have hpow : 2^s=D*2^L := by
    dsimp [D]; rw [←Nat.pow_add]; congr 1; omega
  have hr : (7*B)%2^s=(7*B)%D+D*T := by
    rw [hpow,Nat.mod_mul]
  have hrlt : (7*B)%D<D := Nat.mod_lt _ hd
  have hlow : D≤D*T := by
    apply Nat.le_mul_of_pos_right
    exact hlo
  have hupper : D*(T+2)≤D*2^L := Nat.mul_le_mul_left _ (by omega)
  rw [Nat.mul_add,show D*2=D+D by omega] at hupper
  unfold resMin
  change D≤min ((7*B)%2^s) (2^s-((7*B)%2^s))
  rw [hr,hpow]
  exact Nat.le_min.mpr ⟨by omega,by omega⟩

theorem top_margin (n K L s B : Nat) (hL : L≤n) (hs : L≤s)
    (hlo : 0<top n L (quotient n s B)) (hhi : top n L (quotient n s B)+1<2^L)
    (hgap : (n+K+2)*marginSize n K*2^L<6*2^n) :
    (n+K+2)*marginSize n K*2^s<6*2^n*resMin s B := by
  have h := top_resMin n L s B hL hs hlo hhi
  have hpow : 2^s=2^L*2^(s-L) := by rw [←Nat.pow_add]; congr 1; omega
  rw [hpow,←Nat.mul_assoc]
  exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hgap (Nat.two_pow_pos _)) (Nat.mul_le_mul_left _ h)

#print axioms project
#print axioms lift
#print axioms future_equiv
#print axioms quotient_lt
#print axioms quotient_word
#print axioms fixed_target
#print axioms top_eq
#print axioms top_resMin
#print axioms top_margin
end BB6.Agent9CompactState
