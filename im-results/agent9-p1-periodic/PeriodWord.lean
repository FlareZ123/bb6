import PeriodCore

namespace PeriodWord

theorem edge_affine (L m t v z zp : Nat) (hdiv : z = 2^t*v)
    (hn : 2*zp+1=L+m+t+v) :
    ((((2:Nat)^(t+1):Nat):Int) * (zp:Int)) =
      (z:Int) + ((2:Nat)^t:Int)*((L:Int)+(m:Int)+(t:Int)-1) := by
  have hh : 2*(zp:Int)+1=(L:Int)+m+t+v := by exact_mod_cast hn
  have hz : (z:Int)=((2:Nat)^t:Int)*(v:Int) := by exact_mod_cast hdiv
  have hc : (((2:Nat)^(t+1):Nat):Int)=((2:Nat)^t:Int)*2 := by
    rw [Nat.pow_succ, Int.natCast_mul]
    simp
  rw [hc, hz]
  have hmul := congrArg (fun x:Int => ((2:Nat)^t:Int)*x) hh
  simp only [Int.mul_add, Int.mul_sub] at hmul ⊢
  -- normalize nested multiplication of the dyadic coefficient
  simp only [Int.mul_assoc, Int.mul_comm] at hmul ⊢
  omega


def cost : List Nat → Nat
  | [] => 0
  | t :: ts => t + 1 + cost ts

def weight : List Nat → Nat
  | [] => 0
  | t :: ts => 2^t + 2^(t+1) * weight ts

def offset : List Nat → Int
  | [] => 0
  | t :: ts => ((2:Nat)^t:Int)*((t:Int)-1) +
      ((2:Nat)^(t+1):Int)*(((t:Int)+1)*(weight ts:Int)+offset ts)

inductive Run (L : Nat) : List Nat → Nat → Nat → Nat → Nat → Prop where
  | nil (m z : Nat) : Run L [] m z m z
  | cons {ts : List Nat} {m z z1 m2 z2 : Nat} (t v : Nat) :
      z = 2^t*v → 2*z1+1=L+m+t+v →
      Run L ts (m+t+1) z1 m2 z2 →
      Run L (t::ts) m z m2 z2

theorem run_cost (L : Nat) (ts : List Nat) (m z m2 z2 : Nat)
    (h : Run L ts m z m2 z2) : m2 = m + cost ts := by
  induction h with
  | nil m z => simp [cost]
  | @cons ts m z z1 m2 z2 t v hdiv hn htail ih =>
      simp only [cost]
      omega

theorem block_affine (L : Nat) (ts : List Nat) (m z m2 z2 : Nat)
    (h : Run L ts m z m2 z2) :
    (((2:Nat)^(cost ts):Nat):Int)*(z2:Int) =
      (z:Int)+(weight ts:Int)*((L:Int)+(m:Int))+offset ts := by
  induction h with
  | nil m z => simp [cost,weight,offset]
  | @cons ts m z z1 m2 z2 t v hdiv hn htail ih =>
      have he := edge_affine L m t v z z1 hdiv hn
      have hmul := congrArg (fun x:Int => ((2:Nat)^(t+1):Int)*x) ih
      have hc : (((2:Nat)^(t+1):Nat):Int) = ((2:Nat)^t:Int)*2 := by
        rw [Nat.pow_succ, Int.natCast_mul]
        simp
      rw [← Int.natCast_pow] at hmul
      rw [hc] at hmul
      simp only [cost,weight,offset, Nat.pow_add, Int.natCast_mul] at *
      rw [hc] at *
      grind

theorem linear_cost_orbit (w : List Nat) (m : Nat → Nat)
    (hm : ∀ n, m (n+1) = m n + cost w) :
    ∀ n, m n = m 0 + cost w*n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hm n, ih, Nat.mul_succ]
    omega

theorem periodic_run_integral_slope (L : Nat) (w : List Nat)
    (hw : 0 < cost w) (m z : Nat → Nat)
    (hr : ∀ n, Run L w (m n) (z n) (m (n+1)) (z (n+1))) :
    ∃ d : Int, (((2:Nat)^(cost w):Int)-1)*d =
      (weight w:Int)*(cost w:Int) := by
  have hm : ∀ n, m (n+1) = m n + cost w := by
    intro n
    exact run_cost L w (m n) (z n) (m (n+1)) (z (n+1)) (hr n)
  have hline := linear_cost_orbit w m hm
  let zi : Nat → Int := fun n => (z n : Int)
  have hrec : ∀ n,
      ((2:Nat)^(cost w):Int)*zi (n+1) = zi n +
        (weight w:Int)*((L:Int)+(m 0:Int)) +
        ((weight w:Int)*(cost w:Int))*(n:Int) + offset w := by
    intro n
    have hb := block_affine L w (m n) (z n) (m (n+1)) (z (n+1)) (hr n)
    rw [hline n] at hb
    dsimp [zi]
    simp only [Int.natCast_add,Int.natCast_mul] at hb
    grind
  have hpositive : 2 ≤ (2:Nat)^(cost w) := by
    have := Nat.one_lt_two_pow (Nat.ne_of_gt hw)
    omega
  exact PeriodCore.periodic_integral_slope (2^(cost w)) hpositive
    (weight w:Int) (cost w:Int) ((L:Int)+(m 0:Int)) (offset w) zi hrec

end PeriodWord
#print axioms PeriodWord.block_affine
#print axioms PeriodWord.periodic_run_integral_slope
