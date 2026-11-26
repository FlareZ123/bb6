import Raw13CoupledDrain

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13DrainAll
open BB6.Agent46Raw13RightCounter
open BB6.Agent46Raw13CounterBudget
open BB6.Agent46Raw13DrainCore
open BB6.Agent46Raw13CoupledDrain
open BB6.Agent46Raw13TapeValue (F Reach reach_trans F_pad)

def zeroCount : List Bool → Nat
  | [] => 0
  | false::bs => 1+zeroCount bs
  | true::bs => zeroCount bs

theorem zeroCount_append (a b : List Bool) : zeroCount (a++b)=zeroCount a+zeroCount b := by
  induction a with
  | nil => simp [zeroCount]
  | cons c a ih => cases c <;> simp [zeroCount,ih,Nat.add_assoc]

theorem zeroCount_zeros (n : Nat) : zeroCount (zeros n)=n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change 1+zeroCount (zeros n)=n+1
    omega

def cost (n : Nat) : Nat := if n=0 then 0 else 2^n

theorem mul_bound (a b : Nat) (ha : 2≤a) (hb : 2≤b) : a+b≤a*b := by
  have h : (a-2) ≤ (a-2)*b := by
    have h := Nat.mul_le_mul_left (a-2) (show 1≤b by omega)
    simpa using h
  have he : a*b = 2*b+(a-2)*b := by
    rw [← Nat.add_mul]
    congr 1 <;> omega
  omega

theorem two_le_pow (n : Nat) (h : 0<n) : 2≤2^n := by
  cases n with
  | zero => omega
  | succ n => have hn := Nat.two_pow_pos n; rw [Nat.pow_succ]; omega

theorem cost_add (a b : Nat) : cost a+cost b≤cost (a+b) := by
  by_cases ha : a=0
  · subst a; simp [cost]
  by_cases hb : b=0
  · subst b; simp [cost]
  have h : a+b≠0 := by omega
  simp only [cost,ha,hb,h,ite_false,Nat.pow_add]
  exact mul_bound _ _ (two_le_pow a (by omega)) (two_le_pow b (by omega))

theorem leading (xs : List Bool) : (∃ k, xs=zeros k) ∨ ∃ k ys, xs=zeros k++true::ys := by
  induction xs with
  | nil => exact Or.inl ⟨0,rfl⟩
  | cons a xs ih => cases a with
    | true => exact Or.inr ⟨0,xs,rfl⟩
    | false =>
      rcases ih with ⟨k,rfl⟩|⟨k,ys,rfl⟩
      · exact Or.inl ⟨k+1,rfl⟩
      · exact Or.inr ⟨k+1,ys,rfl⟩

theorem drainRun (h k : Nat) (bs P V : List Bool) (b : Nat) (hb : enough P (b+cost k)) :
    ∃ P', Reach (D h (zeros k++true::bs) (P++V)) (D 0 bs (P'++V)) ∧ enough P' b := by
  cases k with
  | zero =>
    have h' := drainOdd h bs P V b (by simpa [cost] using hb)
    exact ⟨true::zeros (3*h)++true::P,h'⟩
  | succ k =>
    exact drainEven h k bs P V b (by simpa [cost] using hb)

/-- Consume a word plus its final sentinel one, never touching the suffix V.
    Cost is bounded by the exponential of the number of zero digits. -/
theorem consume (h : Nat) (xs bs P V : List Bool) (b : Nat) (hb : enough P (b+cost (zeroCount xs))) :
    ∃ P', Reach (D h (xs++true::bs) (P++V)) (D 0 bs (P'++V)) ∧ enough P' b := by
  rcases leading xs with ⟨k,hk⟩|⟨k,ys,hk⟩
  · rw [hk,zeroCount_zeros] at hb
    rw [hk]
    exact drainRun h k bs P V b hb
  · have hz : zeroCount xs = k+zeroCount ys := by rw [hk,zeroCount_append,zeroCount_zeros]; rfl
    have hb' : enough P (b+cost (zeroCount ys)+cost k) :=
      enough_mono hb (by rw [hz]; have h := cost_add k (zeroCount ys); omega)
    obtain ⟨P1,h1,b1⟩ := drainRun h k (ys++true::bs) P V (b+cost (zeroCount ys)) hb'
    obtain ⟨P2,h2,b2⟩ := consume 0 ys bs P1 V b b1
    rw [hk,List.append_assoc,List.cons_append]
    exact ⟨P2,reach_trans h1 h2,b2⟩
termination_by xs.length
decreasing_by
  rw [hk,List.length_append,List.length_cons]
  omega

theorem finishDrain (h : Nat) (xs P V : List Bool) (hb : enough P (cost (zeroCount xs))) :
    ∃ Q, Reach (D h (xs++[true,true,true]) (P++V)) (F [true] (([true,true,true,true]++Q)++V)) := by
  obtain ⟨P1,h1,b1⟩ := consume h xs [true,true] P V 0 (by simpa using hb)
  obtain ⟨h2,b2⟩ := drainOdd 0 [true] P1 V 0 b1
  obtain ⟨h3,_⟩ := drainOdd 0 [] (true::true::P1) V 0 (by simpa [zeros] using b2)
  have hr := reach_trans (reach_trans h1 h2) h3
  have he : D 0 [] ([true,true,true,true]++P1++V) = F [true] ([true,true,true,true]++P1++V) := by
    change F ([true]++BB6.Agent46Raw13Frames.zeros 2) _ = _
    exact F_pad [true] _ 2
  change Reach (D h (xs++[true,true,true]) (P++V)) (D 0 [] ([true,true,true,true]++P1++V)) at hr
  rw [he] at hr
  exact ⟨P1,hr⟩

#print axioms consume
#print axioms finishDrain
end BB6.Agent46Raw13DrainAll
