import Raw112HighIncrement
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw112CarryRoot
open BB6Coverage BB6Coverage.Agent31Pump Raw112CarrySweeps Raw112HighIncrement

def low : Nat → List Bool
  | 0 => w "110000000000"
  | 1 => w "000000111111"
  | 2 => w "111110111111"
  | 3 => w "110011000001"
  | 4 => w "000001111111"
  | 5 => w "111111111111"
  | _ => []
def mid : Nat → List Bool
  | 0 => w "0011111100000"
  | 1 => w "1111110111111"
  | 2 => w "0000011000001"
  | 3 => w "0011111000001"
  | 4 => w "1111111111111"
  | 5 => w "0000000000000"
  | _ => []

def cFrameEven := w "11111101111111101"
def cFrameOdd := w "11111111111111101"

theorem c_even_enter (L H : List Bool) :
    run0 table 86 (cfg 2 (true::L) (w "010111" ++ (low 2 ++ H))) =
      some (cfg 4 (w "10" ++ (cFrameEven ++ L)) H) := by rfl

theorem c_even_finish (L H : List Bool) :
    run0 table 32 (cfg 3 (true::(cFrameEven ++ L)) (false::H)) =
      some (cfg 1 L (w "101100" ++ (mid 2 ++ H))) := by rfl

theorem c_odd_enter (L H : List Bool) :
    run0 table 84 (cfg 2 (true::L) (w "010111" ++ (low 5 ++ H))) =
      some (cfg 4 (w "10" ++ (cFrameOdd ++ L)) H) := by rfl

theorem c_odd_finish (L H : List Bool) :
    run0 table 24 (cfg 1 (true::(cFrameOdd ++ L)) (true::H)) =
      some (cfg 1 L (w "101100" ++ (mid 5 ++ H))) := by rfl

theorem c_even (k : Nat) (hk : k%2=0) : ∃ t, 0<t ∧ ∀ L,
    run0 table t (cfg 2 (true::L) (w "010111" ++ (low 2 ++ high k))) =
      some (cfg 1 L (w "101100" ++ (mid 2 ++ high (k+1)))) := by
  obtain ⟨t,ht,h⟩ := high_inc k
  refine ⟨86+t+32,by omega,fun L => ?_⟩
  have h1 := c_even_enter L (high k)
  have h2 := h (cFrameEven ++ L)
  simp only [target,hk,ite_true] at h2
  exact join0 (join0 h1 h2) (c_even_finish L (high (k+1)))

theorem c_odd (k : Nat) (hk : k%2≠0) : ∃ t, 0<t ∧ ∀ L,
    run0 table t (cfg 2 (true::L) (w "010111" ++ (low 5 ++ high k))) =
      some (cfg 1 L (w "101100" ++ (mid 5 ++ high (k+1)))) := by
  obtain ⟨t,ht,h⟩ := high_inc k
  refine ⟨84+t+24,by omega,fun L => ?_⟩
  have h1 := c_odd_enter L (high k)
  have h2 := h (cFrameOdd ++ L)
  simp only [target,hk,ite_false] at h2
  exact join0 (join0 h1 h2) (c_odd_finish L (high (k+1)))

/-- All six low phases, including both unbounded recursive carries. -/
theorem c_return (n : Nat) : ∃ t, 0<t ∧ ∀ L,
    run0 table t (cfg 2 (true::L) (w "010111" ++ (low (n%6) ++ high (n/3)))) =
      some (cfg 1 L (w "101100" ++ (mid (n%6) ++ high ((n+1)/3)))) := by
  have hc : n%6=0 ∨ n%6=1 ∨ n%6=2 ∨ n%6=3 ∨ n%6=4 ∨ n%6=5 := by omega
  rcases hc with h|h|h|h|h|h
  · rw [h,show (n+1)/3=n/3 by omega]
    exact ⟨71,by decide,fun L => by rfl⟩
  · rw [h,show (n+1)/3=n/3 by omega]
    exact ⟨59,by decide,fun L => by rfl⟩
  · rw [h,show (n+1)/3=n/3+1 by omega]
    exact c_even (n/3) (by omega)
  · rw [h,show (n+1)/3=n/3 by omega]
    exact ⟨65,by decide,fun L => by rfl⟩
  · rw [h,show (n+1)/3=n/3 by omega]
    exact ⟨59,by decide,fun L => by rfl⟩
  · rw [h,show (n+1)/3=n/3+1 by omega]
    exact c_odd (n/3) (by omega)

/-- The second suffix operation never needs to inspect the high word. -/
theorem d_return (p : Nat) (hp : p<6) : ∃ t, 0<t ∧ ∀ L H,
    run0 table t (cfg 3 (w "011001" ++ L) (w "01100" ++ (mid p ++ H))) =
      some (cfg 1 (w "111" ++ L) (w "100001111" ++ (low ((p+1)%6) ++ H))) := by
  have hc : p=0 ∨ p=1 ∨ p=2 ∨ p=3 ∨ p=4 ∨ p=5 := by omega
  rcases hc with h|h|h|h|h|h <;> subst p
  · exact ⟨121,by decide,fun L H => by rfl⟩
  · exact ⟨63,by decide,fun L H => by rfl⟩
  · exact ⟨69,by decide,fun L H => by rfl⟩
  · exact ⟨115,by decide,fun L H => by rfl⟩
  · exact ⟨63,by decide,fun L H => by rfl⟩
  · exact ⟨69,by decide,fun L H => by rfl⟩

def family (n : Nat) : Z0 := boundary (n+1) (low ((n+1)%6) ++ high ((n+1)/3))

theorem growth (n : Nat) : ∃ t, 0<t ∧ run0 table t (family n) = some (family (n+1)) := by
  obtain ⟨a,ha,hc⟩ := c_return (n+1)
  obtain ⟨b,hb,hd⟩ := d_return ((n+1)%6) (by omega)
  refine ⟨150*n+276+a+b,by omega,?_⟩
  have hp : (((n+1)%6)+1)%6 = (n+2)%6 := by omega
  have h := return_of_suffix n a b (low ((n+1)%6) ++ high ((n+1)/3))
    (mid ((n+1)%6) ++ high ((n+2)/3)) (low ((n+2)%6) ++ high ((n+2)/3)) hc
    (fun L => by simpa only [hp] using hd L (high ((n+2)/3)))
  exact h

theorem entry : run0 table 382 ⟨0,[],[]⟩ = some (family 0) := by
  unfold family
  rw [show (0+1)/3=0 by decide,high_small 0 (by decide)]
  rfl

/-- Arbitrarily long live primitive prefixes from the literal blank start. -/
theorem unbounded_live (N : Nat) : ∃ t n, N ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some (family n) := by
  induction N with
  | zero => exact ⟨382,0,by decide,entry⟩
  | succ N ih =>
    obtain ⟨t,n,ht,hr⟩ := ih
    obtain ⟨d,hd,h⟩ := growth n
    exact ⟨t+d,n+1,by omega,join0 hr h⟩

#print axioms c_return
#print axioms d_return
#print axioms entry
#print axioms growth
#print axioms unbounded_live
end BB6Coverage.Agent31Pump.Raw112CarryRoot
