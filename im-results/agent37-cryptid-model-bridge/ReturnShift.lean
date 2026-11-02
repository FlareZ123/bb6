import FullWordPairs
import Lean.Elab.Tactic.Omega

namespace BB6.CryptidBridge

/-- Count triple-one packet tokens, independently of their ordering. -/
def tripleTokens : List Bool → Nat
  | [] => 0
  | false :: xs => tripleTokens xs
  | true :: xs => 1 + tripleTokens xs

/-- Four more A-left pairs charge 24 steps per `111` packet. -/
theorem wordCost_shift4 (m : Nat) (ws : List Bool) :
    CryptidA.wordCost (m+4) ws =
      CryptidA.wordCost m ws + 24*tripleTokens ws := by
  induction ws generalizing m with
  | nil => rfl
  | cons b ws ih =>
    cases b with
    | false =>
      simp only [CryptidA.wordCost,tripleTokens]
      have h := ih (m+1)
      have hm : m+4+1=(m+1)+4 := by omega
      rw [hm,h]
      omega
    | true =>
      simp only [CryptidA.wordCost,tripleTokens]
      have h := ih (m+4)
      have hm : m+4+4=(m+4)+4 := by omega
      rw [hm,h]
      omega

theorem wordCost_shift4h (m h : Nat) (ws : List Bool) :
    CryptidA.wordCost (m+4*h) ws =
      CryptidA.wordCost m ws + 24*h*tripleTokens ws := by
  induction h with
  | zero => simp
  | succ h ih =>
    have harg : m+4*(h+1)=(m+4*h)+4 := by omega
    rw [harg,wordCost_shift4,ih]
    simp only [Nat.mul_add,Nat.add_mul]
    omega

/-- The exact primitive time certified by `complete_A_word_two_one_pairs`. -/
def pairTime (k q : Nat) (ws : List Bool) : Nat :=
  (12*k*k+41*k+32) +
    (CryptidA.wordCost (4*k+3) ws +
      (2*((4*k+3)+CryptidA.wordInc ws)+16+4*q))

/-- Physical n↦n+3h shift has an exact, closed quadratic timing correction. -/
private theorem quadratic (k h : Nat) :
    12*(k+h)*(k+h)=12*k*k+24*k*h+12*h*h := by
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc]
  have hh : h*k=k*h := Nat.mul_comm h k
  omega

theorem pairTime_shift_h (k h q : Nat) (ws : List Bool) :
  pairTime (k+h) q ws =
    pairTime k q ws + h*(24*k+12*h+49+24*tripleTokens ws) := by
  dsimp [pairTime]
  have hh := wordCost_shift4h (4*k+3) h ws
  have hm : 4*(k+h)+3 = (4*k+3)+4*h := by omega
  rw [hm,hh,quadratic]
  have ha : 24*h*tripleTokens ws = h*(24*tripleTokens ws) := by
    ac_rfl
  have hb : 24*k*h = h*(24*k) := by
    ac_rfl
  have hc : 12*h*h = h*(12*h) := by
    ac_rfl
  rw [ha,hb,hc]
  simp only [Nat.mul_add]
  omega

/-- Original frozen-halt raw-machine source family, with unchanged right suffix. -/
def pairInput (k q : Nat) (ws ys : List Bool) : CryptidBoundary.Cfg :=
  CryptidBoundary.init
    (List.replicate (3*k+1) true ++
      false :: (CryptidA.wordCode ws ++
        ([true,true,false] ++ (CryptidBoundary.pairs q ++ (false::ys)))))

theorem pair_source (k q : Nat) (ws ys : List Bool) :
  CryptidBoundary.run (pairTime k q ws) (pairInput k q ws ys) =
    ⟨[],false,
      List.replicate (2*((4*k+3)+CryptidA.wordInc ws)+1) true ++
        (false :: List.replicate (2*q+6) true ++ ys),5⟩ :=
  complete_A_word_two_one_pairs k q ws ys

private theorem output_prefix_shift (k h inc q : Nat) (ys : List Bool) :
    List.replicate (2*(4*(k+h)+3+inc)+1) true ++
      (false :: List.replicate (2*q+6) true ++ ys) =
    List.replicate (8*h) true ++
      (List.replicate (2*(4*k+3+inc)+1) true ++
        (false :: List.replicate (2*q+6) true ++ ys)) := by
  have hn : 2*(4*(k+h)+3+inc)+1 =
    (8*h)+(2*(4*k+3+inc)+1) := by omega
  rw [hn, ←List.replicate_append_replicate]
  simp only [List.append_assoc]

/-- A genuine source-level shifted-completed-return identity, for all h≥0.
    The two raw Turing machines start with n differing by 3h consecutive
    ones and finish with corresponding F/0 unary words differing by 8h ones;
    their primitive return clocks are related by `pairTime_shift_h`. -/
theorem paired_return_shift_h (k h q : Nat) (ws ys : List Bool) :
    CryptidBoundary.run (pairTime (k+h) q ws)
      (pairInput (k+h) q ws ys) =
    ⟨[],false,
      List.replicate (8*h) true ++
        (CryptidBoundary.run (pairTime k q ws)
          (pairInput k q ws ys)).r,5⟩ := by
  rw [pair_source (k+h) q ws ys, pair_source k q ws ys]
  change
    (⟨[],false,
       List.replicate (2*(4*(k+h)+3+CryptidA.wordInc ws)+1) true ++
         (false :: List.replicate (2*q+6) true ++ ys),5⟩ : CryptidBoundary.Cfg) =
    ⟨[],false,
      List.replicate (8*h) true ++
        (List.replicate (2*(4*k+3+CryptidA.wordInc ws)+1) true ++
          (false :: List.replicate (2*q+6) true ++ ys)),5⟩
  congr 1
  exact output_prefix_shift k h (CryptidA.wordInc ws) q ys

#print axioms wordCost_shift4h
#print axioms pairTime_shift_h
#print axioms paired_return_shift_h
end BB6.CryptidBridge
