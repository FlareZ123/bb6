import ModularCone

namespace BB6.Agent21Duality
open BB6.Agent42ModularCone

private def checkStep (f b : Nat) (s : Pair) : Bool :=
  if 2≤b then
    if Bad s then true else
      let v := valuation b (q s)
      if ValValid b s v then
        (if s.y%2=0 then check f (b-1) (residue (b-1) (direct s)) else true) &&
        (List.range (v+1)).all (fun n =>
          if Allowed s v n then
            decide (HighValid s n) &&
              check f (b-(n+2)) (residue (b-(n+2)) (high s n))
          else true)
      else false
  else false

private theorem checkStep_eq (f b : Nat) (s : Pair) :
    check (f+1) b s=checkStep f b s := rfl

/-- Every parent edge consumes at least one bit of precision, so
    replacing a fuel allowance by any other allowance which covers
    every lower precision leaves the result unchanged. -/
private theorem checkStep_congr (f g b : Nat) (s : Pair)
    (hb : 2≤b)
    (h : ∀ k, k<b → ∀ s' : Pair, check f k s'=check g k s') :
    checkStep f b s=checkStep g b s := by
  have hd : check f (b-1) (residue (b-1) (direct s)) =
      check g (b-1) (residue (b-1) (direct s)) :=
    h (b-1) (by omega) _
  have hfun :
      (fun n : Nat =>
        if Allowed s (valuation b (q s)) n then
          decide (HighValid s n) &&
            check f (b-(n+2)) (residue (b-(n+2)) (high s n))
        else true) =
      (fun n : Nat =>
        if Allowed s (valuation b (q s)) n then
          decide (HighValid s n) &&
            check g (b-(n+2)) (residue (b-(n+2)) (high s n))
        else true) := by
    funext n
    by_cases ha : Allowed s (valuation b (q s)) n
    · simp only [ha,ite_true]
      rw [h (b-(n+2)) (by omega) _]
    · simp only [ha,ite_false]
  dsimp only [checkStep]
  rw [hd,hfun]

/-- A certificate with b available modulus bits never depends on
    more than b recursive parent steps. This exact strong-induction
    theorem supplies the fuel budget needed for checker/word duality. -/
theorem check_fuel_stable (b f : Nat) (s : Pair) (hf : b≤f) :
    check f b s=check b b s := by
  induction b using Nat.strongRecOn generalizing f s with
  | ind b ih =>
    by_cases h0 : b=0
    · subst b
      cases f <;> simp [check]
    by_cases h1 : b=1
    · subst b
      cases f with
      | zero => omega
      | succ f => simp [check]
    have hb : 2≤b := by omega
    cases f with
    | zero => omega
    | succ f' =>
        cases b with
        | zero => omega
        | succ b' =>
            rw [checkStep_eq f' (b'+1) s,checkStep_eq b' (b'+1) s]
            apply checkStep_congr f' b' (b'+1) s (by omega)
            intro k hk s'
            have hfk : k≤f' := by omega
            have hbk : k≤b' := by omega
            calc
              check f' k s'=check k k s' := ih k (by omega) f' s' hfk
              _=check b' k s' := (ih k (by omega) b' s' hbk).symm

#print axioms check_fuel_stable
end BB6.Agent21Duality
