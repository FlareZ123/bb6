import BB429NewRootRows
import BB429NewResidue
import PowerMinusThreeArithmetic
import Lean.Elab.Tactic.Omega

namespace BB429PowerMinusThree
open BB429PowerMinusThreeArithmetic

/-- True blank-root obstruction for the S predecessor of a power-minus-three
first spine; the parameters are arbitrary multiples of 64. -/
theorem side_forbidden (n P Q x y t : Nat)
    (hs : Side P Q x y t) (hxpos : 0<x)
    (hr : BB429.run n (0,0)=some (x,y))
    (ht : t%2=0 ∨ t%8=1 ∨ t%16=3 ∨ t%32=11) : False := by
  rcases ht with he | hone | hthree | heleven
  · obtain ⟨hx,hy⟩ := even_t P Q x y t hs he
    exact hy (BB429RootEven8.rooted_positive_even_eight n x y hr hxpos hx)
  · obtain ⟨hx,hy⟩ := one_mod_eight P Q x y t hs hone
    have ha := BB429Mod8.all_blank_returns_allowed n x y hr
    unfold BB429Mod8.Allowed at ha
    omega
  · obtain ⟨hx,hy⟩ := three_mod_sixteen P Q x y t hs hthree
    have ha := BB429NewRootRows.rooted_eleven n x y hr hx
    omega
  · obtain ⟨hx,hy⟩ := eleven_mod_thirtytwo P Q x y t hs heleven
    have ha := BB429NewRootRows.rooted_nineteen_or_twentyseven n x y hr (Or.inl hx)
    omega

/-- At the specified odd target, the S inverse branch cannot occur on the
genuine blank orbit in these congruence classes; the F ancestor is forced. -/
theorem spine_forced_first (n P Q t a b : Nat)
    (hp : P%64=0) (hq : Q%64=0)
    (ha : a+3=2*Q)
    (hb : b+4*Q+12*t+10=4*P)
    (ha13 : 13≤a)
    (ht : t%2=0 ∨ t%8=1 ∨ t%16=3 ∨ t%32=11)
    (hr : BB429.run (n+1) (0,0)=some (a,b)) :
    BB429.run n (0,0)=some ((a-3)/2,b+a) := by
  simp only [BB429.run] at hr
  cases hm : BB429.run n (0,0) with
  | none => simp [hm] at hr
  | some p =>
    simp only [hm,Option.bind_some] at hr
    have hodd : a%2=1 := by omega
    rcases BB429NewResidue.odd_inverse p.1 p.2 a b ha13 hodd hr with ⟨hf,hy⟩ | ⟨hx,hy,hmod⟩
    · have heq : p=((a-3)/2,b+a) := Prod.ext (by omega) (by omega)
      simpa only [heq] using hm
    · have side : Side P Q p.1 p.2 t := by
        dsimp [Side]
        constructor
        · exact hp
        constructor
        · exact hq
        constructor <;> omega
      have hxpos : 0<p.1 := by omega
      exact False.elim (side_forbidden n P Q p.1 p.2 t side hxpos hm ht)

#print axioms side_forbidden
#print axioms spine_forced_first
end BB429PowerMinusThree
