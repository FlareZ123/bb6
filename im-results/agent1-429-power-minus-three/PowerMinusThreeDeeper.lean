import PowerMinusThreeSource
import Lean.Elab.Tactic.Omega

namespace BB429PowerMinusThreeDeeper
open BB429PowerMinusThreeArithmetic

/-- A t=3 modulo eight secondary parent forces an impossible even predecessor. -/
theorem side_three_mod_eight (n P Q x y t : Nat)
    (hs : Side P Q x y t) (hx : 13≤x)
    (hr : BB429.run n (0,0)=some (x,y))
    (ht : t%8=3) : False := by
  have hxmod : x%8=3 := by
    rcases hs with ⟨hp,hq,hx,hy⟩
    omega
  have hymod : y%4=3 := by
    rcases hs with ⟨hp,hq,hx,hy⟩
    omega
  have hyx : (y+x)%8=6 := by
    rcases hs with ⟨hp,hq,hx,hy⟩
    omega
  rcases BB429NewResidue.odd_back x y hx (by omega) ⟨n,hr⟩ with
    ⟨u,v,⟨m,hm⟩,hf,hy⟩ | ⟨u,v,⟨m,hm⟩,hx,hy,hm4⟩
  · have hupar : u%2=0 := by omega
    have hupos : 0<u := by omega
    have hvmod : v%8=6 := by omega
    have hrmod := BB429RootEven8.rooted_positive_even_eight m u v hm hupos hupar
    omega
  · omega

/-- Two source-necessary forced F inverses prohibit t=5 modulo32. -/
theorem side_five_mod_thirtytwo (n P Q x y t : Nat)
    (hs : Side P Q x y t) (hx : 29≤x)
    (hr : BB429.run n (0,0)=some (x,y))
    (ht : t%32=5) : False := by
  have hxmod : x%32=5 := by
    rcases hs with ⟨hp,hq,hx,hy⟩
    omega
  have hymod : y%4=3 := by
    rcases hs with ⟨hp,hq,hx,hy⟩
    omega
  rcases BB429NewResidue.odd_back x y (by omega) (by omega) ⟨n,hr⟩ with
    ⟨u,v,⟨m,hm⟩,hf,hy⟩ | ⟨u,v,⟨m,hm⟩,hf,hy,hm4⟩
  · have humod : u%16=1 := by omega
    have hvlmod : v%4=0 := by
      rcases hs with ⟨hp,hq,hxa,hya⟩
      omega
    have hul : 13≤u := by omega
    rcases BB429NewResidue.odd_back u v hul (by omega) ⟨m,hm⟩ with
      ⟨p,q,⟨l,hl⟩,hp,hq⟩ | ⟨p,q,⟨l,hl⟩,hp,hq,hmod⟩
    · have hpm : p%8=7 := by omega
      have hqm : q%4=1 := by omega
      have hh := BB429Mod8.all_blank_returns_allowed l p q hl
      unfold BB429Mod8.Allowed at hh
      omega
    · omega
  · omega

/-- Arithmetic criterion covering exactly 25 of the 32 possible residues. -/
def Forbidden25 (t : Nat) : Prop :=
  t%2=0 ∨ t%8=1 ∨ t%8=3 ∨ t%32=5

def Forbidden25Boolean (t : Nat) : Bool :=
  (t%2==0) || (t%8==1) || (t%8==3) || (t%32==5)

theorem forbidden25_count :
  ((List.range 32).filter Forbidden25Boolean).length=25 := by decide

theorem side_forbidden_25 (n P Q x y t : Nat)
    (hs : Side P Q x y t) (hx : 29≤x)
    (hr : BB429.run n (0,0)=some (x,y))
    (ht : Forbidden25 t) : False := by
  rcases ht with he|hone|hthree|hfive
  · exact BB429PowerMinusThree.side_forbidden n P Q x y t hs (by omega) hr (Or.inl he)
  · exact BB429PowerMinusThree.side_forbidden n P Q x y t hs (by omega) hr (Or.inr (Or.inl hone))
  · exact side_three_mod_eight n P Q x y t hs (by omega) hr hthree
  · exact side_five_mod_thirtytwo n P Q x y t hs hx hr hfive

/-- For 25/32 t residues, the genuine source inverse is forced to use F. -/
theorem spine_forced_first_25 (n P Q t a b : Nat)
    (hp : P%64=0) (hq : Q%64=0)
    (ha : a+3=2*Q)
    (hb : b+4*Q+12*t+10=4*P)
    (ha13 : 13≤a)
    (ht : Forbidden25 t)
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
      have hqbig : 64≤Q := by omega
      have hxlarge : 29≤p.1 := by omega
      exact False.elim (side_forbidden_25 n P Q p.1 p.2 t side hxlarge hm ht)

#print axioms forbidden25_count
#print axioms spine_forced_first_25
#print axioms side_three_mod_eight
#print axioms side_five_mod_thirtytwo
end BB429PowerMinusThreeDeeper
