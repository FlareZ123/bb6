import PowerMinusThreeDeeper
import Lean.Elab.Tactic.Omega
namespace BB429PowerMinusThreeSeven
open BB429PowerMinusThreeArithmetic

/-- Secondary predecessors for t=7 or23 modulo32 force a forbidden
genuine blank-root E or subsequent F ancestor. -/
theorem side_seven_twenty_three (n P Q x y t : Nat)
    (hs : Side P Q x y t) (hx : 29≤x)
    (hr : BB429.run n (0,0)=some (x,y))
    (ht : t%32=7 ∨ t%32=23) : False := by
  have hxmod : x%8=7 := by
    rcases hs with ⟨hp,hq,hxa,hya⟩
    rcases ht with ht7|ht23 <;> omega
  have hymod : y%4=3 := by
    rcases hs with ⟨hp,hq,hxa,hya⟩
    rcases ht with ht7|ht23 <;> omega
  rcases BB429NewResidue.odd_back x y (by omega) (by omega) ⟨n,hr⟩ with
    ⟨u,v,⟨m,hm⟩,hu,hv⟩ | ⟨u,v,⟨m,hm⟩,hu,hv,hmod⟩
  · have hupos : 6≤u := by omega
    have humod : u%2=0 := by omega
    rcases BB429NewResidue.even_back u v hupos humod ⟨m,hm⟩ with
      ⟨w,z,⟨l,hl⟩,hfirst,hsecond,hvmod⟩
    rcases ht with ht7|ht23
    · have hwmod : w%8=7 := by
        rcases hs with ⟨hp,hq,hxa,hya⟩
        omega
      have hzmod : z%4=1 := by
        rcases hs with ⟨hp,hq,hxa,hya⟩
        omega
      have hh := BB429Mod8.all_blank_returns_allowed l w z hl
      unfold BB429Mod8.Allowed at hh
      omega
    · have hwmod : w%8=3 := by
        rcases hs with ⟨hp,hq,hxa,hya⟩
        omega
      have hzmod : z%4=1 := by
        rcases hs with ⟨hp,hq,hxa,hya⟩
        omega
      have hz8 : z%8=1 := by
        rcases hs with ⟨hp,hq,hxa,hya⟩
        omega
      have hwlarge : 13≤w := by omega
      rcases BB429NewResidue.odd_back w z hwlarge (by omega) ⟨l,hl⟩ with
        ⟨a,b,⟨j,hj⟩,ha,hb⟩ | ⟨a,b,⟨j,hj⟩,ha,hb,hz2⟩
      · have hapos : 0<a := by omega
        have heven : a%2=0 := by omega
        have hbmod : b%8=4 := by omega
        have hh := BB429RootEven8.rooted_positive_even_eight j a b hj hapos heven
        omega
      · omega
  · omega

def Forbidden27 (t : Nat) : Prop :=
  BB429PowerMinusThreeDeeper.Forbidden25 t ∨ t%32=7 ∨ t%32=23

def Forbidden27Boolean (t : Nat) : Bool :=
  (t%2==0) || (t%8==1) || (t%8==3) || (t%32==5) || (t%32==7) || (t%32==23)

theorem forbidden27_count :
  ((List.range 32).filter Forbidden27Boolean).length=27 := by decide

theorem side_forbidden_27 (n P Q x y t : Nat)
    (hs : Side P Q x y t) (hx : 29≤x)
    (hr : BB429.run n (0,0)=some (x,y))
    (ht : Forbidden27 t) : False := by
  rcases ht with h25 | h7 | h23
  · exact BB429PowerMinusThreeDeeper.side_forbidden_25 n P Q x y t hs hx hr h25
  · exact side_seven_twenty_three n P Q x y t hs hx hr (Or.inl h7)
  · exact side_seven_twenty_three n P Q x y t hs hx hr (Or.inr h23)

/-- True-blank-source forced first predecessor for 27 of 32 secondary-branch
parameter residues, with no hypothetical-root substitution. -/
theorem spine_forced_first_27 (n P Q t a b : Nat)
    (hp : P%64=0) (hq : Q%64=0)
    (ha : a+3=2*Q)
    (hb : b+4*Q+12*t+10=4*P)
    (ha13 : 13≤a)
    (ht : Forbidden27 t)
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
      exact False.elim (side_forbidden_27 n P Q p.1 p.2 t side hxlarge hm ht)

#print axioms forbidden27_count
#print axioms spine_forced_first_27
#print axioms side_seven_twenty_three
end BB429PowerMinusThreeSeven
