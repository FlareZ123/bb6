import Raw14042AMixedTerminal
namespace Raw14042AMixedEven
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Double Raw140VariantTransfer
open Raw14042MixedOuter Raw14042AMixedTerminal
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [local irreducible] run boundary
private theorem rr {k : Nat} {c d : Prim} (h : run base k c = some d) : Reach base c d := ⟨k,h⟩
private theorem ext : Extends M42 := fill_extends _ _

theorem eOdd66 (a : Nat) (W : List Bool) (s : Tail) :
    Reach base (E a 1 (S 6::S 6::(word W ++ tailWord s)))
      (boundary 3 false [] (U 4 (a+5) ++ S 6::(word W ++ word (trips (carry s)) ++ tailWord (rho s)))) := by
  have h₁ := convert2 a (S 4::S 6::S 6::(word W ++ tailWord s))
  have h₂ := Raw14042MixedLocal.eOne66 (U 5 (a+2)) (word W ++ tailWord s)
  have h₃ := bounce (true::W) s (U 5 (a+4))
  have h₄ : Reach base (E a 1 (S 6::S 6::(word W ++ tailWord s)))
      (boundary 3 false (U 5 (a+5)) (S 6::(word W ++ word (trips (carry s)) ++ tailWord (rho s)))) :=
    Reach.trans (Reach.trans ⟨_,h₁⟩ ⟨_,h₂⟩) h₃
  have h₅ := sweepL base 3 (S 5) (S 4) 3 (a+5) []
    (S 6::(word W ++ word (trips (carry s)) ++ tailWord (rho s))) (by rfl)
  exact Reach.trans h₄ ⟨_,by simpa only [U,List.append_nil] using h₅⟩

abbrev T (n : Nat) (s : Tail) := word (trips n) ++ tailWord s

theorem dInitial (k h n : Nat) (s : Tail) (hk : 0<k) :
    Reach base (boundary 3 false (U 6 k ++ [S 4]) (S 6::S 6::(U 4 h ++ T n s)))
      (E 1 (k-1) (S 6::S 6::(U 4 h ++ T (n+(turn k s).1) (turn k s).2))) := by
  let W := [true,true] ++ List.replicate h false ++ trips n
  have h0 := dIter k [S 4] W s
  have hh : Reach base (boundary 3 false (U 6 k ++ [S 4]) (S 6::S 6::(U 4 h ++ T n s)))
      (boundary 3 false [S 4] (U 4 k ++ S 6::S 6::(U 4 h ++ T (n+(turn k s).1) (turn k s).2))) := by
    simpa only [W,T,word_append,word_four,word,ite_true,List.cons_append,List.nil_append,List.append_assoc,← trips_add] using h0
  have h1 := dEndE (k-1) (S 6::S 6::(U 4 h ++ T (n+(turn k s).1) (turn k s).2))
  rw [show k-1+1=k by omega] at h1
  exact Reach.trans hh h1

theorem eOdd66Bank (a h n : Nat) (s : Tail) :
    Reach base (E a 1 (S 6::S 6::(U 4 h ++ T n s)))
      (E (a+5) h (T (n+carry s) (rho s))) := by
  have g := eOdd66 a (List.replicate h false ++ trips n) s
  simpa only [E,T,word_append,word_four,List.append_assoc,trips_add] using g

theorem lastTwo (a n : Nat) (s : Tail) (hn : 2 ≤ n+carry s) (hpos : 1 ≤ n) :
    Reach base (E a 1 (T n s)) (B (a+14) (n+carry s-2) (rho s)) := by
  have he := eOddLast a (false::trips (n-1)) s
  have hh : Reach base (E a 1 (T n s))
      (boundary 3 false [] (U 4 (a+7) ++ T (n-1+carry s) (rho s))) := by
    have hEq : n = n-1+1 := by omega
    have hs : T n s = S 6::S 4::(word (false::trips (n-1)) ++ tailWord s) := by
      conv => lhs; rw [hEq]
      rfl
    rw [← hs] at he
    simpa only [T,word,ite_false,Bool.false_eq_true,List.cons_append,List.append_assoc,rep_cons,← word_append,← trips_add,U,List.replicate_succ] using he
  have htail : T (n-1+carry s) (rho s) = S 6::S 4::S 4::T (n+carry s-2) (rho s) := by
    rw [show n-1+carry s=(n+carry s-2)+1 by omega]
    rfl
  have hi : Reach base (E (a+7) 2 (T (n+carry s-2) (rho s))) (B (a+14) (n+carry s-2) (rho s)) := by
    simpa only [B,show a+7+4*1+3=a+14 by omega] using eEven 1 (a+7) (T (n+carry s-2) (rho s))
  rw [htail] at hh
  exact Reach.trans hh hi

theorem evenOuter (j : Nat) (hj : j%2=0) (n : Nat) (s : Tail) (hs : 6*n+rank s=j+5) :
    ∃ t : Tail, rank t=1 ∧ Reach base (BL (j+6) (j+3) n s) (B (6*j+44) (j/2+1) t) := by
  let k := (j+4)/2
  have hk : 2*k=j+4 := by dsimp [k]; omega
  have h0 := initDrain k (S 4::S 6::(U 4 (j+3) ++ T n s))
  rw [show 2*k+2=j+6 by omega,show 4*k+2=2*j+10 by omega] at h0
  have h0' : Reach base (BL (j+6) (j+3) n s) (A (2*j+10) (S 2::S 4::S 6::(U 4 (j+3) ++ T n s))) := by
    simpa only [BL,T,List.append_assoc] using h0
  have h1 := rr (Raw14042LowLocal.a24ToD (2*j+10) (S 6::(U 4 (j+3) ++ T n s)))
  have h2 := dInitial (2*j+12) (j+3) n s (by omega)
  let n1 := n+(turn (2*j+12) s).1
  let s1 := (turn (2*j+12) s).2
  let n2 := n1+carry s1
  let s2 := rho s1
  have h2' : Reach base (boundary 3 false (U 6 (2*j+12) ++ [S 4]) (S 6::S 6::(U 4 (j+3) ++ T n s)))
      (E 1 (2*j+11) (S 6::S 6::(U 4 (j+3) ++ T n1 s1))) := by
    simpa only [n1,s1,show 2*j+12-1=2*j+11 by omega] using h2
  have h3 := eIter (j+5) 1 1 (S 6::S 6::(U 4 (j+3) ++ T n1 s1))
  rw [show 2*(j+5)+1=2*j+11 by omega,show 1+4*(j+5)=4*j+21 by omega] at h3
  have h4 := eOdd66Bank (4*j+21) (j+3) n1 s1
  have h4' : Reach base (E (4*j+21) 1 (S 6::S 6::(U 4 (j+3) ++ T n1 s1))) (E (4*j+26) (j+3) (T n2 s2)) := by
    simpa only [n2,s2,show 4*j+21+5=4*j+26 by omega] using h4
  have h5 := eIter ((j+2)/2) (4*j+26) 1 (T n2 s2)
  rw [show 2*((j+2)/2)+1=j+3 by omega,show 4*j+26+4*((j+2)/2)=6*j+30 by omega] at h5
  have b1 := turn_balance (2*j+12) s
  have b2 := one_balance s1
  have b3 := one_balance s2
  have l2 := rank_lt s2
  have l3 := rank_lt (rho s2)
  have b4 : 6*n2+rank s2=3*j+18 := by dsimp [n2,s2,n1,s1] at *; omega
  have hn : 2 ≤ n2+carry s2 := by omega
  have hn' : 1 ≤ n2 := by omega
  have h6 := lastTwo (6*j+30) n2 s2 hn hn'
  have hr : rank (rho s2)=1 := by omega
  have hc : n2+carry s2-2=j/2+1 := by omega
  rw [hc,show 6*j+30+14=6*j+44 by omega] at h6
  exact ⟨rho s2,hr,Reach.trans (Reach.trans (Reach.trans (Reach.trans (Reach.trans (Reach.trans h0' h1) h2') h3) h4') h5) h6⟩

theorem a5215_mod0 (p : Nat) (hp : 24≤p) (hm : p%4=0) :
    ∃ s : Tail, rank s=1 ∧ Reach M42 (A p [S 5,S 2,S 1,S 5]) (B (3*p+20) (p/4-1) s) := by
  let j := (p-8)/2
  have hj : p=2*j+8 := by dsimp [j]; omega
  have he : j%2=0 := by dsimp [j]; omega
  obtain ⟨s,hr,h⟩ := deplete j
  obtain ⟨t,ht,g⟩ := evenOuter j he ((j+5)/6) s (by omega)
  have hg := Reach.trans h (Reach.ext ext g)
  exact ⟨t,ht,by simpa only [← hj,show 6*j+44=3*p+20 by omega,show j/2+1=p/4-1 by omega] using hg⟩

#print axioms eOdd66Bank
#print axioms lastTwo
#print axioms evenOuter
#print axioms a5215_mod0
end Raw14042AMixedEven
