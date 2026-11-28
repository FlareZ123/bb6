import Raw14042MixedOuter
import Raw14042Mixed
import Raw14042LowLocal
namespace Raw14042AMixedTerminal
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Double Raw140VariantTransfer
open Raw14042Mixed Raw14042MixedOuter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [local irreducible] run boundary
private theorem rr {k : Nat} {c d : Prim} (h : run base k c = some d) : Reach base c d := ⟨k,h⟩
private theorem ext : Extends M42 := fill_extends _ _
abbrev A (p : Nat) (Z : List Sym) := boundary 0 true (U 3 p ++ [S 2]) Z
abbrev B (p n : Nat) (s : Tail) := boundary 1 true (U 5 p) (word (trips n) ++ tailWord s)
abbrev BL (m h n : Nat) (s : Tail) := boundary 1 false [] (U 2 m ++ S 4::S 6::(U 4 h ++ word (trips n) ++ tailWord s))

theorem deplete (j : Nat) : ∃ s : Tail, rank s = (j+5)%6 ∧
    Reach M42 (A (2*j+8) [S 5,S 2,S 1,S 5]) (BL (j+6) (j+3) ((j+5)/6) s) := by
  let s := (turn j .s6405).2
  let n := (turn j .s6405).1
  have h0 : Reach M42 (A (2*j+8) [S 5,S 2,S 1,S 5])
      (P 3 (U 3 (2*j) ++ [S 2]) [false,false] .s6405) := ⟨_, Raw14042LowLocal.seedMixed (p := 2*j)⟩
  have h1 := pairs j 2 [S 2] [false,false] .s6405
  let W := List.replicate j false ++ [false,false] ++ trips n
  have h2 := depleteEven (2+j) W s
  rw [show 2+j+1=2+1+j by omega] at h2
  have h : Reach base (P 3 (U 3 (2*j) ++ [S 2]) [false,false] .s6405)
      (boundary 1 false [] (U 2 (2+j+4) ++ S 4::S 6::mixedWord (false::(W ++ trips (carry s))) (rho s))) :=
    Reach.trans h1 h2
  have e : false::(W ++ trips (carry s)) = List.replicate (j+3) false ++ trips (n+carry s) := by
    change false::((List.replicate j false ++ [false,false] ++ trips n) ++ trips (carry s)) = _
    rw [trips_add]
    rw [show List.replicate (j+3) false = false::(List.replicate j false ++ [false,false]) by
      rw [show j+3=(j+2)+1 by omega,List.replicate_succ,List.replicate_succ',List.replicate_succ']
      simp only [List.append_assoc,List.singleton_append]]
    simp only [List.cons_append,List.append_assoc]
  rw [e] at h
  have hb := turn_balance j .s6405
  have hs := one_balance s
  have ht := rank_lt (rho s)
  change 6*n + rank s = j+4 at hb
  have hn : n+carry s=(j+5)/6 := by omega
  have hr : rank (rho s)=(j+5)%6 := by omega
  refine ⟨rho s,hr,Reach.trans h0 (Reach.ext ext ?_)⟩
  simpa only [BL,mixedWord,word_append,word_four,List.append_assoc,hn,show 2+j+4=j+6 by omega] using h

theorem pumpFours (k p : Nat) (Y : List Sym) :
    Reach base (A p (S 6::(U 4 (2*k) ++ Y))) (A (p+4*k) (S 6::Y)) := by
  induction k generalizing p with
  | zero => simpa using Reach.refl base (A p (S 6::Y))
  | succ k ih =>
    have h0 := rr (Raw14042LowLocal.pump644 p (U 4 (2*k) ++ Y))
    have h1 := ih (p+4)
    have hh : Reach base (A p (S 6::(U 4 (2*(k+1)) ++ Y))) (A (p+4) (S 6::(U 4 (2*k) ++ Y))) := by
      simpa only [A,U,show 2*(k+1)=2*k+2 by omega,List.replicate_succ,List.cons_append] using h0
    simpa only [show p+4+4*k=p+4*(k+1) by omega] using Reach.trans hh h1

theorem oddOuter (j : Nat) (hj : j%2=1) (n : Nat) (s : Tail) :
    Reach base (BL (j+6) (j+3) n s) (B (4*j+22) n s) := by
  let k := (j+3)/2
  let Z := word (trips n) ++ tailWord s
  have hk : 2*k=j+3 := by dsimp [k]; omega
  have h0 := initDrain k (S 2::S 4::S 6::(U 4 (j+3) ++ Z))
  have h0' : Reach base (boundary 1 false [] (U 2 (2*k+3) ++ S 4::S 6::(U 4 (j+3) ++ Z)))
      (A (4*k+2) (S 2::S 2::S 4::S 6::(U 4 (j+3) ++ Z))) := by
    simpa only [A,U,List.replicate_succ,List.cons_append,rep_cons] using h0
  have h1 : Reach base (BL (j+6) (j+3) n s) (A (2*j+8) (S 2::S 2::S 4::S 6::(U 4 (j+3) ++ Z))) := by
    rw [show 2*k+3=j+6 by omega,show 4*k+2=2*j+8 by omega] at h0'
    simpa only [BL,Z,List.append_assoc] using h0'
  have h2 := a224_to6 (2*j+8) (U 4 (j+3) ++ Z)
  have h3 := pumpFours k (2*j+13) Z
  rw [hk] at h3
  have h4 := rr (Raw14042LowLocal.a6ToB (2*j+13+4*k) Z)
  have h5 := Reach.trans (Reach.trans (Reach.trans h1 h2) h3) h4
  simpa only [B,Z,show 2*j+13+4*k+3=4*j+22 by omega] using h5

theorem a5215_mod2 (p : Nat) (hp : 24≤p) (hm : p%4=2) :
    ∃ s : Tail, rank s=((p-8)/2+5)%6 ∧
      Reach M42 (A p [S 5,S 2,S 1,S 5]) (B (2*p+6) (((p-8)/2+5)/6) s) := by
  let j := (p-8)/2
  have hj : p=2*j+8 := by dsimp [j]; omega
  have ho : j%2=1 := by dsimp [j]; omega
  obtain ⟨s,hr,h⟩ := deplete j
  have g := Reach.trans h (Reach.ext ext (oddOuter j ho _ s))
  exact ⟨s,hr,by simpa only [← hj,show 4*j+22=2*p+6 by omega] using g⟩
#print axioms deplete
#print axioms oddOuter
#print axioms a5215_mod2
end Raw14042AMixedTerminal
