import BB429NewResidue
import BB429RootMod16

namespace BB429Forced13
open BB429NewResidue
set_option maxHeartbeats 30000000
set_option maxRecDepth 30000

/-!
# All-parameter genuine-root forced predecessor for the #429 odd-reset 13-line.

Unlike the signed affine approximation, these statements use the original
BB429.run blank-start reachability and exact source inverse lemmas. The
first three predecessors have forced odd-first F branches. On step four
the F child violates the all-time positive-even eight-gate; therefore
the S child is genuinely root-reachable.
-/

/-- Three forced original positive odd inverse steps, independent of q residue. -/
theorem three_forced_F (q : Nat) (hq : 4 ≤ q)
    (hr : Reach (32*q+13) (64*q+23)) :
    Reach (4*q-1) (120*q+42) := by
  have h1 : Reach (16*q+5) (96*q+36) := by
    rcases odd_back (32*q+13) (64*q+23) (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hb⟩
    · have hxa : x = 16*q+5 := by omega
      have hya : y = 96*q+36 := by omega
      rw [hxa,hya] at hp
      exact hp
    · omega
  have h2 : Reach (8*q+1) (112*q+41) := by
    rcases odd_back (16*q+5) (96*q+36) (by omega) (by omega) h1 with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hb⟩
    · have hxa : x = 8*q+1 := by omega
      have hya : y = 112*q+41 := by omega
      rw [hxa,hya] at hp
      exact hp
    · omega
  rcases odd_back (8*q+1) (112*q+41) (by omega) (by omega) h2 with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hb⟩
  · have hxa : x = 4*q-1 := by omega
    have hya : y = 120*q+42 := by omega
    rw [hxa,hya] at hp
    exact hp
  · omega

/-- Full original-source forced S predecessor, for every q>=4. -/
theorem forced_FFFS (q : Nat) (hq : 4 ≤ q)
    (hr : Reach (32*q+13) (64*q+23)) :
    Reach (34*q+3) (60*q+23) := by
  have h3 := three_forced_F q hq hr
  rcases odd_back (4*q-1) (120*q+42) (by omega) (by omega) h3 with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hb⟩
  · obtain ⟨n,hn⟩ := hp
    have heven : y%8=2 :=
      BB429RootEven8.rooted_positive_even_eight n x y hn
        (by omega) (by omega)
    omega
  · have hxa : x = 34*q+3 := by omega
    have hya : y = 60*q+23 := by omega
    rw [hxa,hya] at hp
    exact hp

/-- Genuine blank-start reachability on the 13-line forces q=0 or 1 mod4.
    This removes *all* q=2/3 mod4 cylinders, uniformly and without any
    symbolic signed-lift limit or finite time cutoff. -/
theorem rooted_13_q_mod4 (q : Nat) (hq : 4 ≤ q)
    (hr : Reach (32*q+13) (64*q+23)) :
    q%4=0 ∨ q%4=1 := by
  have h4 := forced_FFFS q hq hr
  obtain ⟨n,hn⟩ := h4
  have h77 := BB429RootMod16.rooted_not_7_7 n (34*q+3) (60*q+23) hn
  have hall := BB429NewResidue.reach_allowed (34*q+3) (60*q+23) ⟨n,hn⟩
  unfold BB429Mod8.Allowed at hall
  omega

#print axioms three_forced_F
#print axioms forced_FFFS
#print axioms rooted_13_q_mod4
end BB429Forced13
