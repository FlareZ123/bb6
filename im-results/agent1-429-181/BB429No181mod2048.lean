import BB429NewResidue
import BB429RootMod16
import Lean.Elab.Tactic.Omega

namespace BB429No181mod2048
open BB429NewResidue

set_option maxRecDepth 32768
set_option maxHeartbeats 20000000

/-- An exact blank-root odd inverse whose second alternative has
    already been ruled out using a genuine predecessor invariant. -/
private theorem force_odd (a b na nb : Nat)
    (ha : 13 ≤ a) (ho : a % 2 = 1)
    (hf : a = 2*na+3 ∧ nb = b+a)
    (hs : ∀ x y, Reach x y → 4*x+26=4*a+b →
      2*y=b+4 → b%4=2 → False)
    (hr : Reach a b) : Reach na nb := by
  rcases odd_back a b ha ho hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he : x=na ∧ y=nb := by omega
    rcases he with ⟨rfl,rfl⟩
    exact hp
  · exact False.elim (hs x y hp hx hy hw)

/-- Every genuinely reached terminal-line state with first counter
    181 mod 2048 is impossible. The exclusion is over all q, not a
    finite simulation or a bounded inverse search. -/
private theorem exclude_181 (q : Nat) :
    ¬ Reach (2048*q+181) (4096*q+361) := by
  intro h0
  have h1 : Reach (1024*q+89) (6144*q+542) := by
    apply force_odd (2048*q+181) (4096*q+361)
        (1024*q+89) (6144*q+542) (by omega) (by omega) (by omega)
    · intro x y hp hx hy hw
      omega
    · exact h0
  have h2 : Reach (512*q+43) (7168*q+631) := by
    apply force_odd (1024*q+89) (6144*q+542)
        (512*q+43) (7168*q+631) (by omega) (by omega) (by omega)
    · intro x y hp hx hy hw
      have hallowed := reach_allowed x y hp
      unfold BB429Mod8.Allowed at hallowed
      omega
    · exact h1
  have h3 : Reach (256*q+20) (7680*q+674) := by
    apply force_odd (512*q+43) (7168*q+631)
        (256*q+20) (7680*q+674) (by omega) (by omega) (by omega)
    · intro x y hp hx hy hw
      omega
    · exact h2
  have h4 : Reach (2176*q+185) (3840*q+337) := by
    obtain ⟨x,y,hp,hx,hy,hw⟩ :=
      even_back (256*q+20) (7680*q+674) (by omega) (by omega) h3
    have xe : x=2176*q+185 := by omega
    have ye : y=3840*q+337 := by omega
    rw [xe,ye] at hp
    exact hp
  have h5 : Reach (1088*q+91) (6016*q+522) := by
    apply force_odd (2176*q+185) (3840*q+337)
        (1088*q+91) (6016*q+522) (by omega) (by omega) (by omega)
    · intro x y hp hx hy hw
      omega
    · exact h4
  rcases odd_back (1088*q+91) (6016*q+522)
      (by omega) (by omega) h5 with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hallowed := reach_allowed x y hp
    unfold BB429Mod8.Allowed at hallowed
    omega
  · obtain ⟨n,hn⟩ := hp
    have h77 := BB429RootMod16.rooted_not_7_7 n x y hn (by omega)
    omega

theorem blank_halt_not_181_mod2048 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (hg : b+1=2*a) : a%2048≠181 := by
  intro hm
  let q := a/2048
  have ha : a=2048*q+181 := by dsimp [q]; omega
  have hb : b=4096*q+361 := by omega
  have h0 : Reach (2048*q+181) (4096*q+361) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact exclude_181 q h0

#print axioms blank_halt_not_181_mod2048

end BB429No181mod2048
