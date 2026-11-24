import BB429LowWordSlopes
import BB429LowWordProgression

namespace BB429.LowWord.Slopes

/-- Existence of a prepared terminal word is precisely an arithmetic test:
    the guards become automatic at large scales. -/
theorem terminal_cofinal_of_congruence (vs : List Move)
    (hphase : phases vs initial) (m0 : Nat)
    (hc : let f := symbolic vs initial;
      congruence (Modulus f) (Coefficient f) (Offset f) ((16:Int)^m0)) :
    ∀ L : Nat, ∃ m ≥ L, Terminal m vs := by
  obtain ⟨p,hp,hpN,hper⟩ := congruence_period vs
  intro L
  obtain ⟨m,hm,hm1,hs⟩ := cofinal_scale_test vs m0 p hp hphase
    (fun m he => (hper m m0 hc).mpr he) L
  exact ⟨m,hm,(terminal_iff_scale m vs).mpr ⟨hm1,hs⟩⟩

theorem terminal_exists_iff_residue (vs : List Move) :
    let f := symbolic vs initial
    (∃ m, Terminal m vs) ↔ phases vs initial ∧
      ∃ m < reduced (Modulus f) (Coefficient f),
        congruence (Modulus f) (Coefficient f) (Offset f) ((16:Int)^m) := by
  constructor
  · rintro ⟨m,hm⟩
    obtain ⟨_,hphase,hc,_⟩ := (terminal_iff_scale m vs).mp hm
    obtain ⟨p,hp,hpN,hper⟩ := congruence_period vs
    exact ⟨hphase,m%p,Nat.lt_of_lt_of_le (Nat.mod_lt m hp) hpN,
      (hper (m%p) m hc).mpr (Nat.mod_mod m p)⟩
  · rintro ⟨hphase,m,_,hc⟩
    obtain ⟨n,_,hn⟩ := terminal_cofinal_of_congruence vs hphase m hc 1
    exact ⟨n,hn⟩

#print axioms terminal_cofinal_of_congruence
#print axioms terminal_exists_iff_residue
end BB429.LowWord.Slopes
