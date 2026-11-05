import BB429Source24Mod2048
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace BB429Final24
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

def new34 (u : Nat) : Bool :=
  (u%2048 == 181) ||
  (u%2048 == 309) ||
  (u%2048 == 329) ||
  (u%2048 == 373) ||
  (u%2048 == 437) ||
  (u%2048 == 457) ||
  (u%2048 == 501) ||
  (u%2048 == 593) ||
  (u%2048 == 693) ||
  (u%2048 == 713) ||
  (u%2048 == 757) ||
  (u%2048 == 821) ||
  (u%2048 == 841) ||
  (u%2048 == 885) ||
  (u%2048 == 969) ||
  (u%2048 == 977) ||
  (u%2048 == 1013) ||
  (u%2048 == 1077) ||
  (u%2048 == 1105) ||
  (u%2048 == 1205) ||
  (u%2048 == 1333) ||
  (u%2048 == 1353) ||
  (u%2048 == 1397) ||
  (u%2048 == 1481) ||
  (u%2048 == 1525) ||
  (u%2048 == 1609) ||
  (u%2048 == 1617) ||
  (u%2048 == 1653) ||
  (u%2048 == 1745) ||
  (u%2048 == 1845) ||
  (u%2048 == 1865) ||
  (u%2048 == 1909) ||
  (u%2048 == 1993) ||
  (u%2048 == 2037)
def new49 (u : Nat) : Bool := new34 u ||
  (u%2048 == 53) ||
  (u%2048 == 585) ||
  (u%2048 == 629) ||
  (u%2048 == 649) ||
  (u%2048 == 721) ||
  (u%2048 == 1225) ||
  (u%2048 == 1269) ||
  (u%2048 == 1461) ||
  (u%2048 == 1489) ||
  (u%2048 == 1589) ||
  (u%2048 == 1717) ||
  (u%2048 == 1737) ||
  (u%2048 == 1781) ||
  (u%2048 == 1873) ||
  (u%2048 == 2001)
def gate24 (u : Nat) : Bool :=
  ((u%64==9) || (u%128==81) || (u%64==53) || ((u%128==125) && (u%1024!=125))) &&
  (u%1024!=253) && (u%1024!=381) && (u%1024!=509) &&
  (u%512!=393) && (u%512!=265) &&
  (u%1024!=137) && (u%1024!=521) &&
  (u%2048!=1661) && (u%2048!=893) &&
  !(new49 u) && (u%512!=81)
def good24 (u : Nat) : Bool :=
  (u%2048 == 9) ||
  (u%2048 == 73) ||
  (u%2048 == 117) ||
  (u%2048 == 201) ||
  (u%2048 == 209) ||
  (u%2048 == 245) ||
  (u%2048 == 337) ||
  (u%2048 == 465) ||
  (u%2048 == 565) ||
  (u%2048 == 637) ||
  (u%2048 == 765) ||
  (u%2048 == 849) ||
  (u%2048 == 949) ||
  (u%2048 == 1021) ||
  (u%2048 == 1033) ||
  (u%2048 == 1097) ||
  (u%2048 == 1141) ||
  (u%2048 == 1233) ||
  (u%2048 == 1361) ||
  (u%2048 == 1673) ||
  (u%2048 == 1789) ||
  (u%2048 == 1917) ||
  (u%2048 == 1973) ||
  (u%2048 == 2045)

/-- Exhaustive Boolean equality over a full modulus period. -/
theorem finite_cert :
    (List.range 2048).all (fun r => gate24 r == good24 r) = true := by
  decide

private theorem m64 (u : Nat) : (u%2048)%64=u%64 :=
  Nat.mod_mod_of_dvd u (by decide)
private theorem m128 (u : Nat) : (u%2048)%128=u%128 :=
  Nat.mod_mod_of_dvd u (by decide)
private theorem m512 (u : Nat) : (u%2048)%512=u%512 :=
  Nat.mod_mod_of_dvd u (by decide)
private theorem m1024 (u : Nat) : (u%2048)%1024=u%1024 :=
  Nat.mod_mod_of_dvd u (by decide)
private theorem m2048 (u : Nat) : (u%2048)%2048=u%2048 :=
  Nat.mod_mod u 2048

theorem gate_periodic (u : Nat) : gate24 (u%2048) = gate24 u := by
  simp only [gate24, new49, new34, m64, m128, m512, m1024, m2048]

theorem good_periodic (u : Nat) : good24 (u%2048) = good24 u := by
  simp only [good24, m2048]

/-- The finite certificate extends to every natural counter. -/
theorem all_modulo (u : Nat) : gate24 u = good24 u := by
  have hr : (u%2048) ∈ List.range 2048 :=
    List.mem_range.mpr (Nat.mod_lt u (by decide))
  have h : (gate24 (u%2048) == good24 (u%2048)) = true :=
    (List.all_eq_true.mp finite_cert) (u%2048) hr
  have heq : gate24 (u%2048) = good24 (u%2048) := beq_iff_eq.mp h
  simpa only [gate_periodic, good_periodic] using heq

/-- Same native section-filter expression as in raw_halts_iff_24_gates. -/
def nativeFilter (u : Nat) : Prop :=
  ((u%64=9) ∨ (u%128=81) ∨ (u%64=53) ∨ ((u%128=125) ∧ (u%1024≠125))) ∧
  u%1024≠253 ∧ u%1024≠381 ∧ u%1024≠509 ∧
  u%512≠393 ∧ u%512≠265 ∧ u%1024≠137 ∧ u%1024≠521 ∧
  u%2048≠1661 ∧ u%2048≠893 ∧
  ¬BB429New49.NewGate u ∧ u%512≠81

theorem native_filter_iff_gate24 (u : Nat) :
    nativeFilter u ↔ gate24 u = true := by
  simp [nativeFilter, gate24, new49, new34,
    BB429New49.NewGate, BB429New34.NewGate, and_assoc, or_assoc]

def liveClasses : List Nat :=
  [9,73,117,201,209,245,337,465,565,637,765,849,
   949,1021,1033,1097,1141,1233,1361,1673,1789,1917,1973,2045]

theorem good_iff_mem (u : Nat) :
    good24 u = true ↔ u%2048 ∈ liveClasses := by
  simp [good24, liveClasses, or_assoc]

theorem native_iff_mem (u : Nat) :
    nativeFilter u ↔ u%2048 ∈ liveClasses := by
  rw [native_filter_iff_gate24]
  rw [all_modulo]
  exact good_iff_mem u

/-- Authenticated raw-machine halting iff a genuine source terminal has one
    of exactly 24 possible residues. No candidate is proved reachable. -/
theorem raw_halts_iff_24_classes :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        u % 2048 ∈ liveClasses := by
  constructor
  · intro h
    obtain ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521,
      h1661,h893,h49,h81⟩ :=
        BB429ActualHalt24Mod2048.raw_halts_iff_24_gates.mp h
    have hf : nativeFilter u :=
      ⟨hmask,h253,h381,h509,h393,h265,h137,h521,h1661,h893,h49,h81⟩
    exact ⟨n,u,w,hr,hn,(native_iff_mem u).mp hf⟩
  · rintro ⟨n,u,w,hr,hn,hl⟩
    rcases (native_iff_mem u).mpr hl with
      ⟨hmask,h253,h381,h509,h393,h265,h137,h521,h1661,h893,h49,h81⟩
    exact BB429ActualHalt24Mod2048.raw_halts_iff_24_gates.mpr
      ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521,
       h1661,h893,h49,h81⟩

#print axioms finite_cert
#print axioms all_modulo
#print axioms native_filter_iff_gate24
#print axioms raw_halts_iff_24_classes
end BB429Final24
