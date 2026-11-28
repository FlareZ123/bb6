import Lean.Elab.Tactic.Omega
import EChain169Split
import E2UnaryPhysical

set_option maxHeartbeats 60000000
set_option maxRecDepth 20000

namespace BB6.Agent37ExternalCall42

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent37EChainBExit BB6.Agent37EChain169Split
open BB6.Agent37EChain169Split

def k33 (y : Nat) : Nat :=
  692533995824480256*y+610716289322704915
def k34 (y : Nat) : Nat :=
  1846757322198614016*y+1628576771527213109
def k35 (y : Nat) : Nat :=
  4924686192529637376*y+4342871390739234960
def k36 (y : Nat) : Nat :=
  13132496513412366336*y+11580990375304626562
def k37 (y : Nat) : Nat :=
  35019990702432976896*y+30882641000812337501
def k38 (y : Nat) : Nat :=
  93386641873154605056*y+82353709335499566672
def k39 (y : Nat) : Nat :=
  249031044995078946816*y+219609891561332177794
def k40 (y : Nat) : Nat :=
  664082786653543858176*y+585626377496885807453
def k41 (y : Nat) : Nat :=
  1770887431076116955136*y+1561670339991695486544
def k42 (y : Nat) : Nat :=
  4722366482869645213696*y+4164454239977854630786

def call32InputA (y : Nat) : Nat :=
  2077601987473440768*y+1832148867968114749

def call42OutputA (y : Nat) : Nat :=
  37778931862957161709568*y+33315633919822837046293

def externalCall32To42Time (y : Nat) : Nat :=
  eTime (k33 y) 0 +
  (bTime (k34 y) +
  (bTime (k35 y) +
  (eTime (k36 y) 0 +
  (bTime (k37 y) +
  (bTime (k38 y) +
  (eTime (k39 y) 0 +
  (bTime (k40 y) +
  (bTime (k41 y) +
    (12*(k42 y)*(k42 y)+49*(k42 y)+68)))))))))

/-- Calls 33--42 of the pinned external terminal cylinder, including the
    physically blank-trailing E-two boundary at call 42. -/
theorem external_call32_to42 (y : Nat) :
    ObsEq
      (run (externalCall32To42Time y)
        (packet (call32InputA y) 0 11 externalU4))
      (packet (call42OutputA y) 0 6
        [false,true,false,true]) := by
  have ha33 : call32InputA y = 3*k33 y+4 := by
    simp [call32InputA,k33]; omega
  have ha34 : 8*k33 y+9 = 3*k34 y+2 := by
    simp [k33,k34]; omega
  have ha35 : 8*k34 y+10 = 3*k35 y+2 := by
    simp [k34,k35]; omega
  have ha36 : 8*k35 y+10 = 3*k36 y+4 := by
    simp [k35,k36]; omega
  have ha37 : 8*k36 y+9 = 3*k37 y+2 := by
    simp [k36,k37]; omega
  have ha38 : 8*k37 y+10 = 3*k38 y+2 := by
    simp [k37,k38]; omega
  have ha39 : 8*k38 y+10 = 3*k39 y+4 := by
    simp [k38,k39]; omega
  have ha40 : 8*k39 y+9 = 3*k40 y+2 := by
    simp [k39,k40]; omega
  have ha41 : 8*k40 y+10 = 3*k41 y+2 := by
    simp [k40,k41]; omega
  have ha42 : 8*k41 y+10 = 3*k42 y+4 := by
    simp [k41,k42]; omega
  have hout : 8*k42 y+5 = call42OutputA y := by
    simp [k42,call42OutputA]; omega
  have he33 :
      run (eTime (k33 y) 0)
        (packet (3*k33 y+4) 0 11 externalU4) =
      packet (8*k33 y+9) 2 8 externalU4 := by
    simpa using
      (BB6.Agent31PacketSource.e_packet (k33 y) 0 8 externalU4)
  have hb34 :
      run (bTime (k34 y))
        (packet (3*k34 y+2) 2 8 externalU4) =
      packet (8*k34 y+10) 1 8 externalU4 :=
    BB6.Agent31PacketSource.b_packet (k34 y) 1 8 externalU4
  have hb35 :
      run (bTime (k35 y))
        (packet (3*k35 y+2) 1 8 externalU4) =
      packet (8*k35 y+10) 0 8 externalU4 :=
    BB6.Agent31PacketSource.b_packet (k35 y) 0 8 externalU4
  have he36 :
      run (eTime (k36 y) 0)
        (packet (3*k36 y+4) 0 8 externalU4) =
      packet (8*k36 y+9) 2 5 externalU4 := by
    simpa using
      (BB6.Agent31PacketSource.e_packet (k36 y) 0 5 externalU4)
  have hb37 :
      run (bTime (k37 y))
        (packet (3*k37 y+2) 2 5 externalU4) =
      packet (8*k37 y+10) 1 5 externalU4 :=
    BB6.Agent31PacketSource.b_packet (k37 y) 1 5 externalU4
  have hb38 :
      run (bTime (k38 y))
        (packet (3*k38 y+2) 1 5 externalU4) =
      packet (8*k38 y+10) 0 5 externalU4 :=
    BB6.Agent31PacketSource.b_packet (k38 y) 0 5 externalU4
  have he39 :
      run (eTime (k39 y) 0)
        (packet (3*k39 y+4) 0 5 externalU4) =
      packet (8*k39 y+9) 2 2 externalU4 := by
    simpa using
      (BB6.Agent31PacketSource.e_packet (k39 y) 0 2 externalU4)
  have hb40 :
      run (bTime (k40 y))
        (packet (3*k40 y+2) 2 2 externalU4) =
      packet (8*k40 y+10) 1 2 externalU4 :=
    BB6.Agent31PacketSource.b_packet (k40 y) 1 2 externalU4
  have hb41 :
      run (bTime (k41 y))
        (packet (3*k41 y+2) 1 2 externalU4) =
      packet (8*k41 y+10) 0 2 externalU4 :=
    BB6.Agent31PacketSource.b_packet (k41 y) 0 2 externalU4
  have he42 :=
    BB6.Agent37E2UnaryPhysical.e_two_111_implicit_blank (k42 y) 0
  unfold externalCall32To42Time
  rw [run_add,ha33,he33,ha34,
    run_add,hb34,ha35,
    run_add,hb35,ha36,
    run_add,he36,ha37,
    run_add,hb37,ha38,
    run_add,hb38,ha39,
    run_add,he39,ha40,
    run_add,hb40,ha41,
    run_add,hb41,ha42]
  have h42 :
      ObsEq
        (run (12*(k42 y)*(k42 y)+49*(k42 y)+68)
          (packet (3*k42 y+4) 0 2 externalU4))
        (packet (call42OutputA y) 0 6
          [false,true,false,true,false,false]) := by
    simpa [hout] using he42
  have hpad0 :=
    BB6.BoundaryPadding.source_pad 0 0 2
      (packet (call42OutputA y) 0 6 [false,true,false,true])
  have hpad :
      ObsEq
        (packet (call42OutputA y) 0 6
          [false,true,false,true,false,false])
        (packet (call42OutputA y) 0 6
          [false,true,false,true]) := by
    have hs := BB6.Padding.cfgEq_symm hpad0
    simpa [CryptidBoundary.run] using hs
  exact BB6.Padding.cfgEq_trans h42 hpad

/-- Source-connected external terminal cylinder through call 42.
    The modulus is 3^24; this is the exact 17-trit refinement of the
    previously uncovered k≡169 (mod 243) branch selected by the pinned
    terminal replay. -/
theorem external169_call42_prefix (y : Nat) :
    ∃ T,
      ObsEq
        (run T
          (packet
            (3*(282429536481*y+249062601337)+4) 0 2
            (false :: List.replicate 6 true)))
        (packet (call42OutputA y) 0 6
          [false,true,false,true]) := by
  let r := 59049*y+52072
  obtain ⟨t0,h0⟩ := external169_call32_prefix r
  have hk :
      4782969*r+3839569 =
        282429536481*y+249062601337 := by
    dsimp [r]; omega
  have ha :
      35184372088832*r+28244558454845 =
        call32InputA y := by
    simp [r,call32InputA]; omega
  rw [hk] at h0
  rw [ha] at h0
  refine ⟨t0+externalCall32To42Time y,?_⟩
  rw [run_add,h0]
  exact external_call32_to42 y

#print axioms external_call32_to42
#print axioms external169_call42_prefix

end BB6.Agent37ExternalCall42
