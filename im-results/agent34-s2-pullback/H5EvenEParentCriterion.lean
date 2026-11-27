import ModularConeSource
import Lean.Elab.Tactic.Omega

namespace BB6.Agent34EvenECriterion
open BB6.Agent42ModularCone
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- The odd/even H5 E-state is affine in two *free* natural parameters.
    Nothing in the following source theorem assumes that a high stop exists. -/
def Eax (r B : Nat) : Nat := 1735479+3388496*r+6776976*B
def Eay (r B : Nat) : Nat := 1280448+2500056*r+5000120*B
def Q (r B : Nat) : Nat := 376991+736069*r+1472137*B

def DA (r B : Nat) : Nat := 3015925+5888552*r+11777096*B
def DK (r B : Nat) : Nat := 640223+1250028*r+2500060*B
def HA (r B : Nat) : Nat := 753979+1472138*r+2944274*B
def HK (r B : Nat) : Nat := 1771193+3458235*r+6916471*B

/-- The two possible source parents, once Q is odd, depend on Q alone
    at 16-bit precision; the residual parameter dependence is 2^22 times
    the common direction r+2B. -/
def directQ (q : Nat) : Pair :=
  ⟨8*(q:Int)-3,2148187-4*(q:Int)⟩
def highQ (q : Nat) : Pair :=
  ⟨2*(q:Int)-3,2148184-(q:Int)⟩

theorem mass (r B : Nat) :
    Eax r B+Eay r B+1=8*Q r B := by
  dsimp [Eax,Eay,Q]
  omega

theorem direct_matches_16 (r B : Nat) :
    Matches 16 (DA r B) (DK r B) (directQ (Q r B)) := by
  unfold Matches
  constructor
  · unfold Cong
    refine ⟨0, ?_⟩
    change _=(65536:Int)*_
    dsimp [DA,directQ,Q]
    omega
  · unfold Cong
    refine ⟨64*((r:Int)+2*(B:Int)), ?_⟩
    change _=(65536:Int)*_
    dsimp [DK,directQ,Q]
    omega

theorem high_matches_16 (r B : Nat) :
    Matches 16 (HA r B) (HK r B) (highQ (Q r B)) := by
  unfold Matches
  constructor
  · unfold Cong
    refine ⟨0, ?_⟩
    change _=(65536:Int)*_
    dsimp [HA,highQ,Q]
    omega
  · unfold Cong
    refine ⟨64*((r:Int)+2*(B:Int)), ?_⟩
    change _=(65536:Int)*_
    dsimp [HK,highQ,Q]
    omega

/-- A one-dimensional, source-faithful **all-time** absence criterion:
    for every odd Q, if the 16-bit original inverse cone excludes both
    of the only permitted parents, the E-state is blank-unreachable.
    This is stronger than merely eliminating a fixed stopping root. -/
theorem evenE_source_excluded (r B : Nat)
    (ho : Q r B % 2 = 1)
    (hd : excluded 16 (directQ (Q r B)) = true)
    (hh : excluded 16 (highQ (Q r B)) = true) :
    ¬ BB6.Agent3.CReach (Eax r B) (Eay r B) := by
  intro hr
  have hxOdd : Eax r B % 2 = 1 := by dsimp [Eax]; omega
  have hyEven : Eay r B % 2 = 0 := by dsimp [Eay]; omega
  have hsumOdd : (Eax r B+Eay r B)%2=1 := by omega
  have hmass := mass r B
  have hval : (Eax r B+Eay r B+
      (Eax r B+Eay r B)%2)%P (3+1)=P 3 := by
    change (Eax r B+Eay r B+
      (Eax r B+Eay r B)%2)%16=8
    omega
  have hgt : P 3 < Eax r B+Eay r B+
      (Eax r B+Eay r B)%2 := by
    change 8 < Eax r B+Eay r B+
      (Eax r B+Eay r B)%2
    dsimp [Eax,Eay]
    omega
  have hge : 8≤Eay r B := by dsimp [Eay]; omega
  obtain ⟨a,k,hparent,hinv⟩ :=
    source_parent (Eax r B) (Eay r B) 3 hr hge hval hgt
  rcases hinv with ⟨_,ha,hk⟩ | ⟨n,hn,hpar,hq,hw⟩
  · have hda : a=DA r B := by
      dsimp [DA,Eax,Eay] at ha ⊢
      omega
    have hdk : k=DK r B := by
      dsimp [DK,Eay] at hk ⊢
      omega
    have hl : Large 16 k := by
      change 3*65536≤k+2
      rw [hdk]
      dsimp [DK]
      omega
    have hm : Matches 16 a k (directQ (Q r B)) := by
      rw [hda,hdk]
      exact direct_matches_16 r B
    exact (source_excluded 16 (directQ (Q r B)) hd a k hl hm) hparent
  · have hn1 : n=1 := by omega
    subst n
    have hq' : Eax r B+Eay r B+1=4*(a+3) := by
      simpa [P,hsumOdd] using hq
    have hw' : 2*k+a+10=Eax r B+2*Eay r B := by
      simpa using hw
    have hha : a=HA r B := by
      dsimp [Eax,Eay,HA] at hq' ⊢
      omega
    have hhk : k=HK r B := by
      rw [hha] at hw'
      dsimp [Eax,Eay,HA,HK] at hw' ⊢
      omega
    have hl : Large 16 k := by
      change 3*65536≤k+2
      rw [hhk]
      dsimp [HK]
      omega
    have hm : Matches 16 a k (highQ (Q r B)) := by
      rw [hha,hhk]
      exact high_matches_16 r B
    exact (source_excluded 16 (highQ (Q r B)) hh a k hl hm) hparent

/-- Uniform examples of the one-dimensional checker: an odd residue
    whose exact source E-state is unreachable even though the old root
    32-bit test misses the H5 parameters r=0,w=30. -/
theorem example_Q10083 :
    excluded 16 (directQ 10083) = true ∧
    excluded 16 (highQ 10083) = true := by decide

#print axioms mass
#print axioms direct_matches_16
#print axioms high_matches_16
#print axioms evenE_source_excluded
#print axioms example_Q10083
end BB6.Agent34EvenECriterion
