import BirthLocate
namespace BB6.Agent43BirthLocate
open BB6.Agent9BatchCarry (Walk)
open BB6.Agent9FoldedProbe

/-- A numerical checkpoint only needs to contain every genuinely live
    folded start; it need not prove every proposed entry is live. -/
def LiveUpper (q j : Nat) (ends : List Nat) : Prop :=
  ∀ a z, FoldedWalk q a j z → a∈ends

/-- One certificate for each proposed endpoint. A complete long reverse
    path reaches a retained lower carry, or its unique earliest ancestor
    is a recorded maximal folded class. No fitted-length restriction. -/
def BlockCover (q k : Nat) (ends lower born : List Nat) : Prop :=
  ∀ z∈ends,
    (∃ a∈lower, FoldedWalk q a k z) ∨
    ∃ b∈born, q<b ∧ b≤q+k ∧ FoldedWalk b ((b-2)/2) (q+k-b) z

/-- A maximal ancestor at b excludes every longer strict suffix. -/
theorem center_no_earlier {F b z q : Nat} (hb : 0<b) (hbF : b≤F) (hqb : q<b)
    (hw : FoldedWalk b ((b-2)/2) (F-b) z) : ¬ HasSuffix F z (F-q) := by
  have hclock : b-1+1=b := by omega
  have hc : b-1-1=b-2 := by omega
  have hw' : FoldedWalk (b-1+1) ((b-1-1)/2) (F-b) z := by rwa [hclock,hc]
  have hn := (first_failure_iff (b-1) (F-b) z).1 hw' |>.2
  have hnot : ¬HasSuffix F z (F-b+1) := by
    unfold HasSuffix
    rw [show F-(F-b+1)=b-1 by omega]
    exact hn
  intro h
  exact hnot (suffix_mono F z (F-q) (F-b+1) (by omega) (by omega) h)

/-- No terminal class can have two different maximal ancestors. -/
theorem unique_center_clock {F b d z : Nat} (hb : 0<b) (hd : 0<d)
    (hbF : b≤F) (hdF : d≤F)
    (h : FoldedWalk b ((b-2)/2) (F-b) z)
    (h' : FoldedWalk d ((d-2)/2) (F-d) z) : b=d := by
  by_cases hbd : b<d
  · exfalso
    apply center_no_earlier hd hdF hbd h'
    exact ⟨_,by simpa [show F-(F-b)=b by omega] using h⟩
  · by_cases hdb : d<b
    · exfalso
      apply center_no_earlier hb hbF hdb h
      exact ⟨_,by simpa [show F-(F-d)=d by omega] using h'⟩
    · omega

/-- A block certificate transports the one-sided live cover. -/
theorem block_cover_lower (q k j : Nat) (ends lower born : List Nat)
    (he : LiveUpper (q+k) j ends) (hc : BlockCover q k ends lower born) :
    LiveUpper q (k+j) lower := by
  intro a w hw
  obtain ⟨z,h1,h2⟩ := folded_split hw
  have hz := he z w h2
  rcases hc z hz with ⟨a',ha',hh⟩|⟨b,hb,hqb,hbF,hh⟩
  · have h := unique_start h1 hh
    rwa [h]
  · exfalso
    apply center_no_earlier (by omega : 0<b) hbF hqb hh
    exact ⟨a,by simpa using h1⟩

/-- The born list need only overapproximate surviving centers in the
    block. Odd maximal classes may be included; only even clocks matter
    for the original critical-index application. -/
def BirthUpper (q F j : Nat) (born : List Nat) : Prop :=
  ∀ b z, q<b → b≤F → Walk b ((b-2)/2) (F-b+j) z → b∈born

/-- All central births in the skipped block are retained, even when the
    input cover contains spurious endpoints and the block is arbitrarily
    long. Checking a maximal-ancestor witness replaces a negative search. -/
theorem block_cover_births (q k j : Nat) (ends lower born : List Nat)
    (he : LiveUpper (q+k) j ends) (hc : BlockCover q k ends lower born) :
    BirthUpper q (q+k) j born := by
  intro b w hqb hbF hw
  have hb4 : 4≤b := by
    have hi := walk_start hw
    unfold BB6.Agent9BatchCarry.Interior at hi
    omega
  have hcan := center_canon b hb4
  have hf : FoldedWalk b ((b-2)/2) (q+k-b+j) (fold (b+(q+k-b+j)) w) :=
    ⟨_,w,hw,hcan.2,rfl⟩
  obtain ⟨z,h1,h2⟩ := folded_split hf
  have ht : FoldedWalk (q+k) z j (fold (b+(q+k-b+j)) w) := by
    simpa [show b+(q+k-b)=q+k by omega] using h2
  rcases hc z (he _ _ ht) with ⟨a,ha,hh⟩|⟨d,hd,hqd,hdF,hh⟩
  · exfalso
    apply center_no_earlier (by omega : 0<b) hbF hqb h1
    exact ⟨a,by simpa using hh⟩
  · have hb := unique_center_clock (by omega : 0<b) (by omega : 0<d) hbF hdF h1 hh
    rwa [hb]

/-- Combine arbitrarily many certified sparse blocks without claiming
    exact equality of any of their live covers. -/
theorem birth_upper_append (q p F j : Nat) (a b : List Nat)
    (hqp : q≤p) (hpF : p≤F)
    (ha : BirthUpper q p (F-p+j) a) (hb : BirthUpper p F j b) :
    BirthUpper q F j (a++b) := by
  intro c z hqc hcF hw
  apply List.mem_append.mpr
  by_cases hcp : c≤p
  · left
    exact ha c z hqc hcp (by simpa [show p-c+(F-p+j)=F-c+j by omega] using hw)
  · right
    exact hb c z (by omega) hcF hw

/-- The final lower clock is handled by an ordinary live-cover test. -/
theorem lower_center_mem (q j z : Nat) (ends : List Nat)
    (he : LiveUpper q j ends) (hw : Walk q ((q-2)/2) j z) : ((q-2)/2)∈ends := by
  have hi := walk_start hw
  unfold BB6.Agent9BatchCarry.Interior at hi
  have hcan := center_canon q (by omega)
  exact he _ _ ⟨_,z,hw,hcan.2,rfl⟩

#print axioms center_no_earlier
#print axioms unique_center_clock
#print axioms block_cover_lower
#print axioms block_cover_births
#print axioms birth_upper_append
#print axioms lower_center_mem
end BB6.Agent43BirthLocate
