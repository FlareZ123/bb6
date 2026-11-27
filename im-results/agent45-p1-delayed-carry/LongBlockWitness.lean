import AllDigitWeight
import ReverseBlockCompose

namespace BB6.Agent45ReverseBlock

def wordValue (L F k B : Nat) : Nat := (F-k)*B+sumWeight L L 0 B

theorem word_value_eq (L F k B : Nat) (hFk : k≤F) (hL : k≤2^L) (hB : B<2^k) :
    wordValue L F k B + corr k B = F*B := by
  have hw := all_weight_corr L 0 k B (by omega) hB
  simp only [Nat.zero_add] at hw
  have he : F*B = (F-k)*B+k*B := by rw [← Nat.add_mul]; congr 1; omega
  unfold wordValue
  omega

/-- Legal word values are separated by the entire initial carry range,
    with no fitted-block restriction. -/
theorem word_value_gap (L F k B C : Nat) (hFk : k≤F) (hL : k≤2^L)
    (hBC : B<C) (hC : C<2^k) : wordValue L F k B + (F-k) ≤ wordValue L F k C := by
  have hB : B<2^k := by omega
  have hb := word_value_eq L F k B hFk hL hB
  have hc := word_value_eq L F k C hFk hL hC
  let d := C-B
  have hd : C=B+d := by dsimp [d]; omega
  have hcorr := corr_add_bound k B d
  have hF : F*C=F*B+F*d := by rw [hd,Nat.mul_add]
  have hFd : F*d=k*d+(F-k)*d := by rw [←Nat.add_mul]; congr 1; omega
  have hq : F-k≤(F-k)*d := by
    have hd1 : 1≤d := by dsimp [d]; omega
    simpa using Nat.mul_le_mul_left (F-k) hd1
  rw [←hd] at hcorr
  omega

/-- A valid predecessor needs one word equality; a dead predecessor needs
    a gap between adjacent word values (or the final possible word).
    Sentinel F-k means that the reverse image is empty. -/
def witnessCheck (L F k X B out : Nat) : Bool :=
  let q := F-k
  let W := wordValue L F k B
  decide (B<2^k ∧ W≤X) &&
    (if X-W<q then out==X-W else
       (out==q && (decide (B+1=2^k) || decide (X<wordValue L F k (B+1)))))

theorem witness_word_sound (L F k X B out C c : Nat)
    (hL : k≤2^L) (hC : C<2^k) (hc : c<F-k)
    (he : X+corr k C=F*C+c)
    (hcheck : witnessCheck L F k X B out=true) : out=c ∧ B=C := by
  have hFk : k≤F := by omega
  have hw := word_value_eq L F k C hFk hL hC
  have hx : X=wordValue L F k C+c := by omega
  simp only [witnessCheck,Bool.and_eq_true,decide_eq_true_eq] at hcheck
  obtain ⟨⟨hB,hWB⟩,hrest⟩ := hcheck
  by_cases hlt : X-wordValue L F k B<F-k
  · simp [hlt] at hrest
    have hBC : B=C := by
      by_cases h : B<C
      · have hg := word_value_gap L F k B C hFk hL h hC
        omega
      · by_cases hh : C<B
        · have hg := word_value_gap L F k C B hFk hL hh hB
          omega
        · omega
    rw [hBC] at hrest
    exact ⟨by omega,hBC⟩
  · simp [hlt] at hrest
    obtain ⟨_,hnext⟩ := hrest
    by_cases h : C<B
    · have hg := word_value_gap L F k C B hFk hL h hB
      omega
    · by_cases h' : C=B
      · rw [h'] at hx
        omega
      · have hlt' : B+1≤C := by omega
        have hB' : B+1<2^k := by omega
        have hle : wordValue L F k (B+1)≤wordValue L F k C := by
          by_cases hEq : B+1=C
          · rw [hEq]; exact Nat.le_refl _
          · have hg := word_value_gap L F k (B+1) C hFk hL (by omega) hC
            omega
        rcases hnext with hlast|hnext <;> omega

theorem witness_sound (L F k X B out C c : Nat)
    (hL : k≤2^L) (hC : C<2^k) (hc : c<F-k)
    (he : X+corr k C=F*C+c)
    (hcheck : witnessCheck L F k X B out=true) : out=c :=
  (witness_word_sound L F k X B out C c hL hC hc he hcheck).1

/-- Any genuine original-source Walk has the unique certified predecessor.
    In particular a sentinel witness excludes all Walks from that endpoint. -/
theorem witness_walk (L F z : Nat) (ys : List Nat) (B out c : Nat)
    (hL : ys.length≤2^L)
    (hcheck : witnessCheck L F ys.length (2^ys.length*z+digits ys) B out=true)
    (hw : Walk F z ys c) : out=c := by
  obtain ⟨C,hC,he⟩ := eq_of_walk hw
  exact witness_sound L F ys.length _ B out C c hL hC (walk_bound hw) he hcheck

/-- The generator supplies one (endpoint, word, predecessor-or-sentinel) row.
    Numerical certificates need not enumerate every possible wrap word. -/
abbrev WitnessRow := Nat × Nat × Nat

def rowCheck (L F k Y : Nat) (row : WitnessRow) : Bool :=
  witnessCheck L F k (2^k*row.1+Y) row.2.1 row.2.2

def rowsOut (F k : Nat) (rows : List WitnessRow) : List Nat :=
  (rows.filter (fun row => row.2.2 < F-k)).map (fun row => row.2.2)

theorem rows_cover (L F : Nat) (ys : List Nat) (rows : List WitnessRow)
    (hL : ys.length≤2^L) (hc : rows.all (rowCheck L F ys.length (digits ys))=true)
    (z c : Nat) (hz : z∈rows.map Prod.fst) (hw : Walk F z ys c) :
    c∈rowsOut F ys.length rows := by
  obtain ⟨row,hr,hz'⟩ := List.mem_map.mp hz
  have hcheck := List.all_eq_true.mp hc row hr
  unfold rowCheck at hcheck
  rw [hz'] at hcheck
  have he := witness_walk L F z ys row.2.1 row.2.2 c hL hcheck hw
  apply List.mem_map.mpr
  refine ⟨row, List.mem_filter.mpr ⟨hr,?_⟩,he⟩
  simp [he,walk_bound hw]

#print axioms word_value_eq
#print axioms word_value_gap
#print axioms witness_word_sound
#print axioms witness_sound
#print axioms witness_walk
#print axioms rows_cover

end BB6.Agent45ReverseBlock
