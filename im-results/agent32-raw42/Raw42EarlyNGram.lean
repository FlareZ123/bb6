import Raw42Cut
import AsymNGram
import Raw42WideCuts
import Raw42NestedCuts

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw42Early
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent10ZipAudit BB6.Agent31ThreeHole BB6.Agent50TNFPilot
open BB6.Agent32AsymNGram BB6.Agent1NGram

def mkTrie : Nat → List Nat → Trie
  | 0,xs => if xs.contains 0 then .leaf else .empty
  | k+1,xs =>
    if xs.isEmpty then .empty else if xs.all (· == 0) then .leaf else
      .branch (mkTrie k ((xs.filter (fun x => x%2 == 0)).map (· / 2)))
              (mkTrie k ((xs.filter (fun x => x%2 == 1)).map (· / 2)))

structure Entry where
  code : Nat
  nl : Nat
  nr : Nat
  left : List Nat
  right : List Nat
  states : List (List Nat)

def Entry.cert (e : Entry) : BB6.Agent32AsymNGram.Cert :=
  ⟨e.nl,e.nr,mkTrie (e.nl+2) e.left,mkTrie (e.nr+2) e.right,
    (e.states.map (mkTrie (e.nl+e.nr+2))).toArray⟩

def mv (n : Nat) : Move := ⟨n/12 == 1, n%12 >= 6, ⟨n%6, Nat.mod_lt _ (by decide)⟩⟩

def slot (n : Nat) : Slot := (⟨n/2%6,Nat.mod_lt _ (by decide)⟩,n%2 == 1)

structure Cut where
  first : Nat
  time : Nat
  query : Nat
  rows : List Entry
  extra : List Nat := []

def parent (c : Cut) : PartialMachine := BB6.Agent32Raw42.child (mv c.first)
def sub (c : Cut) (n : Nat) : PartialMachine := refine (parent c) (slot c.query) (some (mv n))
def codes (c : Cut) : List Nat := c.rows.map Entry.code ++ c.extra

def checkCut (c : Cut) : Bool :=
  zipQueryOK 64 (parent c) c.time (slot c.query) &&
  c.rows.all (fun e => BB6.Agent32AsymNGram.check (sub c e.code) e.cert)

def residual (c : Cut) : List Move := BB6.Agent32Raw42.moves.filter (fun m => !((codes c).map mv).contains m)

theorem bankCover (c : Cut) (h : checkCut c = true) (e : Entry)
    (hm : e ∈ c.rows) (B : Nat) : Cover (WeightedBound B) (sub c e.code) := by
  have hc := h
  simp only [checkCut,Bool.and_eq_true] at hc
  have hh := hc.2
  rw [List.all_eq_true] at hh
  have hh := hh e hm
  exact .leaf _ (fun m hc => weighted_never B m (BB6.Agent32AsymNGram.never _ _ hh m hc))

theorem coverCut (c : Cut) (h : checkCut c = true) (B : Nat) (hB : 64 ≤ B)
    (hextra : ∀ n ∈ c.extra, Cover (WeightedBound B) (sub c n))
    (hrest : ∀ m ∈ residual c, Cover (WeightedBound B) (refine (parent c) (slot c.query) (some m))) :
    Cover (WeightedBound B) (parent c) := by
  have hq : zipQueryOK 64 (parent c) c.time (slot c.query) = true := by
    simp only [checkCut,Bool.and_eq_true] at h
    exact h.1
  obtain ⟨hread,hhole,hw⟩ := zipQueryOK_sound hq
  refine .branch _ _ hhole ?_
  intro t _
  cases t with
  | none =>
    refine .leaf _ ?_
    intro m hm
    cases hr : knownRun (parent c) c.time with
    | none => simp [hr] at hread
    | some z =>
      have hs : readSlot z = slot c.query := by simpa [hr] using hread
      have hroot : parent c initialSlot = some (some ⟨true,true,1⟩) := by
        exact refine_preserves_firstOne BB6.Agent32Raw42.parent (1,true) (some (mv c.first)) (by decide) BB6.Agent32Raw42.parent_root
      have hb := first_hole_weighted_halt 64 (parent c) c.time z hroot hr
        (by simpa only [hs] using hhole) (by simpa only [hs] using weightOK_sound _ _ _ _ hw)
        m (by simpa only [hs] using hm)
      intro k d hk hd
      exact Nat.le_trans (hb k d hk hd) hB
  | some m =>
    by_cases he : m ∈ (codes c).map mv
    · obtain ⟨n,hn,rfl⟩ := List.mem_map.mp he
      rcases List.mem_append.mp hn with ha | hb
      · obtain ⟨e,hv,heq⟩ := List.mem_map.mp ha
        change e.code = n at heq
        subst n
        exact bankCover c h e hv B
      · exact hextra n hb
    · exact hrest m (List.mem_filter.mpr ⟨BB6.Agent32Raw42.moves_complete m,by simpa using he⟩)

#print axioms coverCut
def cut0 : Cut := ⟨0,20,1,[
  ⟨0,0,1,[0, 1, 2, 3],[0, 1, 2, 3, 4, 5, 6, 7],[[0, 4], [0, 4], [0, 2, 4, 6], [2, 6], [4, 5, 6, 7], [], [0, 1, 2, 3, 5, 7], [0, 1, 2, 3, 7], [], [], [], []]⟩,
  ⟨1,0,1,[0, 1, 2, 3],[0, 1, 2, 3, 4, 5, 6, 7],[[0, 4], [0, 4], [0, 2, 4, 6], [0, 2, 4, 6], [4, 5, 6, 7], [], [0, 1, 2, 3, 5, 7], [0, 1, 2, 3, 7], [], [], [], []]⟩,
  ⟨3,0,1,[0, 1, 2, 3],[0, 1, 2, 3, 4, 5, 6, 7],[[0, 4], [0, 4], [0, 2, 4, 6], [0, 2, 4, 6], [4, 5, 6, 7], [], [0, 1, 2, 3, 4, 5, 7], [0, 1, 2, 3, 4, 5, 7], [], [], [], []]⟩,
  ⟨7,0,1,[0, 1, 2, 3],[0, 1, 2, 3, 4, 5, 6, 7],[[0, 4], [0, 4], [0, 2, 4, 6], [2, 6], [4, 5, 6, 7], [], [0, 1, 2, 3, 5, 7], [0, 1, 2, 3, 7], [], [], [], []]⟩,
  ⟨8,0,1,[0, 1, 2, 3],[0, 1, 2, 3, 4, 5, 6, 7],[[0, 4], [0, 4], [0, 2, 4, 6], [2, 6], [0, 2, 4, 5, 6, 7], [], [0, 1, 2, 3, 5, 7], [0, 1, 2, 3, 7], [], [], [], []]⟩,
  ⟨9,0,1,[0, 1, 2, 3],[0, 1, 2, 3, 4, 5, 6, 7],[[0, 4], [0, 4], [0, 2, 4, 6], [2, 6], [4, 5, 6, 7], [], [0, 1, 2, 3, 5, 7], [0, 1, 2, 3, 7], [], [], [], []]⟩,
  ⟨12,0,1,[0, 1, 2, 3],[0, 1, 2, 3, 4, 5, 6, 7],[[0, 1, 3, 4, 5, 7], [0, 1, 2, 3, 4, 5, 6, 7], [0, 2, 4, 6], [2, 4, 5, 6, 7], [4, 5, 6, 7], [], [0, 1, 2, 3, 5, 7], [0, 1, 2, 3, 7], [], [], [], []]⟩,
  ⟨15,0,1,[0, 1, 2, 3],[0, 1, 2, 3, 4, 5, 6, 7],[[0, 4], [0, 4], [0, 2, 4, 6], [2, 6], [4, 5, 6, 7], [], [0, 1, 2, 3, 5, 7], [0, 1, 2, 3, 5, 7], [], [], [], []]⟩,
  ⟨19,0,1,[0, 1, 2, 3],[0, 1, 2, 3, 4, 5, 6, 7],[[0, 4], [0, 4], [0, 2, 4, 6], [2, 6], [4, 5, 6, 7], [], [0, 1, 2, 3, 5, 7], [0, 1, 2, 3, 7], [], [], [], []]⟩,
  ⟨21,0,1,[0, 1, 2, 3],[0, 1, 2, 3, 4, 5, 6, 7],[[0, 4], [0, 4], [0, 2, 4, 6], [2, 6], [4, 5, 6, 7], [], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 5, 7], [], [], [], []]⟩
],[20]⟩
theorem ok0 : checkCut cut0 = true := by decide
def cut4 : Cut := ⟨4,7,8,[
  ⟨0,1,2,[0, 2, 5, 6],[0, 1, 2, 3, 6, 7, 9, 11, 12, 13, 14, 15],[[0], [], [8, 12], [6], [24, 28, 30], [], [16, 19, 20, 22, 23, 25, 29, 31], [11, 15], [4], [], [], []]⟩,
  ⟨2,1,2,[0, 2, 5, 6],[0, 1, 2, 3, 6, 7, 9, 11, 12, 13, 14, 15],[[0], [], [8, 12], [6], [0, 24, 28, 30], [], [0, 1, 3, 4, 7, 16, 19, 20, 22, 23, 25, 29, 31], [11, 15], [4], [], [], []]⟩,
  ⟨3,1,2,[0, 2, 5, 6],[0, 1, 2, 3, 6, 7, 9, 11, 12, 13, 14, 15],[[0], [], [8, 12], [6], [24, 28, 30], [], [0, 1, 3, 7, 16, 19, 20, 22, 23, 25, 29, 31], [11, 15], [4], [], [], []]⟩,
  ⟨4,1,2,[0, 2, 5, 6],[0, 1, 2, 3, 6, 7, 9, 11, 12, 13, 14, 15],[[0], [], [8, 12], [6], [24, 28, 30], [], [16, 19, 20, 22, 23, 25, 29, 31], [11, 15], [0, 4], [], [], []]⟩,
  ⟨8,1,2,[0, 2, 5, 6],[0, 2, 6, 9, 12, 14, 15],[[0], [], [8], [6], [6, 24], [], [3, 7, 16, 25], [11], [4], [], [], []]⟩,
  ⟨9,1,2,[0, 2, 5, 6],[0, 2, 6, 7, 9, 11, 12, 14, 15],[[0], [], [8], [6], [24], [], [3, 5, 6, 7, 16, 25], [11], [4], [], [], []]⟩,
  ⟨15,1,2,[0, 2, 5, 6],[0, 2, 3, 6, 9, 12, 14, 15],[[0], [], [8], [6], [24], [], [1, 3, 7, 16, 25], [11], [4], [], [], []]⟩,
  ⟨16,1,2,[0, 2, 5, 6],[0, 2, 3, 6, 9, 12, 14, 15],[[0], [], [8], [6], [24], [], [16, 25], [11], [1, 3, 4, 7], [], [], []]⟩,
  ⟨21,2,2,[0, 2, 4, 6, 12],[0, 2, 5, 6, 9, 11, 12, 13, 14, 15],[[0], [], [2, 8, 12], [6], [13, 24, 30], [], [14, 25, 31, 48, 51, 55], [5, 11, 15, 22], [4], [], [], []]⟩
],[]⟩
theorem ok4 : checkCut cut4 = true := by decide
def cut10 : Cut := ⟨10,7,8,[
  ⟨1,0,1,[0, 1, 2, 3],[0, 2, 4, 5, 6, 7],[[0], [], [0, 2, 4, 6], [2, 6], [4, 5, 7], [], [0, 1, 3, 5, 7], [0, 1, 3, 7], [1, 3], [], [], []]⟩,
  ⟨2,0,1,[0, 1, 2, 3],[0, 2, 4, 5, 6, 7],[[0], [], [0, 2, 4, 6], [2, 6], [2, 4, 5, 6, 7], [], [0, 1, 3, 5, 7], [0, 1, 3, 7], [1, 3], [], [], []]⟩,
  ⟨3,0,1,[0, 1, 2, 3],[0, 1, 2, 3, 4, 5, 6, 7],[[0], [], [0, 2, 4, 6], [2, 6], [4, 5, 6, 7], [], [0, 1, 2, 3, 5, 6, 7], [0, 1, 2, 3, 5, 7], [1, 3], [], [], []]⟩,
  ⟨4,1,2,[0, 2, 5, 6],[0, 1, 2, 3, 6, 7, 9, 11, 12, 13, 14, 15],[[0], [], [8, 12], [6], [24, 28, 30], [], [16, 19, 20, 22, 23, 25, 29, 31], [11, 15], [0, 3, 4, 6, 7], [], [], []]⟩,
  ⟨9,0,1,[0, 1, 2, 3],[0, 2, 4, 5, 6, 7],[[0], [], [0, 2, 4, 6], [2, 6], [4, 5, 7], [], [0, 1, 3, 5, 7], [0, 1, 3, 7], [1, 3], [], [], []]⟩,
  ⟨14,0,1,[0, 1, 2, 3],[0, 2, 4, 5, 6, 7],[[0], [], [0, 2, 4, 6], [2, 6], [3, 4, 5, 7], [], [0, 1, 3, 5, 7], [0, 1, 3, 7], [1, 3], [], [], []]⟩,
  ⟨15,0,1,[0, 1, 2, 3],[0, 2, 4, 5, 6, 7],[[0], [], [0, 2, 4, 6], [2, 6], [4, 5, 7], [], [0, 1, 3, 5, 7], [0, 1, 3, 7], [1, 3], [], [], []]⟩,
  ⟨16,1,1,[0, 2, 5, 6],[0, 2, 5, 6, 7],[[0], [], [4], [2], [12], [], [8, 13], [7], [3], [], [], []]⟩,
  ⟨21,0,1,[0, 1, 2, 3],[0, 2, 4, 5, 6, 7],[[0], [], [0, 2, 4, 6], [0, 2, 4, 6], [4, 5, 7], [], [0, 1, 3, 4, 5, 7], [0, 1, 3, 4, 5, 7], [0, 1, 3], [], [], []]⟩
],[]⟩
theorem ok10 : checkCut cut10 = true := by decide
def cut12 : Cut := ⟨12,9,1,[
  ⟨1,0,1,[0, 1, 2, 3],[0, 1, 2, 3, 4, 5, 6, 7],[[0, 1, 5], [1, 5], [0, 2, 4, 6], [2, 4, 6], [4, 5, 6, 7], [], [0, 1, 2, 3, 5, 7], [0, 1, 2, 3, 7], [], [], [], []]⟩,
  ⟨2,1,1,[0, 2, 5, 6],[0, 2, 3, 4, 5, 6, 7],[[0, 1], [1], [4], [2, 4, 6], [2, 12], [], [1, 3, 8, 13], [7], [], [], [], []]⟩,
  ⟨3,0,1,[0, 1, 2, 3],[0, 1, 2, 3, 4, 5, 6, 7],[[0, 1, 5], [1, 5], [0, 2, 4, 6], [0, 2, 4, 6], [4, 5, 6, 7], [], [0, 1, 2, 3, 5, 6, 7], [0, 1, 2, 3, 5, 6, 7], [], [], [], []]⟩,
  ⟨6,0,2,[0, 1, 2, 3],[0, 2, 4, 6, 11, 12, 13, 14, 15],[[0, 3, 5, 7, 13], [0, 1, 3, 5, 6, 7, 11, 13, 15], [0, 2, 6, 8, 10, 14], [6, 9, 11, 14, 15], [8, 9, 11, 15], [], [0, 1, 3, 7, 9, 11, 15], [0, 1, 3, 7, 11, 15], [], [], [], []]⟩,
  ⟨7,0,1,[0, 1, 2, 3],[0, 1, 2, 3, 4, 5, 6, 7],[[0, 1, 5], [1, 5], [0, 2, 4, 6], [0, 2, 4, 6], [4, 5, 6, 7], [], [0, 1, 2, 3, 5, 7], [0, 1, 2, 3, 7], [], [], [], []]⟩,
  ⟨12,0,1,[0, 1, 2, 3],[0, 1, 2, 3, 4, 5, 6, 7],[[0, 1, 3, 5, 7], [1, 3, 5, 7], [0, 2, 4, 6], [2, 4, 5, 6, 7], [4, 5, 6, 7], [], [0, 1, 2, 3, 5, 7], [0, 1, 2, 3, 7], [], [], [], []]⟩,
  ⟨14,2,2,[0, 2, 4, 6, 12],[0, 2, 4, 5, 6, 7, 9, 11, 12, 13, 14, 15],[[0, 5], [5], [2, 8, 12], [6, 14], [3, 9, 13, 24, 30], [], [25, 31, 48, 51, 55], [1, 5, 11, 15, 16, 22], [], [], [], []]⟩,
  ⟨15,0,1,[0, 1, 2, 3],[0, 1, 2, 3, 4, 5, 6, 7],[[0, 1, 5], [1, 5], [0, 2, 4, 6], [2, 4, 6], [4, 5, 6, 7], [], [0, 1, 2, 3, 5, 7], [0, 1, 2, 3, 7], [], [], [], []]⟩,
  ⟨18,0,2,[0, 1, 2, 3],[0, 2, 4, 6, 11, 12, 13, 14, 15],[[0, 5, 8, 11, 13, 15], [3, 5, 7, 8, 9, 11, 13, 14, 15], [0, 2, 6, 8, 10, 14], [6, 9, 11, 14, 15], [8, 9, 11, 15], [], [0, 1, 3, 7, 9, 11, 15], [0, 1, 3, 7, 11, 15], [], [], [], []]⟩,
  ⟨19,0,1,[0, 1, 2, 3],[0, 1, 2, 3, 4, 5, 6, 7],[[0, 1, 5], [1, 5], [0, 2, 4, 6], [2, 4, 6], [4, 5, 6, 7], [], [0, 1, 2, 3, 5, 7], [0, 1, 2, 3, 7], [], [], [], []]⟩,
  ⟨21,0,1,[0, 1, 2, 3],[0, 1, 2, 3, 4, 5, 6, 7],[[0, 1, 5], [1, 5], [0, 2, 4, 6], [0, 2, 4, 6], [4, 5, 6, 7], [], [0, 1, 2, 3, 5, 7], [0, 1, 2, 3, 4, 6, 7], [], [], [], []]⟩
],[9]⟩
theorem ok12 : checkCut cut12 = true := by decide
def cut13 : Cut := ⟨13,8,5,[
  ⟨1,0,0,[0, 1, 2, 3],[0, 1, 2, 3],[[0], [], [0, 1, 2, 3], [0, 1, 2, 3], [2, 3], [2, 3], [0, 1, 3], [0, 1, 3], [], [], [], []]⟩,
  ⟨2,0,0,[0, 1, 2, 3],[0, 1, 2, 3],[[0], [], [0, 1, 2, 3], [0, 1, 2, 3], [0, 2, 3], [0, 2, 3], [0, 1, 3], [0, 1, 3], [], [], [], []]⟩,
  ⟨7,0,0,[0, 1, 2, 3],[0, 1, 2, 3],[[0], [], [0, 1, 2, 3], [0, 1, 2, 3], [2, 3], [2, 3], [0, 1, 3], [0, 1, 3], [], [], [], []]⟩,
  ⟨8,0,0,[0, 1, 2, 3],[0, 1, 2, 3],[[0], [], [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 3], [0, 1, 3], [], [], [], []]⟩,
  ⟨13,0,0,[0, 1, 2, 3],[0, 1, 2, 3],[[0], [], [0, 1, 2, 3], [0, 1, 2, 3], [2, 3], [2, 3], [0, 1, 3], [0, 1, 3], [], [], [], []]⟩,
  ⟨14,0,0,[0, 1, 2, 3],[0, 1, 2, 3],[[0], [], [0, 1, 2, 3], [0, 1, 2, 3], [1, 2, 3], [1, 2, 3], [0, 1, 3], [0, 1, 3], [], [], [], []]⟩,
  ⟨15,0,0,[0, 1, 2, 3],[0, 1, 2, 3],[[0], [], [0, 1, 2, 3], [0, 1, 2, 3], [2, 3], [2, 3], [0, 1, 3], [0, 1, 3], [], [], [], []]⟩,
  ⟨19,0,0,[0, 1, 2, 3],[0, 1, 2, 3],[[0], [], [0, 1, 2, 3], [0, 1, 2, 3], [2, 3], [2, 3], [0, 1, 3], [0, 1, 3], [], [], [], []]⟩,
  ⟨21,0,0,[0, 1, 2, 3],[0, 1, 2, 3],[[0], [], [0, 1, 2, 3], [0, 1, 2, 3], [2, 3], [2, 3], [0, 1, 2, 3], [0, 1, 2, 3], [], [], [], []]⟩
],[3, 9, 20]⟩
theorem ok13 : checkCut cut13 = true := by decide
def cut14 : Cut := ⟨14,32,5,[
  ⟨1,0,0,[0, 1, 2, 3],[0, 1, 2, 3],[[0], [], [0, 2, 3], [0, 2], [1, 2, 3], [1, 2, 3], [0, 1, 3], [0, 1, 3], [], [], [], []]⟩,
  ⟨2,0,0,[0, 1, 2, 3],[0, 1, 2, 3],[[0], [], [0, 2, 3], [0, 2], [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 3], [0, 1, 3], [], [], [], []]⟩,
  ⟨3,0,0,[0, 1, 2, 3],[0, 1, 2, 3],[[0], [], [0, 2, 3], [0, 2], [1, 2, 3], [1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3], [], [], [], []]⟩,
  ⟨8,0,0,[0, 1, 2, 3],[0, 1, 2, 3],[[0], [], [0, 2, 3], [0, 2], [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 3], [0, 1, 3], [], [], [], []]⟩,
  ⟨13,0,0,[0, 1, 2, 3],[0, 1, 2, 3],[[0], [], [0, 1, 2, 3], [0, 1, 2, 3], [1, 2, 3], [1, 2, 3], [0, 1, 3], [0, 1, 3], [], [], [], []]⟩,
  ⟨15,0,0,[0, 1, 2, 3],[0, 1, 2, 3],[[0], [], [0, 2, 3], [0, 2], [1, 2, 3], [1, 2, 3], [0, 1, 3], [0, 1, 3], [], [], [], []]⟩,
  ⟨19,0,0,[0, 1, 2, 3],[0, 1, 2, 3],[[0], [], [0, 2, 3], [0, 2, 3], [1, 2, 3], [1, 2, 3], [0, 1, 3], [0, 1, 3], [], [], [], []]⟩,
  ⟨20,0,0,[0, 1, 2, 3],[0, 1, 2, 3],[[0], [], [0, 2, 3], [0, 2], [1, 2, 3], [1, 2, 3], [0, 1, 3], [0, 1, 3], [], [], [], []]⟩,
  ⟨21,0,0,[0, 1, 2, 3],[0, 1, 2, 3],[[0], [], [0, 2, 3], [0, 2], [1, 2, 3], [1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3], [], [], [], []]⟩
],[7, 9, 14]⟩
theorem ok14 : checkCut cut14 = true := by decide
def cut16 : Cut := ⟨16,7,8,[
  ⟨1,2,2,[0, 2, 4, 6, 12],[0, 2, 5, 6, 9, 11, 12, 13, 14, 15],[[0], [], [2, 8, 12], [6], [13, 24, 30], [], [25, 31, 48, 51, 55], [11, 15, 22], [5], [], [], []]⟩,
  ⟨2,1,1,[0, 2, 5, 6],[0, 2, 3, 4, 5, 6, 7],[[0], [], [4], [2], [2, 12], [], [1, 3, 8, 13], [7], [1], [], [], []]⟩,
  ⟨3,1,1,[0, 2, 5, 6],[0, 2, 3, 4, 5, 6, 7],[[0], [], [4], [2], [12], [], [1, 2, 3, 8, 13], [7], [1], [], [], []]⟩,
  ⟨4,1,2,[0, 2, 5, 6],[0, 1, 2, 3, 5, 6, 7, 8, 10, 11, 12, 13, 14],[[0], [], [8, 12], [6], [24, 26, 28], [], [16, 18, 20, 21, 25, 27, 29], [11, 15], [0, 2, 4, 5], [], [], []]⟩,
  ⟨7,1,1,[0, 2, 5, 6],[0, 2, 3, 5, 6],[[0], [], [4], [0, 2], [12], [], [8, 13], [7], [1], [], [], []]⟩,
  ⟨14,2,2,[0, 2, 4, 6, 12],[0, 2, 4, 5, 6, 7, 9, 11, 12, 13, 14, 15],[[0], [], [2, 8, 12], [6], [3, 9, 13, 24, 30], [], [25, 31, 48, 51, 55], [1, 5, 11, 15, 16, 22], [5], [], [], []]⟩,
  ⟨15,1,1,[0, 2, 5, 6],[0, 2, 3, 5, 6, 7],[[0], [], [4], [2], [12], [], [3, 8, 13], [7], [1], [], [], []]⟩,
  ⟨16,1,1,[0, 2, 5, 6],[0, 2, 3, 5, 6, 7],[[0], [], [4], [2], [12], [], [8, 13], [7], [1, 3], [], [], []]⟩,
  ⟨21,1,2,[0, 2, 5, 6],[0, 1, 2, 3, 6, 7, 9, 11, 12, 13, 14, 15],[[0], [], [8, 12], [0, 4, 6], [24, 28, 30], [], [16, 19, 20, 22, 23, 25, 29, 31], [8, 11, 12, 14, 15], [1, 5], [], [], []]⟩
],[]⟩
theorem ok16 : checkCut cut16 = true := by decide
def cut18 : Cut := ⟨18,9,1,[
  ⟨0,0,2,[0, 1, 2, 3],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],[[0, 4, 8, 11, 12, 15], [0, 2, 4, 6, 8, 9, 10, 11, 12, 13, 14, 15], [0, 2, 4, 6, 8, 10, 12, 14], [6, 9, 11, 13, 14, 15], [8, 9, 10, 11, 12, 13, 14, 15], [], [0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 13, 15], [0, 1, 2, 3, 4, 5, 6, 7, 11, 15], [], [], [], []]⟩,
  ⟨1,0,1,[0, 1, 2, 3],[0, 2, 4, 5, 6, 7],[[0, 4, 5, 7], [4, 5, 7], [0, 2, 4, 6], [0, 2, 4, 5, 6, 7], [4, 5, 7], [], [0, 1, 3, 5, 7], [0, 1, 3, 7], [], [], [], []]⟩,
  ⟨3,1,1,[0, 2, 5, 6, 7],[0, 2, 5, 6],[[0, 4, 7, 12, 15], [12], [4, 12], [0, 2, 4, 6, 12, 13, 14], [12], [], [8, 13], [4, 7, 12, 15], [], [], [], []]⟩,
  ⟨6,0,1,[0, 1, 2, 3],[0, 2, 4, 5, 6, 7],[[0, 4, 5, 7], [0, 1, 3, 4, 5, 7], [0, 2, 4, 6], [2, 4, 5, 6, 7], [4, 5, 7], [], [0, 1, 3, 5, 7], [0, 1, 3, 7], [], [], [], []]⟩,
  ⟨7,0,1,[0, 1, 2, 3],[0, 2, 4, 5, 6, 7],[[0, 4, 5, 7], [4, 5, 7], [0, 2, 4, 6], [0, 1, 2, 3, 4, 5, 6, 7], [4, 5, 7], [], [0, 1, 3, 5, 7], [0, 1, 3, 7], [], [], [], []]⟩,
  ⟨9,0,1,[0, 1, 2, 3],[0, 2, 4, 5, 6, 7],[[0, 4, 5, 7], [4, 5, 7], [0, 2, 4, 6], [2, 4, 5, 6, 7], [4, 5, 7], [], [0, 1, 3, 5, 7], [0, 1, 3, 7], [], [], [], []]⟩,
  ⟨12,0,1,[0, 1, 2, 3],[0, 2, 4, 5, 6, 7],[[0, 3, 4, 5, 7], [1, 3, 4, 5, 7], [0, 2, 4, 6], [2, 4, 5, 6, 7], [4, 5, 7], [], [0, 1, 3, 5, 7], [0, 1, 3, 7], [], [], [], []]⟩,
  ⟨13,0,1,[0, 1, 2, 3],[0, 2, 4, 5, 6, 7],[[0, 4, 5, 7], [4, 5, 7], [0, 2, 4, 6], [1, 2, 3, 4, 5, 6, 7], [4, 5, 7], [], [0, 1, 3, 5, 7], [0, 1, 3, 7], [], [], [], []]⟩,
  ⟨15,0,1,[0, 1, 2, 3],[0, 2, 4, 5, 6, 7],[[0, 4, 5, 7], [4, 5, 7], [0, 2, 4, 6], [2, 4, 5, 6, 7], [4, 5, 7], [], [0, 1, 3, 5, 7], [0, 1, 3, 5, 7], [], [], [], []]⟩,
  ⟨18,0,1,[0, 1, 2, 3],[0, 2, 4, 5, 6, 7],[[0, 4, 5, 7], [4, 5, 7], [0, 2, 4, 6], [2, 4, 5, 6, 7], [4, 5, 7], [], [0, 1, 3, 5, 7], [0, 1, 3, 7], [], [], [], []]⟩,
  ⟨19,0,1,[0, 1, 2, 3],[0, 2, 4, 5, 6, 7],[[0, 4, 5, 7], [4, 5, 7], [0, 2, 4, 6], [2, 4, 5, 6, 7], [4, 5, 7], [], [0, 1, 3, 5, 7], [0, 1, 3, 7], [], [], [], []]⟩,
  ⟨20,1,1,[0, 2, 5, 6, 7],[0, 2, 5, 6],[[0, 7, 15], [12], [4], [2, 6, 13, 14], [12], [], [8, 13], [7, 15], [], [], [], []]⟩,
  ⟨21,0,1,[0, 1, 2, 3],[0, 2, 4, 5, 6, 7],[[0, 4, 5, 7], [4, 5, 7], [0, 2, 4, 6], [0, 2, 4, 5, 6, 7], [4, 5, 7], [], [0, 1, 3, 4, 5, 7], [0, 1, 3, 4, 5, 7], [], [], [], []]⟩
],[]⟩
theorem ok18 : checkCut cut18 = true := by decide
def cut19 : Cut := ⟨19,8,5,[
  ⟨1,0,0,[0, 1, 2, 3],[0, 1, 2, 3],[[0], [], [0, 2, 3], [0, 2], [2, 3], [2, 3], [0, 1, 3], [0, 1, 3], [], [], [], []]⟩,
  ⟨2,0,0,[0, 1, 2, 3],[0, 1, 2, 3],[[0], [], [0, 2, 3], [0, 2], [0, 2, 3], [0, 2, 3], [0, 1, 3], [0, 1, 3], [], [], [], []]⟩,
  ⟨3,0,0,[0, 1, 2, 3],[0, 1, 2, 3],[[0], [], [0, 2, 3], [0, 2], [2, 3], [2, 3], [0, 1, 3], [0, 1, 2, 3], [], [], [], []]⟩,
  ⟨7,0,0,[0, 1, 2, 3],[0, 1, 2, 3],[[0], [], [0, 1, 2, 3], [0, 1, 2, 3], [2, 3], [2, 3], [0, 1, 3], [0, 1, 3], [], [], [], []]⟩,
  ⟨9,0,0,[0, 1, 2, 3],[0, 1, 2, 3],[[0], [], [0, 2, 3], [0, 2], [2, 3], [2, 3], [0, 1, 3], [0, 1, 3], [], [], [], []]⟩,
  ⟨13,0,0,[0, 1, 2, 3],[0, 1, 2, 3],[[0], [], [0, 2, 3], [0, 1, 2, 3], [2, 3], [2, 3], [0, 1, 3], [0, 1, 3], [], [], [], []]⟩,
  ⟨15,0,0,[0, 1, 2, 3],[0, 1, 2, 3],[[0], [], [0, 2, 3], [0, 2], [2, 3], [2, 3], [0, 1, 3], [0, 1, 3], [], [], [], []]⟩,
  ⟨19,0,0,[0, 1, 2, 3],[0, 1, 2, 3],[[0], [], [0, 2, 3], [0, 2, 3], [2, 3], [2, 3], [0, 1, 3], [0, 1, 3], [], [], [], []]⟩,
  ⟨20,0,0,[0, 1, 2, 3],[0, 1, 2, 3],[[0], [], [0, 2, 3], [0, 2], [2, 3], [2, 3], [0, 1, 3], [0, 1, 3], [], [], [], []]⟩,
  ⟨21,0,0,[0, 1, 2, 3],[0, 1, 2, 3],[[0], [], [0, 2, 3], [0, 2], [2, 3], [2, 3], [0, 1, 2, 3], [0, 1, 2, 3], [], [], [], []]⟩
],[8, 14]⟩
theorem ok19 : checkCut cut19 = true := by decide
def cut22 : Cut := ⟨22,7,8,[
  ⟨1,0,1,[0, 1, 2, 3],[0, 2, 4, 5, 6, 7],[[0], [], [0, 2, 4, 6], [2, 6], [4, 5, 7], [], [0, 1, 3, 5, 7], [0, 1, 3, 7], [5, 7], [], [], []]⟩,
  ⟨3,0,1,[0, 1, 2, 3],[0, 1, 2, 3, 4, 5, 6, 7],[[0], [], [0, 2, 4, 6], [0, 2, 4, 6], [4, 5, 6, 7], [], [0, 1, 2, 3, 5, 7], [0, 1, 2, 3, 4, 6, 7], [4, 5, 6, 7], [], [], []]⟩,
  ⟨9,0,1,[0, 1, 2, 3],[0, 2, 4, 5, 6, 7],[[0], [], [0, 2, 4, 6], [2, 6], [4, 5, 7], [], [0, 1, 3, 5, 7], [0, 1, 3, 7], [5, 7], [], [], []]⟩,
  ⟨21,0,1,[0, 1, 2, 3],[0, 2, 4, 5, 6, 7],[[0], [], [0, 2, 4, 6], [0, 2, 4, 6], [4, 5, 7], [], [0, 1, 3, 4, 5, 7], [0, 1, 3, 4, 5, 7], [4, 5, 7], [], [], []]⟩
],[15]⟩
theorem ok22 : checkCut cut22 = true := by decide
def cuts : List Cut := [cut0,cut4,cut10,cut12,cut13,cut14,cut16,cut18,cut19,cut22]
theorem count_new : (cuts.map (fun c => c.rows.length)).sum = 93 := by decide
theorem count_residual : (cuts.map (fun c => (residual c).length)).sum = 136 := by decide

theorem cover0 (B : Nat) (hB : 64 ≤ B)
    (hrest : ∀ m ∈ residual cut0, Cover (WeightedBound B) (refine (parent cut0) (slot cut0.query) (some m))) :
    Cover (WeightedBound B) (parent cut0) := by
  refine coverCut cut0 ok0 B hB ?_ hrest
  intro n hn
  change n ∈ [20] at hn
  simp only [List.mem_singleton] at hn
  subst n
  exact BB6.Agent32Raw42WideCuts.coverZeroLAOneRC B

theorem cover4 (B : Nat) (hB : 64 ≤ B)
    (hrest : ∀ m ∈ residual cut4, Cover (WeightedBound B) (refine (parent cut4) (slot cut4.query) (some m))) :
    Cover (WeightedBound B) (parent cut4) := by
  refine coverCut cut4 ok4 B hB ?_ hrest
  intro n hn
  change n ∈ [] at hn
  simp at hn

theorem cover10 (B : Nat) (hB : 64 ≤ B)
    (hrest : ∀ m ∈ residual cut10, Cover (WeightedBound B) (refine (parent cut10) (slot cut10.query) (some m))) :
    Cover (WeightedBound B) (parent cut10) := by
  refine coverCut cut10 ok10 B hB ?_ hrest
  intro n hn
  change n ∈ [] at hn
  simp at hn

theorem cover12 (B : Nat) (hB : 64 ≤ B)
    (hrest : ∀ m ∈ residual cut12, Cover (WeightedBound B) (refine (parent cut12) (slot cut12.query) (some m))) :
    Cover (WeightedBound B) (parent cut12) := by
  refine coverCut cut12 ok12 B hB ?_ hrest
  intro n hn
  change n ∈ [9] at hn
  simp only [List.mem_singleton] at hn
  subst n
  exact BB6.Agent32Raw42WideCuts.coverOneLAZeroRD B

theorem cover13 (B : Nat) (hB : 64 ≤ B)
    (hrest : ∀ m ∈ residual cut13, Cover (WeightedBound B) (refine (parent cut13) (slot cut13.query) (some m))) :
    Cover (WeightedBound B) (parent cut13) := by
  refine coverCut cut13 ok13 B hB ?_ hrest
  intro n hn
  change n ∈ [3, 9, 20] at hn
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
  rcases hn with rfl|rfl|rfl
  · exact BB6.Agent32Raw42NestedCuts.coverOneLBZeroLD B
  · exact BB6.Agent32Raw42NestedCuts.coverOneLBZeroRD B
  · exact BB6.Agent32Raw42WideCuts.coverOneLBOneRC B

theorem cover14 (B : Nat) (hB : 64 ≤ B)
    (hrest : ∀ m ∈ residual cut14, Cover (WeightedBound B) (refine (parent cut14) (slot cut14.query) (some m))) :
    Cover (WeightedBound B) (parent cut14) := by
  refine coverCut cut14 ok14 B hB ?_ hrest
  intro n hn
  change n ∈ [7, 9, 14] at hn
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
  rcases hn with rfl|rfl|rfl
  · exact BB6.Agent32Raw42WideCuts.coverOneLCZeroRB B
  · exact BB6.Agent32Raw42WideCuts.coverOneLCZeroRD B
  · exact BB6.Agent32Raw42NestedCuts.coverOneLCOneLC B

theorem cover16 (B : Nat) (hB : 64 ≤ B)
    (hrest : ∀ m ∈ residual cut16, Cover (WeightedBound B) (refine (parent cut16) (slot cut16.query) (some m))) :
    Cover (WeightedBound B) (parent cut16) := by
  refine coverCut cut16 ok16 B hB ?_ hrest
  intro n hn
  change n ∈ [] at hn
  simp at hn

theorem cover18 (B : Nat) (hB : 64 ≤ B)
    (hrest : ∀ m ∈ residual cut18, Cover (WeightedBound B) (refine (parent cut18) (slot cut18.query) (some m))) :
    Cover (WeightedBound B) (parent cut18) := by
  refine coverCut cut18 ok18 B hB ?_ hrest
  intro n hn
  change n ∈ [] at hn
  simp at hn

theorem cover19 (B : Nat) (hB : 64 ≤ B)
    (hrest : ∀ m ∈ residual cut19, Cover (WeightedBound B) (refine (parent cut19) (slot cut19.query) (some m))) :
    Cover (WeightedBound B) (parent cut19) := by
  refine coverCut cut19 ok19 B hB ?_ hrest
  intro n hn
  change n ∈ [8, 14] at hn
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
  rcases hn with rfl|rfl
  · exact BB6.Agent32Raw42WideCuts.coverOneRBZeroRC B
  · exact BB6.Agent32Raw42WideCuts.coverOneRBOneLC B

theorem cover22 (B : Nat) (hB : 64 ≤ B)
    (hrest : ∀ m ∈ residual cut22, Cover (WeightedBound B) (refine (parent cut22) (slot cut22.query) (some m))) :
    Cover (WeightedBound B) (parent cut22) := by
  refine coverCut cut22 ok22 B hB ?_ hrest
  intro n hn
  change n ∈ [15] at hn
  simp only [List.mem_singleton] at hn
  subst n
  exact BB6.Agent32Raw42WideCuts.coverOneREOneLD B

theorem code_distinct : cuts.all (fun c => (codes c).eraseDups.length == (codes c).length) = true := by decide

theorem first_distinct : (cuts.map Cut.first).eraseDups.length = cuts.length := by decide

theorem cover_all (B : Nat) (hB : 64 ≤ B)
    (hrest : ∀ c ∈ cuts, ∀ m ∈ residual c,
      Cover (WeightedBound B) (refine (parent c) (slot c.query) (some m))) :
    ∀ c ∈ cuts, Cover (WeightedBound B) (parent c) := by
  intro c hc
  have hm := hrest c hc
  simp only [cuts,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact cover0 B hB hm
  · exact cover4 B hB hm
  · exact cover10 B hB hm
  · exact cover12 B hB hm
  · exact cover13 B hB hm
  · exact cover14 B hB hm
  · exact cover16 B hB hm
  · exact cover18 B hB hm
  · exact cover19 B hB hm
  · exact cover22 B hB hm

#print axioms bankCover
#print axioms cover_all
#print axioms code_distinct
#print axioms count_new
#print axioms count_residual
end BB6.Agent32Raw42Early
