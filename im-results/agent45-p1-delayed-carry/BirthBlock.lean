import BirthWindow
namespace BB6.Agent45ReverseBlock
open BB6.Agent9BatchCarry (Interior Edge back birth sweep live terminal mem_birth mem_live mem_batch mem_terminal)

/-- Monotonicity only: checkpoint lists may overapproximate genuine carries. -/
theorem back_cover (q c z : Nat) (zs : List Nat) (hz : z∈zs) (he : Edge q c z) : c∈back q zs := by
  obtain ⟨hc,hp⟩ := (BB6.Agent9BatchCarry.edge_iff_parent q c z he.2.1).mp he
  unfold back
  rw [BB6.Agent9BatchCarry.mem_join,BB6.Agent9BatchCarry.mem_branch,BB6.Agent9BatchCarry.mem_branch]
  cases hb : decide (2*z<q)
  · right; exact ⟨⟨z,hz,hb,hp.symm⟩,hc⟩
  · left; exact ⟨⟨z,hz,hb,hp.symm⟩,hc⟩

theorem sweep_of_walk (F k n z : Nat) (zs : List Nat) (hF : k+4≤F)
    (hlo : F-k≤n+4) (hhi : n+4≤F) (heven : n%2=0)
    (hw : SourceWalk (n+4) ((n+2)/2) (F-(n+4)) z) (hz : z∈zs) : n∈sweep F zs k := by
  induction k generalizing F z zs with
  | zero =>
    have hq : F=n+4 := by omega
    subst F
    simp only [Nat.sub_self] at hw
    cases hw
    exact (mem_birth _ n _ (by omega)).mpr ⟨rfl,heven,hz⟩
  | succ k ih =>
    rw [sweep,List.mem_append]
    by_cases hq : n+4=F
    · subst F
      simp only [Nat.sub_self] at hw
      cases hw
      exact Or.inl ((mem_birth _ n _ (by omega)).mpr ⟨rfl,heven,hz⟩)
    · have hlen : F-(n+4)=F-1-(n+4)+1 := by omega
      rw [hlen] at hw
      obtain ⟨y,hy,ht⟩ := source_split _ _ _ _ _ hw
      have ht' : SourceWalk (F-1) y 1 z := by simpa [show n+4+(F-1-(n+4))=F-1 by omega] using ht
      cases ht' with
      | cons _ _ d _ _ he htail =>
        cases htail
        exact Or.inr (ih (F-1) y (back (F-1) zs) (by omega) (by omega) (by omega) hy (back_cover _ _ _ _ hz he))

def windowFilter (F k : Nat) (xs : List Nat) : List Nat :=
  xs.filter (fun z => decide (F-2^(k+2)<(2^(k+1)*z)%F))

/-- A single static modular filter preserves every central birth in the block. -/
theorem birth_in_window (F k n j : Nat) (xs : List Nat)
    (hF : k+4≤F) (hfit : 2^(k+2)≤F)
    (hs : ∀ c∈live F j,c∈xs)
    (hlo : F-k≤n+4) (hhi : n+4≤F) (heven : n%2=0)
    (hc : (n+2)/2∈live (n+4) (F+j-(n+4))) : n∈sweep F (windowFilter F k xs) k := by
  obtain ⟨w,hw⟩ := (mem_live _ _ _).mp hc
  rw [show F+j-(n+4)=F-(n+4)+j by omega] at hw
  obtain ⟨z,hz,ht⟩ := source_split _ _ _ _ _ hw
  have hz' : SourceWalk (n+4) (((n+4)-2)/2) (F-(n+4)) z := by simpa using hz
  have hwin := source_center_window hhi (by omega) hfit (by omega) hz'
  have htail : SourceWalk F z j w := by simpa [show n+4+(F-(n+4))=F by omega] using ht
  have hm := hs z ((mem_live _ _ _).mpr ⟨w,htail⟩)
  exact sweep_of_walk F k n z _ hF hlo hhi heven hz (List.mem_filter.mpr ⟨hm,by simpa using hwin⟩)

def birthsChecked (F k R : Nat) (xs : List Nat) : Bool :=
  (sweep F (windowFilter F k xs) k).all (·>R)

theorem birthsChecked_sound (F k R j n : Nat) (xs : List Nat)
    (hF : k+4≤F) (hfit : 2^(k+2)≤F)
    (hs : ∀ c∈live F j,c∈xs) (hcheck : birthsChecked F k R xs=true)
    (hlo : F-k≤n+4) (hhi : n+4≤F) (heven : n%2=0) (hr : n≤R) :
    (n+2)/2∉live (n+4) (F+j-(n+4)) := by
  intro hc
  have hm := birth_in_window F k n j xs hF hfit hs hlo hhi heven hc
  have hh := List.all_eq_true.mp hcheck n hm
  simp at hh
  omega

/-- Fuelled median-pivot partition sort. The membership theorem does not
    require adequate fuel or any ordering assumptions on the input. -/
def quickUnique : Nat → List Nat → List Nat
  | 0,xs => xs
  | _+1,[] => []
  | k+1,x::xs =>
    let ys := x::xs
    let p := ys.getD (ys.length/2) x
    quickUnique k (ys.filter (·<p)) ++ p :: quickUnique k (ys.filter (·>p))

theorem mem_quickUnique (a k : Nat) (xs : List Nat) : a∈quickUnique k xs ↔ a∈xs := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih =>
    cases xs with
    | nil => simp [quickUnique]
    | cons x xs =>
      let ys := x::xs
      let p := ys.getD (ys.length/2) x
      have hlt : ys.length/2<ys.length := by dsimp [ys]; omega
      have hp : p∈ys := by
        dsimp only [p,List.getD]
        rw [List.getElem?_eq_getElem hlt]
        exact List.getElem_mem hlt
      change a∈quickUnique k (ys.filter (·<p)) ++ p :: quickUnique k (ys.filter (·>p)) ↔ a∈ys
      simp only [List.mem_append,List.mem_cons,ih,List.mem_filter,decide_eq_true_eq]
      constructor
      · rintro (⟨h,_⟩|rfl|⟨h,_⟩) <;> assumption
      · intro hm
        by_cases h : a<p
        · exact Or.inl ⟨hm,h⟩
        · by_cases he : a=p
          · exact Or.inr (Or.inl he)
          · exact Or.inr (Or.inr ⟨hm,by omega⟩)

def uniqueSorted (xs : List Nat) : List Nat := quickUnique 64 xs

theorem mem_uniqueSorted (a : Nat) (xs : List Nat) : a∈uniqueSorted xs ↔ a∈xs := mem_quickUnique _ _ _

def blockBack (F k : Nat) (xs : List Nat) : List Nat :=
  uniqueSorted (backBlock (F-k) k xs)

theorem blockBack_cover (F k j : Nat) (xs : List Nat) (hk : k≤F) (hfit : 2^(k+1)≤F)
    (hs : ∀ c∈live F j,c∈xs) : ∀ c∈live (F-k) (k+j),c∈blockBack F k xs := by
  intro c hc
  obtain ⟨w,hw⟩ := (mem_live _ _ _).mp hc
  obtain ⟨z,hz,ht⟩ := source_split _ _ _ _ _ hw
  have ht' : SourceWalk F z j w := by simpa [show F-k+k=F by omega] using ht
  rw [blockBack,mem_uniqueSorted,mem_backBlock _ _ _ _ (by simpa [show F-k+k=F by omega] using hfit)]
  exact ⟨z,hs z ((mem_live _ _ _).mpr ⟨w,ht'⟩),hz⟩

#print axioms birthsChecked_sound
#print axioms blockBack_cover
end BB6.Agent45ReverseBlock
