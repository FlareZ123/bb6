import CanonicalPartial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent50FastKey
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier

def slots : List Slot := (List.finRange 6).flatMap fun q => [false,true].map fun b => (q,b)
def code : Option Transition → Nat
  | none => 25
  | some none => 24
  | some (some m) => 4*m.next.val+2*m.write.toNat+m.right.toNat

theorem code_lt (x : Option Transition) : code x < 26 := by
  rcases x with _ | (_ | m)
  · decide
  · decide
  · rcases m with ⟨w,r,q⟩
    cases w <;> cases r <;> simp [code, Bool.toNat] <;> omega

theorem code_move_lt (m : Move) : code (some (some m)) < 24 := by
  rcases m with ⟨w,r,q⟩
  cases w <;> cases r <;> simp [code, Bool.toNat] <;> omega

theorem code_move_inj {m n : Move} (h : code (some (some m)) = code (some (some n))) : m = n := by
  rcases m with ⟨w,r,q⟩; rcases n with ⟨w',r',q'⟩
  cases w <;> cases r <;> cases w' <;> cases r' <;> simp [code, Bool.toNat] at h ⊢ <;> try omega
  all_goals apply Fin.ext; omega

theorem code_inj {x y : Option Transition} (h : code x = code y) : x = y := by
  rcases x with _ | (_ | m)
  · rcases y with _ | (_ | n)
    · rfl
    · simp [code] at h
    · have hn := code_move_lt n; change 25 = code (some (some n)) at h; omega
  · rcases y with _ | (_ | n)
    · simp [code] at h
    · rfl
    · have hn := code_move_lt n; change 24 = code (some (some n)) at h; omega
  · rcases y with _ | (_ | n)
    · have hm := code_move_lt m; change code (some (some m)) = 25 at h; omega
    · have hm := code_move_lt m; change code (some (some m)) = 24 at h; omega
    · rw [code_move_inj h]

def pack : List (Option Transition) → Nat
  | [] => 0
  | x::xs => code x + 26*pack xs

theorem pack_inj {xs ys : List (Option Transition)} (hlen : xs.length = ys.length)
    (h : pack xs = pack ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have hx := code_lt x
      have hy := code_lt y
      simp only [pack] at h
      have hxy : code x = code y := by omega
      have htail : pack xs = pack ys := by omega
      have hlen' : xs.length = ys.length := by simpa using hlen
      rw [code_inj hxy, ih hlen' htail]

def tableCode (p : PartialMachine) : Nat := pack (slots.map p)
theorem tableCode_inj {p q : PartialMachine} (h : tableCode p = tableCode q) : p = q := by
  funext s
  have hmap : slots.map p = slots.map q := pack_inj (by simp) h
  apply List.map_inj_left.mp hmap
  rcases s with ⟨q,b⟩
  exact List.mem_flatMap.mpr ⟨q,List.mem_finRange q,List.mem_map.mpr ⟨b,by cases b <;> simp,rfl⟩⟩

inductive KeySet where
  | empty
  | leaf (k : Nat)
  | branch (pivot : Nat) (lt ge : KeySet)
def KeySet.elements : KeySet → List Nat
  | .empty => []
  | .leaf k => [k]
  | .branch _ lt ge => lt.elements ++ ge.elements
def KeySet.contains (k : Nat) : KeySet → Bool
  | .empty => false
  | .leaf v => decide (k = v)
  | .branch p lt ge => if k < p then lt.contains k else ge.contains k
theorem KeySet.contains_sound {k : Nat} {s : KeySet} (h : s.contains k = true) : k ∈ s.elements := by
  induction s with
  | empty => simp [KeySet.contains] at h
  | leaf v => simpa [KeySet.contains,KeySet.elements] using h
  | branch p lt ge ihl ihg =>
    by_cases hk : k < p
    · have hh : lt.contains k = true := by simpa [KeySet.contains,hk] using h
      exact List.mem_append_left _ (ihl hh)
    · have hh : ge.contains k = true := by simpa [KeySet.contains,hk] using h
      exact List.mem_append_right _ (ihg hh)
#print axioms tableCode_inj
#print axioms KeySet.contains_sound
end BB6.Agent50FastKey
