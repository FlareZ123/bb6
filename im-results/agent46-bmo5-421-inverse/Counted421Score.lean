import Counted421Bridge
import CapRoot

namespace Counted421

def cfg (x : Nat) := C1 (Cap.oddCounter x)
def score (x : Nat) := (sectionEval (Cap.oddCounter x)).1

theorem score_exact (x : Nat) (hx : 0<x) : Exact (cfg x) (score x) ((Cap.f x).map cfg) := by
  have h := section_exact (Cap.oddCounter x)
  rw [section_f x hx] at h
  change Exact (C1 (Cap.oddCounter x)) (sectionEval (Cap.oddCounter x)).1 ((Cap.f x).map (fun y=>C1 (Cap.oddCounter y)))
  simpa [Option.map_map,Function.comp_def] using h

theorem score_pos (x : Nat) : 0<score x := by
  unfold score
  generalize Cap.oddCounter x=a
  rcases a with _|_|a
  · decide
  · decide
  · unfold sectionEval
    cases eval (a+2*a+7) (.d 0 a 1) <;> simp <;> omega

theorem score_bound (x : Nat) : score x≤100*(2*x+10)^2 := by
  have h := section_bound (Cap.oddCounter x)
  unfold score Cap.oddCounter at *
  apply Nat.le_trans h
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

theorem none_persists {c : Cfg} {n m : Nat} (h : run n c=none) (hm : n≤m) : run m c=none := by
  rw [show m=n+(m-n) by omega,run_add,h]; rfl

theorem exact_none {c : Cfg} {n : Nat} (h : Exact c n none) : run n c=none := by
  obtain ⟨k,d,rfl,hr,hs⟩ := h
  rw [run_add,hr]
  simp [run,hs]

theorem exact_unique {c : Cfg} {n m : Nat} (h : Exact c n none) (h' : Exact c m none) : n=m := by
  have hn := exact_none h
  have hm := exact_none h'
  obtain ⟨k,d,hk,hr,_⟩ := h
  obtain ⟨l,e,hl,hr',_⟩ := h'
  by_cases hlt : n<m
  · have e := none_persists hn (show n≤l by omega)
    rw [hr'] at e; contradiction
  · by_cases hgt : m<n
    · have e := none_persists hm (show m≤k by omega)
      rw [hr] at e; contradiction
    · omega

theorem exact_split {c d : Cfg} {a n : Nat} (h : run a c=some d) (hh : Exact c n none) :
    ∃ m, n=a+m ∧ Exact d m none := by
  have hn := exact_none hh
  obtain ⟨k,e,hk,hr,hs⟩ := hh
  have ha : a≤k := by
    by_cases hgood : a≤k
    · exact hgood
    · have he := none_persists hn (show n≤a by omega)
      rw [h] at he; contradiction
  have he : run (k-a) d=some e := by
    rw [show k=a+(k-a) by omega,run_add,h] at hr
    exact hr
  exact ⟨k-a+1,by omega,⟨k-a,e,rfl,he,hs⟩⟩

/-- Exact arrival cost along the unique inverse chain, excluding the last section. -/
def arrivalCost (x : Nat) : Nat :=
  match _h : Cap.predecessor x with
  | none => 0
  | some p => arrivalCost p + score p
termination_by x
decreasing_by exact Cap.edge_grows (Cap.predecessor_sound _h)

theorem arrival_edge {x y : Nat} (h : Cap.Edge x y) : arrivalCost y=arrivalCost x+score x := by
  rw [arrivalCost,Cap.predecessor_complete h]

theorem arrival_two : arrivalCost 2=0 := by rw [arrivalCost]; rfl

theorem arrival_exact {x : Nat} (h : Cap.Reach 2 x) : run (arrivalCost x) (cfg 2)=some (cfg x) := by
  induction h with
  | refl => rw [arrival_two]; rfl
  | @tail x y h e ih =>
    have he := score_exact x (by have := Cap.reach_le h; omega)
    rw [Cap.edge_iff.mp e] at he
    rw [arrival_edge e]
    exact seq ih he

theorem reachable_halt_score {x : Nat} (hr : Cap.Reach 2 x) (hf : Cap.f x=none) :
    Exact ⟨.A,0,0⟩ (8+arrivalCost x+score x) none := by
  have he := score_exact x (by have := Cap.reach_le hr; omega)
  rw [hf] at he
  have h := seq (show run 8 ⟨.A,0,0⟩=some (cfg 2) from blank) (arrival_exact hr)
  exact exact_seq h he

/-- Any genuine finite halt from a reachable section must end at a terminal in the graph. -/
theorem halt_reaches_terminal {x n : Nat} (hx : Cap.Reach 2 x) (hn : Exact (cfg x) n none) :
    ∃ y, Cap.Reach 2 y ∧ Cap.f y=none := by
  induction n using Nat.strongRecOn generalizing x with
  | ind n ih =>
    have he := score_exact x (by have := Cap.reach_le hx; omega)
    cases hf : Cap.f x with
    | none => exact ⟨x,hx,hf⟩
    | some y =>
      rw [hf] at he
      change run (score x) (cfg x)=some (cfg y) at he
      obtain ⟨m,hm,hex⟩ := exact_split he hn
      exact ih m (by have := score_pos x; omega) (Cap.Reach.tail hx (Cap.edge_iff.mpr hf)) hex

theorem exact_blank_iff (n : Nat) : Exact ⟨.A,0,0⟩ n none ↔
    ∃ i, Cap.rootOf (Cap.halt i)=2 ∧ n=8+arrivalCost (Cap.halt i)+score (Cap.halt i) := by
  constructor
  · intro h
    obtain ⟨m,_,hm⟩ := exact_split (show run 8 ⟨.A,0,0⟩=some (cfg 2) from blank) h
    obtain ⟨y,hy,hf⟩ := halt_reaches_terminal Cap.Reach.refl hm
    obtain ⟨i,rfl⟩ := (Cap.f_none_iff (Cap.reach_le hy)).mp hf
    exact ⟨i,(Cap.root_iff_reach _).mpr hy,exact_unique h (reachable_halt_score hy hf)⟩
  · rintro ⟨i,hr,rfl⟩
    have hh : Cap.Reach 2 (Cap.halt i) := (Cap.root_iff_reach _).mp hr
    exact reachable_halt_score hh ((Cap.f_none_iff (Cap.reach_le hh)).mpr ⟨i,rfl⟩)

-- Uniform crude polynomial bound on the score of any reachable terminal.
theorem arrival_bound {x M : Nat} (hr : Cap.Reach 2 x) (hx : x≤M) :
    arrivalCost x≤x*(100*(2*M+10)^2) := by
  induction hr with
  | refl => rw [arrival_two]; omega
  | @tail x y h e ih =>
    have hxy := Cap.edge_grows e
    have hx' : x≤M := by omega
    have h1 := ih hx'
    have h2 := score_bound x
    have h3 : 100*(2*x+10)^2≤100*(2*M+10)^2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    have h4 := Nat.mul_le_mul_right (100*(2*M+10)^2) (show x+1≤y by omega)
    rw [Nat.add_mul,Nat.one_mul] at h4
    rw [arrival_edge e]
    omega

theorem halt_score_bound (n : Nat) (h : Exact ⟨.A,0,0⟩ n none) :
    ∃ i, Cap.rootOf (Cap.halt i)=2 ∧ n≤1000000*8^i := by
  obtain ⟨i,hr,hn⟩ := (exact_blank_iff n).mp h
  refine ⟨i,hr,?_⟩
  let T := Cap.halt i
  have ht := Cap.halt_formula i
  have hpos : 0<2^i := Nat.two_pow_pos i
  have hT : T+1≤10*2^i := by dsimp [T]; omega
  have hb := arrival_bound ((Cap.root_iff_reach _).mp hr) (Nat.le_refl (Cap.halt i))
  have hs := score_bound (Cap.halt i)
  have hC : 2*T+10≤30*2^i := by omega
  have hmul := Nat.mul_le_mul hT (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left hC 2))
  have hsum : n≤8+(T+1)*(100*(2*T+10)^2) := by
    rw [Nat.add_mul,Nat.one_mul]; dsimp [T] at *; omega
  have he : 10*2^i*(100*(30*2^i)^2)=900000*8^i := by
    rw [Nat.mul_pow,Nat.pow_two (2^i)]
    calc
      10*2^i*(100*(30^2*(2^i*2^i))) = (10*100*30^2)*(2^i*2^i*2^i) := by ac_rfl
      _ = 900000*8^i := by rw [←Nat.mul_pow,←Nat.mul_pow]
  rw [he] at hmul
  have h8 := Nat.pow_pos (n:=i) (show 0<8 by decide)
  omega

#print axioms exact_blank_iff
#print axioms halt_score_bound
end Counted421
