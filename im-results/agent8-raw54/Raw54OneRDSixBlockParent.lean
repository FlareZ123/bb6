import Raw54OneRDSixBlockZeroRA
import ZipThreeHoleAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option autoImplicit false

namespace BB6.Agent8Raw54.SixBlock
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent13BlankDelay BB6.Agent10ZipAudit BB6.Agent31ThreeHole

def a0LF : Move := ⟨false,false,5⟩
def a1LB : Move := ⟨true,false,1⟩
def a1RB : Move := ⟨true,true,1⟩
def a1LF : Move := ⟨true,false,5⟩
def M : List Bool := [true,true,true,false]
def G (k : Nat) : Z0 := ⟨3,lp ++ M ++ rep P (k+1),[]⟩

theorem entry0LF : run0 (table a0LF) 110 ⟨0,[],[]⟩ = some (G 0) := by decide +kernel
theorem entry1LB : run0 (table a1LB) 112 ⟨0,[],[]⟩ = some (G 0) := by decide +kernel
theorem entry1RB : run0 (table a1RB) 106 ⟨0,[],[]⟩ = some (G 0) := by decide +kernel

theorem marked_epoch (a : Move) (c k : Nat)
    (hstart : ∀ L : List Bool, run0 (table a) 8 ⟨3,lp ++ M ++ L,[]⟩ = some ⟨3,rp ++ L,[true,true,true,true]⟩)
    (hmid : ∀ L : List Bool, run0 (table a) 16 ⟨3,rp ++ L,[true,true,true,true]⟩ = some ⟨3,lp ++ L,[false,false,true,true]⟩)
    (hend : ∀ L : List Bool, run0 (table a) c ⟨3,rp ++ L,[true,false,false,true,true]⟩ = some ⟨3,lp ++ M ++ P ++ L,[]⟩) :
    run0 (table a) (81+c+36*k) (G k) = some (G (k+1)) := by
  have h1 := hstart (rep P (k+1))
  have h2 := hmid (rep P (k+1))
  have h3 := pass a (k+1) [false,false,true,true]
  have h4 := hend (rep P (k+1))
  rw [show 81+c+36*k=8+16+(21+36*(k+1))+c by omega]
  simpa only [G,rep,List.append_assoc] using join0 (join0 (join0 h1 h2) h3) h4

theorem never_marked (a : Move) (n c : Nat)
    (he : run0 (table a) n ⟨0,[],[]⟩ = some (G 0))
    (hr : ∀ k, run0 (table a) (81+c+36*k) (G k) = some (G (k+1)))
    (m : Machine) (hm : compatible (table a) m) : NeverHalts m :=
  never_of_growth (table a) G n (fun k => 81+c+36*k) he (by intro k; omega) hr m hm

theorem never0LF : ∀ m, compatible (table a0LF) m → NeverHalts m :=
  never_marked a0LF 110 17 entry0LF (fun k => marked_epoch a0LF 17 k (by intro L; rfl) (by intro L; rfl) (by intro L; rfl))
theorem never1LB : ∀ m, compatible (table a1LB) m → NeverHalts m :=
  never_marked a1LB 112 19 entry1LB (fun k => marked_epoch a1LB 19 k (by intro L; rfl) (by intro L; rfl) (by intro L; rfl))
theorem never1RB : ∀ m, compatible (table a1RB) m → NeverHalts m :=
  never_marked a1RB 106 13 entry1RB (fun k => marked_epoch a1RB 13 k (by intro L; rfl) (by intro L; rfl) (by intro L; rfl))

def cycleZ : Z0 := ⟨0,[true,true,false,true,true,true,true,true,true,false],[true]⟩
theorem cycleEntry : run0 (table a1LF) 99 ⟨0,[],[]⟩ = some cycleZ := by decide +kernel
theorem cycleReturn : run0 (table a1LF) 4 cycleZ = some cycleZ := by rfl
theorem never1LF : ∀ m, compatible (table a1LF) m → NeverHalts m :=
  never_of_growth (table a1LF) (fun _ => cycleZ) 99 (fun _ => 4) cycleEntry (by intro k; decide) (fun _ => cycleReturn)

def a1 : Slot := (0,true)
def c1 : Slot := (2,true)
def parent : PartialMachine := fun s => if s = a1 then none else table a0LA s

theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide +kernel
theorem parent_hole : parent a1 = none := by decide +kernel
theorem parent_nohalt : weightedTNFNoAssignedHalt parent := by
  intro ⟨q,b⟩
  have h : q.val = 0 ∨ q.val = 1 ∨ q.val = 2 ∨ q.val = 3 ∨ q.val = 4 ∨ q.val = 5 := by omega
  obtain ⟨i,hi⟩ := q
  simp only at h
  rcases h with h|h|h|h|h|h <;> subst i <;> cases b <;> decide +kernel +revert

noncomputable def kids (a : Move) : Audit :=
  match a.write,a.right,a.next.val with
  | false,false,0 => .proven (table a0LA) (never_at a0LA 404 2 entry_a0LA)
  | false,false,1 => .proven (table a0LB) (never_at a0LB 212 2 entry_a0LB)
  | false,false,2 => .last 100 c1
  | false,false,3 => .last 104 c1
  | false,false,4 => .proven (table a0LE) (never_at a0LE 151 1 entry_a0LE)
  | false,false,5 => .proven (table a0LF) never0LF
  | false,true,0 => .proven (table ZeroRA.a) ZeroRA.never
  | false,true,1 => .proven (table a0RB) (never_at a0RB 544 3 entry_a0RB)
  | false,true,2 => .last 100 c1
  | false,true,3 => .proven (table a0RD) (never_at a0RD 247 2 entry_a0RD)
  | false,true,4 => .proven (table a0RE) (never_at a0RE 210 2 entry_a0RE)
  | false,true,5 => .proven (table ZeroRF.a) ZeroRF.never
  | true,false,0 => .last 146 c1
  | true,false,1 => .proven (table a1LB) never1LB
  | true,false,2 => .last 100 c1
  | true,false,3 => .proven (table a1LD) (never_at a1LD 149 1 entry_a1LD)
  | true,false,4 => .proven (table a1LE) (never_at a1LE 153 1 entry_a1LE)
  | true,false,5 => .proven (table a1LF) never1LF
  | true,true,0 => .proven (table a1RA) (never_at a1RA 464 3 entry_a1RA)
  | true,true,1 => .proven (table a1RB) never1RB
  | true,true,2 => .last 100 c1
  | true,true,3 => .proven (table a1RD) (never_at a1RD 155 1 entry_a1RD)
  | true,true,4 => .proven (table OneRE.a) OneRE.never
  | true,true,5 => .proven (table a1RF) (never_at a1RF 108 1 entry_a1RF)
  | _,_,_ => .last 0 c1

noncomputable def audit : Audit := .split 99 a1 kids

theorem check : zipCheck 147 parent audit = true := by decide +kernel
noncomputable def certificate : WeightedTNFCertificate 147 parent 6 :=
  certifiedZip 147 parent audit parent_root parent_nohalt check

theorem all_completions_weighted : ∀ m, compatible parent m → WeightedBound 147 m := certificate.sound

theorem cover : Cover (WeightedBound 147) parent := Cover.leaf parent all_completions_weighted

theorem attained : ∃ m, compatible parent m ∧ HaltsAfter m 146 := by
  let p := refine parent a1 (some ⟨true,false,0⟩)
  let m := weightedTNFDefaultCompletion (refine p c1 none)
  have hr : (knownRun p 146).map readSlot = some c1 := by decide +kernel
  have hh : p c1 = none := by decide +kernel
  have hm : compatible (refine p c1 none) m := weightedTNFDefaultCompletion_compatible _
  have hmp : compatible p m := refine_preserves_compat p m c1 none hh hm
  have hparent : compatible parent m := refine_preserves_compat parent m a1 (some ⟨true,false,0⟩) parent_hole hmp
  refine ⟨m,hparent,?_⟩
  cases hrun : knownRun p 146 with
  | none => simp [hrun] at hr
  | some c =>
    have hs : readSlot c = c1 := by simpa [hrun] using hr
    apply first_hole_halts p 146 c hrun
    · simpa [hs] using hh
    · simpa [hs] using hm

theorem exact_weighted_threshold (B : Nat) :
    (∀ m, compatible parent m → WeightedBound B m) ↔ 147 ≤ B := by
  constructor
  · intro h
    obtain ⟨m,hm,hh⟩ := attained
    have hz := firstOne_terminal parent parent_root m hm
    have hd : 0 ∈ delays (zeroNext m) 0 := (mem_delays_iff hz).mpr ⟨0, TerminalPath.stop 0 hz⟩
    have hb := h m hm 146 0 hh hd
    omega
  · intro hb m hm k d hk hd
    exact Nat.le_trans (all_completions_weighted m hm k d hk hd) hb

#print axioms cover
#print axioms attained
#print axioms exact_weighted_threshold
end BB6.Agent8Raw54.SixBlock
