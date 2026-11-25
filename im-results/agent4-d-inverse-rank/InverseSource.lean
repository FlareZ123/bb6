import Boundary
import InverseGrammar
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace DExit
open CryptidBoundary

def bit (b : Bool) : Nat := if b then 1 else 0
def enc : List Bool → Nat
  | [] => 0
  | b::bs => bit b + 2*enc bs

theorem enc_head (b : Bool) (bs : List Bool) : enc (b::bs)%2 = bit b := by
  cases b <;> simp [enc,bit] <;> omega

theorem enc_tail (b : Bool) (bs : List Bool) : enc (b::bs)/2 = enc bs := by
  cases b <;> simp [enc,bit] <;> omega

def compatible (L : List Nat) (ls : List Bool) : Prop := L = ls.map bit

theorem stepL (q v r : Nat) (l : List Bool) (b : Bool) (bs : List Bool)
    (h : rule q (bit b) = some (v,false,r)) :
    step ⟨l,b,bs,q⟩ = goL ⟨l,b,bs,q⟩ (v==1) r := by
  have hq := (rule_valid h).1
  have hcases : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hcases with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> simp [rule,bit] at h <;> obtain ⟨rfl,rfl⟩ := h <;> rfl

theorem stepR (q v r : Nat) (l : List Bool) (b : Bool) (bs : List Bool)
    (h : rule q (bit b) = some (v,true,r)) :
    step ⟨l,b,bs,q⟩ = goR ⟨l,b,bs,q⟩ (v==1) r := by
  have hq := (rule_valid h).1
  have hcases : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hcases with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> simp [rule,bit] at h <;> obtain ⟨rfl,rfl⟩ := h <;> rfl

theorem bit_eq {v : Nat} (hv : v < 2) : bit (v==1)=v := by
  have h : v=0 ∨ v=1 := by omega
  rcases h with rfl|rfl <;> rfl

theorem raw_source {t q w r y : Nat} {L : List Nat}
    (h : RawExit t L q w r y) (ls : List Bool) (hl : compatible L ls)
    (a : Bool) (T : List Bool) (b : Bool) (bs : List Bool)
    (hw : w = enc (b::bs)) :
    let c := Cfg.mk (ls++a::T) b bs q
    let d := run t c
    d.l = T ∧ d.h = a ∧ d.st = r ∧ enc d.r = y ∧
    ∀ i<t, (run i c).l.length ≥ (a::T).length := by
  induction h generalizing ls b bs with
  | done q w v r hr =>
    have hls : ls=[] := by cases ls <;> simp_all [compatible]
    subst ls; subst w
    rw [enc_head] at hr
    rw [enc_tail]
    have hv := (rule_valid hr).2.1
    simp only [List.nil_append,run,stepL _ _ _ _ _ _ hr,goL,Cfg.l,Cfg.h,Cfg.st,Cfg.r,enc,bit_eq hv, true_and]
    constructor
    · omega
    · intro i hi; have : i=0 := by omega
      subst i; simp [run]
  | left t q w v r a0 L r' y hr hrest ih =>
    cases ls with
    | nil => simp [compatible] at hl
    | cons x xs =>
      simp [compatible] at hl
      obtain ⟨rfl,hxs⟩ := hl
      subst w
      rw [enc_head] at hr
      rw [enc_tail] at ih
      have hv := (rule_valid hr).2.1
      have hw' : 2*(2*enc bs+v)+bit x = enc (x::(v==1)::bs) := by
        simp [enc,bit_eq hv]; omega
      have hrec := ih xs hxs x ( (v==1)::bs ) hw'
      simp only [List.cons_append,run,stepL _ _ _ _ _ _ hr,goL] at *
      obtain ⟨h1,h2,h3,h4,h5⟩ := hrec
      refine ⟨h1,h2,h3,h4,?_⟩
      intro i hi
      cases i with
      | zero => simp [run] <;> omega
      | succ i => simpa only [run,stepL _ _ _ _ _ _ hr,goL,List.cons_append] using h5 i (by omega)
  | right t q w v r L r' y hr hrest ih =>
    subst w
    rw [enc_head] at hr
    rw [enc_tail] at ih
    have hv := (rule_valid hr).2.1
    have hl' : compatible (v::L) ((v==1)::ls) := by
      simp [compatible,bit_eq hv]; exact hl
    cases bs with
    | nil =>
      have hrec := ih ((v==1)::ls) hl' false [] (by simp [enc,bit])
      simp only [List.cons_append,run,stepR _ _ _ _ _ _ hr,goR] at *
      obtain ⟨h1,h2,h3,h4,h5⟩ := hrec
      refine ⟨h1,h2,h3,h4,?_⟩
      intro i hi
      cases i with
      | zero => simp [run] <;> omega
      | succ i => simpa only [run,stepR _ _ _ _ _ _ hr,goR,List.cons_append] using h5 i (by omega)
    | cons x xs =>
      have hrec := ih ((v==1)::ls) hl' x xs rfl
      simp only [List.cons_append,run,stepR _ _ _ _ _ _ hr,goR] at *
      obtain ⟨h1,h2,h3,h4,h5⟩ := hrec
      refine ⟨h1,h2,h3,h4,?_⟩
      intro i hi
      cases i with
      | zero => simp [run] <;> omega
      | succ i => simpa only [run,stepR _ _ _ _ _ _ hr,goR,List.cons_append] using h5 i (by omega)

/-- Every bounded inverse answer is an actual first crossing, in every
    nonempty left frame, independent of the representation of trailing zeros. -/
theorem inverse_source_sound {q w r y : Nat}
    (h : InverseBounded (DLowerRank.rank y) q w r y)
    (a : Bool) (T : List Bool) (b : Bool) (bs : List Bool)
    (hw : w = enc (b::bs)) :
    ∃ t, let c := Cfg.mk (a::T) b bs q
         let d := run t c
         d.l = T ∧ d.h = a ∧ d.st = r ∧ enc d.r = y ∧
         ∀ i<t, (run i c).l.length ≥ (a::T).length := by
  obtain ⟨t,ht⟩ := (raw_inverse_iff q w r y).2 h
  exact ⟨t, raw_source ht [] rfl a T b bs hw⟩

#print axioms raw_source
#print axioms inverse_source_sound
end DExit
