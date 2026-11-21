import SheepPower1458LowRowTable
import SheepPower1458RootEdgeTable
import SheepPower1458High
import SheepPower1458All
import SheepPower1458Target

set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace SheepPower1458

open SheepPower1458SourceIntegration
open SheepPower1458AffineBounds
open SheepPower1458LowRowTable
open SheepEven

def blankRootNode : AffineNode :=
  { s := 0, b := 0, c := 0, C := 1, r := 7, v3C := 0 }

def indexedAffineBasin (t : Nat) (nodeAt : Nat → AffineNode)
    (N y : Nat) : Prop :=
  ∃ n, n < N ∧ affineNodeValue t (nodeAt n) y

theorem genericChildValue
    (t : Nat) (parent child : AffineNode) (a h v x : Nat)
    (hx : x = 2^a * v)
    (hgen :
      parent.C * 3^h * (2^(a+1)+1) * v +
        2*a*(parent.C*3^h) +
        2^(h+1)*(parent.C-parent.b+parent.c)
        = 2^(1458*t+parent.s+h+1) + 3*(parent.C*3^h))
    (hchildS : child.s = parent.s+a+h+1)
    (hchildC : child.C = parent.C*3^h*(2^(a+1)+1))
    (hchildOffset :
      (child.c : Int) - child.b =
        (2^a : Int) *
          ((2*a*(parent.C*3^h) +
              2^(h+1)*(parent.C-parent.b+parent.c) : Nat) : Int)
        - (2^a : Int) * (3*(parent.C*3^h) : Nat)) :
    affineNodeValue t child x := by
  have hxI : (x : Int) = (2^a : Int) * (v : Int) := by
    exact_mod_cast hx
  have hgenI :
      (parent.C*3^h : Int) * ((2^(a+1)+1 : Nat) : Int) * (v : Int)
        + 2*(a : Int)*(parent.C*3^h : Int)
        + (2^(h+1)*(parent.C-parent.b+parent.c) : Nat)
        = (2^(1458*t+parent.s+h+1) : Int) + 3*(parent.C*3^h : Int) := by
    exact_mod_cast hgen
  have hpowNat :
      2^a * 2^(1458*t+parent.s+h+1)
        = 2^(1458*t+parent.s+a+h+1) := by
    rw [← Nat.pow_add]
    congr 1 <;> omega
  have hpow :
      (2^a : Int) * (2^(1458*t+parent.s+h+1) : Int)
        = (2^(1458*t+parent.s+a+h+1) : Int) := by
    exact_mod_cast hpowNat
  have hchildInt :
      (child.C : Int)*(x : Int) + (child.c : Int) - child.b
        = (2^(1458*t+parent.s+a+h+1) : Int) := by
    rw [hchildC, hchildOffset, hxI]
    calc
      _ = (2^a : Int) *
          ((parent.C*3^h : Int) * ((2^(a+1)+1 : Nat) : Int) * (v : Int)
            + 2*(a : Int)*(parent.C*3^h : Int)
            + (2^(h+1)*(parent.C-parent.b+parent.c) : Nat)
            - 3*(parent.C*3^h : Int)) := by
              ring
      _ = (2^a : Int) * (2^(1458*t+parent.s+h+1) : Int) := by
            linear_combination (2^a : Int) * hgenI
      _ = (2^(1458*t+parent.s+a+h+1) : Int) := hpow
  have hchildInt' :
      (child.C : Int)*(x : Int) + (child.c : Int) - child.b
        = (2^(1458*t+child.s) : Int) := by
    simpa [hchildS, Nat.add_assoc] using hchildInt
  have hchildNat :
      child.C*x+child.c = 2^(1458*t+child.s)+child.b := by
    exact_mod_cast hchildInt'
  simpa [affineNodeValue] using hchildNat

structure FrozenTreeTable where
  rs : List Nat
  period : Nat
  nodeCount : Nat
  nodeAt : Nat → AffineNode
  lowRows : List (LowRowCert rs period nodeAt)
  nonrootEdgeKeys : List (Nat × Nat × Nat)
  cutoff : Nat → Nat → Nat
  highCerts : List (HighCert nodeAt)
  valCerts : List (ValCert rs period nodeAt)
  edges : List (Nat × Nat × Nat × Nat)
  rootNodeEq : nodeAt 0 = blankRootNode
  nodeCountPos : 0 < nodeCount
  residuePos : ∀ r, r ∈ rs → 1 ≤ r
  residueMod3 : ∀ r, r ∈ rs → r % 3 ≠ 0
  periodMod3 : period % 3 = 0
  lowComplete :
    ∀ n h a, 1 ≤ n → n < nodeCount → h ≤ (nodeAt n).r →
      1 ≤ a → a < cutoff n h →
      (n,h,a) ∈ lowRows.map lowRowKey ∨ (n,h,a) ∈ nonrootEdgeKeys
  highCutoffComplete :
    ∀ n h, 1 ≤ n → n < nodeCount → h ≤ (nodeAt n).r →
      ∃ cert, cert ∈ highCerts ∧ cert.node = n ∧ cert.h = h ∧
        cert.A = cutoff n h
  valComplete :
    ∀ n, 1 ≤ n → n < nodeCount → n ∈ valCerts.map valCertKey
  edgeKeySound :
    ∀ n h a, (n,h,a) ∈ nonrootEdgeKeys →
      ∃ child, child < nodeCount ∧ (n,child,h,a) ∈ edges
  edgeShape :
    ∀ n child h a, (n,child,h,a) ∈ edges →
      child < nodeCount ∧
      (nodeAt child).s = (nodeAt n).s+a+h+1 ∧
      (nodeAt child).C = (nodeAt n).C*3^h*(2^(a+1)+1) ∧
      ((nodeAt child).c : Int) - (nodeAt child).b =
        (2^a : Int) *
          ((2*a*((nodeAt n).C*3^h) +
              2^(h+1)*((nodeAt n).C-(nodeAt n).b+(nodeAt n).c) : Nat) : Int)
        - (2^a : Int) * (3*((nodeAt n).C*3^h) : Nat)
  nodeProps :
    ∀ n, n < nodeCount →
      (nodeAt n).b ≤ (nodeAt n).C ∧
      ((nodeAt n).b = 0 ∨ (nodeAt n).c = 0)
  specialBounds :
    ∀ n, n < nodeCount → ∀ h, h ≤ (nodeAt n).r →
      0 < (nodeAt n).C*3^h ∧
      (nodeAt n).C*3^h ≤ 4000000 ∧
      2^h*((nodeAt n).C-(nodeAt n).b+(nodeAt n).c) ≤ 4000000
  nodeTenBound :
    ∀ n, n < nodeCount →
      (nodeAt n).C*10+(nodeAt n).c < 2^55
  rootGate :
    ∀ r k h a v, r ∈ rs → h ≤ 7 → 1 ≤ a →
      (h = 0 → a = 1) → (0 < h → a ≤ 2*h+2) →
      3^h*(2^(a+1)+1)*v + 2*a*3^h + 2^(h+1)
        = 2^(1458*(r+period*k)+h+1) + 3*3^h →
      ∃ child, child < nodeCount ∧ (0,child,h,a) ∈ edges

theorem treeParentClosed (F : FrozenTreeTable) (r k : Nat)
    (hr : r ∈ F.rs) :
    ∀ {x y}, indexedAffineBasin (r+F.period*k) F.nodeAt F.nodeCount y →
      EvenEdge x y →
      indexedAffineBasin (r+F.period*k) F.nodeAt F.nodeCount x := by
  let t := r+F.period*k
  have ht : t = r+F.period*k := rfl
  have htpos : 1 ≤ t := by
    have := F.residuePos r hr
    omega
  have ht3 : t % 3 ≠ 0 := by
    have hTk : (F.period*k) % 3 = 0 := by
      rw [Nat.mul_mod, F.periodMod3]
      simp
    rw [ht, Nat.add_mod, hTk]
    exact F.residueMod3 r hr
  intro x y hedge hyBasin
  rcases hyBasin with ⟨n, hn, hval⟩
  have hnodeProps := F.nodeProps n hn
  have hpower :
      (F.nodeAt n).C*y+(F.nodeAt n).c
        = 2^(1458*t+(F.nodeAt n).s)+(F.nodeAt n).b := by
    simpa [affineNodeValue] using hval
  have hHidden :
      ∀ {h u}, y = 1+3^h*u → u%2=1 → h ≤ (F.nodeAt n).r := by
    intro h u hydef huodd
    by_cases hn0 : n = 0
    · subst n
      have hvalRoot : affineNodeValue t blankRootNode y := by
        simpa [F.rootNodeEq] using hval
      have hyEq : y = 2^(1458*t) := by
        simpa [affineNodeValue, blankRootNode] using hvalRoot
      have hyPower : 2^(1458*t) = 1+3^h*u := hyEq.symm.trans hydef
      have hh : h ≤ 7 := target_hidden_le7 t h u ht3 hyPower
      simpa [F.rootNodeEq, blankRootNode] using hh
    · have hnpos : 1 ≤ n := by omega
      obtain ⟨cert, hcertMem, hcertNode⟩ :=
        valCert_mem_of_key (F.valComplete n hnpos hn)
      have hval' : affineNodeValue t (F.nodeAt cert.node) y := by
        simpa [hcertNode] using hval
      exact affine_node_hidden_bound_from_cert cert t r k h y u ht hr hval' hydef huodd
  rcases affine_edge_inverse_cases hedge hnodeProps.1 hnodeProps.2 hpower with
    hgen | hspecial
  · rcases hgen with ⟨a,h,v,u,ha,hv,hvodd,huodd,hxdef,hydef,hEq⟩
    have hh : h ≤ (F.nodeAt n).r := hHidden hydef huodd
    by_cases hn0 : n = 0
    · subst n
      have hEqRoot :
          3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)
            = 2^(1458*t+h+1)+3*3^h := by
        simpa [F.rootNodeEq, blankRootNode] using hEq
      have hnotHigh :
          ¬ (if h=0 then 2 else 2*h+3) ≤ a := by
        intro hbig
        exact no_high_source h a t v hh hbig hEqRoot
      have hzero : h=0 → a=1 := by
        intro h0
        have h2 : 2 ≤ a := by omega
        have hbad : (if h=0 then 2 else 2*h+3) ≤ a := by
          simp [h0]
          exact h2
        exact False.elim (hnotHigh hbad)
      have hpos : 0<h → a≤2*h+2 := by
        intro hp
        have hbig : 2*h+3 ≤ a := by omega
        have hbad : (if h=0 then 2 else 2*h+3) ≤ a := by
          simp [Nat.ne_of_gt hp]
          exact hbig
        exact False.elim (hnotHigh hbad)
      obtain ⟨child,hchild,hEdge⟩ :=
        F.rootGate r k h a v hr hh ha hzero hpos hEqRoot
      obtain ⟨hchildBound,hchildS,hchildC,hchildOffset⟩ :=
        F.edgeShape 0 child h a hEdge
      have hchildVal :=
        genericChildValue t (F.nodeAt 0) (F.nodeAt child)
          a h v x hxdef hEq hchildS hchildC hchildOffset
      exact ⟨child,hchildBound,hchildVal⟩
    · have hnpos : 1 ≤ n := by omega
      obtain ⟨cert,hcertMem,hcertNode,hcertH,hcertA⟩ :=
        F.highCutoffComplete n h hnpos hn hh
      by_cases hhigh : cert.A ≤ a
      · have hgenCert :
          cert.D*(2^(a+1)+1)*v+2*a*cert.D+cert.E
            = 2^(1458*t+(F.nodeAt n).s+h+1)+3*cert.D := by
          rcases cert.matches with ⟨hD,hE⟩
          rw [hD,hE]
          simpa [hcertNode,hcertH] using hEq
        exact False.elim
          (no_generic_high_affine cert.D cert.E cert.A a
            (1458*t+(F.nodeAt n).s+h+1) v
            cert.cutoff_lower cert.base_gap hhigh hgenCert)
      · have haLow : a < F.cutoff n h := by omega
        rcases F.lowComplete n h a hnpos hn hh ha haLow with hrowKey | hEdgeKey
        · obtain ⟨row,hrowMem,hrowNode,hrowH,hrowA⟩ :=
            lowRow_mem_of_key hrowKey
          have hEqRow :
              (F.nodeAt row.node).C*3^row.h*(2^(row.a+1)+1)*v
                +2*row.a*((F.nodeAt row.node).C*3^row.h)
                +2^(row.h+1)*((F.nodeAt row.node).C-(F.nodeAt row.node).b+(F.nodeAt row.node).c)
                =2^(1458*t+(F.nodeAt row.node).s+row.h+1)
                  +3*((F.nodeAt row.node).C*3^row.h) := by
            simpa [hrowNode,hrowH,hrowA] using hEq
          exact False.elim (lowRow_no_generic row r k t v hr ht hEqRow)
        · obtain ⟨child,hchildBound,hEdge⟩ :=
            F.edgeKeySound n h a hEdgeKey
          obtain ⟨hchildBound',hchildS,hchildC,hchildOffset⟩ :=
            F.edgeShape n child h a hEdge
          have hchildVal :=
            genericChildValue t (F.nodeAt n) (F.nodeAt child)
              a h v x hxdef hEq hchildS hchildC hchildOffset
          exact ⟨child,hchildBound',hchildVal⟩
  · rcases hspecial with ⟨a,h,u,ha,huodd,hxdef,hydef,hspecial⟩
    have hh : h ≤ (F.nodeAt n).r := hHidden hydef huodd
    obtain ⟨hDpos,hD,hS⟩ := F.specialBounds n hn hh
    have hN : 55 ≤ 1458*t+(F.nodeAt n).s+h := by omega
    exact False.elim
      (no_special_affine
        ((F.nodeAt n).C*3^h)
        (2^h*((F.nodeAt n).C-(F.nodeAt n).b+(F.nodeAt n).c))
        a (1458*t+(F.nodeAt n).s+h)
        hDpos hD hS hN hspecial)

theorem indexedBasin_not10 (F : FrozenTreeTable) (t : Nat)
    (ht : 1 ≤ t) :
    ¬ indexedAffineBasin t F.nodeAt F.nodeCount 10 := by
  rintro ⟨n,hn,hval⟩
  have hN : 55 ≤ 1458*t+(F.nodeAt n).s := by omega
  have hpow : 2^55 ≤ 2^(1458*t+(F.nodeAt n).s) :=
    Nat.pow_le_pow_right (by decide) hN
  have hsmall := F.nodeTenBound n hn
  unfold affineNodeValue at hval
  omega

theorem no_evenReach_of_indexedBasin
    (t N : Nat) (nodeAt : Nat → AffineNode)
    (hclosed :
      ∀ {x y}, indexedAffineBasin t nodeAt N y → EvenEdge x y →
        indexedAffineBasin t nodeAt N x)
    (hnot10 : ¬ indexedAffineBasin t nodeAt N 10)
    (hroot : indexedAffineBasin t nodeAt N (2^(1458*t))) :
    ¬ EvenReach 10 (2^(1458*t)) := by
  intro hreach
  have hten : indexedAffineBasin t nodeAt N 10 := by
    induction hreach with
    | refl x => exact hroot
    | @cons x y z edge tail ih => exact hclosed (ih hroot) edge
  exact hnot10 hten

theorem treeNoEvenReach (F : FrozenTreeTable) (r k : Nat)
    (hr : r ∈ F.rs) :
    ¬ EvenReach 10 (2^(1458*(r+F.period*k))) := by
  let t := r+F.period*k
  have ht : 1 ≤ t := by
    have := F.residuePos r hr
    omega
  have hclosed := treeParentClosed F r k hr
  have hnot10 := indexedBasin_not10 F t ht
  have hroot : indexedAffineBasin t F.nodeAt F.nodeCount (2^(1458*t)) := by
    refine ⟨0,F.nodeCountPos,?_⟩
    simpa [affineNodeValue,F.rootNodeEq,blankRootNode]
  have hno := no_evenReach_of_indexedBasin t F.nodeCount F.nodeAt hclosed hnot10 hroot
  simpa [t] using hno

end SheepPower1458
