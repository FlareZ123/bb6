import SheepPower1458LowRows

/-!
# Frozen low-row, valuation, and high-cutoff interface for the 1458 affine families

This module packages existing theorem constants and finite node/edge keys.
It adds no residue classes or arithmetic certificates. The five-family
source-parent classifier and its original-blank-root conclusion remain a
separate, unaccepted obligation. This module has not yet passed the required
local Lean 4.36.0-rc2 preflight.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace SheepPower1458

def defaultAffineNode : AffineNode :=
  { s := 0, b := 0, c := 0, C := 1, r := 0, v3C := 0 }

def lowTarget (node : AffineNode) (h a : Nat) : Nat :=
  let D := node.C * 3^h
  let E := 2^(h+1) * (node.C-node.b+node.c)
  if 3*D ≤ 2*a*D+E then 2*a*D+E-3*D else 0

def lowShift (node : AffineNode) (h a : Nat) : Nat :=
  let D := node.C * 3^h
  let E := 2^(h+1) * (node.C-node.b+node.c)
  if 3*D ≤ 2*a*D+E then 0 else 3*D-(2*a*D+E)

/-- A single existing low-a non-hit/period pair, with its exact source row. -/
structure LowRowCert (rs : List Nat) (T : Nat)
    (nodeAt : Nat → AffineNode) where
  node : Nat
  h : Nat
  a : Nat
  modulus : Nat
  base : Nat
  shift : Nat
  target : Nat
  modulus_gt_one : 1 < modulus
  «matches» :
    modulus = (nodeAt node).C * 3^h * (2^(a+1)+1) ∧
    base = (nodeAt node).s + h + 1 ∧
    shift = lowShift (nodeAt node) h a ∧
    target = lowTarget (nodeAt node) h a
  nohit : ∀ r ∈ rs,
    (Nat.powMod 2 (1458*r+base) modulus + shift) % modulus ≠ target % modulus
  period : Nat.powMod 2 (1458*T) modulus = 1

def lowRowKey {rs T nodeAt} (row : LowRowCert rs T nodeAt) :
    Nat × Nat × Nat := (row.node,row.h,row.a)

theorem lowRow_mem_of_key {rs T nodeAt}
    {rows : List (LowRowCert rs T nodeAt)} {n h a : Nat}
    (hm : (n,h,a) ∈ rows.map lowRowKey) :
    ∃ row, row ∈ rows ∧ row.node=n ∧ row.h=h ∧ row.a=a := by
  rcases List.mem_map.mp hm with ⟨row,hrow,hkey⟩
  cases hkey
  exact ⟨row,hrow,rfl,rfl,rfl⟩

/-- A progression-specific low-row modular certificate excludes its whole
arithmetic progression, not merely its stored base residue. -/
theorem lowRow_no_generic_progression {rs T nodeAt}
    (row : LowRowCert rs T nodeAt) (r k t v : Nat)
    (hr : r ∈ rs) (ht : t = r + T*k)
    (heq : row.modulus*v + row.target =
      2^(row.base+1458*t) + row.shift) : False := by
  have hp : 2^(1458*T) % row.modulus = 1 := by
    simpa only [Nat.powMod_def] using row.period
  have hc :
      (2^(1458*r+row.base)+row.shift) % row.modulus ≠
        row.target % row.modulus := by
    simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using row.nohit r hr
  have hexp : row.base+1458*t =
      (1458*r+row.base)+(1458*T)*k := by
    rw [ht, Nat.mul_add, Nat.mul_assoc]
    omega
  have heq' := heq
  rw [hexp] at heq'
  exact no_generic_fixed_period row.modulus (1458*r+row.base)
    row.shift row.target (1458*T) k v row.modulus_gt_one hp hc heq'

/-- Consume the signed generic-source equation using the exact row data.
The target/shift split is intentional: two rows have a negative signed offset. -/
theorem lowRow_no_generic {rs T nodeAt}
    (row : LowRowCert rs T nodeAt) (r k t v : Nat)
    (hr : r ∈ rs) (ht : t = r + T*k)
    (hgen :
      ((nodeAt row.node).C*3^row.h)*(2^(row.a+1)+1)*v +
        2*row.a*((nodeAt row.node).C*3^row.h) +
        2^(row.h+1)*((nodeAt row.node).C-(nodeAt row.node).b+(nodeAt row.node).c) =
      2^(1458*t+(nodeAt row.node).s+row.h+1) +
        3*((nodeAt row.node).C*3^row.h)) : False := by
  rcases row.matches with ⟨hm,hbase,hshift,htarget⟩
  let D := (nodeAt row.node).C * 3^row.h
  let E := 2^(row.h+1) *
    ((nodeAt row.node).C-(nodeAt row.node).b+(nodeAt row.node).c)
  have hexp : 1458*t+(nodeAt row.node).s+row.h+1 =
      (nodeAt row.node).s+row.h+1+1458*t := by omega
  have hgen' := hgen
  rw [hexp] at hgen'
  have hsource :
      row.modulus*v + (2*row.a*D+E) =
        2^(row.base+1458*t)+3*D := by
    rw [hm,hbase]
    simpa [D,E, Nat.add_assoc] using hgen'
  by_cases hsign : 3*D ≤ 2*row.a*D+E
  · have htgt : row.target = 2*row.a*D+E-3*D := by
      simpa [lowTarget,D,E,hsign] using htarget
    have hsh : row.shift=0 := by
      simpa [lowShift,D,E,hsign] using hshift
    have heq : row.modulus*v+row.target =
        2^(row.base+1458*t)+row.shift := by
      rw [htgt,hsh]
      omega
    exact lowRow_no_generic_progression row r k t v hr ht heq
  · have htgt : row.target=0 := by
      simpa [lowTarget,D,E,hsign] using htarget
    have hsh : row.shift=3*D-(2*row.a*D+E) := by
      simpa [lowShift,D,E,hsign] using hshift
    have heq : row.modulus*v+row.target =
        2^(row.base+1458*t)+row.shift := by
      rw [htgt,hsh]
      omega
    exact lowRow_no_generic_progression row r k t v hr ht heq

/-- Valuation certificate for one non-root affine node. -/
structure ValCert (rs : List Nat) (T : Nat)
    (nodeAt : Nat → AffineNode) where
  node : Nat
  modulus : Nat
  base : Nat
  target : Nat
  «matches» :
    modulus = 3^((nodeAt node).r+(nodeAt node).v3C+1) ∧
    base = (nodeAt node).s ∧
    target = (nodeAt node).C-(nodeAt node).b+(nodeAt node).c
  offset_bound : (nodeAt node).b ≤ (nodeAt node).C
  coefficient_valuation : 3^(nodeAt node).v3C ∣ (nodeAt node).C
  nohit : ∀ r ∈ rs,
    Nat.powMod 2 (1458*r+base) modulus ≠ target % modulus
  period : Nat.powMod 2 (1458*T) modulus = 1

def valCertKey {rs T nodeAt} (cert : ValCert rs T nodeAt) : Nat := cert.node

theorem valCert_mem_of_key {rs T nodeAt}
    {certs : List (ValCert rs T nodeAt)} {n : Nat}
    (hm : n ∈ certs.map valCertKey) :
    ∃ cert, cert ∈ certs ∧ cert.node=n := by
  rcases List.mem_map.mp hm with ⟨cert,hcert,hkey⟩
  cases hkey
  exact ⟨cert,hcert,rfl⟩

/-- Turn a stored valuation pair into the hidden-length bound used by the
original EvenReach node classifier. -/
theorem affine_node_hidden_bound_from_cert {rs T nodeAt}
    (cert : ValCert rs T nodeAt) (t r k h y u : Nat)
    (ht : t = r+T*k) (hr : r ∈ rs)
    (hval : affineNodeValue t (nodeAt cert.node) y)
    (hydef : y=1+3^h*u) (huodd : u%2=1) :
    h ≤ (nodeAt cert.node).r := by
  rcases cert.matches with ⟨hm,hbase,htarget⟩
  have hbase' :
      2^(1458*r+(nodeAt cert.node).s) %
        3^((nodeAt cert.node).r+(nodeAt cert.node).v3C+1) ≠
      ((nodeAt cert.node).C-(nodeAt cert.node).b+(nodeAt cert.node).c) %
        3^((nodeAt cert.node).r+(nodeAt cert.node).v3C+1) := by
    simpa only [Nat.powMod_def, hm, hbase, htarget] using cert.nohit r hr
  have hperiod' :
      2^(1458*T) %
        3^((nodeAt cert.node).r+(nodeAt cert.node).v3C+1) = 1 := by
    simpa only [Nat.powMod_def, hm] using cert.period
  exact affine_node_hidden_bound t r T k h y u (nodeAt cert.node) ht
    cert.offset_bound hval hydef huodd cert.coefficient_valuation hbase' hperiod'

/-- Exact signed-power cutoff data for one non-root node and hidden length. -/
structure HighCert (nodeAt : Nat → AffineNode) where
  node : Nat
  h : Nat
  A : Nat
  D : Nat
  E : Nat
  cutoff_lower : 2 ≤ A
  «matches» :
    D = (nodeAt node).C*3^h ∧
    E = 2^(h+1)*((nodeAt node).C-(nodeAt node).b+(nodeAt node).c)
  base_gap :
    1 < SheepGenericHigh.Q D E A ∧
    SheepGenericHigh.Q D E A % 2 = 1 ∧
    SheepGenericHigh.Q D E A < 2^A ∧
    2*D ≤ 2^A

def highCertKey {nodeAt} (cert : HighCert nodeAt) : Nat × Nat :=
  (cert.node,cert.h)

theorem highCert_mem_of_key {nodeAt}
    {certs : List (HighCert nodeAt)} {n h : Nat}
    (hm : (n,h) ∈ certs.map highCertKey) :
    ∃ cert, cert ∈ certs ∧ cert.node=n ∧ cert.h=h := by
  rcases List.mem_map.mp hm with ⟨cert,hcert,hkey⟩
  cases hkey
  exact ⟨cert,hcert,rfl,rfl⟩

def highCertTripleKey {nodeAt} (cert : HighCert nodeAt) : Nat × Nat × Nat :=
  (cert.node,cert.h,cert.A)

theorem highCertTriple_mem_of_key {nodeAt}
    {certs : List (HighCert nodeAt)} {n h A : Nat}
    (hm : (n,h,A) ∈ certs.map highCertTripleKey) :
    ∃ cert, cert ∈ certs ∧ cert.node=n ∧ cert.h=h ∧ cert.A=A := by
  rcases List.mem_map.mp hm with ⟨cert,hcert,hkey⟩
  cases hkey
  exact ⟨cert,hcert,rfl,rfl,rfl⟩


def nodeAt_t1 (n : Nat) : AffineNode :=
  match n with
  | 0 => { s := 0, b := 0, c := 0, C := 1, r := 7, v3C := 0 }
  | 1 => { s := 3, b := 0, c := 2, C := 15, r := 1, v3C := 1 }
  | 2 => { s := 5, b := 22, c := 0, C := 135, r := 1, v3C := 3 }
  | 3 => { s := 7, b := 358, c := 0, C := 1215, r := 1, v3C := 5 }
  | 4 => { s := 9, b := 3862, c := 0, C := 10935, r := 0, v3C := 7 }
  | 5 => { s := 10, b := 0, c := 9772, C := 19683, r := 0, v3C := 9 }
  | 6 => { s := 7, b := 0, c := 452, C := 405, r := 2, v3C := 4 }
  | 7 => { s := 7, b := 0, c := 182, C := 675, r := 3, v3C := 3 }
  | 8 => { s := 9, b := 0, c := 3428, C := 3645, r := 1, v3C := 6 }
  | 9 => { s := 11, b := 0, c := 42872, C := 20655, r := 0, v3C := 5 }
  | 10 => { s := 12, b := 0, c := 78454, C := 98415, r := 0, v3C := 9 }
  | 11 => { s := 13, b := 0, c := 156908, C := 98415, r := 0, v3C := 9 }
  | 12 => { s := 13, b := 0, c := 212798, C := 103275, r := 0, v3C := 5 }
  | 13 => { s := 14, b := 0, c := 510646, C := 492075, r := 0, v3C := 9 }
  | 14 => { s := 16, b := 0, c := 2436244, C := 885735, r := 0, v3C := 11 }
  | _ => defaultAffineNode


def nodeAt_h1a3 (n : Nat) : AffineNode :=
  match n with
  | 0 => { s := 0, b := 0, c := 0, C := 1, r := 7, v3C := 0 }
  | 1 => { s := 5, b := 0, c := 104, C := 51, r := 0, v3C := 1 }
  | 2 => { s := 7, b := 0, c := 518, C := 255, r := 0, v3C := 1 }
  | 3 => { s := 8, b := 0, c := 1444, C := 459, r := 0, v3C := 3 }
  | 4 => { s := 10, b := 0, c := 6694, C := 2295, r := 0, v3C := 3 }
  | 5 => { s := 13, b := 0, c := 81092, C := 20655, r := 0, v3C := 5 }
  | 6 => { s := 16, b := 0, c := 896596, C := 185895, r := 0, v3C := 7 }
  | _ => defaultAffineNode


def nodeAt_h3a6 (n : Nat) : AffineNode :=
  match n with
  | 0 => { s := 0, b := 0, c := 0, C := 1, r := 7, v3C := 0 }
  | 1 => { s := 10, b := 0, c := 16576, C := 3483, r := 0, v3C := 4 }
  | 2 => { s := 13, b := 0, c := 174404, C := 31347, r := 0, v3C := 6 }
  | _ => defaultAffineNode


def nodeAt_h7a2 (n : Nat) : AffineNode :=
  match n with
  | 0 => { s := 0, b := 0, c := 0, C := 1, r := 7, v3C := 0 }
  | 1 => { s := 10, b := 0, c := 9772, C := 19683, r := 0, v3C := 9 }
  | _ => defaultAffineNode


def nodeAt_h7a4 (n : Nat) : AffineNode :=
  match n with
  | 0 => { s := 0, b := 0, c := 0, C := 1, r := 7, v3C := 0 }
  | 1 => { s := 12, b := 0, c := 179056, C := 72171, r := 0, v3C := 8 }
  | _ => defaultAffineNode


def lowRows_t1 : List (LowRowCert residues_t1 period_t1 nodeAt_t1) :=
[
  { node := 1, h := 0, a := 1, modulus := 75, base := 4, shift := 0, target := 19,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n1_h0_a1,
    period := low_period_t1_n1_h0_a1 },
  { node := 1, h := 0, a := 2, modulus := 135, base := 4, shift := 0, target := 49,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n1_h0_a2,
    period := low_period_t1_n1_h0_a2 },
  { node := 1, h := 0, a := 3, modulus := 255, base := 4, shift := 0, target := 79,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n1_h0_a3,
    period := low_period_t1_n1_h0_a3 },
  { node := 1, h := 0, a := 4, modulus := 495, base := 4, shift := 0, target := 109,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n1_h0_a4,
    period := low_period_t1_n1_h0_a4 },
  { node := 1, h := 0, a := 5, modulus := 975, base := 4, shift := 0, target := 139,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n1_h0_a5,
    period := low_period_t1_n1_h0_a5 },
  { node := 1, h := 0, a := 6, modulus := 1935, base := 4, shift := 0, target := 169,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n1_h0_a6,
    period := low_period_t1_n1_h0_a6 },
  { node := 1, h := 0, a := 7, modulus := 3855, base := 4, shift := 0, target := 199,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n1_h0_a7,
    period := low_period_t1_n1_h0_a7 },
  { node := 1, h := 1, a := 1, modulus := 225, base := 5, shift := 0, target := 23,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n1_h1_a1,
    period := low_period_t1_n1_h1_a1 },
  { node := 1, h := 1, a := 3, modulus := 765, base := 5, shift := 0, target := 203,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n1_h1_a3,
    period := low_period_t1_n1_h1_a3 },
  { node := 1, h := 1, a := 4, modulus := 1485, base := 5, shift := 0, target := 293,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n1_h1_a4,
    period := low_period_t1_n1_h1_a4 },
  { node := 1, h := 1, a := 5, modulus := 2925, base := 5, shift := 0, target := 383,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n1_h1_a5,
    period := low_period_t1_n1_h1_a5 },
  { node := 1, h := 1, a := 6, modulus := 5805, base := 5, shift := 0, target := 473,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n1_h1_a6,
    period := low_period_t1_n1_h1_a6 },
  { node := 1, h := 1, a := 7, modulus := 11565, base := 5, shift := 0, target := 563,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n1_h1_a7,
    period := low_period_t1_n1_h1_a7 },
  { node := 1, h := 1, a := 8, modulus := 23085, base := 5, shift := 0, target := 653,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n1_h1_a8,
    period := low_period_t1_n1_h1_a8 },
  { node := 1, h := 1, a := 9, modulus := 46125, base := 5, shift := 0, target := 743,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n1_h1_a9,
    period := low_period_t1_n1_h1_a9 },
  { node := 2, h := 0, a := 2, modulus := 1215, base := 6, shift := 0, target := 361,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n2_h0_a2,
    period := low_period_t1_n2_h0_a2 },
  { node := 2, h := 0, a := 3, modulus := 2295, base := 6, shift := 0, target := 631,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n2_h0_a3,
    period := low_period_t1_n2_h0_a3 },
  { node := 2, h := 0, a := 4, modulus := 4455, base := 6, shift := 0, target := 901,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n2_h0_a4,
    period := low_period_t1_n2_h0_a4 },
  { node := 2, h := 0, a := 5, modulus := 8775, base := 6, shift := 0, target := 1171,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n2_h0_a5,
    period := low_period_t1_n2_h0_a5 },
  { node := 2, h := 0, a := 6, modulus := 17415, base := 6, shift := 0, target := 1441,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n2_h0_a6,
    period := low_period_t1_n2_h0_a6 },
  { node := 2, h := 0, a := 7, modulus := 34695, base := 6, shift := 0, target := 1711,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n2_h0_a7,
    period := low_period_t1_n2_h0_a7 },
  { node := 2, h := 0, a := 8, modulus := 69255, base := 6, shift := 0, target := 1981,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n2_h0_a8,
    period := low_period_t1_n2_h0_a8 },
  { node := 2, h := 0, a := 9, modulus := 138375, base := 6, shift := 0, target := 2251,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n2_h0_a9,
    period := low_period_t1_n2_h0_a9 },
  { node := 2, h := 0, a := 10, modulus := 276615, base := 6, shift := 0, target := 2521,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n2_h0_a10,
    period := low_period_t1_n2_h0_a10 },
  { node := 2, h := 0, a := 11, modulus := 553095, base := 6, shift := 0, target := 2791,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n2_h0_a11,
    period := low_period_t1_n2_h0_a11 },
  { node := 2, h := 1, a := 1, modulus := 2025, base := 7, shift := 0, target := 47,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n2_h1_a1,
    period := low_period_t1_n2_h1_a1 },
  { node := 2, h := 1, a := 3, modulus := 6885, base := 7, shift := 0, target := 1667,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n2_h1_a3,
    period := low_period_t1_n2_h1_a3 },
  { node := 2, h := 1, a := 4, modulus := 13365, base := 7, shift := 0, target := 2477,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n2_h1_a4,
    period := low_period_t1_n2_h1_a4 },
  { node := 2, h := 1, a := 5, modulus := 26325, base := 7, shift := 0, target := 3287,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n2_h1_a5,
    period := low_period_t1_n2_h1_a5 },
  { node := 2, h := 1, a := 6, modulus := 52245, base := 7, shift := 0, target := 4097,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n2_h1_a6,
    period := low_period_t1_n2_h1_a6 },
  { node := 2, h := 1, a := 7, modulus := 104085, base := 7, shift := 0, target := 4907,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n2_h1_a7,
    period := low_period_t1_n2_h1_a7 },
  { node := 2, h := 1, a := 8, modulus := 207765, base := 7, shift := 0, target := 5717,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n2_h1_a8,
    period := low_period_t1_n2_h1_a8 },
  { node := 2, h := 1, a := 9, modulus := 415125, base := 7, shift := 0, target := 6527,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n2_h1_a9,
    period := low_period_t1_n2_h1_a9 },
  { node := 2, h := 1, a := 10, modulus := 829845, base := 7, shift := 0, target := 7337,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n2_h1_a10,
    period := low_period_t1_n2_h1_a10 },
  { node := 2, h := 1, a := 11, modulus := 1659285, base := 7, shift := 0, target := 8147,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n2_h1_a11,
    period := low_period_t1_n2_h1_a11 },
  { node := 2, h := 1, a := 12, modulus := 3318165, base := 7, shift := 0, target := 8957,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n2_h1_a12,
    period := low_period_t1_n2_h1_a12 },
  { node := 2, h := 1, a := 13, modulus := 6635925, base := 7, shift := 0, target := 9767,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n2_h1_a13,
    period := low_period_t1_n2_h1_a13 },
  { node := 3, h := 0, a := 1, modulus := 6075, base := 8, shift := 0, target := 499,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n3_h0_a1,
    period := low_period_t1_n3_h0_a1 },
  { node := 3, h := 0, a := 2, modulus := 10935, base := 8, shift := 0, target := 2929,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n3_h0_a2,
    period := low_period_t1_n3_h0_a2 },
  { node := 3, h := 0, a := 4, modulus := 40095, base := 8, shift := 0, target := 7789,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n3_h0_a4,
    period := low_period_t1_n3_h0_a4 },
  { node := 3, h := 0, a := 5, modulus := 78975, base := 8, shift := 0, target := 10219,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n3_h0_a5,
    period := low_period_t1_n3_h0_a5 },
  { node := 3, h := 0, a := 6, modulus := 156735, base := 8, shift := 0, target := 12649,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n3_h0_a6,
    period := low_period_t1_n3_h0_a6 },
  { node := 3, h := 0, a := 7, modulus := 312255, base := 8, shift := 0, target := 15079,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n3_h0_a7,
    period := low_period_t1_n3_h0_a7 },
  { node := 3, h := 0, a := 8, modulus := 623295, base := 8, shift := 0, target := 17509,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n3_h0_a8,
    period := low_period_t1_n3_h0_a8 },
  { node := 3, h := 0, a := 9, modulus := 1245375, base := 8, shift := 0, target := 19939,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n3_h0_a9,
    period := low_period_t1_n3_h0_a9 },
  { node := 3, h := 0, a := 10, modulus := 2489535, base := 8, shift := 0, target := 22369,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n3_h0_a10,
    period := low_period_t1_n3_h0_a10 },
  { node := 3, h := 0, a := 11, modulus := 4977855, base := 8, shift := 0, target := 24799,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n3_h0_a11,
    period := low_period_t1_n3_h0_a11 },
  { node := 3, h := 0, a := 12, modulus := 9954495, base := 8, shift := 0, target := 27229,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n3_h0_a12,
    period := low_period_t1_n3_h0_a12 },
  { node := 3, h := 0, a := 13, modulus := 19907775, base := 8, shift := 0, target := 29659,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n3_h0_a13,
    period := low_period_t1_n3_h0_a13 },
  { node := 3, h := 0, a := 14, modulus := 39814335, base := 8, shift := 0, target := 32089,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n3_h0_a14,
    period := low_period_t1_n3_h0_a14 },
  { node := 3, h := 0, a := 15, modulus := 79627455, base := 8, shift := 0, target := 34519,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n3_h0_a15,
    period := low_period_t1_n3_h0_a15 },
  { node := 3, h := 1, a := 1, modulus := 18225, base := 9, shift := 217, target := 0,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n3_h1_a1,
    period := low_period_t1_n3_h1_a1 },
  { node := 3, h := 1, a := 2, modulus := 32805, base := 9, shift := 0, target := 7073,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n3_h1_a2,
    period := low_period_t1_n3_h1_a2 },
  { node := 3, h := 1, a := 3, modulus := 61965, base := 9, shift := 0, target := 14363,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n3_h1_a3,
    period := low_period_t1_n3_h1_a3 },
  { node := 3, h := 1, a := 4, modulus := 120285, base := 9, shift := 0, target := 21653,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n3_h1_a4,
    period := low_period_t1_n3_h1_a4 },
  { node := 3, h := 1, a := 5, modulus := 236925, base := 9, shift := 0, target := 28943,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n3_h1_a5,
    period := low_period_t1_n3_h1_a5 },
  { node := 3, h := 1, a := 6, modulus := 470205, base := 9, shift := 0, target := 36233,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n3_h1_a6,
    period := low_period_t1_n3_h1_a6 },
  { node := 3, h := 1, a := 7, modulus := 936765, base := 9, shift := 0, target := 43523,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n3_h1_a7,
    period := low_period_t1_n3_h1_a7 },
  { node := 3, h := 1, a := 8, modulus := 1869885, base := 9, shift := 0, target := 50813,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n3_h1_a8,
    period := low_period_t1_n3_h1_a8 },
  { node := 3, h := 1, a := 9, modulus := 3736125, base := 9, shift := 0, target := 58103,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n3_h1_a9,
    period := low_period_t1_n3_h1_a9 },
  { node := 3, h := 1, a := 10, modulus := 7468605, base := 9, shift := 0, target := 65393,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n3_h1_a10,
    period := low_period_t1_n3_h1_a10 },
  { node := 3, h := 1, a := 11, modulus := 14933565, base := 9, shift := 0, target := 72683,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n3_h1_a11,
    period := low_period_t1_n3_h1_a11 },
  { node := 3, h := 1, a := 12, modulus := 29863485, base := 9, shift := 0, target := 79973,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n3_h1_a12,
    period := low_period_t1_n3_h1_a12 },
  { node := 3, h := 1, a := 13, modulus := 59723325, base := 9, shift := 0, target := 87263,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n3_h1_a13,
    period := low_period_t1_n3_h1_a13 },
  { node := 3, h := 1, a := 14, modulus := 119443005, base := 9, shift := 0, target := 94553,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n3_h1_a14,
    period := low_period_t1_n3_h1_a14 },
  { node := 3, h := 1, a := 15, modulus := 238882365, base := 9, shift := 0, target := 101843,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n3_h1_a15,
    period := low_period_t1_n3_h1_a15 },
  { node := 3, h := 1, a := 16, modulus := 477761085, base := 9, shift := 0, target := 109133,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n3_h1_a16,
    period := low_period_t1_n3_h1_a16 },
  { node := 4, h := 0, a := 1, modulus := 54675, base := 10, shift := 0, target := 3211,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n4_h0_a1,
    period := low_period_t1_n4_h0_a1 },
  { node := 4, h := 0, a := 2, modulus := 98415, base := 10, shift := 0, target := 25081,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n4_h0_a2,
    period := low_period_t1_n4_h0_a2 },
  { node := 4, h := 0, a := 3, modulus := 185895, base := 10, shift := 0, target := 46951,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n4_h0_a3,
    period := low_period_t1_n4_h0_a3 },
  { node := 4, h := 0, a := 4, modulus := 360855, base := 10, shift := 0, target := 68821,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n4_h0_a4,
    period := low_period_t1_n4_h0_a4 },
  { node := 4, h := 0, a := 5, modulus := 710775, base := 10, shift := 0, target := 90691,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n4_h0_a5,
    period := low_period_t1_n4_h0_a5 },
  { node := 4, h := 0, a := 6, modulus := 1410615, base := 10, shift := 0, target := 112561,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n4_h0_a6,
    period := low_period_t1_n4_h0_a6 },
  { node := 4, h := 0, a := 7, modulus := 2810295, base := 10, shift := 0, target := 134431,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n4_h0_a7,
    period := low_period_t1_n4_h0_a7 },
  { node := 4, h := 0, a := 8, modulus := 5609655, base := 10, shift := 0, target := 156301,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n4_h0_a8,
    period := low_period_t1_n4_h0_a8 },
  { node := 4, h := 0, a := 9, modulus := 11208375, base := 10, shift := 0, target := 178171,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n4_h0_a9,
    period := low_period_t1_n4_h0_a9 },
  { node := 4, h := 0, a := 10, modulus := 22405815, base := 10, shift := 0, target := 200041,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n4_h0_a10,
    period := low_period_t1_n4_h0_a10 },
  { node := 4, h := 0, a := 11, modulus := 44800695, base := 10, shift := 0, target := 221911,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n4_h0_a11,
    period := low_period_t1_n4_h0_a11 },
  { node := 4, h := 0, a := 12, modulus := 89590455, base := 10, shift := 0, target := 243781,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n4_h0_a12,
    period := low_period_t1_n4_h0_a12 },
  { node := 4, h := 0, a := 13, modulus := 179169975, base := 10, shift := 0, target := 265651,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n4_h0_a13,
    period := low_period_t1_n4_h0_a13 },
  { node := 4, h := 0, a := 14, modulus := 358329015, base := 10, shift := 0, target := 287521,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n4_h0_a14,
    period := low_period_t1_n4_h0_a14 },
  { node := 4, h := 0, a := 15, modulus := 716647095, base := 10, shift := 0, target := 309391,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n4_h0_a15,
    period := low_period_t1_n4_h0_a15 },
  { node := 4, h := 0, a := 16, modulus := 1433283255, base := 10, shift := 0, target := 331261,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n4_h0_a16,
    period := low_period_t1_n4_h0_a16 },
  { node := 4, h := 0, a := 17, modulus := 2866555575, base := 10, shift := 0, target := 353131,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n4_h0_a17,
    period := low_period_t1_n4_h0_a17 },
  { node := 4, h := 0, a := 18, modulus := 5733100215, base := 10, shift := 0, target := 375001,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n4_h0_a18,
    period := low_period_t1_n4_h0_a18 },
  { node := 5, h := 0, a := 2, modulus := 177147, base := 11, shift := 0, target := 78593,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n5_h0_a2,
    period := low_period_t1_n5_h0_a2 },
  { node := 5, h := 0, a := 3, modulus := 334611, base := 11, shift := 0, target := 117959,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n5_h0_a3,
    period := low_period_t1_n5_h0_a3 },
  { node := 5, h := 0, a := 4, modulus := 649539, base := 11, shift := 0, target := 157325,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n5_h0_a4,
    period := low_period_t1_n5_h0_a4 },
  { node := 5, h := 0, a := 5, modulus := 1279395, base := 11, shift := 0, target := 196691,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n5_h0_a5,
    period := low_period_t1_n5_h0_a5 },
  { node := 5, h := 0, a := 6, modulus := 2539107, base := 11, shift := 0, target := 236057,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n5_h0_a6,
    period := low_period_t1_n5_h0_a6 },
  { node := 5, h := 0, a := 7, modulus := 5058531, base := 11, shift := 0, target := 275423,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n5_h0_a7,
    period := low_period_t1_n5_h0_a7 },
  { node := 5, h := 0, a := 8, modulus := 10097379, base := 11, shift := 0, target := 314789,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n5_h0_a8,
    period := low_period_t1_n5_h0_a8 },
  { node := 5, h := 0, a := 9, modulus := 20175075, base := 11, shift := 0, target := 354155,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n5_h0_a9,
    period := low_period_t1_n5_h0_a9 },
  { node := 5, h := 0, a := 10, modulus := 40330467, base := 11, shift := 0, target := 393521,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n5_h0_a10,
    period := low_period_t1_n5_h0_a10 },
  { node := 5, h := 0, a := 11, modulus := 80641251, base := 11, shift := 0, target := 432887,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n5_h0_a11,
    period := low_period_t1_n5_h0_a11 },
  { node := 5, h := 0, a := 12, modulus := 161262819, base := 11, shift := 0, target := 472253,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n5_h0_a12,
    period := low_period_t1_n5_h0_a12 },
  { node := 5, h := 0, a := 13, modulus := 322505955, base := 11, shift := 0, target := 511619,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n5_h0_a13,
    period := low_period_t1_n5_h0_a13 },
  { node := 5, h := 0, a := 14, modulus := 644992227, base := 11, shift := 0, target := 550985,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n5_h0_a14,
    period := low_period_t1_n5_h0_a14 },
  { node := 5, h := 0, a := 15, modulus := 1289964771, base := 11, shift := 0, target := 590351,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n5_h0_a15,
    period := low_period_t1_n5_h0_a15 },
  { node := 5, h := 0, a := 16, modulus := 2579909859, base := 11, shift := 0, target := 629717,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n5_h0_a16,
    period := low_period_t1_n5_h0_a16 },
  { node := 5, h := 0, a := 17, modulus := 5159800035, base := 11, shift := 0, target := 669083,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n5_h0_a17,
    period := low_period_t1_n5_h0_a17 },
  { node := 5, h := 0, a := 18, modulus := 10319580387, base := 11, shift := 0, target := 708449,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n5_h0_a18,
    period := low_period_t1_n5_h0_a18 },
  { node := 5, h := 0, a := 19, modulus := 20639141091, base := 11, shift := 0, target := 747815,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n5_h0_a19,
    period := low_period_t1_n5_h0_a19 },
  { node := 6, h := 0, a := 1, modulus := 2025, base := 8, shift := 0, target := 1309,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h0_a1,
    period := low_period_t1_n6_h0_a1 },
  { node := 6, h := 0, a := 2, modulus := 3645, base := 8, shift := 0, target := 2119,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h0_a2,
    period := low_period_t1_n6_h0_a2 },
  { node := 6, h := 0, a := 3, modulus := 6885, base := 8, shift := 0, target := 2929,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h0_a3,
    period := low_period_t1_n6_h0_a3 },
  { node := 6, h := 0, a := 4, modulus := 13365, base := 8, shift := 0, target := 3739,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h0_a4,
    period := low_period_t1_n6_h0_a4 },
  { node := 6, h := 0, a := 5, modulus := 26325, base := 8, shift := 0, target := 4549,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h0_a5,
    period := low_period_t1_n6_h0_a5 },
  { node := 6, h := 0, a := 6, modulus := 52245, base := 8, shift := 0, target := 5359,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h0_a6,
    period := low_period_t1_n6_h0_a6 },
  { node := 6, h := 0, a := 7, modulus := 104085, base := 8, shift := 0, target := 6169,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h0_a7,
    period := low_period_t1_n6_h0_a7 },
  { node := 6, h := 0, a := 8, modulus := 207765, base := 8, shift := 0, target := 6979,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h0_a8,
    period := low_period_t1_n6_h0_a8 },
  { node := 6, h := 0, a := 9, modulus := 415125, base := 8, shift := 0, target := 7789,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h0_a9,
    period := low_period_t1_n6_h0_a9 },
  { node := 6, h := 0, a := 10, modulus := 829845, base := 8, shift := 0, target := 8599,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h0_a10,
    period := low_period_t1_n6_h0_a10 },
  { node := 6, h := 0, a := 11, modulus := 1659285, base := 8, shift := 0, target := 9409,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h0_a11,
    period := low_period_t1_n6_h0_a11 },
  { node := 6, h := 0, a := 12, modulus := 3318165, base := 8, shift := 0, target := 10219,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h0_a12,
    period := low_period_t1_n6_h0_a12 },
  { node := 6, h := 0, a := 13, modulus := 6635925, base := 8, shift := 0, target := 11029,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h0_a13,
    period := low_period_t1_n6_h0_a13 },
  { node := 6, h := 1, a := 1, modulus := 6075, base := 9, shift := 0, target := 2213,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h1_a1,
    period := low_period_t1_n6_h1_a1 },
  { node := 6, h := 1, a := 2, modulus := 10935, base := 9, shift := 0, target := 4643,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h1_a2,
    period := low_period_t1_n6_h1_a2 },
  { node := 6, h := 1, a := 3, modulus := 20655, base := 9, shift := 0, target := 7073,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h1_a3,
    period := low_period_t1_n6_h1_a3 },
  { node := 6, h := 1, a := 4, modulus := 40095, base := 9, shift := 0, target := 9503,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h1_a4,
    period := low_period_t1_n6_h1_a4 },
  { node := 6, h := 1, a := 5, modulus := 78975, base := 9, shift := 0, target := 11933,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h1_a5,
    period := low_period_t1_n6_h1_a5 },
  { node := 6, h := 1, a := 6, modulus := 156735, base := 9, shift := 0, target := 14363,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h1_a6,
    period := low_period_t1_n6_h1_a6 },
  { node := 6, h := 1, a := 7, modulus := 312255, base := 9, shift := 0, target := 16793,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h1_a7,
    period := low_period_t1_n6_h1_a7 },
  { node := 6, h := 1, a := 8, modulus := 623295, base := 9, shift := 0, target := 19223,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h1_a8,
    period := low_period_t1_n6_h1_a8 },
  { node := 6, h := 1, a := 9, modulus := 1245375, base := 9, shift := 0, target := 21653,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h1_a9,
    period := low_period_t1_n6_h1_a9 },
  { node := 6, h := 1, a := 10, modulus := 2489535, base := 9, shift := 0, target := 24083,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h1_a10,
    period := low_period_t1_n6_h1_a10 },
  { node := 6, h := 1, a := 11, modulus := 4977855, base := 9, shift := 0, target := 26513,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h1_a11,
    period := low_period_t1_n6_h1_a11 },
  { node := 6, h := 1, a := 12, modulus := 9954495, base := 9, shift := 0, target := 28943,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h1_a12,
    period := low_period_t1_n6_h1_a12 },
  { node := 6, h := 1, a := 13, modulus := 19907775, base := 9, shift := 0, target := 31373,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h1_a13,
    period := low_period_t1_n6_h1_a13 },
  { node := 6, h := 1, a := 14, modulus := 39814335, base := 9, shift := 0, target := 33803,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h1_a14,
    period := low_period_t1_n6_h1_a14 },
  { node := 6, h := 1, a := 15, modulus := 79627455, base := 9, shift := 0, target := 36233,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h1_a15,
    period := low_period_t1_n6_h1_a15 },
  { node := 6, h := 2, a := 1, modulus := 18225, base := 10, shift := 0, target := 3211,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h2_a1,
    period := low_period_t1_n6_h2_a1 },
  { node := 6, h := 2, a := 2, modulus := 32805, base := 10, shift := 0, target := 10501,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h2_a2,
    period := low_period_t1_n6_h2_a2 },
  { node := 6, h := 2, a := 3, modulus := 61965, base := 10, shift := 0, target := 17791,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h2_a3,
    period := low_period_t1_n6_h2_a3 },
  { node := 6, h := 2, a := 4, modulus := 120285, base := 10, shift := 0, target := 25081,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h2_a4,
    period := low_period_t1_n6_h2_a4 },
  { node := 6, h := 2, a := 5, modulus := 236925, base := 10, shift := 0, target := 32371,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h2_a5,
    period := low_period_t1_n6_h2_a5 },
  { node := 6, h := 2, a := 6, modulus := 470205, base := 10, shift := 0, target := 39661,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h2_a6,
    period := low_period_t1_n6_h2_a6 },
  { node := 6, h := 2, a := 7, modulus := 936765, base := 10, shift := 0, target := 46951,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h2_a7,
    period := low_period_t1_n6_h2_a7 },
  { node := 6, h := 2, a := 8, modulus := 1869885, base := 10, shift := 0, target := 54241,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h2_a8,
    period := low_period_t1_n6_h2_a8 },
  { node := 6, h := 2, a := 9, modulus := 3736125, base := 10, shift := 0, target := 61531,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h2_a9,
    period := low_period_t1_n6_h2_a9 },
  { node := 6, h := 2, a := 10, modulus := 7468605, base := 10, shift := 0, target := 68821,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h2_a10,
    period := low_period_t1_n6_h2_a10 },
  { node := 6, h := 2, a := 11, modulus := 14933565, base := 10, shift := 0, target := 76111,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h2_a11,
    period := low_period_t1_n6_h2_a11 },
  { node := 6, h := 2, a := 12, modulus := 29863485, base := 10, shift := 0, target := 83401,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h2_a12,
    period := low_period_t1_n6_h2_a12 },
  { node := 6, h := 2, a := 13, modulus := 59723325, base := 10, shift := 0, target := 90691,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h2_a13,
    period := low_period_t1_n6_h2_a13 },
  { node := 6, h := 2, a := 14, modulus := 119443005, base := 10, shift := 0, target := 97981,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h2_a14,
    period := low_period_t1_n6_h2_a14 },
  { node := 6, h := 2, a := 15, modulus := 238882365, base := 10, shift := 0, target := 105271,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h2_a15,
    period := low_period_t1_n6_h2_a15 },
  { node := 6, h := 2, a := 16, modulus := 477761085, base := 10, shift := 0, target := 112561,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n6_h2_a16,
    period := low_period_t1_n6_h2_a16 },
  { node := 7, h := 0, a := 1, modulus := 3375, base := 8, shift := 0, target := 1039,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h0_a1,
    period := low_period_t1_n7_h0_a1 },
  { node := 7, h := 0, a := 2, modulus := 6075, base := 8, shift := 0, target := 2389,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h0_a2,
    period := low_period_t1_n7_h0_a2 },
  { node := 7, h := 0, a := 3, modulus := 11475, base := 8, shift := 0, target := 3739,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h0_a3,
    period := low_period_t1_n7_h0_a3 },
  { node := 7, h := 0, a := 4, modulus := 22275, base := 8, shift := 0, target := 5089,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h0_a4,
    period := low_period_t1_n7_h0_a4 },
  { node := 7, h := 0, a := 5, modulus := 43875, base := 8, shift := 0, target := 6439,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h0_a5,
    period := low_period_t1_n7_h0_a5 },
  { node := 7, h := 0, a := 6, modulus := 87075, base := 8, shift := 0, target := 7789,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h0_a6,
    period := low_period_t1_n7_h0_a6 },
  { node := 7, h := 0, a := 7, modulus := 173475, base := 8, shift := 0, target := 9139,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h0_a7,
    period := low_period_t1_n7_h0_a7 },
  { node := 7, h := 0, a := 8, modulus := 346275, base := 8, shift := 0, target := 10489,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h0_a8,
    period := low_period_t1_n7_h0_a8 },
  { node := 7, h := 0, a := 9, modulus := 691875, base := 8, shift := 0, target := 11839,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h0_a9,
    period := low_period_t1_n7_h0_a9 },
  { node := 7, h := 0, a := 10, modulus := 1383075, base := 8, shift := 0, target := 13189,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h0_a10,
    period := low_period_t1_n7_h0_a10 },
  { node := 7, h := 0, a := 11, modulus := 2765475, base := 8, shift := 0, target := 14539,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h0_a11,
    period := low_period_t1_n7_h0_a11 },
  { node := 7, h := 0, a := 12, modulus := 5530275, base := 8, shift := 0, target := 15889,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h0_a12,
    period := low_period_t1_n7_h0_a12 },
  { node := 7, h := 0, a := 13, modulus := 11059875, base := 8, shift := 0, target := 17239,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h0_a13,
    period := low_period_t1_n7_h0_a13 },
  { node := 7, h := 0, a := 14, modulus := 22119075, base := 8, shift := 0, target := 18589,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h0_a14,
    period := low_period_t1_n7_h0_a14 },
  { node := 7, h := 1, a := 1, modulus := 10125, base := 9, shift := 0, target := 1403,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h1_a1,
    period := low_period_t1_n7_h1_a1 },
  { node := 7, h := 1, a := 2, modulus := 18225, base := 9, shift := 0, target := 5453,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h1_a2,
    period := low_period_t1_n7_h1_a2 },
  { node := 7, h := 1, a := 3, modulus := 34425, base := 9, shift := 0, target := 9503,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h1_a3,
    period := low_period_t1_n7_h1_a3 },
  { node := 7, h := 1, a := 4, modulus := 66825, base := 9, shift := 0, target := 13553,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h1_a4,
    period := low_period_t1_n7_h1_a4 },
  { node := 7, h := 1, a := 5, modulus := 131625, base := 9, shift := 0, target := 17603,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h1_a5,
    period := low_period_t1_n7_h1_a5 },
  { node := 7, h := 1, a := 6, modulus := 261225, base := 9, shift := 0, target := 21653,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h1_a6,
    period := low_period_t1_n7_h1_a6 },
  { node := 7, h := 1, a := 7, modulus := 520425, base := 9, shift := 0, target := 25703,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h1_a7,
    period := low_period_t1_n7_h1_a7 },
  { node := 7, h := 1, a := 8, modulus := 1038825, base := 9, shift := 0, target := 29753,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h1_a8,
    period := low_period_t1_n7_h1_a8 },
  { node := 7, h := 1, a := 9, modulus := 2075625, base := 9, shift := 0, target := 33803,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h1_a9,
    period := low_period_t1_n7_h1_a9 },
  { node := 7, h := 1, a := 10, modulus := 4149225, base := 9, shift := 0, target := 37853,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h1_a10,
    period := low_period_t1_n7_h1_a10 },
  { node := 7, h := 1, a := 11, modulus := 8296425, base := 9, shift := 0, target := 41903,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h1_a11,
    period := low_period_t1_n7_h1_a11 },
  { node := 7, h := 1, a := 12, modulus := 16590825, base := 9, shift := 0, target := 45953,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h1_a12,
    period := low_period_t1_n7_h1_a12 },
  { node := 7, h := 1, a := 13, modulus := 33179625, base := 9, shift := 0, target := 50003,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h1_a13,
    period := low_period_t1_n7_h1_a13 },
  { node := 7, h := 1, a := 14, modulus := 66357225, base := 9, shift := 0, target := 54053,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h1_a14,
    period := low_period_t1_n7_h1_a14 },
  { node := 7, h := 1, a := 15, modulus := 132712425, base := 9, shift := 0, target := 58103,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h1_a15,
    period := low_period_t1_n7_h1_a15 },
  { node := 7, h := 2, a := 1, modulus := 30375, base := 10, shift := 0, target := 781,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h2_a1,
    period := low_period_t1_n7_h2_a1 },
  { node := 7, h := 2, a := 2, modulus := 54675, base := 10, shift := 0, target := 12931,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h2_a2,
    period := low_period_t1_n7_h2_a2 },
  { node := 7, h := 2, a := 3, modulus := 103275, base := 10, shift := 0, target := 25081,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h2_a3,
    period := low_period_t1_n7_h2_a3 },
  { node := 7, h := 2, a := 4, modulus := 200475, base := 10, shift := 0, target := 37231,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h2_a4,
    period := low_period_t1_n7_h2_a4 },
  { node := 7, h := 2, a := 5, modulus := 394875, base := 10, shift := 0, target := 49381,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h2_a5,
    period := low_period_t1_n7_h2_a5 },
  { node := 7, h := 2, a := 6, modulus := 783675, base := 10, shift := 0, target := 61531,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h2_a6,
    period := low_period_t1_n7_h2_a6 },
  { node := 7, h := 2, a := 7, modulus := 1561275, base := 10, shift := 0, target := 73681,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h2_a7,
    period := low_period_t1_n7_h2_a7 },
  { node := 7, h := 2, a := 8, modulus := 3116475, base := 10, shift := 0, target := 85831,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h2_a8,
    period := low_period_t1_n7_h2_a8 },
  { node := 7, h := 2, a := 9, modulus := 6226875, base := 10, shift := 0, target := 97981,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h2_a9,
    period := low_period_t1_n7_h2_a9 },
  { node := 7, h := 2, a := 10, modulus := 12447675, base := 10, shift := 0, target := 110131,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h2_a10,
    period := low_period_t1_n7_h2_a10 },
  { node := 7, h := 2, a := 11, modulus := 24889275, base := 10, shift := 0, target := 122281,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h2_a11,
    period := low_period_t1_n7_h2_a11 },
  { node := 7, h := 2, a := 12, modulus := 49772475, base := 10, shift := 0, target := 134431,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h2_a12,
    period := low_period_t1_n7_h2_a12 },
  { node := 7, h := 2, a := 13, modulus := 99538875, base := 10, shift := 0, target := 146581,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h2_a13,
    period := low_period_t1_n7_h2_a13 },
  { node := 7, h := 2, a := 14, modulus := 199071675, base := 10, shift := 0, target := 158731,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h2_a14,
    period := low_period_t1_n7_h2_a14 },
  { node := 7, h := 2, a := 15, modulus := 398137275, base := 10, shift := 0, target := 170881,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h2_a15,
    period := low_period_t1_n7_h2_a15 },
  { node := 7, h := 2, a := 16, modulus := 796268475, base := 10, shift := 0, target := 183031,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h2_a16,
    period := low_period_t1_n7_h2_a16 },
  { node := 7, h := 2, a := 17, modulus := 1592530875, base := 10, shift := 0, target := 195181,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h2_a17,
    period := low_period_t1_n7_h2_a17 },
  { node := 7, h := 3, a := 1, modulus := 91125, base := 11, shift := 4513, target := 0,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h3_a1,
    period := low_period_t1_n7_h3_a1 },
  { node := 7, h := 3, a := 2, modulus := 164025, base := 11, shift := 0, target := 31937,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h3_a2,
    period := low_period_t1_n7_h3_a2 },
  { node := 7, h := 3, a := 3, modulus := 309825, base := 11, shift := 0, target := 68387,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h3_a3,
    period := low_period_t1_n7_h3_a3 },
  { node := 7, h := 3, a := 4, modulus := 601425, base := 11, shift := 0, target := 104837,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h3_a4,
    period := low_period_t1_n7_h3_a4 },
  { node := 7, h := 3, a := 5, modulus := 1184625, base := 11, shift := 0, target := 141287,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h3_a5,
    period := low_period_t1_n7_h3_a5 },
  { node := 7, h := 3, a := 6, modulus := 2351025, base := 11, shift := 0, target := 177737,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h3_a6,
    period := low_period_t1_n7_h3_a6 },
  { node := 7, h := 3, a := 7, modulus := 4683825, base := 11, shift := 0, target := 214187,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h3_a7,
    period := low_period_t1_n7_h3_a7 },
  { node := 7, h := 3, a := 8, modulus := 9349425, base := 11, shift := 0, target := 250637,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h3_a8,
    period := low_period_t1_n7_h3_a8 },
  { node := 7, h := 3, a := 9, modulus := 18680625, base := 11, shift := 0, target := 287087,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h3_a9,
    period := low_period_t1_n7_h3_a9 },
  { node := 7, h := 3, a := 10, modulus := 37343025, base := 11, shift := 0, target := 323537,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h3_a10,
    period := low_period_t1_n7_h3_a10 },
  { node := 7, h := 3, a := 11, modulus := 74667825, base := 11, shift := 0, target := 359987,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h3_a11,
    period := low_period_t1_n7_h3_a11 },
  { node := 7, h := 3, a := 12, modulus := 149317425, base := 11, shift := 0, target := 396437,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h3_a12,
    period := low_period_t1_n7_h3_a12 },
  { node := 7, h := 3, a := 13, modulus := 298616625, base := 11, shift := 0, target := 432887,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h3_a13,
    period := low_period_t1_n7_h3_a13 },
  { node := 7, h := 3, a := 14, modulus := 597215025, base := 11, shift := 0, target := 469337,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h3_a14,
    period := low_period_t1_n7_h3_a14 },
  { node := 7, h := 3, a := 15, modulus := 1194411825, base := 11, shift := 0, target := 505787,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h3_a15,
    period := low_period_t1_n7_h3_a15 },
  { node := 7, h := 3, a := 16, modulus := 2388805425, base := 11, shift := 0, target := 542237,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h3_a16,
    period := low_period_t1_n7_h3_a16 },
  { node := 7, h := 3, a := 17, modulus := 4777592625, base := 11, shift := 0, target := 578687,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h3_a17,
    period := low_period_t1_n7_h3_a17 },
  { node := 7, h := 3, a := 18, modulus := 9555167025, base := 11, shift := 0, target := 615137,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h3_a18,
    period := low_period_t1_n7_h3_a18 },
  { node := 7, h := 3, a := 19, modulus := 19110315825, base := 11, shift := 0, target := 651587,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n7_h3_a19,
    period := low_period_t1_n7_h3_a19 },
  { node := 8, h := 0, a := 1, modulus := 18225, base := 10, shift := 0, target := 10501,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h0_a1,
    period := low_period_t1_n8_h0_a1 },
  { node := 8, h := 0, a := 2, modulus := 32805, base := 10, shift := 0, target := 17791,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h0_a2,
    period := low_period_t1_n8_h0_a2 },
  { node := 8, h := 0, a := 3, modulus := 61965, base := 10, shift := 0, target := 25081,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h0_a3,
    period := low_period_t1_n8_h0_a3 },
  { node := 8, h := 0, a := 4, modulus := 120285, base := 10, shift := 0, target := 32371,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h0_a4,
    period := low_period_t1_n8_h0_a4 },
  { node := 8, h := 0, a := 5, modulus := 236925, base := 10, shift := 0, target := 39661,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h0_a5,
    period := low_period_t1_n8_h0_a5 },
  { node := 8, h := 0, a := 6, modulus := 470205, base := 10, shift := 0, target := 46951,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h0_a6,
    period := low_period_t1_n8_h0_a6 },
  { node := 8, h := 0, a := 7, modulus := 936765, base := 10, shift := 0, target := 54241,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h0_a7,
    period := low_period_t1_n8_h0_a7 },
  { node := 8, h := 0, a := 8, modulus := 1869885, base := 10, shift := 0, target := 61531,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h0_a8,
    period := low_period_t1_n8_h0_a8 },
  { node := 8, h := 0, a := 9, modulus := 3736125, base := 10, shift := 0, target := 68821,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h0_a9,
    period := low_period_t1_n8_h0_a9 },
  { node := 8, h := 0, a := 10, modulus := 7468605, base := 10, shift := 0, target := 76111,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h0_a10,
    period := low_period_t1_n8_h0_a10 },
  { node := 8, h := 0, a := 11, modulus := 14933565, base := 10, shift := 0, target := 83401,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h0_a11,
    period := low_period_t1_n8_h0_a11 },
  { node := 8, h := 0, a := 12, modulus := 29863485, base := 10, shift := 0, target := 90691,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h0_a12,
    period := low_period_t1_n8_h0_a12 },
  { node := 8, h := 0, a := 13, modulus := 59723325, base := 10, shift := 0, target := 97981,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h0_a13,
    period := low_period_t1_n8_h0_a13 },
  { node := 8, h := 0, a := 14, modulus := 119443005, base := 10, shift := 0, target := 105271,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h0_a14,
    period := low_period_t1_n8_h0_a14 },
  { node := 8, h := 0, a := 15, modulus := 238882365, base := 10, shift := 0, target := 112561,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h0_a15,
    period := low_period_t1_n8_h0_a15 },
  { node := 8, h := 0, a := 16, modulus := 477761085, base := 10, shift := 0, target := 119851,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h0_a16,
    period := low_period_t1_n8_h0_a16 },
  { node := 8, h := 1, a := 1, modulus := 54675, base := 11, shift := 0, target := 17357,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h1_a1,
    period := low_period_t1_n8_h1_a1 },
  { node := 8, h := 1, a := 3, modulus := 185895, base := 11, shift := 0, target := 61097,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h1_a3,
    period := low_period_t1_n8_h1_a3 },
  { node := 8, h := 1, a := 4, modulus := 360855, base := 11, shift := 0, target := 82967,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h1_a4,
    period := low_period_t1_n8_h1_a4 },
  { node := 8, h := 1, a := 5, modulus := 710775, base := 11, shift := 0, target := 104837,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h1_a5,
    period := low_period_t1_n8_h1_a5 },
  { node := 8, h := 1, a := 6, modulus := 1410615, base := 11, shift := 0, target := 126707,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h1_a6,
    period := low_period_t1_n8_h1_a6 },
  { node := 8, h := 1, a := 7, modulus := 2810295, base := 11, shift := 0, target := 148577,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h1_a7,
    period := low_period_t1_n8_h1_a7 },
  { node := 8, h := 1, a := 8, modulus := 5609655, base := 11, shift := 0, target := 170447,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h1_a8,
    period := low_period_t1_n8_h1_a8 },
  { node := 8, h := 1, a := 9, modulus := 11208375, base := 11, shift := 0, target := 192317,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h1_a9,
    period := low_period_t1_n8_h1_a9 },
  { node := 8, h := 1, a := 10, modulus := 22405815, base := 11, shift := 0, target := 214187,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h1_a10,
    period := low_period_t1_n8_h1_a10 },
  { node := 8, h := 1, a := 11, modulus := 44800695, base := 11, shift := 0, target := 236057,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h1_a11,
    period := low_period_t1_n8_h1_a11 },
  { node := 8, h := 1, a := 12, modulus := 89590455, base := 11, shift := 0, target := 257927,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h1_a12,
    period := low_period_t1_n8_h1_a12 },
  { node := 8, h := 1, a := 13, modulus := 179169975, base := 11, shift := 0, target := 279797,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h1_a13,
    period := low_period_t1_n8_h1_a13 },
  { node := 8, h := 1, a := 14, modulus := 358329015, base := 11, shift := 0, target := 301667,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h1_a14,
    period := low_period_t1_n8_h1_a14 },
  { node := 8, h := 1, a := 15, modulus := 716647095, base := 11, shift := 0, target := 323537,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h1_a15,
    period := low_period_t1_n8_h1_a15 },
  { node := 8, h := 1, a := 16, modulus := 1433283255, base := 11, shift := 0, target := 345407,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h1_a16,
    period := low_period_t1_n8_h1_a16 },
  { node := 8, h := 1, a := 17, modulus := 2866555575, base := 11, shift := 0, target := 367277,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h1_a17,
    period := low_period_t1_n8_h1_a17 },
  { node := 8, h := 1, a := 18, modulus := 5733100215, base := 11, shift := 0, target := 389147,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n8_h1_a18,
    period := low_period_t1_n8_h1_a18 },
  { node := 9, h := 0, a := 2, modulus := 185895, base := 12, shift := 0, target := 147709,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n9_h0_a2,
    period := low_period_t1_n9_h0_a2 },
  { node := 9, h := 0, a := 3, modulus := 351135, base := 12, shift := 0, target := 189019,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n9_h0_a3,
    period := low_period_t1_n9_h0_a3 },
  { node := 9, h := 0, a := 4, modulus := 681615, base := 12, shift := 0, target := 230329,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n9_h0_a4,
    period := low_period_t1_n9_h0_a4 },
  { node := 9, h := 0, a := 5, modulus := 1342575, base := 12, shift := 0, target := 271639,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n9_h0_a5,
    period := low_period_t1_n9_h0_a5 },
  { node := 9, h := 0, a := 6, modulus := 2664495, base := 12, shift := 0, target := 312949,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n9_h0_a6,
    period := low_period_t1_n9_h0_a6 },
  { node := 9, h := 0, a := 7, modulus := 5308335, base := 12, shift := 0, target := 354259,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n9_h0_a7,
    period := low_period_t1_n9_h0_a7 },
  { node := 9, h := 0, a := 8, modulus := 10596015, base := 12, shift := 0, target := 395569,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n9_h0_a8,
    period := low_period_t1_n9_h0_a8 },
  { node := 9, h := 0, a := 9, modulus := 21171375, base := 12, shift := 0, target := 436879,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n9_h0_a9,
    period := low_period_t1_n9_h0_a9 },
  { node := 9, h := 0, a := 10, modulus := 42322095, base := 12, shift := 0, target := 478189,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n9_h0_a10,
    period := low_period_t1_n9_h0_a10 },
  { node := 9, h := 0, a := 11, modulus := 84623535, base := 12, shift := 0, target := 519499,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n9_h0_a11,
    period := low_period_t1_n9_h0_a11 },
  { node := 9, h := 0, a := 12, modulus := 169226415, base := 12, shift := 0, target := 560809,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n9_h0_a12,
    period := low_period_t1_n9_h0_a12 },
  { node := 9, h := 0, a := 13, modulus := 338432175, base := 12, shift := 0, target := 602119,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n9_h0_a13,
    period := low_period_t1_n9_h0_a13 },
  { node := 9, h := 0, a := 14, modulus := 676843695, base := 12, shift := 0, target := 643429,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n9_h0_a14,
    period := low_period_t1_n9_h0_a14 },
  { node := 9, h := 0, a := 15, modulus := 1353666735, base := 12, shift := 0, target := 684739,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n9_h0_a15,
    period := low_period_t1_n9_h0_a15 },
  { node := 9, h := 0, a := 16, modulus := 2707312815, base := 12, shift := 0, target := 726049,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n9_h0_a16,
    period := low_period_t1_n9_h0_a16 },
  { node := 9, h := 0, a := 17, modulus := 5414604975, base := 12, shift := 0, target := 767359,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n9_h0_a17,
    period := low_period_t1_n9_h0_a17 },
  { node := 9, h := 0, a := 18, modulus := 10829189295, base := 12, shift := 0, target := 808669,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n9_h0_a18,
    period := low_period_t1_n9_h0_a18 },
  { node := 9, h := 0, a := 19, modulus := 21658357935, base := 12, shift := 0, target := 849979,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n9_h0_a19,
    period := low_period_t1_n9_h0_a19 },
  { node := 10, h := 0, a := 2, modulus := 885735, base := 13, shift := 0, target := 452153,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n10_h0_a2,
    period := low_period_t1_n10_h0_a2 },
  { node := 10, h := 0, a := 3, modulus := 1673055, base := 13, shift := 0, target := 648983,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n10_h0_a3,
    period := low_period_t1_n10_h0_a3 },
  { node := 10, h := 0, a := 4, modulus := 3247695, base := 13, shift := 0, target := 845813,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n10_h0_a4,
    period := low_period_t1_n10_h0_a4 },
  { node := 10, h := 0, a := 5, modulus := 6396975, base := 13, shift := 0, target := 1042643,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n10_h0_a5,
    period := low_period_t1_n10_h0_a5 },
  { node := 10, h := 0, a := 6, modulus := 12695535, base := 13, shift := 0, target := 1239473,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n10_h0_a6,
    period := low_period_t1_n10_h0_a6 },
  { node := 10, h := 0, a := 7, modulus := 25292655, base := 13, shift := 0, target := 1436303,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n10_h0_a7,
    period := low_period_t1_n10_h0_a7 },
  { node := 10, h := 0, a := 8, modulus := 50486895, base := 13, shift := 0, target := 1633133,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n10_h0_a8,
    period := low_period_t1_n10_h0_a8 },
  { node := 10, h := 0, a := 9, modulus := 100875375, base := 13, shift := 0, target := 1829963,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n10_h0_a9,
    period := low_period_t1_n10_h0_a9 },
  { node := 10, h := 0, a := 10, modulus := 201652335, base := 13, shift := 0, target := 2026793,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n10_h0_a10,
    period := low_period_t1_n10_h0_a10 },
  { node := 10, h := 0, a := 11, modulus := 403206255, base := 13, shift := 0, target := 2223623,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n10_h0_a11,
    period := low_period_t1_n10_h0_a11 },
  { node := 10, h := 0, a := 12, modulus := 806314095, base := 13, shift := 0, target := 2420453,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n10_h0_a12,
    period := low_period_t1_n10_h0_a12 },
  { node := 10, h := 0, a := 13, modulus := 1612529775, base := 13, shift := 0, target := 2617283,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n10_h0_a13,
    period := low_period_t1_n10_h0_a13 },
  { node := 10, h := 0, a := 14, modulus := 3224961135, base := 13, shift := 0, target := 2814113,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n10_h0_a14,
    period := low_period_t1_n10_h0_a14 },
  { node := 10, h := 0, a := 15, modulus := 6449823855, base := 13, shift := 0, target := 3010943,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n10_h0_a15,
    period := low_period_t1_n10_h0_a15 },
  { node := 10, h := 0, a := 16, modulus := 12899549295, base := 13, shift := 0, target := 3207773,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n10_h0_a16,
    period := low_period_t1_n10_h0_a16 },
  { node := 10, h := 0, a := 17, modulus := 25799000175, base := 13, shift := 0, target := 3404603,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n10_h0_a17,
    period := low_period_t1_n10_h0_a17 },
  { node := 10, h := 0, a := 18, modulus := 51597901935, base := 13, shift := 0, target := 3601433,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n10_h0_a18,
    period := low_period_t1_n10_h0_a18 },
  { node := 10, h := 0, a := 19, modulus := 103195705455, base := 13, shift := 0, target := 3798263,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n10_h0_a19,
    period := low_period_t1_n10_h0_a19 },
  { node := 10, h := 0, a := 20, modulus := 206391312495, base := 13, shift := 0, target := 3995093,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n10_h0_a20,
    period := low_period_t1_n10_h0_a20 },
  { node := 10, h := 0, a := 21, modulus := 412782526575, base := 13, shift := 0, target := 4191923,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n10_h0_a21,
    period := low_period_t1_n10_h0_a21 },
  { node := 10, h := 0, a := 22, modulus := 825564954735, base := 13, shift := 0, target := 4388753,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n10_h0_a22,
    period := low_period_t1_n10_h0_a22 },
  { node := 11, h := 0, a := 1, modulus := 492075, base := 14, shift := 0, target := 412231,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n11_h0_a1,
    period := low_period_t1_n11_h0_a1 },
  { node := 11, h := 0, a := 3, modulus := 1673055, base := 14, shift := 0, target := 805891,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n11_h0_a3,
    period := low_period_t1_n11_h0_a3 },
  { node := 11, h := 0, a := 4, modulus := 3247695, base := 14, shift := 0, target := 1002721,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n11_h0_a4,
    period := low_period_t1_n11_h0_a4 },
  { node := 11, h := 0, a := 5, modulus := 6396975, base := 14, shift := 0, target := 1199551,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n11_h0_a5,
    period := low_period_t1_n11_h0_a5 },
  { node := 11, h := 0, a := 6, modulus := 12695535, base := 14, shift := 0, target := 1396381,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n11_h0_a6,
    period := low_period_t1_n11_h0_a6 },
  { node := 11, h := 0, a := 7, modulus := 25292655, base := 14, shift := 0, target := 1593211,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n11_h0_a7,
    period := low_period_t1_n11_h0_a7 },
  { node := 11, h := 0, a := 8, modulus := 50486895, base := 14, shift := 0, target := 1790041,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n11_h0_a8,
    period := low_period_t1_n11_h0_a8 },
  { node := 11, h := 0, a := 9, modulus := 100875375, base := 14, shift := 0, target := 1986871,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n11_h0_a9,
    period := low_period_t1_n11_h0_a9 },
  { node := 11, h := 0, a := 10, modulus := 201652335, base := 14, shift := 0, target := 2183701,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n11_h0_a10,
    period := low_period_t1_n11_h0_a10 },
  { node := 11, h := 0, a := 11, modulus := 403206255, base := 14, shift := 0, target := 2380531,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n11_h0_a11,
    period := low_period_t1_n11_h0_a11 },
  { node := 11, h := 0, a := 12, modulus := 806314095, base := 14, shift := 0, target := 2577361,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n11_h0_a12,
    period := low_period_t1_n11_h0_a12 },
  { node := 11, h := 0, a := 13, modulus := 1612529775, base := 14, shift := 0, target := 2774191,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n11_h0_a13,
    period := low_period_t1_n11_h0_a13 },
  { node := 11, h := 0, a := 14, modulus := 3224961135, base := 14, shift := 0, target := 2971021,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n11_h0_a14,
    period := low_period_t1_n11_h0_a14 },
  { node := 11, h := 0, a := 15, modulus := 6449823855, base := 14, shift := 0, target := 3167851,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n11_h0_a15,
    period := low_period_t1_n11_h0_a15 },
  { node := 11, h := 0, a := 16, modulus := 12899549295, base := 14, shift := 0, target := 3364681,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n11_h0_a16,
    period := low_period_t1_n11_h0_a16 },
  { node := 11, h := 0, a := 17, modulus := 25799000175, base := 14, shift := 0, target := 3561511,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n11_h0_a17,
    period := low_period_t1_n11_h0_a17 },
  { node := 11, h := 0, a := 18, modulus := 51597901935, base := 14, shift := 0, target := 3758341,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n11_h0_a18,
    period := low_period_t1_n11_h0_a18 },
  { node := 11, h := 0, a := 19, modulus := 103195705455, base := 14, shift := 0, target := 3955171,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n11_h0_a19,
    period := low_period_t1_n11_h0_a19 },
  { node := 11, h := 0, a := 20, modulus := 206391312495, base := 14, shift := 0, target := 4152001,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n11_h0_a20,
    period := low_period_t1_n11_h0_a20 },
  { node := 11, h := 0, a := 21, modulus := 412782526575, base := 14, shift := 0, target := 4348831,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n11_h0_a21,
    period := low_period_t1_n11_h0_a21 },
  { node := 11, h := 0, a := 22, modulus := 825564954735, base := 14, shift := 0, target := 4545661,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n11_h0_a22,
    period := low_period_t1_n11_h0_a22 },
  { node := 12, h := 0, a := 1, modulus := 516375, base := 14, shift := 0, target := 528871,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n12_h0_a1,
    period := low_period_t1_n12_h0_a1 },
  { node := 12, h := 0, a := 2, modulus := 929475, base := 14, shift := 0, target := 735421,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n12_h0_a2,
    period := low_period_t1_n12_h0_a2 },
  { node := 12, h := 0, a := 3, modulus := 1755675, base := 14, shift := 0, target := 941971,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n12_h0_a3,
    period := low_period_t1_n12_h0_a3 },
  { node := 12, h := 0, a := 4, modulus := 3408075, base := 14, shift := 0, target := 1148521,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n12_h0_a4,
    period := low_period_t1_n12_h0_a4 },
  { node := 12, h := 0, a := 5, modulus := 6712875, base := 14, shift := 0, target := 1355071,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n12_h0_a5,
    period := low_period_t1_n12_h0_a5 },
  { node := 12, h := 0, a := 6, modulus := 13322475, base := 14, shift := 0, target := 1561621,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n12_h0_a6,
    period := low_period_t1_n12_h0_a6 },
  { node := 12, h := 0, a := 7, modulus := 26541675, base := 14, shift := 0, target := 1768171,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n12_h0_a7,
    period := low_period_t1_n12_h0_a7 },
  { node := 12, h := 0, a := 8, modulus := 52980075, base := 14, shift := 0, target := 1974721,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n12_h0_a8,
    period := low_period_t1_n12_h0_a8 },
  { node := 12, h := 0, a := 9, modulus := 105856875, base := 14, shift := 0, target := 2181271,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n12_h0_a9,
    period := low_period_t1_n12_h0_a9 },
  { node := 12, h := 0, a := 10, modulus := 211610475, base := 14, shift := 0, target := 2387821,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n12_h0_a10,
    period := low_period_t1_n12_h0_a10 },
  { node := 12, h := 0, a := 11, modulus := 423117675, base := 14, shift := 0, target := 2594371,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n12_h0_a11,
    period := low_period_t1_n12_h0_a11 },
  { node := 12, h := 0, a := 12, modulus := 846132075, base := 14, shift := 0, target := 2800921,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n12_h0_a12,
    period := low_period_t1_n12_h0_a12 },
  { node := 12, h := 0, a := 13, modulus := 1692160875, base := 14, shift := 0, target := 3007471,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n12_h0_a13,
    period := low_period_t1_n12_h0_a13 },
  { node := 12, h := 0, a := 14, modulus := 3384218475, base := 14, shift := 0, target := 3214021,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n12_h0_a14,
    period := low_period_t1_n12_h0_a14 },
  { node := 12, h := 0, a := 15, modulus := 6768333675, base := 14, shift := 0, target := 3420571,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n12_h0_a15,
    period := low_period_t1_n12_h0_a15 },
  { node := 12, h := 0, a := 16, modulus := 13536564075, base := 14, shift := 0, target := 3627121,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n12_h0_a16,
    period := low_period_t1_n12_h0_a16 },
  { node := 12, h := 0, a := 17, modulus := 27073024875, base := 14, shift := 0, target := 3833671,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n12_h0_a17,
    period := low_period_t1_n12_h0_a17 },
  { node := 12, h := 0, a := 18, modulus := 54145946475, base := 14, shift := 0, target := 4040221,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n12_h0_a18,
    period := low_period_t1_n12_h0_a18 },
  { node := 12, h := 0, a := 19, modulus := 108291789675, base := 14, shift := 0, target := 4246771,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n12_h0_a19,
    period := low_period_t1_n12_h0_a19 },
  { node := 12, h := 0, a := 20, modulus := 216583476075, base := 14, shift := 0, target := 4453321,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n12_h0_a20,
    period := low_period_t1_n12_h0_a20 },
  { node := 12, h := 0, a := 21, modulus := 433166848875, base := 14, shift := 0, target := 4659871,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n12_h0_a21,
    period := low_period_t1_n12_h0_a21 },
  { node := 12, h := 0, a := 22, modulus := 866333594475, base := 14, shift := 0, target := 4866421,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n12_h0_a22,
    period := low_period_t1_n12_h0_a22 },
  { node := 13, h := 0, a := 1, modulus := 2460375, base := 15, shift := 0, target := 1513367,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n13_h0_a1,
    period := low_period_t1_n13_h0_a1 },
  { node := 13, h := 0, a := 2, modulus := 4428675, base := 15, shift := 0, target := 2497517,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n13_h0_a2,
    period := low_period_t1_n13_h0_a2 },
  { node := 13, h := 0, a := 3, modulus := 8365275, base := 15, shift := 0, target := 3481667,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n13_h0_a3,
    period := low_period_t1_n13_h0_a3 },
  { node := 13, h := 0, a := 4, modulus := 16238475, base := 15, shift := 0, target := 4465817,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n13_h0_a4,
    period := low_period_t1_n13_h0_a4 },
  { node := 13, h := 0, a := 5, modulus := 31984875, base := 15, shift := 0, target := 5449967,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n13_h0_a5,
    period := low_period_t1_n13_h0_a5 },
  { node := 13, h := 0, a := 6, modulus := 63477675, base := 15, shift := 0, target := 6434117,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n13_h0_a6,
    period := low_period_t1_n13_h0_a6 },
  { node := 13, h := 0, a := 7, modulus := 126463275, base := 15, shift := 0, target := 7418267,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n13_h0_a7,
    period := low_period_t1_n13_h0_a7 },
  { node := 13, h := 0, a := 8, modulus := 252434475, base := 15, shift := 0, target := 8402417,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n13_h0_a8,
    period := low_period_t1_n13_h0_a8 },
  { node := 13, h := 0, a := 9, modulus := 504376875, base := 15, shift := 0, target := 9386567,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n13_h0_a9,
    period := low_period_t1_n13_h0_a9 },
  { node := 13, h := 0, a := 10, modulus := 1008261675, base := 15, shift := 0, target := 10370717,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n13_h0_a10,
    period := low_period_t1_n13_h0_a10 },
  { node := 13, h := 0, a := 11, modulus := 2016031275, base := 15, shift := 0, target := 11354867,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n13_h0_a11,
    period := low_period_t1_n13_h0_a11 },
  { node := 13, h := 0, a := 12, modulus := 4031570475, base := 15, shift := 0, target := 12339017,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n13_h0_a12,
    period := low_period_t1_n13_h0_a12 },
  { node := 13, h := 0, a := 13, modulus := 8062648875, base := 15, shift := 0, target := 13323167,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n13_h0_a13,
    period := low_period_t1_n13_h0_a13 },
  { node := 13, h := 0, a := 14, modulus := 16124805675, base := 15, shift := 0, target := 14307317,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n13_h0_a14,
    period := low_period_t1_n13_h0_a14 },
  { node := 13, h := 0, a := 15, modulus := 32249119275, base := 15, shift := 0, target := 15291467,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n13_h0_a15,
    period := low_period_t1_n13_h0_a15 },
  { node := 13, h := 0, a := 16, modulus := 64497746475, base := 15, shift := 0, target := 16275617,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n13_h0_a16,
    period := low_period_t1_n13_h0_a16 },
  { node := 13, h := 0, a := 17, modulus := 128995000875, base := 15, shift := 0, target := 17259767,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n13_h0_a17,
    period := low_period_t1_n13_h0_a17 },
  { node := 13, h := 0, a := 18, modulus := 257989509675, base := 15, shift := 0, target := 18243917,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n13_h0_a18,
    period := low_period_t1_n13_h0_a18 },
  { node := 13, h := 0, a := 19, modulus := 515978527275, base := 15, shift := 0, target := 19228067,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n13_h0_a19,
    period := low_period_t1_n13_h0_a19 },
  { node := 13, h := 0, a := 20, modulus := 1031956562475, base := 15, shift := 0, target := 20212217,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n13_h0_a20,
    period := low_period_t1_n13_h0_a20 },
  { node := 13, h := 0, a := 21, modulus := 2063912632875, base := 15, shift := 0, target := 21196367,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n13_h0_a21,
    period := low_period_t1_n13_h0_a21 },
  { node := 13, h := 0, a := 22, modulus := 4127824773675, base := 15, shift := 0, target := 22180517,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n13_h0_a22,
    period := low_period_t1_n13_h0_a22 },
  { node := 13, h := 0, a := 23, modulus := 8255649055275, base := 15, shift := 0, target := 23164667,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n13_h0_a23,
    period := low_period_t1_n13_h0_a23 },
  { node := 13, h := 0, a := 24, modulus := 16511297618475, base := 15, shift := 0, target := 24148817,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n13_h0_a24,
    period := low_period_t1_n13_h0_a24 },
  { node := 14, h := 0, a := 1, modulus := 4428675, base := 17, shift := 0, target := 5758223,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n14_h0_a1,
    period := low_period_t1_n14_h0_a1 },
  { node := 14, h := 0, a := 2, modulus := 7971615, base := 17, shift := 0, target := 7529693,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n14_h0_a2,
    period := low_period_t1_n14_h0_a2 },
  { node := 14, h := 0, a := 3, modulus := 15057495, base := 17, shift := 0, target := 9301163,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n14_h0_a3,
    period := low_period_t1_n14_h0_a3 },
  { node := 14, h := 0, a := 4, modulus := 29229255, base := 17, shift := 0, target := 11072633,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n14_h0_a4,
    period := low_period_t1_n14_h0_a4 },
  { node := 14, h := 0, a := 5, modulus := 57572775, base := 17, shift := 0, target := 12844103,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n14_h0_a5,
    period := low_period_t1_n14_h0_a5 },
  { node := 14, h := 0, a := 6, modulus := 114259815, base := 17, shift := 0, target := 14615573,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n14_h0_a6,
    period := low_period_t1_n14_h0_a6 },
  { node := 14, h := 0, a := 7, modulus := 227633895, base := 17, shift := 0, target := 16387043,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n14_h0_a7,
    period := low_period_t1_n14_h0_a7 },
  { node := 14, h := 0, a := 8, modulus := 454382055, base := 17, shift := 0, target := 18158513,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n14_h0_a8,
    period := low_period_t1_n14_h0_a8 },
  { node := 14, h := 0, a := 9, modulus := 907878375, base := 17, shift := 0, target := 19929983,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n14_h0_a9,
    period := low_period_t1_n14_h0_a9 },
  { node := 14, h := 0, a := 10, modulus := 1814871015, base := 17, shift := 0, target := 21701453,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n14_h0_a10,
    period := low_period_t1_n14_h0_a10 },
  { node := 14, h := 0, a := 11, modulus := 3628856295, base := 17, shift := 0, target := 23472923,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n14_h0_a11,
    period := low_period_t1_n14_h0_a11 },
  { node := 14, h := 0, a := 12, modulus := 7256826855, base := 17, shift := 0, target := 25244393,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n14_h0_a12,
    period := low_period_t1_n14_h0_a12 },
  { node := 14, h := 0, a := 13, modulus := 14512767975, base := 17, shift := 0, target := 27015863,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n14_h0_a13,
    period := low_period_t1_n14_h0_a13 },
  { node := 14, h := 0, a := 14, modulus := 29024650215, base := 17, shift := 0, target := 28787333,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n14_h0_a14,
    period := low_period_t1_n14_h0_a14 },
  { node := 14, h := 0, a := 15, modulus := 58048414695, base := 17, shift := 0, target := 30558803,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n14_h0_a15,
    period := low_period_t1_n14_h0_a15 },
  { node := 14, h := 0, a := 16, modulus := 116095943655, base := 17, shift := 0, target := 32330273,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n14_h0_a16,
    period := low_period_t1_n14_h0_a16 },
  { node := 14, h := 0, a := 17, modulus := 232191001575, base := 17, shift := 0, target := 34101743,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n14_h0_a17,
    period := low_period_t1_n14_h0_a17 },
  { node := 14, h := 0, a := 18, modulus := 464381117415, base := 17, shift := 0, target := 35873213,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n14_h0_a18,
    period := low_period_t1_n14_h0_a18 },
  { node := 14, h := 0, a := 19, modulus := 928761349095, base := 17, shift := 0, target := 37644683,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n14_h0_a19,
    period := low_period_t1_n14_h0_a19 },
  { node := 14, h := 0, a := 20, modulus := 1857521812455, base := 17, shift := 0, target := 39416153,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n14_h0_a20,
    period := low_period_t1_n14_h0_a20 },
  { node := 14, h := 0, a := 21, modulus := 3715042739175, base := 17, shift := 0, target := 41187623,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n14_h0_a21,
    period := low_period_t1_n14_h0_a21 },
  { node := 14, h := 0, a := 22, modulus := 7430084592615, base := 17, shift := 0, target := 42959093,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n14_h0_a22,
    period := low_period_t1_n14_h0_a22 },
  { node := 14, h := 0, a := 23, modulus := 14860168299495, base := 17, shift := 0, target := 44730563,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n14_h0_a23,
    period := low_period_t1_n14_h0_a23 },
  { node := 14, h := 0, a := 24, modulus := 29720335713255, base := 17, shift := 0, target := 46502033,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n14_h0_a24,
    period := low_period_t1_n14_h0_a24 },
  { node := 14, h := 0, a := 25, modulus := 59440670540775, base := 17, shift := 0, target := 48273503,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_t1_n14_h0_a25,
    period := low_period_t1_n14_h0_a25 }
]
def lowRowKeys_t1 : List (Nat × Nat × Nat) := lowRows_t1.map lowRowKey


def nonrootEdgeKeys_t1 : List (Nat × Nat × Nat) := [⟨1, 1, 2⟩, ⟨2, 0, 1⟩, ⟨2, 1, 2⟩, ⟨3, 0, 3⟩, ⟨5, 0, 1⟩, ⟨8, 1, 2⟩, ⟨9, 0, 1⟩, ⟨10, 0, 1⟩, ⟨11, 0, 2⟩]


def cutoff_t1 (n h : Nat) : Nat :=
  match n, h with
  | 1, 0 => 8
  | 1, 1 => 10
  | 2, 0 => 12
  | 2, 1 => 14
  | 3, 0 => 16
  | 3, 1 => 17
  | 4, 0 => 19
  | 5, 0 => 20
  | 6, 0 => 14
  | 6, 1 => 16
  | 6, 2 => 17
  | 7, 0 => 15
  | 7, 1 => 16
  | 7, 2 => 18
  | 7, 3 => 20
  | 8, 0 => 17
  | 8, 1 => 19
  | 9, 0 => 20
  | 10, 0 => 23
  | 11, 0 => 23
  | 12, 0 => 23
  | 13, 0 => 25
  | 14, 0 => 26
  | _, _ => 0


theorem lowRowKey_complete_fin_t1 :
    ∀ n : Fin 15, 1 ≤ n.val →
      ∀ h : Fin ((nodeAt_t1 n.val).r+1),
        ∀ a : Fin (cutoff_t1 n.val h.val),
          1 ≤ a.val →
          (n.val,h.val,a.val) ∈ lowRowKeys_t1 ∨
            (n.val,h.val,a.val) ∈ nonrootEdgeKeys_t1 := by
  decide


theorem lowRowKey_complete_t1 (n h a : Nat)
    (hn : 1 ≤ n) (hn' : n < 15)
    (hh : h ≤ (nodeAt_t1 n).r)
    (ha : 1 ≤ a) (ha' : a < cutoff_t1 n h) :
    (n,h,a) ∈ lowRowKeys_t1 ∨ (n,h,a) ∈ nonrootEdgeKeys_t1 := by
  exact lowRowKey_complete_fin_t1 ⟨n,hn'⟩ hn ⟨h, by simpa using Nat.lt_succ_of_le hh⟩ ⟨a,ha'⟩ ha


def highCerts_t1 : List (HighCert nodeAt_t1) :=
[
  { node := 1, h := 0, A := 8, D := 15, E := 34,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide },
  { node := 1, h := 1, A := 10, D := 45, E := 68,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide },
  { node := 2, h := 0, A := 12, D := 135, E := 226,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide },
  { node := 2, h := 1, A := 14, D := 405, E := 452,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide },
  { node := 3, h := 0, A := 16, D := 1215, E := 1714,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide },
  { node := 3, h := 1, A := 17, D := 3645, E := 3428,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide },
  { node := 4, h := 0, A := 19, D := 10935, E := 14146,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide },
  { node := 5, h := 0, A := 20, D := 19683, E := 58910,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide },
  { node := 6, h := 0, A := 14, D := 405, E := 1714,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide },
  { node := 6, h := 1, A := 16, D := 1215, E := 3428,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide },
  { node := 6, h := 2, A := 17, D := 3645, E := 6856,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide },
  { node := 7, h := 0, A := 15, D := 675, E := 1714,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide },
  { node := 7, h := 1, A := 16, D := 2025, E := 3428,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide },
  { node := 7, h := 2, A := 18, D := 6075, E := 6856,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide },
  { node := 7, h := 3, A := 20, D := 18225, E := 13712,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide },
  { node := 8, h := 0, A := 17, D := 3645, E := 14146,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide },
  { node := 8, h := 1, A := 19, D := 10935, E := 28292,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide },
  { node := 9, h := 0, A := 20, D := 20655, E := 127054,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide },
  { node := 10, h := 0, A := 23, D := 98415, E := 353738,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide },
  { node := 11, h := 0, A := 23, D := 98415, E := 510646,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide },
  { node := 12, h := 0, A := 23, D := 103275, E := 632146,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide },
  { node := 13, h := 0, A := 25, D := 492075, E := 2005442,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide },
  { node := 14, h := 0, A := 26, D := 885735, E := 6643958,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide }
]
def highCertKeys_t1 : List (Nat × Nat) := highCerts_t1.map highCertKey


theorem highCertKey_complete_fin_t1 :
    ∀ n : Fin 15, 1 ≤ n.val →
      ∀ h : Fin ((nodeAt_t1 n.val).r+1),
        (n.val,h.val) ∈ highCertKeys_t1 := by
  decide


theorem highCertKey_complete_t1 (n h : Nat)
    (hn : 1 ≤ n) (hn' : n < 15)
    (hh : h ≤ (nodeAt_t1 n).r) :
    (n,h) ∈ highCertKeys_t1 := by
  exact highCertKey_complete_fin_t1 ⟨n,hn'⟩ hn ⟨h, by simpa using Nat.lt_succ_of_le hh⟩

def highCertTripleKeys_t1 : List (Nat × Nat × Nat) :=
  highCerts_t1.map highCertTripleKey

theorem highCertCutoffKey_complete_fin_t1 :
    ∀ n : Fin 15, 1 ≤ n.val →
      ∀ h : Fin ((nodeAt_t1 n.val).r+1),
        (n.val,h.val,cutoff_t1 n.val h.val) ∈ highCertTripleKeys_t1 := by
  decide

theorem highCertCutoff_complete_t1 (n h : Nat)
    (hn : 1 ≤ n) (hn' : n < 15)
    (hh : h ≤ (nodeAt_t1 n).r) :
    ∃ cert, cert ∈ highCerts_t1 ∧ cert.node=n ∧
      cert.h=h ∧ cert.A=cutoff_t1 n h := by
  have hkey := highCertCutoffKey_complete_fin_t1 ⟨n,hn'⟩ hn ⟨h, by simpa using Nat.lt_succ_of_le hh⟩
  exact highCertTriple_mem_of_key hkey


def valCerts_t1 : List (ValCert residues_t1 period_t1 nodeAt_t1) :=
[
  { node := 1, modulus := 27, base := 3, target := 17,
    «matches» := by decide, offset_bound := by decide, coefficient_valuation := by decide,
    nohit := val_nohit_t1_n1, period := val_period_t1_n1 },
  { node := 2, modulus := 243, base := 5, target := 113,
    «matches» := by decide, offset_bound := by decide, coefficient_valuation := by decide,
    nohit := val_nohit_t1_n2, period := val_period_t1_n2 },
  { node := 3, modulus := 2187, base := 7, target := 857,
    «matches» := by decide, offset_bound := by decide, coefficient_valuation := by decide,
    nohit := val_nohit_t1_n3, period := val_period_t1_n3 },
  { node := 4, modulus := 6561, base := 9, target := 7073,
    «matches» := by decide, offset_bound := by decide, coefficient_valuation := by decide,
    nohit := val_nohit_t1_n4, period := val_period_t1_n4 },
  { node := 5, modulus := 59049, base := 10, target := 29455,
    «matches» := by decide, offset_bound := by decide, coefficient_valuation := by decide,
    nohit := val_nohit_t1_n5, period := val_period_t1_n5 },
  { node := 6, modulus := 2187, base := 7, target := 857,
    «matches» := by decide, offset_bound := by decide, coefficient_valuation := by decide,
    nohit := val_nohit_t1_n6, period := val_period_t1_n6 },
  { node := 7, modulus := 2187, base := 7, target := 857,
    «matches» := by decide, offset_bound := by decide, coefficient_valuation := by decide,
    nohit := val_nohit_t1_n7, period := val_period_t1_n7 },
  { node := 8, modulus := 6561, base := 9, target := 7073,
    «matches» := by decide, offset_bound := by decide, coefficient_valuation := by decide,
    nohit := val_nohit_t1_n8, period := val_period_t1_n8 },
  { node := 9, modulus := 729, base := 11, target := 63527,
    «matches» := by decide, offset_bound := by decide, coefficient_valuation := by decide,
    nohit := val_nohit_t1_n9, period := val_period_t1_n9 },
  { node := 10, modulus := 59049, base := 12, target := 176869,
    «matches» := by decide, offset_bound := by decide, coefficient_valuation := by decide,
    nohit := val_nohit_t1_n10, period := val_period_t1_n10 },
  { node := 11, modulus := 59049, base := 13, target := 255323,
    «matches» := by decide, offset_bound := by decide, coefficient_valuation := by decide,
    nohit := val_nohit_t1_n11, period := val_period_t1_n11 },
  { node := 12, modulus := 729, base := 13, target := 316073,
    «matches» := by decide, offset_bound := by decide, coefficient_valuation := by decide,
    nohit := val_nohit_t1_n12, period := val_period_t1_n12 },
  { node := 13, modulus := 59049, base := 14, target := 1002721,
    «matches» := by decide, offset_bound := by decide, coefficient_valuation := by decide,
    nohit := val_nohit_t1_n13, period := val_period_t1_n13 },
  { node := 14, modulus := 531441, base := 16, target := 3321979,
    «matches» := by decide, offset_bound := by decide, coefficient_valuation := by decide,
    nohit := val_nohit_t1_n14, period := val_period_t1_n14 }
]
def valCertKeys_t1 : List Nat := valCerts_t1.map valCertKey


theorem valCertKey_complete_fin_t1 :
    ∀ n : Fin 15, 1 ≤ n.val → n.val ∈ valCertKeys_t1 := by
  decide


theorem valCertKey_complete_t1 (n : Nat)
    (hn : 1 ≤ n) (hn' : n < 15) :
    n ∈ valCertKeys_t1 := by
  exact valCertKey_complete_fin_t1 ⟨n,hn'⟩ hn


def lowRows_h1a3 : List (LowRowCert residues_h1a3 period_h1a3 nodeAt_h1a3) :=
[
  { node := 1, h := 0, a := 3, modulus := 867, base := 6, shift := 0, target := 463,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n1_h0_a3,
    period := low_period_h1a3_n1_h0_a3 },
  { node := 1, h := 0, a := 4, modulus := 1683, base := 6, shift := 0, target := 565,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n1_h0_a4,
    period := low_period_h1a3_n1_h0_a4 },
  { node := 1, h := 0, a := 5, modulus := 3315, base := 6, shift := 0, target := 667,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n1_h0_a5,
    period := low_period_h1a3_n1_h0_a5 },
  { node := 1, h := 0, a := 6, modulus := 6579, base := 6, shift := 0, target := 769,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n1_h0_a6,
    period := low_period_h1a3_n1_h0_a6 },
  { node := 1, h := 0, a := 7, modulus := 13107, base := 6, shift := 0, target := 871,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n1_h0_a7,
    period := low_period_h1a3_n1_h0_a7 },
  { node := 1, h := 0, a := 8, modulus := 26163, base := 6, shift := 0, target := 973,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n1_h0_a8,
    period := low_period_h1a3_n1_h0_a8 },
  { node := 1, h := 0, a := 9, modulus := 52275, base := 6, shift := 0, target := 1075,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n1_h0_a9,
    period := low_period_h1a3_n1_h0_a9 },
  { node := 1, h := 0, a := 10, modulus := 104499, base := 6, shift := 0, target := 1177,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n1_h0_a10,
    period := low_period_h1a3_n1_h0_a10 },
  { node := 2, h := 0, a := 1, modulus := 1275, base := 8, shift := 0, target := 1291,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n2_h0_a1,
    period := low_period_h1a3_n2_h0_a1 },
  { node := 2, h := 0, a := 2, modulus := 2295, base := 8, shift := 0, target := 1801,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n2_h0_a2,
    period := low_period_h1a3_n2_h0_a2 },
  { node := 2, h := 0, a := 3, modulus := 4335, base := 8, shift := 0, target := 2311,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n2_h0_a3,
    period := low_period_h1a3_n2_h0_a3 },
  { node := 2, h := 0, a := 4, modulus := 8415, base := 8, shift := 0, target := 2821,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n2_h0_a4,
    period := low_period_h1a3_n2_h0_a4 },
  { node := 2, h := 0, a := 5, modulus := 16575, base := 8, shift := 0, target := 3331,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n2_h0_a5,
    period := low_period_h1a3_n2_h0_a5 },
  { node := 2, h := 0, a := 6, modulus := 32895, base := 8, shift := 0, target := 3841,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n2_h0_a6,
    period := low_period_h1a3_n2_h0_a6 },
  { node := 2, h := 0, a := 7, modulus := 65535, base := 8, shift := 0, target := 4351,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n2_h0_a7,
    period := low_period_h1a3_n2_h0_a7 },
  { node := 2, h := 0, a := 8, modulus := 130815, base := 8, shift := 0, target := 4861,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n2_h0_a8,
    period := low_period_h1a3_n2_h0_a8 },
  { node := 2, h := 0, a := 9, modulus := 261375, base := 8, shift := 0, target := 5371,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n2_h0_a9,
    period := low_period_h1a3_n2_h0_a9 },
  { node := 2, h := 0, a := 10, modulus := 522495, base := 8, shift := 0, target := 5881,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n2_h0_a10,
    period := low_period_h1a3_n2_h0_a10 },
  { node := 2, h := 0, a := 11, modulus := 1044735, base := 8, shift := 0, target := 6391,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n2_h0_a11,
    period := low_period_h1a3_n2_h0_a11 },
  { node := 2, h := 0, a := 12, modulus := 2089215, base := 8, shift := 0, target := 6901,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n2_h0_a12,
    period := low_period_h1a3_n2_h0_a12 },
  { node := 3, h := 0, a := 2, modulus := 4131, base := 9, shift := 0, target := 4265,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n3_h0_a2,
    period := low_period_h1a3_n3_h0_a2 },
  { node := 3, h := 0, a := 3, modulus := 7803, base := 9, shift := 0, target := 5183,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n3_h0_a3,
    period := low_period_h1a3_n3_h0_a3 },
  { node := 3, h := 0, a := 4, modulus := 15147, base := 9, shift := 0, target := 6101,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n3_h0_a4,
    period := low_period_h1a3_n3_h0_a4 },
  { node := 3, h := 0, a := 5, modulus := 29835, base := 9, shift := 0, target := 7019,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n3_h0_a5,
    period := low_period_h1a3_n3_h0_a5 },
  { node := 3, h := 0, a := 6, modulus := 59211, base := 9, shift := 0, target := 7937,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n3_h0_a6,
    period := low_period_h1a3_n3_h0_a6 },
  { node := 3, h := 0, a := 7, modulus := 117963, base := 9, shift := 0, target := 8855,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n3_h0_a7,
    period := low_period_h1a3_n3_h0_a7 },
  { node := 3, h := 0, a := 8, modulus := 235467, base := 9, shift := 0, target := 9773,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n3_h0_a8,
    period := low_period_h1a3_n3_h0_a8 },
  { node := 3, h := 0, a := 9, modulus := 470475, base := 9, shift := 0, target := 10691,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n3_h0_a9,
    period := low_period_h1a3_n3_h0_a9 },
  { node := 3, h := 0, a := 10, modulus := 940491, base := 9, shift := 0, target := 11609,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n3_h0_a10,
    period := low_period_h1a3_n3_h0_a10 },
  { node := 3, h := 0, a := 11, modulus := 1880523, base := 9, shift := 0, target := 12527,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n3_h0_a11,
    period := low_period_h1a3_n3_h0_a11 },
  { node := 3, h := 0, a := 12, modulus := 3760587, base := 9, shift := 0, target := 13445,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n3_h0_a12,
    period := low_period_h1a3_n3_h0_a12 },
  { node := 3, h := 0, a := 13, modulus := 7520715, base := 9, shift := 0, target := 14363,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n3_h0_a13,
    period := low_period_h1a3_n3_h0_a13 },
  { node := 4, h := 0, a := 1, modulus := 11475, base := 11, shift := 0, target := 15683,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n4_h0_a1,
    period := low_period_h1a3_n4_h0_a1 },
  { node := 4, h := 0, a := 3, modulus := 39015, base := 11, shift := 0, target := 24863,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n4_h0_a3,
    period := low_period_h1a3_n4_h0_a3 },
  { node := 4, h := 0, a := 4, modulus := 75735, base := 11, shift := 0, target := 29453,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n4_h0_a4,
    period := low_period_h1a3_n4_h0_a4 },
  { node := 4, h := 0, a := 5, modulus := 149175, base := 11, shift := 0, target := 34043,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n4_h0_a5,
    period := low_period_h1a3_n4_h0_a5 },
  { node := 4, h := 0, a := 6, modulus := 296055, base := 11, shift := 0, target := 38633,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n4_h0_a6,
    period := low_period_h1a3_n4_h0_a6 },
  { node := 4, h := 0, a := 7, modulus := 589815, base := 11, shift := 0, target := 43223,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n4_h0_a7,
    period := low_period_h1a3_n4_h0_a7 },
  { node := 4, h := 0, a := 8, modulus := 1177335, base := 11, shift := 0, target := 47813,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n4_h0_a8,
    period := low_period_h1a3_n4_h0_a8 },
  { node := 4, h := 0, a := 9, modulus := 2352375, base := 11, shift := 0, target := 52403,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n4_h0_a9,
    period := low_period_h1a3_n4_h0_a9 },
  { node := 4, h := 0, a := 10, modulus := 4702455, base := 11, shift := 0, target := 56993,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n4_h0_a10,
    period := low_period_h1a3_n4_h0_a10 },
  { node := 4, h := 0, a := 11, modulus := 9402615, base := 11, shift := 0, target := 61583,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n4_h0_a11,
    period := low_period_h1a3_n4_h0_a11 },
  { node := 4, h := 0, a := 12, modulus := 18802935, base := 11, shift := 0, target := 66173,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n4_h0_a12,
    period := low_period_h1a3_n4_h0_a12 },
  { node := 4, h := 0, a := 13, modulus := 37603575, base := 11, shift := 0, target := 70763,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n4_h0_a13,
    period := low_period_h1a3_n4_h0_a13 },
  { node := 4, h := 0, a := 14, modulus := 75204855, base := 11, shift := 0, target := 75353,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n4_h0_a14,
    period := low_period_h1a3_n4_h0_a14 },
  { node := 4, h := 0, a := 15, modulus := 150407415, base := 11, shift := 0, target := 79943,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n4_h0_a15,
    period := low_period_h1a3_n4_h0_a15 },
  { node := 4, h := 0, a := 16, modulus := 300812535, base := 11, shift := 0, target := 84533,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n4_h0_a16,
    period := low_period_h1a3_n4_h0_a16 },
  { node := 5, h := 0, a := 1, modulus := 103275, base := 14, shift := 0, target := 182839,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n5_h0_a1,
    period := low_period_h1a3_n5_h0_a1 },
  { node := 5, h := 0, a := 3, modulus := 351135, base := 14, shift := 0, target := 265459,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n5_h0_a3,
    period := low_period_h1a3_n5_h0_a3 },
  { node := 5, h := 0, a := 4, modulus := 681615, base := 14, shift := 0, target := 306769,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n5_h0_a4,
    period := low_period_h1a3_n5_h0_a4 },
  { node := 5, h := 0, a := 5, modulus := 1342575, base := 14, shift := 0, target := 348079,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n5_h0_a5,
    period := low_period_h1a3_n5_h0_a5 },
  { node := 5, h := 0, a := 6, modulus := 2664495, base := 14, shift := 0, target := 389389,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n5_h0_a6,
    period := low_period_h1a3_n5_h0_a6 },
  { node := 5, h := 0, a := 7, modulus := 5308335, base := 14, shift := 0, target := 430699,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n5_h0_a7,
    period := low_period_h1a3_n5_h0_a7 },
  { node := 5, h := 0, a := 8, modulus := 10596015, base := 14, shift := 0, target := 472009,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n5_h0_a8,
    period := low_period_h1a3_n5_h0_a8 },
  { node := 5, h := 0, a := 9, modulus := 21171375, base := 14, shift := 0, target := 513319,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n5_h0_a9,
    period := low_period_h1a3_n5_h0_a9 },
  { node := 5, h := 0, a := 10, modulus := 42322095, base := 14, shift := 0, target := 554629,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n5_h0_a10,
    period := low_period_h1a3_n5_h0_a10 },
  { node := 5, h := 0, a := 11, modulus := 84623535, base := 14, shift := 0, target := 595939,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n5_h0_a11,
    period := low_period_h1a3_n5_h0_a11 },
  { node := 5, h := 0, a := 12, modulus := 169226415, base := 14, shift := 0, target := 637249,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n5_h0_a12,
    period := low_period_h1a3_n5_h0_a12 },
  { node := 5, h := 0, a := 13, modulus := 338432175, base := 14, shift := 0, target := 678559,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n5_h0_a13,
    period := low_period_h1a3_n5_h0_a13 },
  { node := 5, h := 0, a := 14, modulus := 676843695, base := 14, shift := 0, target := 719869,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n5_h0_a14,
    period := low_period_h1a3_n5_h0_a14 },
  { node := 5, h := 0, a := 15, modulus := 1353666735, base := 14, shift := 0, target := 761179,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n5_h0_a15,
    period := low_period_h1a3_n5_h0_a15 },
  { node := 5, h := 0, a := 16, modulus := 2707312815, base := 14, shift := 0, target := 802489,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n5_h0_a16,
    period := low_period_h1a3_n5_h0_a16 },
  { node := 5, h := 0, a := 17, modulus := 5414604975, base := 14, shift := 0, target := 843799,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n5_h0_a17,
    period := low_period_h1a3_n5_h0_a17 },
  { node := 5, h := 0, a := 18, modulus := 10829189295, base := 14, shift := 0, target := 885109,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n5_h0_a18,
    period := low_period_h1a3_n5_h0_a18 },
  { node := 5, h := 0, a := 19, modulus := 21658357935, base := 14, shift := 0, target := 926419,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n5_h0_a19,
    period := low_period_h1a3_n5_h0_a19 },
  { node := 6, h := 0, a := 1, modulus := 929475, base := 17, shift := 0, target := 1979087,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n6_h0_a1,
    period := low_period_h1a3_n6_h0_a1 },
  { node := 6, h := 0, a := 2, modulus := 1673055, base := 17, shift := 0, target := 2350877,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n6_h0_a2,
    period := low_period_h1a3_n6_h0_a2 },
  { node := 6, h := 0, a := 3, modulus := 3160215, base := 17, shift := 0, target := 2722667,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n6_h0_a3,
    period := low_period_h1a3_n6_h0_a3 },
  { node := 6, h := 0, a := 4, modulus := 6134535, base := 17, shift := 0, target := 3094457,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n6_h0_a4,
    period := low_period_h1a3_n6_h0_a4 },
  { node := 6, h := 0, a := 5, modulus := 12083175, base := 17, shift := 0, target := 3466247,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n6_h0_a5,
    period := low_period_h1a3_n6_h0_a5 },
  { node := 6, h := 0, a := 6, modulus := 23980455, base := 17, shift := 0, target := 3838037,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n6_h0_a6,
    period := low_period_h1a3_n6_h0_a6 },
  { node := 6, h := 0, a := 7, modulus := 47775015, base := 17, shift := 0, target := 4209827,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n6_h0_a7,
    period := low_period_h1a3_n6_h0_a7 },
  { node := 6, h := 0, a := 8, modulus := 95364135, base := 17, shift := 0, target := 4581617,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n6_h0_a8,
    period := low_period_h1a3_n6_h0_a8 },
  { node := 6, h := 0, a := 9, modulus := 190542375, base := 17, shift := 0, target := 4953407,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n6_h0_a9,
    period := low_period_h1a3_n6_h0_a9 },
  { node := 6, h := 0, a := 10, modulus := 380898855, base := 17, shift := 0, target := 5325197,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n6_h0_a10,
    period := low_period_h1a3_n6_h0_a10 },
  { node := 6, h := 0, a := 11, modulus := 761611815, base := 17, shift := 0, target := 5696987,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n6_h0_a11,
    period := low_period_h1a3_n6_h0_a11 },
  { node := 6, h := 0, a := 12, modulus := 1523037735, base := 17, shift := 0, target := 6068777,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n6_h0_a12,
    period := low_period_h1a3_n6_h0_a12 },
  { node := 6, h := 0, a := 13, modulus := 3045889575, base := 17, shift := 0, target := 6440567,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n6_h0_a13,
    period := low_period_h1a3_n6_h0_a13 },
  { node := 6, h := 0, a := 14, modulus := 6091593255, base := 17, shift := 0, target := 6812357,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n6_h0_a14,
    period := low_period_h1a3_n6_h0_a14 },
  { node := 6, h := 0, a := 15, modulus := 12183000615, base := 17, shift := 0, target := 7184147,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n6_h0_a15,
    period := low_period_h1a3_n6_h0_a15 },
  { node := 6, h := 0, a := 16, modulus := 24365815335, base := 17, shift := 0, target := 7555937,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n6_h0_a16,
    period := low_period_h1a3_n6_h0_a16 },
  { node := 6, h := 0, a := 17, modulus := 48731444775, base := 17, shift := 0, target := 7927727,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n6_h0_a17,
    period := low_period_h1a3_n6_h0_a17 },
  { node := 6, h := 0, a := 18, modulus := 97462703655, base := 17, shift := 0, target := 8299517,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n6_h0_a18,
    period := low_period_h1a3_n6_h0_a18 },
  { node := 6, h := 0, a := 19, modulus := 194925221415, base := 17, shift := 0, target := 8671307,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n6_h0_a19,
    period := low_period_h1a3_n6_h0_a19 },
  { node := 6, h := 0, a := 20, modulus := 389850256935, base := 17, shift := 0, target := 9043097,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n6_h0_a20,
    period := low_period_h1a3_n6_h0_a20 },
  { node := 6, h := 0, a := 21, modulus := 779700327975, base := 17, shift := 0, target := 9414887,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n6_h0_a21,
    period := low_period_h1a3_n6_h0_a21 },
  { node := 6, h := 0, a := 22, modulus := 1559400470055, base := 17, shift := 0, target := 9786677,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n6_h0_a22,
    period := low_period_h1a3_n6_h0_a22 },
  { node := 6, h := 0, a := 23, modulus := 3118800754215, base := 17, shift := 0, target := 10158467,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h1a3_n6_h0_a23,
    period := low_period_h1a3_n6_h0_a23 }
]
def lowRowKeys_h1a3 : List (Nat × Nat × Nat) := lowRows_h1a3.map lowRowKey


def nonrootEdgeKeys_h1a3 : List (Nat × Nat × Nat) := [⟨1, 0, 1⟩, ⟨1, 0, 2⟩, ⟨3, 0, 1⟩, ⟨4, 0, 2⟩, ⟨5, 0, 2⟩]


def cutoff_h1a3 (n h : Nat) : Nat :=
  match n, h with
  | 1, 0 => 11
  | 2, 0 => 13
  | 3, 0 => 14
  | 4, 0 => 17
  | 5, 0 => 20
  | 6, 0 => 24
  | _, _ => 0


theorem lowRowKey_complete_fin_h1a3 :
    ∀ n : Fin 7, 1 ≤ n.val →
      ∀ h : Fin ((nodeAt_h1a3 n.val).r+1),
        ∀ a : Fin (cutoff_h1a3 n.val h.val),
          1 ≤ a.val →
          (n.val,h.val,a.val) ∈ lowRowKeys_h1a3 ∨
            (n.val,h.val,a.val) ∈ nonrootEdgeKeys_h1a3 := by
  decide


theorem lowRowKey_complete_h1a3 (n h a : Nat)
    (hn : 1 ≤ n) (hn' : n < 7)
    (hh : h ≤ (nodeAt_h1a3 n).r)
    (ha : 1 ≤ a) (ha' : a < cutoff_h1a3 n h) :
    (n,h,a) ∈ lowRowKeys_h1a3 ∨ (n,h,a) ∈ nonrootEdgeKeys_h1a3 := by
  exact lowRowKey_complete_fin_h1a3 ⟨n,hn'⟩ hn ⟨h, by simpa using Nat.lt_succ_of_le hh⟩ ⟨a,ha'⟩ ha


def highCerts_h1a3 : List (HighCert nodeAt_h1a3) :=
[
  { node := 1, h := 0, A := 11, D := 51, E := 310,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide },
  { node := 2, h := 0, A := 13, D := 255, E := 1546,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide },
  { node := 3, h := 0, A := 14, D := 459, E := 3806,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide },
  { node := 4, h := 0, A := 17, D := 2295, E := 17978,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide },
  { node := 5, h := 0, A := 20, D := 20655, E := 203494,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide },
  { node := 6, h := 0, A := 24, D := 185895, E := 2164982,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide }
]
def highCertKeys_h1a3 : List (Nat × Nat) := highCerts_h1a3.map highCertKey


theorem highCertKey_complete_fin_h1a3 :
    ∀ n : Fin 7, 1 ≤ n.val →
      ∀ h : Fin ((nodeAt_h1a3 n.val).r+1),
        (n.val,h.val) ∈ highCertKeys_h1a3 := by
  decide


theorem highCertKey_complete_h1a3 (n h : Nat)
    (hn : 1 ≤ n) (hn' : n < 7)
    (hh : h ≤ (nodeAt_h1a3 n).r) :
    (n,h) ∈ highCertKeys_h1a3 := by
  exact highCertKey_complete_fin_h1a3 ⟨n,hn'⟩ hn ⟨h, by simpa using Nat.lt_succ_of_le hh⟩

def highCertTripleKeys_h1a3 : List (Nat × Nat × Nat) :=
  highCerts_h1a3.map highCertTripleKey

theorem highCertCutoffKey_complete_fin_h1a3 :
    ∀ n : Fin 7, 1 ≤ n.val →
      ∀ h : Fin ((nodeAt_h1a3 n.val).r+1),
        (n.val,h.val,cutoff_h1a3 n.val h.val) ∈ highCertTripleKeys_h1a3 := by
  decide

theorem highCertCutoff_complete_h1a3 (n h : Nat)
    (hn : 1 ≤ n) (hn' : n < 7)
    (hh : h ≤ (nodeAt_h1a3 n).r) :
    ∃ cert, cert ∈ highCerts_h1a3 ∧ cert.node=n ∧
      cert.h=h ∧ cert.A=cutoff_h1a3 n h := by
  have hkey := highCertCutoffKey_complete_fin_h1a3 ⟨n,hn'⟩ hn ⟨h, by simpa using Nat.lt_succ_of_le hh⟩
  exact highCertTriple_mem_of_key hkey


def valCerts_h1a3 : List (ValCert residues_h1a3 period_h1a3 nodeAt_h1a3) :=
[
  { node := 1, modulus := 9, base := 5, target := 155,
    «matches» := by decide, offset_bound := by decide, coefficient_valuation := by decide,
    nohit := val_nohit_h1a3_n1, period := val_period_h1a3_n1 },
  { node := 2, modulus := 9, base := 7, target := 773,
    «matches» := by decide, offset_bound := by decide, coefficient_valuation := by decide,
    nohit := val_nohit_h1a3_n2, period := val_period_h1a3_n2 },
  { node := 3, modulus := 81, base := 8, target := 1903,
    «matches» := by decide, offset_bound := by decide, coefficient_valuation := by decide,
    nohit := val_nohit_h1a3_n3, period := val_period_h1a3_n3 },
  { node := 4, modulus := 81, base := 10, target := 8989,
    «matches» := by decide, offset_bound := by decide, coefficient_valuation := by decide,
    nohit := val_nohit_h1a3_n4, period := val_period_h1a3_n4 },
  { node := 5, modulus := 729, base := 13, target := 101747,
    «matches» := by decide, offset_bound := by decide, coefficient_valuation := by decide,
    nohit := val_nohit_h1a3_n5, period := val_period_h1a3_n5 },
  { node := 6, modulus := 6561, base := 16, target := 1082491,
    «matches» := by decide, offset_bound := by decide, coefficient_valuation := by decide,
    nohit := val_nohit_h1a3_n6, period := val_period_h1a3_n6 }
]
def valCertKeys_h1a3 : List Nat := valCerts_h1a3.map valCertKey


theorem valCertKey_complete_fin_h1a3 :
    ∀ n : Fin 7, 1 ≤ n.val → n.val ∈ valCertKeys_h1a3 := by
  decide


theorem valCertKey_complete_h1a3 (n : Nat)
    (hn : 1 ≤ n) (hn' : n < 7) :
    n ∈ valCertKeys_h1a3 := by
  exact valCertKey_complete_fin_h1a3 ⟨n,hn'⟩ hn


def lowRows_h3a6 : List (LowRowCert residues_h3a6 period_h3a6 nodeAt_h3a6) :=
[
  { node := 1, h := 0, a := 1, modulus := 17415, base := 11, shift := 0, target := 36635,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n1_h0_a1,
    period := low_period_h3a6_n1_h0_a1 },
  { node := 1, h := 0, a := 3, modulus := 59211, base := 11, shift := 0, target := 50567,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n1_h0_a3,
    period := low_period_h3a6_n1_h0_a3 },
  { node := 1, h := 0, a := 4, modulus := 114939, base := 11, shift := 0, target := 57533,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n1_h0_a4,
    period := low_period_h3a6_n1_h0_a4 },
  { node := 1, h := 0, a := 5, modulus := 226395, base := 11, shift := 0, target := 64499,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n1_h0_a5,
    period := low_period_h3a6_n1_h0_a5 },
  { node := 1, h := 0, a := 6, modulus := 449307, base := 11, shift := 0, target := 71465,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n1_h0_a6,
    period := low_period_h3a6_n1_h0_a6 },
  { node := 1, h := 0, a := 7, modulus := 895131, base := 11, shift := 0, target := 78431,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n1_h0_a7,
    period := low_period_h3a6_n1_h0_a7 },
  { node := 1, h := 0, a := 8, modulus := 1786779, base := 11, shift := 0, target := 85397,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n1_h0_a8,
    period := low_period_h3a6_n1_h0_a8 },
  { node := 1, h := 0, a := 9, modulus := 3570075, base := 11, shift := 0, target := 92363,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n1_h0_a9,
    period := low_period_h3a6_n1_h0_a9 },
  { node := 1, h := 0, a := 10, modulus := 7136667, base := 11, shift := 0, target := 99329,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n1_h0_a10,
    period := low_period_h3a6_n1_h0_a10 },
  { node := 1, h := 0, a := 11, modulus := 14269851, base := 11, shift := 0, target := 106295,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n1_h0_a11,
    period := low_period_h3a6_n1_h0_a11 },
  { node := 1, h := 0, a := 12, modulus := 28536219, base := 11, shift := 0, target := 113261,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n1_h0_a12,
    period := low_period_h3a6_n1_h0_a12 },
  { node := 1, h := 0, a := 13, modulus := 57068955, base := 11, shift := 0, target := 120227,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n1_h0_a13,
    period := low_period_h3a6_n1_h0_a13 },
  { node := 1, h := 0, a := 14, modulus := 114134427, base := 11, shift := 0, target := 127193,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n1_h0_a14,
    period := low_period_h3a6_n1_h0_a14 },
  { node := 1, h := 0, a := 15, modulus := 228265371, base := 11, shift := 0, target := 134159,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n1_h0_a15,
    period := low_period_h3a6_n1_h0_a15 },
  { node := 1, h := 0, a := 16, modulus := 456527259, base := 11, shift := 0, target := 141125,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n1_h0_a16,
    period := low_period_h3a6_n1_h0_a16 },
  { node := 1, h := 0, a := 17, modulus := 913051035, base := 11, shift := 0, target := 148091,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n1_h0_a17,
    period := low_period_h3a6_n1_h0_a17 },
  { node := 2, h := 0, a := 1, modulus := 156735, base := 14, shift := 0, target := 380155,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n2_h0_a1,
    period := low_period_h3a6_n2_h0_a1 },
  { node := 2, h := 0, a := 2, modulus := 282123, base := 14, shift := 0, target := 442849,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n2_h0_a2,
    period := low_period_h3a6_n2_h0_a2 },
  { node := 2, h := 0, a := 3, modulus := 532899, base := 14, shift := 0, target := 505543,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n2_h0_a3,
    period := low_period_h3a6_n2_h0_a3 },
  { node := 2, h := 0, a := 4, modulus := 1034451, base := 14, shift := 0, target := 568237,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n2_h0_a4,
    period := low_period_h3a6_n2_h0_a4 },
  { node := 2, h := 0, a := 5, modulus := 2037555, base := 14, shift := 0, target := 630931,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n2_h0_a5,
    period := low_period_h3a6_n2_h0_a5 },
  { node := 2, h := 0, a := 6, modulus := 4043763, base := 14, shift := 0, target := 693625,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n2_h0_a6,
    period := low_period_h3a6_n2_h0_a6 },
  { node := 2, h := 0, a := 7, modulus := 8056179, base := 14, shift := 0, target := 756319,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n2_h0_a7,
    period := low_period_h3a6_n2_h0_a7 },
  { node := 2, h := 0, a := 8, modulus := 16081011, base := 14, shift := 0, target := 819013,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n2_h0_a8,
    period := low_period_h3a6_n2_h0_a8 },
  { node := 2, h := 0, a := 9, modulus := 32130675, base := 14, shift := 0, target := 881707,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n2_h0_a9,
    period := low_period_h3a6_n2_h0_a9 },
  { node := 2, h := 0, a := 10, modulus := 64230003, base := 14, shift := 0, target := 944401,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n2_h0_a10,
    period := low_period_h3a6_n2_h0_a10 },
  { node := 2, h := 0, a := 11, modulus := 128428659, base := 14, shift := 0, target := 1007095,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n2_h0_a11,
    period := low_period_h3a6_n2_h0_a11 },
  { node := 2, h := 0, a := 12, modulus := 256825971, base := 14, shift := 0, target := 1069789,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n2_h0_a12,
    period := low_period_h3a6_n2_h0_a12 },
  { node := 2, h := 0, a := 13, modulus := 513620595, base := 14, shift := 0, target := 1132483,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n2_h0_a13,
    period := low_period_h3a6_n2_h0_a13 },
  { node := 2, h := 0, a := 14, modulus := 1027209843, base := 14, shift := 0, target := 1195177,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n2_h0_a14,
    period := low_period_h3a6_n2_h0_a14 },
  { node := 2, h := 0, a := 15, modulus := 2054388339, base := 14, shift := 0, target := 1257871,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n2_h0_a15,
    period := low_period_h3a6_n2_h0_a15 },
  { node := 2, h := 0, a := 16, modulus := 4108745331, base := 14, shift := 0, target := 1320565,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n2_h0_a16,
    period := low_period_h3a6_n2_h0_a16 },
  { node := 2, h := 0, a := 17, modulus := 8217459315, base := 14, shift := 0, target := 1383259,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n2_h0_a17,
    period := low_period_h3a6_n2_h0_a17 },
  { node := 2, h := 0, a := 18, modulus := 16434887283, base := 14, shift := 0, target := 1445953,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n2_h0_a18,
    period := low_period_h3a6_n2_h0_a18 },
  { node := 2, h := 0, a := 19, modulus := 32869743219, base := 14, shift := 0, target := 1508647,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n2_h0_a19,
    period := low_period_h3a6_n2_h0_a19 },
  { node := 2, h := 0, a := 20, modulus := 65739455091, base := 14, shift := 0, target := 1571341,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h3a6_n2_h0_a20,
    period := low_period_h3a6_n2_h0_a20 }
]
def lowRowKeys_h3a6 : List (Nat × Nat × Nat) := lowRows_h3a6.map lowRowKey


def nonrootEdgeKeys_h3a6 : List (Nat × Nat × Nat) := [⟨1, 0, 2⟩]


def cutoff_h3a6 (n h : Nat) : Nat :=
  match n, h with
  | 1, 0 => 18
  | 2, 0 => 21
  | _, _ => 0


theorem lowRowKey_complete_fin_h3a6 :
    ∀ n : Fin 3, 1 ≤ n.val →
      ∀ h : Fin ((nodeAt_h3a6 n.val).r+1),
        ∀ a : Fin (cutoff_h3a6 n.val h.val),
          1 ≤ a.val →
          (n.val,h.val,a.val) ∈ lowRowKeys_h3a6 ∨
            (n.val,h.val,a.val) ∈ nonrootEdgeKeys_h3a6 := by
  decide


theorem lowRowKey_complete_h3a6 (n h a : Nat)
    (hn : 1 ≤ n) (hn' : n < 3)
    (hh : h ≤ (nodeAt_h3a6 n).r)
    (ha : 1 ≤ a) (ha' : a < cutoff_h3a6 n h) :
    (n,h,a) ∈ lowRowKeys_h3a6 ∨ (n,h,a) ∈ nonrootEdgeKeys_h3a6 := by
  exact lowRowKey_complete_fin_h3a6 ⟨n,hn'⟩ hn ⟨h, by simpa using Nat.lt_succ_of_le hh⟩ ⟨a,ha'⟩ ha


def highCerts_h3a6 : List (HighCert nodeAt_h3a6) :=
[
  { node := 1, h := 0, A := 18, D := 3483, E := 40118,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide },
  { node := 2, h := 0, A := 21, D := 31347, E := 411502,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide }
]
def highCertKeys_h3a6 : List (Nat × Nat) := highCerts_h3a6.map highCertKey


theorem highCertKey_complete_fin_h3a6 :
    ∀ n : Fin 3, 1 ≤ n.val →
      ∀ h : Fin ((nodeAt_h3a6 n.val).r+1),
        (n.val,h.val) ∈ highCertKeys_h3a6 := by
  decide


theorem highCertKey_complete_h3a6 (n h : Nat)
    (hn : 1 ≤ n) (hn' : n < 3)
    (hh : h ≤ (nodeAt_h3a6 n).r) :
    (n,h) ∈ highCertKeys_h3a6 := by
  exact highCertKey_complete_fin_h3a6 ⟨n,hn'⟩ hn ⟨h, by simpa using Nat.lt_succ_of_le hh⟩

def highCertTripleKeys_h3a6 : List (Nat × Nat × Nat) :=
  highCerts_h3a6.map highCertTripleKey

theorem highCertCutoffKey_complete_fin_h3a6 :
    ∀ n : Fin 3, 1 ≤ n.val →
      ∀ h : Fin ((nodeAt_h3a6 n.val).r+1),
        (n.val,h.val,cutoff_h3a6 n.val h.val) ∈ highCertTripleKeys_h3a6 := by
  decide

theorem highCertCutoff_complete_h3a6 (n h : Nat)
    (hn : 1 ≤ n) (hn' : n < 3)
    (hh : h ≤ (nodeAt_h3a6 n).r) :
    ∃ cert, cert ∈ highCerts_h3a6 ∧ cert.node=n ∧
      cert.h=h ∧ cert.A=cutoff_h3a6 n h := by
  have hkey := highCertCutoffKey_complete_fin_h3a6 ⟨n,hn'⟩ hn ⟨h, by simpa using Nat.lt_succ_of_le hh⟩
  exact highCertTriple_mem_of_key hkey


def valCerts_h3a6 : List (ValCert residues_h3a6 period_h3a6 nodeAt_h3a6) :=
[
  { node := 1, modulus := 243, base := 10, target := 20059,
    «matches» := by decide, offset_bound := by decide, coefficient_valuation := by decide,
    nohit := val_nohit_h3a6_n1, period := val_period_h3a6_n1 },
  { node := 2, modulus := 2187, base := 13, target := 205751,
    «matches» := by decide, offset_bound := by decide, coefficient_valuation := by decide,
    nohit := val_nohit_h3a6_n2, period := val_period_h3a6_n2 }
]
def valCertKeys_h3a6 : List Nat := valCerts_h3a6.map valCertKey


theorem valCertKey_complete_fin_h3a6 :
    ∀ n : Fin 3, 1 ≤ n.val → n.val ∈ valCertKeys_h3a6 := by
  decide


theorem valCertKey_complete_h3a6 (n : Nat)
    (hn : 1 ≤ n) (hn' : n < 3) :
    n ∈ valCertKeys_h3a6 := by
  exact valCertKey_complete_fin_h3a6 ⟨n,hn'⟩ hn


def lowRows_h7a2 : List (LowRowCert residues_h7a2 period_h7a2 nodeAt_h7a2) :=
[
  { node := 1, h := 0, a := 1, modulus := 98415, base := 11, shift := 0, target := 39227,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a2_n1_h0_a1,
    period := low_period_h7a2_n1_h0_a1 },
  { node := 1, h := 0, a := 2, modulus := 177147, base := 11, shift := 0, target := 78593,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a2_n1_h0_a2,
    period := low_period_h7a2_n1_h0_a2 },
  { node := 1, h := 0, a := 3, modulus := 334611, base := 11, shift := 0, target := 117959,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a2_n1_h0_a3,
    period := low_period_h7a2_n1_h0_a3 },
  { node := 1, h := 0, a := 4, modulus := 649539, base := 11, shift := 0, target := 157325,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a2_n1_h0_a4,
    period := low_period_h7a2_n1_h0_a4 },
  { node := 1, h := 0, a := 5, modulus := 1279395, base := 11, shift := 0, target := 196691,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a2_n1_h0_a5,
    period := low_period_h7a2_n1_h0_a5 },
  { node := 1, h := 0, a := 6, modulus := 2539107, base := 11, shift := 0, target := 236057,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a2_n1_h0_a6,
    period := low_period_h7a2_n1_h0_a6 },
  { node := 1, h := 0, a := 7, modulus := 5058531, base := 11, shift := 0, target := 275423,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a2_n1_h0_a7,
    period := low_period_h7a2_n1_h0_a7 },
  { node := 1, h := 0, a := 8, modulus := 10097379, base := 11, shift := 0, target := 314789,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a2_n1_h0_a8,
    period := low_period_h7a2_n1_h0_a8 },
  { node := 1, h := 0, a := 9, modulus := 20175075, base := 11, shift := 0, target := 354155,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a2_n1_h0_a9,
    period := low_period_h7a2_n1_h0_a9 },
  { node := 1, h := 0, a := 10, modulus := 40330467, base := 11, shift := 0, target := 393521,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a2_n1_h0_a10,
    period := low_period_h7a2_n1_h0_a10 },
  { node := 1, h := 0, a := 11, modulus := 80641251, base := 11, shift := 0, target := 432887,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a2_n1_h0_a11,
    period := low_period_h7a2_n1_h0_a11 },
  { node := 1, h := 0, a := 12, modulus := 161262819, base := 11, shift := 0, target := 472253,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a2_n1_h0_a12,
    period := low_period_h7a2_n1_h0_a12 },
  { node := 1, h := 0, a := 13, modulus := 322505955, base := 11, shift := 0, target := 511619,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a2_n1_h0_a13,
    period := low_period_h7a2_n1_h0_a13 },
  { node := 1, h := 0, a := 14, modulus := 644992227, base := 11, shift := 0, target := 550985,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a2_n1_h0_a14,
    period := low_period_h7a2_n1_h0_a14 },
  { node := 1, h := 0, a := 15, modulus := 1289964771, base := 11, shift := 0, target := 590351,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a2_n1_h0_a15,
    period := low_period_h7a2_n1_h0_a15 },
  { node := 1, h := 0, a := 16, modulus := 2579909859, base := 11, shift := 0, target := 629717,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a2_n1_h0_a16,
    period := low_period_h7a2_n1_h0_a16 },
  { node := 1, h := 0, a := 17, modulus := 5159800035, base := 11, shift := 0, target := 669083,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a2_n1_h0_a17,
    period := low_period_h7a2_n1_h0_a17 },
  { node := 1, h := 0, a := 18, modulus := 10319580387, base := 11, shift := 0, target := 708449,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a2_n1_h0_a18,
    period := low_period_h7a2_n1_h0_a18 },
  { node := 1, h := 0, a := 19, modulus := 20639141091, base := 11, shift := 0, target := 747815,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a2_n1_h0_a19,
    period := low_period_h7a2_n1_h0_a19 }
]
def lowRowKeys_h7a2 : List (Nat × Nat × Nat) := lowRows_h7a2.map lowRowKey


def nonrootEdgeKeys_h7a2 : List (Nat × Nat × Nat) := []


def cutoff_h7a2 (n h : Nat) : Nat :=
  match n, h with
  | 1, 0 => 20
  | _, _ => 0


theorem lowRowKey_complete_fin_h7a2 :
    ∀ n : Fin 2, 1 ≤ n.val →
      ∀ h : Fin ((nodeAt_h7a2 n.val).r+1),
        ∀ a : Fin (cutoff_h7a2 n.val h.val),
          1 ≤ a.val →
          (n.val,h.val,a.val) ∈ lowRowKeys_h7a2 ∨
            (n.val,h.val,a.val) ∈ nonrootEdgeKeys_h7a2 := by
  decide


theorem lowRowKey_complete_h7a2 (n h a : Nat)
    (hn : 1 ≤ n) (hn' : n < 2)
    (hh : h ≤ (nodeAt_h7a2 n).r)
    (ha : 1 ≤ a) (ha' : a < cutoff_h7a2 n h) :
    (n,h,a) ∈ lowRowKeys_h7a2 ∨ (n,h,a) ∈ nonrootEdgeKeys_h7a2 := by
  exact lowRowKey_complete_fin_h7a2 ⟨n,hn'⟩ hn ⟨h, by simpa using Nat.lt_succ_of_le hh⟩ ⟨a,ha'⟩ ha


def highCerts_h7a2 : List (HighCert nodeAt_h7a2) :=
[
  { node := 1, h := 0, A := 20, D := 19683, E := 58910,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide }
]
def highCertKeys_h7a2 : List (Nat × Nat) := highCerts_h7a2.map highCertKey


theorem highCertKey_complete_fin_h7a2 :
    ∀ n : Fin 2, 1 ≤ n.val →
      ∀ h : Fin ((nodeAt_h7a2 n.val).r+1),
        (n.val,h.val) ∈ highCertKeys_h7a2 := by
  decide


theorem highCertKey_complete_h7a2 (n h : Nat)
    (hn : 1 ≤ n) (hn' : n < 2)
    (hh : h ≤ (nodeAt_h7a2 n).r) :
    (n,h) ∈ highCertKeys_h7a2 := by
  exact highCertKey_complete_fin_h7a2 ⟨n,hn'⟩ hn ⟨h, by simpa using Nat.lt_succ_of_le hh⟩

def highCertTripleKeys_h7a2 : List (Nat × Nat × Nat) :=
  highCerts_h7a2.map highCertTripleKey

theorem highCertCutoffKey_complete_fin_h7a2 :
    ∀ n : Fin 2, 1 ≤ n.val →
      ∀ h : Fin ((nodeAt_h7a2 n.val).r+1),
        (n.val,h.val,cutoff_h7a2 n.val h.val) ∈ highCertTripleKeys_h7a2 := by
  decide

theorem highCertCutoff_complete_h7a2 (n h : Nat)
    (hn : 1 ≤ n) (hn' : n < 2)
    (hh : h ≤ (nodeAt_h7a2 n).r) :
    ∃ cert, cert ∈ highCerts_h7a2 ∧ cert.node=n ∧
      cert.h=h ∧ cert.A=cutoff_h7a2 n h := by
  have hkey := highCertCutoffKey_complete_fin_h7a2 ⟨n,hn'⟩ hn ⟨h, by simpa using Nat.lt_succ_of_le hh⟩
  exact highCertTriple_mem_of_key hkey


def valCerts_h7a2 : List (ValCert residues_h7a2 period_h7a2 nodeAt_h7a2) :=
[
  { node := 1, modulus := 59049, base := 10, target := 29455,
    «matches» := by decide, offset_bound := by decide, coefficient_valuation := by decide,
    nohit := val_nohit_h7a2_n1, period := val_period_h7a2_n1 }
]
def valCertKeys_h7a2 : List Nat := valCerts_h7a2.map valCertKey


theorem valCertKey_complete_fin_h7a2 :
    ∀ n : Fin 2, 1 ≤ n.val → n.val ∈ valCertKeys_h7a2 := by
  decide


theorem valCertKey_complete_h7a2 (n : Nat)
    (hn : 1 ≤ n) (hn' : n < 2) :
    n ∈ valCertKeys_h7a2 := by
  exact valCertKey_complete_fin_h7a2 ⟨n,hn'⟩ hn


def lowRows_h7a4 : List (LowRowCert residues_h7a4 period_h7a4 nodeAt_h7a4) :=
[
  { node := 1, h := 0, a := 1, modulus := 360855, base := 13, shift := 0, target := 430283,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a4_n1_h0_a1,
    period := low_period_h7a4_n1_h0_a1 },
  { node := 1, h := 0, a := 2, modulus := 649539, base := 13, shift := 0, target := 574625,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a4_n1_h0_a2,
    period := low_period_h7a4_n1_h0_a2 },
  { node := 1, h := 0, a := 3, modulus := 1226907, base := 13, shift := 0, target := 718967,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a4_n1_h0_a3,
    period := low_period_h7a4_n1_h0_a3 },
  { node := 1, h := 0, a := 4, modulus := 2381643, base := 13, shift := 0, target := 863309,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a4_n1_h0_a4,
    period := low_period_h7a4_n1_h0_a4 },
  { node := 1, h := 0, a := 5, modulus := 4691115, base := 13, shift := 0, target := 1007651,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a4_n1_h0_a5,
    period := low_period_h7a4_n1_h0_a5 },
  { node := 1, h := 0, a := 6, modulus := 9310059, base := 13, shift := 0, target := 1151993,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a4_n1_h0_a6,
    period := low_period_h7a4_n1_h0_a6 },
  { node := 1, h := 0, a := 7, modulus := 18547947, base := 13, shift := 0, target := 1296335,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a4_n1_h0_a7,
    period := low_period_h7a4_n1_h0_a7 },
  { node := 1, h := 0, a := 8, modulus := 37023723, base := 13, shift := 0, target := 1440677,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a4_n1_h0_a8,
    period := low_period_h7a4_n1_h0_a8 },
  { node := 1, h := 0, a := 9, modulus := 73975275, base := 13, shift := 0, target := 1585019,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a4_n1_h0_a9,
    period := low_period_h7a4_n1_h0_a9 },
  { node := 1, h := 0, a := 10, modulus := 147878379, base := 13, shift := 0, target := 1729361,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a4_n1_h0_a10,
    period := low_period_h7a4_n1_h0_a10 },
  { node := 1, h := 0, a := 11, modulus := 295684587, base := 13, shift := 0, target := 1873703,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a4_n1_h0_a11,
    period := low_period_h7a4_n1_h0_a11 },
  { node := 1, h := 0, a := 12, modulus := 591297003, base := 13, shift := 0, target := 2018045,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a4_n1_h0_a12,
    period := low_period_h7a4_n1_h0_a12 },
  { node := 1, h := 0, a := 13, modulus := 1182521835, base := 13, shift := 0, target := 2162387,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a4_n1_h0_a13,
    period := low_period_h7a4_n1_h0_a13 },
  { node := 1, h := 0, a := 14, modulus := 2364971499, base := 13, shift := 0, target := 2306729,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a4_n1_h0_a14,
    period := low_period_h7a4_n1_h0_a14 },
  { node := 1, h := 0, a := 15, modulus := 4729870827, base := 13, shift := 0, target := 2451071,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a4_n1_h0_a15,
    period := low_period_h7a4_n1_h0_a15 },
  { node := 1, h := 0, a := 16, modulus := 9459669483, base := 13, shift := 0, target := 2595413,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a4_n1_h0_a16,
    period := low_period_h7a4_n1_h0_a16 },
  { node := 1, h := 0, a := 17, modulus := 18919266795, base := 13, shift := 0, target := 2739755,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a4_n1_h0_a17,
    period := low_period_h7a4_n1_h0_a17 },
  { node := 1, h := 0, a := 18, modulus := 37838461419, base := 13, shift := 0, target := 2884097,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a4_n1_h0_a18,
    period := low_period_h7a4_n1_h0_a18 },
  { node := 1, h := 0, a := 19, modulus := 75676850667, base := 13, shift := 0, target := 3028439,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a4_n1_h0_a19,
    period := low_period_h7a4_n1_h0_a19 },
  { node := 1, h := 0, a := 20, modulus := 151353629163, base := 13, shift := 0, target := 3172781,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a4_n1_h0_a20,
    period := low_period_h7a4_n1_h0_a20 },
  { node := 1, h := 0, a := 21, modulus := 302707186155, base := 13, shift := 0, target := 3317123,
    modulus_gt_one := by decide, «matches» := by decide,
    nohit := low_nohit_h7a4_n1_h0_a21,
    period := low_period_h7a4_n1_h0_a21 }
]
def lowRowKeys_h7a4 : List (Nat × Nat × Nat) := lowRows_h7a4.map lowRowKey


def nonrootEdgeKeys_h7a4 : List (Nat × Nat × Nat) := []


def cutoff_h7a4 (n h : Nat) : Nat :=
  match n, h with
  | 1, 0 => 22
  | _, _ => 0


theorem lowRowKey_complete_fin_h7a4 :
    ∀ n : Fin 2, 1 ≤ n.val →
      ∀ h : Fin ((nodeAt_h7a4 n.val).r+1),
        ∀ a : Fin (cutoff_h7a4 n.val h.val),
          1 ≤ a.val →
          (n.val,h.val,a.val) ∈ lowRowKeys_h7a4 ∨
            (n.val,h.val,a.val) ∈ nonrootEdgeKeys_h7a4 := by
  decide


theorem lowRowKey_complete_h7a4 (n h a : Nat)
    (hn : 1 ≤ n) (hn' : n < 2)
    (hh : h ≤ (nodeAt_h7a4 n).r)
    (ha : 1 ≤ a) (ha' : a < cutoff_h7a4 n h) :
    (n,h,a) ∈ lowRowKeys_h7a4 ∨ (n,h,a) ∈ nonrootEdgeKeys_h7a4 := by
  exact lowRowKey_complete_fin_h7a4 ⟨n,hn'⟩ hn ⟨h, by simpa using Nat.lt_succ_of_le hh⟩ ⟨a,ha'⟩ ha


def highCerts_h7a4 : List (HighCert nodeAt_h7a4) :=
[
  { node := 1, h := 0, A := 22, D := 72171, E := 502454,
    cutoff_lower := by decide, «matches» := by decide, base_gap := by decide }
]
def highCertKeys_h7a4 : List (Nat × Nat) := highCerts_h7a4.map highCertKey


theorem highCertKey_complete_fin_h7a4 :
    ∀ n : Fin 2, 1 ≤ n.val →
      ∀ h : Fin ((nodeAt_h7a4 n.val).r+1),
        (n.val,h.val) ∈ highCertKeys_h7a4 := by
  decide


theorem highCertKey_complete_h7a4 (n h : Nat)
    (hn : 1 ≤ n) (hn' : n < 2)
    (hh : h ≤ (nodeAt_h7a4 n).r) :
    (n,h) ∈ highCertKeys_h7a4 := by
  exact highCertKey_complete_fin_h7a4 ⟨n,hn'⟩ hn ⟨h, by simpa using Nat.lt_succ_of_le hh⟩

def highCertTripleKeys_h7a4 : List (Nat × Nat × Nat) :=
  highCerts_h7a4.map highCertTripleKey

theorem highCertCutoffKey_complete_fin_h7a4 :
    ∀ n : Fin 2, 1 ≤ n.val →
      ∀ h : Fin ((nodeAt_h7a4 n.val).r+1),
        (n.val,h.val,cutoff_h7a4 n.val h.val) ∈ highCertTripleKeys_h7a4 := by
  decide

theorem highCertCutoff_complete_h7a4 (n h : Nat)
    (hn : 1 ≤ n) (hn' : n < 2)
    (hh : h ≤ (nodeAt_h7a4 n).r) :
    ∃ cert, cert ∈ highCerts_h7a4 ∧ cert.node=n ∧
      cert.h=h ∧ cert.A=cutoff_h7a4 n h := by
  have hkey := highCertCutoffKey_complete_fin_h7a4 ⟨n,hn'⟩ hn ⟨h, by simpa using Nat.lt_succ_of_le hh⟩
  exact highCertTriple_mem_of_key hkey


def valCerts_h7a4 : List (ValCert residues_h7a4 period_h7a4 nodeAt_h7a4) :=
[
  { node := 1, modulus := 19683, base := 12, target := 251227,
    «matches» := by decide, offset_bound := by decide, coefficient_valuation := by decide,
    nohit := val_nohit_h7a4_n1, period := val_period_h7a4_n1 }
]
def valCertKeys_h7a4 : List Nat := valCerts_h7a4.map valCertKey


theorem valCertKey_complete_fin_h7a4 :
    ∀ n : Fin 2, 1 ≤ n.val → n.val ∈ valCertKeys_h7a4 := by
  decide


theorem valCertKey_complete_h7a4 (n : Nat)
    (hn : 1 ≤ n) (hn' : n < 2) :
    n ∈ valCertKeys_h7a4 := by
  exact valCertKey_complete_fin_h7a4 ⟨n,hn'⟩ hn


#print axioms lowRow_no_generic_progression
#print axioms lowRow_no_generic
#print axioms affine_node_hidden_bound_from_cert

end SheepPower1458
