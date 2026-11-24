import Cert0
import Cert1
import Cert2
import Cert3
import Cert4
import Cert5
import Cert6
import Cert7
import Cert8
import Cert9
import Cert10
import Cert11
import Cert12
import Cert13
import Cert14
import Cert15
import Cert16
import Cert17
import Cert18
import Cert19
import Cert20
import Cert21
import Cert22
import Cert23
import Cert24
import Cert25
import Cert26
import Cert27
import Cert28
import Cert29
import Cert30
import Cert31
import Cert32
import Cert33
import Cert34
import Cert35
import Cert36
import Cert37
import Cert38
open BB6.Agent28BitCarry
namespace BB6.Agent28ModScreen
def certs : List (Nat × Nat) := cert0 ++ cert1 ++ cert2 ++ cert3 ++ cert4 ++ cert5 ++ cert6 ++ cert7 ++ cert8 ++ cert9 ++ cert10 ++ cert11 ++ cert12 ++ cert13 ++ cert14 ++ cert15 ++ cert16 ++ cert17 ++ cert18 ++ cert19 ++ cert20 ++ cert21 ++ cert22 ++ cert23 ++ cert24 ++ cert25 ++ cert26 ++ cert27 ++ cert28 ++ cert29 ++ cert30 ++ cert31 ++ cert32 ++ cert33 ++ cert34 ++ cert35 ++ cert36 ++ cert37 ++ cert38
theorem certs_ok : certs.all checkCert = true := by
  simp only [certs, List.all_append, cert0_ok, cert1_ok, cert2_ok, cert3_ok, cert4_ok, cert5_ok, cert6_ok, cert7_ok, cert8_ok, cert9_ok, cert10_ok, cert11_ok, cert12_ok, cert13_ok, cert14_ok, cert15_ok, cert16_ok, cert17_ok, cert18_ok, cert19_ok, cert20_ok, cert21_ok, cert22_ok, cert23_ok, cert24_ok, cert25_ok, cert26_ok, cert27_ok, cert28_ok, cert29_ok, cert30_ok, cert31_ok, cert32_ok, cert33_ok, cert34_ok, cert35_ok, cert36_ok, cert37_ok, cert38_ok, Bool.and_self]

def survivor (n : Nat) : Bool := [30,286,350,1614,2990,3342].contains n

def certIndices (p : Nat × Nat) : List Nat :=
  let r := p.1
  let K := p.2+1
  let raw := if K≤14 then (List.range (10000 / 2^K+1)).map (fun t => r+2^K*t) else [r]
  raw.filter (fun n => decide (14≤n ∧ n≤10000 ∧ K≤n) && (n%2==0) && !survivor n)

def targetIndices : List Nat := (List.range 10001).filter (fun n => decide (14≤n) && n%2==0 && !survivor n)

def bits : List Nat → Nat
  | [] => 0
  | n::ns => (1 <<< n) ||| bits ns

theorem bit_mem (ns : List Nat) (n : Nat) : (bits ns).testBit n=true ↔ n∈ns := by
  induction ns with
  | nil => simp [bits]
  | cons x xs ih =>
      simp only [bits, Nat.testBit_or, Bool.or_eq_true, ih, List.mem_cons]
      have h : (1 <<< x).testBit n=true ↔ n=x := by
        rw [Nat.one_shiftLeft]
        simp [Nat.testBit_two_pow, eq_comm]
      rw [h]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem coverage_ok : bits (certs.flatMap certIndices) = bits targetIndices := by decide

theorem certificate_of_non_survivor (n : Nat) (hlo : 14≤n) (hhi : n≤10000)
    (he : n%2=0) (hs : survivor n=false) :
    ∃ r k, r%2=0 ∧ k+1≤n ∧ (∃ t, n=r+2^(k+1)*t) ∧ listRun r 1 [((r+2)/2)] k=[] := by
  have ht : n∈targetIndices := by
    simp [targetIndices, hlo, he, hs]; omega
  have hbit := (bit_mem targetIndices n).2 ht
  rw [← coverage_ok] at hbit
  obtain ⟨p,hp,hcover⟩ := List.mem_flatMap.mp ((bit_mem _ n).1 hbit)
  have hvalid := checkCert_sound p (List.all_eq_true.mp certs_ok p hp)
  obtain ⟨r,k⟩ := p
  simp only [certIndices, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq,
    Prod.fst, Prod.snd] at hcover
  refine ⟨r,k,hvalid.1,hcover.2.1.1.2.2,?_,hvalid.2⟩
  by_cases hK : k+1≤14
  · rw [if_pos hK] at hcover
    obtain ⟨t,_,h⟩ := List.mem_map.mp hcover.1
    exact ⟨t,h.symm⟩
  · rw [if_neg hK] at hcover
    have h : n=r := List.mem_singleton.mp hcover.1
    exact ⟨0,by simp [h]⟩

#print axioms certificate_of_non_survivor
end BB6.Agent28ModScreen
