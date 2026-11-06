import BB429InverseKernel16
import Lean.Elab.Tactic.Omega

namespace BB429SplitSieve
open BB429NewResidue BB429Kernel16
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

/-- Seventeen-bit terminal counter sieve. The lists are strict
    subfamilies of the prior 58/16384 necessary true-root gate.
    Every certificate is evaluated in Lean's kernel via 'decide'. -/
def part0 : List Nat := [337, 1097, 1973, 2057, 2165, 2513, 2685, 3145, 3189, 4169, 4661, 4733, 5045, 5457, 6345, 6389, 6709, 7093, 7933, 8757, 9041, 9425, 11089, 12213, 12405, 12533, 12925, 13309, 13321, 14409, 14901, 15101, 16009]
theorem part0_certificate :
    part0.all (fun r => cert 20 ⟨262144,r,524288,2*r-1⟩) = true := by decide
theorem part0_count : part0.length = 33 := by decide

def part1 : List Nat := [16393, 16721, 16849, 18173, 18357, 18441, 18549, 18769, 18897, 19069, 19281, 19573, 20725, 21045, 21117, 21429, 22525, 22729, 23093, 23477, 24201, 24317, 24445, 25141, 25425, 25809, 26825, 26833, 27089, 27985, 28541, 28597, 28789, 28873, 28881, 28917, 29309, 29521, 29693, 30589, 31485, 31741, 32393]
theorem part1_certificate :
    part1.all (fun r => cert 20 ⟨262144,r,524288,2*r-1⟩) = true := by decide
theorem part1_count : part1.length = 43 := by decide

def part2 : List Nat := [32777, 33105, 33533, 33909, 34557, 34741, 34825, 35153, 35281, 35453, 35665, 35849, 35913, 35957, 36049, 36937, 37109, 37429, 37501, 37813, 38225, 38909, 39113, 39157, 39477, 39861, 40585, 40701, 40829, 41525, 41809, 43209, 43217, 43473, 43857, 44369, 44981, 45173, 45257, 45265, 45301, 45693, 46089, 46973, 47177, 47669, 47869, 48125, 48777]
theorem part2_certificate :
    part2.all (fun r => cert 20 ⟨262144,r,524288,2*r-1⟩) = true := by decide
theorem part2_count : part2.length = 49 := by decide

def part3 : List Nat := [49161, 49617, 50825, 50941, 51125, 51209, 51317, 51537, 51665, 51837, 52049, 52341, 53321, 53493, 53813, 55497, 56245, 56969, 57085, 57213, 58577, 59593, 59601, 59857, 60753, 61309, 61649, 62289, 62461, 62473, 63561, 64509, 65161]
theorem part3_certificate :
    part3.all (fun r => cert 20 ⟨262144,r,524288,2*r-1⟩) = true := by decide
theorem part3_count : part3.length = 33 := by decide

def part4 : List Nat := [65545, 66001, 66301, 66633, 66677, 67325, 67701, 67921, 68433, 68617, 68681, 68725, 68817, 69705, 69877, 70197, 70269, 70581, 70993, 71881, 71925, 72245, 73353, 73469, 73597, 74293, 74577, 74961, 75977, 75985, 76241, 76625, 77137, 77693, 77749, 77941, 78033, 78069, 78461, 78673, 78857, 79945, 80637, 81545]
theorem part4_certificate :
    part4.all (fun r => cert 20 ⟨262144,r,524288,2*r-1⟩) = true := by decide
theorem part4_count : part4.length = 44 := by decide

def part5 : List Nat := [82257, 82685, 83017, 83061, 83709, 83893, 83977, 84085, 84305, 84433, 84605, 85001, 85065, 86089, 86261, 86581, 88061, 88309, 89013, 89737, 89853, 89981, 90677, 90961, 91345, 92361, 92369, 92625, 93009, 94077, 94325, 94417, 94453, 94845, 95057, 95229, 96125, 96821, 97021, 97277, 97929]
theorem part5_certificate :
    part5.all (fun r => cert 20 ⟨262144,r,524288,2*r-1⟩) = true := by decide
theorem part5_count : part5.length = 41 := by decide

def part6 : List Nat := [98313, 98769, 99069, 99401, 99977, 100093, 100277, 100469, 100689, 101201, 101385, 101449, 101493, 101585, 102473, 102645, 103037, 103761, 104649, 104693, 105013, 106365, 107061, 107345, 107729, 108745, 108753, 109009, 109393, 109905, 110461, 110517, 110709, 110801, 110837, 111229, 111613, 111625, 112509, 112713, 113205, 114313]
theorem part6_certificate :
    part6.all (fun r => cert 20 ⟨262144,r,524288,2*r-1⟩) = true := by decide
theorem part6_count : part6.length = 42 := by decide

def part7 : List Nat := [115025, 115153, 115785, 115829, 116477, 116661, 116745, 116853, 117073, 117201, 117769, 117833, 117969, 118857, 119029, 119421, 119733, 120145, 120829, 121077, 121781, 122621, 122749, 123445, 123729, 125129, 125393, 125777, 126289, 127093, 127177, 127185, 127221, 127613, 127825, 127997, 128009, 128893, 129589, 129789, 130045]
theorem part7_certificate :
    part7.all (fun r => cert 20 ⟨262144,r,524288,2*r-1⟩) = true := by decide
theorem part7_count : part7.length = 41 := by decide

def part8 : List Nat := [131081, 131409, 131837, 132213, 132745, 132861, 133045, 133237, 133757, 133969, 134153, 134217, 134261, 134353, 135413, 135733, 135805, 136117, 136529, 137213, 137417, 137461, 137781, 138165, 138889, 139005, 139829, 140113, 140497, 141513, 141521, 141777, 142161, 142673, 143229, 143285, 143477, 143561, 143569, 143605, 143997, 144209, 144381, 144393, 145481, 145973, 146429, 147453]
theorem part8_certificate :
    part8.all (fun r => cert 20 ⟨262144,r,524288,2*r-1⟩) = true := by decide
theorem part8_count : part8.length = 48 := by decide

def part9 : List Nat := [147465, 147793, 148221, 148553, 148597, 149129, 149245, 149429, 149513, 149841, 149969, 150353, 150537, 150737, 151625, 151797, 152501, 152913, 154165, 154549, 155389, 155517, 157905, 158161, 158545, 159057, 159613, 159669, 159945, 159953, 160593, 160777, 161865, 162357, 162557, 162813]
theorem part9_certificate :
    part9.all (fun r => cert 20 ⟨262144,r,524288,2*r-1⟩) = true := by decide
theorem part9_count : part9.length = 36 := by decide

def part10 : List Nat := [164177, 164305, 164605, 164937, 164981, 165813, 165897, 166005, 166985, 167029, 167121, 168009, 168501, 168573, 168885, 169297, 169981, 170185, 170229, 170549, 170933, 171657, 171773, 172597, 173265, 174289, 174929, 175441, 175997, 176053, 176245, 176373, 176765, 176977, 177149, 177161, 178249, 178941, 179849, 180221]
theorem part10_certificate :
    part10.all (fun r => cert 20 ⟨262144,r,524288,2*r-1⟩) = true := by decide
theorem part10_count : part10.length = 40 := by decide

def part11 : List Nat := [180233, 180561, 180989, 181321, 181365, 182013, 182281, 182609, 182737, 182909, 183121, 183305, 183369, 183505, 184393, 184885, 184957, 185269, 185681, 186365, 186569, 186933, 187317, 188041, 188285, 189265, 189649, 190673, 190929, 191313, 191825, 192381, 192437, 192713, 192721, 192757, 193149, 193361, 193533, 194429, 195125, 195325, 195581, 196233]
theorem part11_certificate :
    part11.all (fun r => cert 20 ⟨262144,r,524288,2*r-1⟩) = true := by decide
theorem part11_count : part11.length = 44 := by decide

def part12 : List Nat := [196617, 196945, 197073, 197373, 197705, 197749, 198281, 198581, 198665, 198993, 199121, 199505, 199689, 199753, 199797, 199889, 200777, 200949, 201341, 202065, 202749, 202953, 202997, 203317, 203701, 204425, 204669, 205365, 207049, 207057, 207313, 207697, 208209, 208765, 208821, 209013, 209097, 209533, 209745, 209917, 209929, 210813, 211017, 211509, 211709, 211965, 212617, 212989]
theorem part12_certificate :
    part12.all (fun r => cert 20 ⟨262144,r,524288,2*r-1⟩) = true := by decide
theorem part12_count : part12.length = 48 := by decide

def part13 : List Nat := [213001, 213457, 214089, 214133, 214665, 214781, 215049, 215157, 215377, 215505, 215889, 216073, 216137, 216181, 217161, 217653, 217725, 218037, 218449, 219133, 219337, 220085, 220809, 221053, 221749, 222033, 222417, 223433, 223697, 224593, 225481, 225489, 225525, 226129, 226301, 226313, 227197, 227401, 227893, 228349, 229001]
theorem part13_certificate :
    part13.all (fun r => cert 20 ⟨262144,r,524288,2*r-1⟩) = true := by decide
theorem part13_count : part13.length = 41 := by decide

def part14 : List Nat := [229385, 229713, 230141, 230473, 230517, 231049, 231165, 231541, 231889, 232061, 232273, 232457, 232521, 232565, 232657, 233717, 234037, 234109, 234421, 234833, 235517, 235721, 235765, 236085, 237193, 237309, 237437, 238133, 238417, 238801, 239817, 240465, 241533, 241589, 241781, 241873, 242301, 242513, 242685, 242697, 243785, 244277, 244477, 244733, 245757]
theorem part14_certificate :
    part14.all (fun r => cert 20 ⟨262144,r,524288,2*r-1⟩) = true := by decide
theorem part14_count : part14.length = 45 := by decide

def part15 : List Nat := [245769, 246097, 246525, 246857, 246901, 247433, 247549, 247733, 247817, 247925, 248145, 248273, 248657, 248841, 248949, 249041, 250101, 250421, 250493, 250805, 251901, 252469, 252853, 253577, 253693, 253821, 254517, 254801, 255185, 256201, 256209, 256465, 257917, 257973, 258165, 258249, 258257, 258293, 258897, 259965, 260169, 260661, 260861, 261117, 261769]
theorem part15_certificate :
    part15.all (fun r => cert 20 ⟨262144,r,524288,2*r-1⟩) = true := by decide
theorem part15_count : part15.length = 45 := by decide

/-- Precisely 673 explicitly certified, pairwise distinct representatives
    (listed in increasing order in disjoint 16384-sized blocks). -/
def excluded : List Nat := part0 ++ part1 ++ part2 ++ part3 ++ part4 ++ part5 ++ part6 ++ part7 ++ part8 ++ part9 ++ part10 ++ part11 ++ part12 ++ part13 ++ part14 ++ part15

theorem excluded_count : excluded.length = 673 := by
  simp [excluded, List.length_append, part0_count, part1_count, part2_count, part3_count, part4_count, part5_count, part6_count, part7_count, part8_count, part9_count, part10_count, part11_count, part12_count, part13_count, part14_count, part15_count]

theorem excluded_certificate :
    excluded.all (fun r => cert 20 ⟨262144,r,524288,2*r-1⟩) = true := by
  simp only [excluded, List.all_append]
  simp [part0_certificate, part1_certificate, part2_certificate, part3_certificate, part4_certificate, part5_certificate, part6_certificate, part7_certificate, part8_certificate, part9_certificate, part10_certificate, part11_certificate, part12_certificate, part13_certificate, part14_certificate, part15_certificate]

theorem excluded_positive : excluded.all (fun r => decide (0<r)) = true := by
  decide

private theorem member_cert (r : Nat) (hr : r ∈ excluded) :
    cert 20 ⟨262144,r,524288,2*r-1⟩ = true :=
  (List.all_eq_true.mp excluded_certificate) r hr

private theorem member_pos (r : Nat) (hr : r ∈ excluded) : 0<r :=
  of_decide_eq_true ((List.all_eq_true.mp excluded_positive) r hr)

/-- The existing source-proved inverse soundness theorem transports
    each finite kernel check to every quotient, with no search cutoff. -/
theorem no_reach_cylinder (q r : Nat) (hr : r ∈ excluded) :
    ¬ Reach (262144*q+r) (524288*q+2*r-1) := by
  let s : Affine := ⟨262144,r,524288,2*r-1⟩
  have hc := cert_sound 20 s q (member_cert r hr)
  have hA : va s q = 262144*q+r := by rfl
  have hB : vb s q = 524288*q+2*r-1 := by
    dsimp [vb,s]
    have hp := member_pos r hr
    omega
  simpa only [hA,hB] using hc

/-- For every genuine BB429 blank-root section on its exact halting
    line, the first counter avoids all 673 listed classes modulo 262144. -/
theorem blank_halt_not_excluded (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (hg : b+1=2*a) : a%262144 ∉ excluded := by
  intro hm
  let r := a%262144
  let q := a/262144
  have hrmem : r ∈ excluded := by simpa only [r] using hm
  have hrpos : 0<r := member_pos r hrmem
  have ha : a=262144*q+r := by dsimp [q,r]; omega
  have hb : b=524288*q+2*r-1 := by omega
  have hp : BB429.run n (0,0)=some (262144*q+r,524288*q+2*r-1) := by
    rw [← ha, ← hb]
    exact hr
  exact no_reach_cylinder q r hrmem ⟨n,hp⟩

#print axioms excluded_count
#print axioms excluded_certificate
#print axioms no_reach_cylinder
#print axioms blank_halt_not_excluded
end BB429SplitSieve
