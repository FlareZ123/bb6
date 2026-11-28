import Raw40LateCrossingTripleTable
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent19Raw40LateCrossing.C1REM1096
open BB6Coverage Agent42Crossing Agent19OrientedCrossing Agent50Zipper Agent13PackedZipper
def e0 : P := ⟨2,0x0,0x0⟩
def e1 : P := ⟨3,0xffffffffffffffffffffffffffffffffc1ffcfcfcfcfcfc02,0x77045c3⟩
theorem step1 : runP oriented 16384 e0 = some e1 := by decide +kernel
theorem prefix1 : runP oriented 16384 e0 = some e1 := step1
def e2 : P := ⟨3,0x7fffffffffffe,0x77007007e77001c1c1c1c1c1c1cee001c000000000000000000000000000000000000⟩
theorem step2 : runP oriented 16384 e1 = some e2 := by decide +kernel
theorem prefix2 : runP oriented 32768 e0 = some e2 := joinP prefix1 step2
def e3 : P := ⟨3,0x1ffffffffffffffffe,0x1dc01c01f9dddc70707070707070707fc3b8f8070000000000000000000000000000000000000000000000⟩
theorem step3 : runP oriented 16384 e2 = some e3 := by decide +kernel
theorem prefix3 : runP oriented 49152 e0 = some e3 := joinP prefix2 step3
def e4 : P := ⟨3,0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe,0x1dc0717ee1dc0000707070707070707070707073b8007000000000000⟩
theorem step4 : runP oriented 16384 e3 = some e4 := by decide +kernel
theorem prefix4 : runP oriented 65536 e0 = some e4 := joinP prefix3 step4
def e5 : P := ⟨5,0x7fffffffffffffffffffffffffffffffffffffffffffffffff,0x7701c5fb87700771c1c1c1c1c1c1c1c1c1c1c1c1c1cefdc0ee000000000000000000000000000000000⟩
theorem step5 : runP oriented 16384 e4 = some e5 := by decide +kernel
theorem prefix5 : runP oriented 81920 e0 = some e5 := joinP prefix4 step5
def e6 : P := ⟨5,0x1fffffffffffffffffffffffffffffffffffffff,0x7701c5fb87701f9dc1c1c1c1c1c1c1c1c1c1c1c1c1c1c1cefdddfb80000000000000000000000000000000000000000000000000000⟩
theorem step6 : runP oriented 16384 e5 = some e6 := by decide +kernel
theorem prefix6 : runP oriented 98304 e0 = some e6 := joinP prefix5 step6
def e7 : P := ⟨5,0x1fff,0x7701c5fb9c5c1c1c01c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1cefdddfb8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem step7 : runP oriented 16384 e6 = some e7 := by decide +kernel
theorem prefix7 : runP oriented 114688 e0 = some e7 := joinP prefix6 step7
def e8 : P := ⟨5,0x3,0x7701c5fb9c5c1c7171c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1cefdddc700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem step8 : runP oriented 16384 e7 = some e8 := by decide +kernel
theorem prefix8 : runP oriented 131072 e0 = some e8 := joinP prefix7 step8
def e9 : P := ⟨5,0xffffffffff,0x7701c5fb9c5c1c7ee381c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1cefdc01c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem step9 : runP oriented 16384 e8 = some e9 := by decide +kernel
theorem prefix9 : runP oriented 147456 e0 = some e9 := joinP prefix8 step9
def e10 : P := ⟨3,0x3ffffffffffffffffffffffffe,0x7701c5fb9c5c1c7eefc1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1cee00ee000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem step10 : runP oriented 16384 e9 = some e10 := by decide +kernel
theorem prefix10 : runP oriented 163840 e0 = some e10 := joinP prefix9 step10
def e11 : P := ⟨4,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc1ffcfcfcfcfcfcfc03,0x7701c5fb9c5c1c7eefc1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c7⟩
theorem step11 : runP oriented 16384 e10 = some e11 := by decide +kernel
theorem prefix11 : runP oriented 180224 e0 = some e11 := joinP prefix10 step11
def e12 : P := ⟨3,0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff3ff,0x1dc0717ee717ee3f700070707070707070707070707070707070707070707070707fc05df⟩
theorem step12 : runP oriented 16384 e11 = some e12 := by decide +kernel
theorem prefix12 : runP oriented 196608 e0 = some e12 := joinP prefix11 step12
def e13 : P := ⟨5,0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x7701c5fb9c5fb8fdc771c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1cefdddfb800000000⟩
theorem step13 : runP oriented 16384 e12 = some e13 := by decide +kernel
theorem prefix13 : runP oriented 212992 e0 = some e13 := joinP prefix12 step13
def e14 : P := ⟨5,0x7ffffffffffff,0x7701c5fb9c5fb8fddf9dc1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1cee00ee000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem step14 : runP oriented 16384 e13 = some e14 := by decide +kernel
theorem prefix14 : runP oriented 229376 e0 = some e14 := joinP prefix13 step14
def e15 : P := ⟨5,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x1dc0717ee717ee3f77e77070707070707070707070707070707070707070707070707070707fc3b8ff71c00000000000000000000000000000000000000000000000000000000000⟩
theorem step15 : runP oriented 16384 e14 = some e15 := by decide +kernel
theorem prefix15 : runP oriented 245760 e0 = some e15 := joinP prefix14 step15
def e16 : P := ⟨3,0xfffffffe,0x7701fb87701c01c7001c01c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1cefdddfb80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem step16 : runP oriented 16384 e15 = some e16 := by decide +kernel
theorem prefix16 : runP oriented 262144 e0 = some e16 := joinP prefix15 step16
def e17 : P := ⟨3,0x7ffffffffffffffffffffffffffffffffffffffffffe,0x7701fb87701c01c7007171c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1cee001c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem step17 : runP oriented 16384 e16 = some e17 := by decide +kernel
theorem prefix17 : runP oriented 278528 e0 = some e17 := joinP prefix16 step17
def e18 : P := ⟨5,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x7701fb87701c01c7007171c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1ff0ee3e01c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem step18 : runP oriented 16384 e17 = some e18 := by decide +kernel
theorem prefix18 : runP oriented 294912 e0 = some e18 := joinP prefix17 step18
def e19 : P := ⟨3,0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe,0x1dc07ee1dc070071c01fb8e07070707070707070707070707070707070707070707070707070707070707073bf7007000000000000000000000000000000000000000000⟩
theorem step19 : runP oriented 16384 e18 = some e19 := by decide +kernel
theorem prefix19 : runP oriented 311296 e0 = some e19 := joinP prefix18 step19
def e20 : P := ⟨3,0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe,0x1dc07ee1dc070071c01fb8e0707070707070707070707070707070707070707070707070707070707070707fc3b8ff7ee000000000000000000⟩
theorem step20 : runP oriented 16384 e19 = some e20 := by decide +kernel
theorem prefix20 : runP oriented 327680 e0 = some e20 := joinP prefix19 step20
def e21 : P := ⟨3,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe,0x7701fb87701c01c7007eefc1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1cefdddfb8000000⟩
theorem step21 : runP oriented 16384 e20 = some e21 := by decide +kernel
theorem prefix21 : runP oriented 344064 e0 = some e21 := joinP prefix20 step21
def e22 : P := ⟨5,0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff07ff3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3,0x1dc07ee1dc070071c3bf7000707070⟩
theorem step22 : runP oriented 16384 e21 = some e22 := by decide +kernel
theorem prefix22 : runP oriented 360448 e0 = some e22 := joinP prefix21 step22
def e23 : P := ⟨3,0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe,0x7701fb87701c01c70efdc001c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1ff01700ee00000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem step23 : runP oriented 16384 e22 = some e23 := by decide +kernel
theorem prefix23 : runP oriented 376832 e0 = some e23 := joinP prefix22 step23
def e24 : P := ⟨3,0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe,0x1dc07ee1dc070071c3bf71dc7070707070707070707070707070707070707070707070707070707070707070707070707073b8007000000⟩
theorem step24 : runP oriented 16384 e23 = some e24 := by decide +kernel
theorem prefix24 : runP oriented 393216 e0 = some e24 := joinP prefix23 step24
def e25 : P := ⟨3,0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe,0x1dc07ee1dc070071c3bf71dc707070707070707070707070707070707070707070707070707070707070707070707070707fc05c771c00000000000000000000000000000000000000000000000⟩
theorem step25 : runP oriented 16384 e24 = some e25 := by decide +kernel
theorem prefix25 : runP oriented 409600 e0 = some e25 := joinP prefix24 step25
def e26 : P := ⟨3,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe,0x1dc07ee1dc070071c3bf77e770707070707070707070707070707070707070707070707070707070707070707070707070707073b803b800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem step26 : runP oriented 16384 e25 = some e26 := by decide +kernel
theorem prefix26 : runP oriented 425984 e0 = some e26 := joinP prefix25 step26
def e27 : P := ⟨5,0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x7701fb87701c01c70efddf9dc1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1ff0171dfb8000000000000000000000000000000000000000000000000000000000000⟩
theorem step27 : runP oriented 16384 e26 = some e27 := by decide +kernel
theorem prefix27 : runP oriented 442368 e0 = some e27 := joinP prefix26 step27
def e28 : P := ⟨5,0x7ffff,0x7701fb87701c01c73f07001c01c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1cee00ee000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem step28 : runP oriented 16384 e27 = some e28 := by decide +kernel
theorem prefix28 : runP oriented 458752 e0 = some e28 := joinP prefix27 step28
def e29 : P := ⟨3,0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe,0x7701fb87701c01c73f07001c01c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1ff0171dc700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem step29 : runP oriented 16384 e28 = some e29 := by decide +kernel
theorem prefix29 : runP oriented 475136 e0 = some e29 := joinP prefix28 step29
def e30 : P := ⟨0,0x0,0x1dc07ee1dc070071cfc1c00700707070707070707070707070707070707070707070707070707070707070707070707070707070707fc3b8ff7ee000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
theorem step30 : runP oriented 8768 e29 = some e30 := by decide +kernel
theorem prefix30 : runP oriented 483904 e0 = some e30 := joinP prefix29 step30
def entryP : P := e30
theorem entryRun : runP oriented 483904 (encode (initialZ true)) = some entryP := prefix30
#print axioms entryRun

end BB6Coverage.Agent19Raw40LateCrossing.C1REM1096
