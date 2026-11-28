import Window5Domains
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Window5Bank128
open BB6Coverage BB6.Agent50Window5 BB6.Agent50Window5Domains

/-!
A finite bank of 128 five-cell inductive predicates, sorted by exact
marginal volume outside an older source-accepted Raw34 portfolio.
The matching 25-action product-domain masks, candidate trace witnesses,
and independent BigInt MDD union audit are in mask-bank-128.json and
audit_mask_bank_union.mjs.

Soundness of ANY domain determined by one of these masks follows
from the general original-infinite-tape theorem never_of_permitted,
not from the untrusted discovery procedure. This module kernel-checks
that all 128 masks admit the literal four authentic Raw34 root rows.
-/

def masks : List Nat := [
  0xf000f000fffffffffffffccccccccfcc00000001,
  0xf000f0ffffffffffccfcffcccccfcc00000001,
  0xf0f0f0f000ff0000ff00ff00ff00ff00ffffffff,
  0x303030300fff0ffffffffffff000f3000c0c0c0d,
  0x30303030ffffffffcfcccccc00000300f000f001,
  0xf000f000ffffffffcfcccccc0000030030303031,
  0xc0c0c0c0ffffffccffeaeeeaff00ff00ffffffff,
  0xf000f000fffffffffffffffff0fff300cccccccd,
  0xc0c0c0c000ff0000ff000c00ff00ff00ffffffff,
  0xc0c0c0c0f0fff000ff00ff00ffffffff00000001,
  0xf000c00cff0cc8cf88cc88f888cb880c080c09,
  0x3030303000ff00ff7f7f7f7ff000f3000c0c0c0d,
  0xf000f000ffffffc8cfc8ccc800000300c0c0c0c1,
  0xc000f0ffffffffcfccfcff88cc8bcc00000001,
  0xf0f0f0f0ffffff30cfc0ccc0f000f300cccccccd,
  0x30303030ffff0000ff00ff00ff0fff0fffffffff,
  0x30303030ffffffffcfcfcccff000f30000000001,
  0xc080c08000ff00c0ff88cc88f000c3000c080c09,
  0xc080c080f0ffc0000f000c00f000c300cc88cc89,
  0xf000c000c0ffc0800f000c00f000c300cc88cc89,
  0x303030300fff0fffcffcccfff000f3000c0c0c0d,
  0xc0f0c0c08cff8cc88f888c88f000c300cc88cc89,
  0xc0c0c0c000ff0000ff00fc00feeeefee0c000c01,
  0x3030303000ff0000ff000f00ff00ff00ffffffff,
  0xc0c0c0c0fafffafacfccccccf000f300cccccccd,
  0xf000f000ffffffffcfcccccc3030333000000001,
  0xf000f000f0fff0f0ff00fc00cccccfcc00000001,
  0x30303030ffffffffcfccccccf000f30000000001,
  0xf000c000ffffc080ff00cc00cc88cf8800000001,
  0x30303030ffff0000ff00cc00ff00ff00ffffffff,
  0x3030303000ff0000ff000c00ff00ff00ffffffff,
  0xc0c0c0c0ffffffccffeafeeaf000f300cccccccd,
  0xc0c0c0c0bbffbbfbcfcccccc00000300f000f001,
  0xf000f00000ff0000ff000c00ff0003000c000c01,
  0xc000c000c0ffc0000f000c00f00003008c808c81,
  0xf000f000bbffbbfbcfcccccc00000300c0c0c0c1,
  0x80808080ccffccc88f888c8800000300c000c001,
  0xc000c000ccffccc88f888c880000030080808081,
  0xc0c0c0c0eeffeefecfcccccc00000300f000f001,
  0x3000300030ff30ff0f0f0c0cf000f3004c4c4c4d,
  0x3000300030ff30000f000c00f00003004c404c41,
  0xf000c00cff0cc8cf88cc88f000c3000c080c09,
  0xc000c00cff0cff8f8f8c8f00000300000000f1,
  0xc0c0c0c000ff00fc2f2e2e2ef000f3000c0c0c0d,
  0x30303030ffffffffffffccccff000300ff00ff01,
  0xc0c0c0c0ffffffffffffccccff000300ff00ff01,
  0xc000c000f0ff0000ff000f00ff31ff31ffffffff,
  0xc080c080ffff0000ff00cc00ff00ff00ffffffff,
  0xf0f0f0f000ff0000ff000c00ff00ff00ff00ff01,
  0xf000c0ffffccc8ff88cc88cc88cf8800000001,
  0x30303030ffffff00ffc0ccc0ff00ff00ffffffff,
  0x3020302000ff0000ff00cc00ffc8ffc80f000c01,
  0x3020302000ff0000ff00cc00ff88cf880f000c01,
  0xc000c0008cff8cc88f888c880000030080808081,
  0x1010101003ff03ff4f4f4c4f0000030030003001,
  0x3000300003ff03ff4f4f4c4f0000030010101011,
  0xf0000000ff0000ff000c000f000f00c300c301,
  0xf000000000ff0000cf00cc00f8c8fbc80c000c01,
  0xc000c00000ff0000ff000c00ff0003000c000c01,
  0x3030303000ff0000ff00ff00ff0003000f000f01,
  0xc000c00cff0cff8f8c8c8c00000300000000f1,
  0x20202020ccffcccc8f888c8800000300c000c001,
  0xf000f0ffffff30cfc0ccc0f000f3000c0c0c0d,
  0xf00030ffff3331cf44cc44f00033000c040c05,
  0x8080808000ff00c0cf00cc00f888cb880c080c09,
  0x3000300033ff33334f444c440000030040404041,
  0x4040404033ff33334f444c440000030030003001,
  0x3030303000ff0000ff00ff00ff0f030f0c000c01,
  0xf000f0ffffffc0cfc0ccc0f000f3000c0c0c0d,
  0xf00cff0cff8f8c8c8c0000030000c000c1,
  0xc000c0fcffccc88f888c88c000c30008080809,
  0xf0000000fcfffcc88f888c8800000300c000c001,
  0x30003030ff30ff0f0c0c0ff000f3004c4c4c4d,
  0xc000c000fcfffcc88f888c8800000300f0000001,
  0xc000c00000ff0000ff000c000f000f0003f00301,
  0xc000c000c0ffc0800f000c00f000c3008c888c89,
  0x3000300000ff0000ff000c000f000f0013131313,
  0x8080808000ff0000cf00cc00f8c8cbc80c000c01,
  0x3030303000ff00ffff0ffc0f0f0c0f0c11111111,
  0xc0c0c0c000ff00000f000c00f000c3008c888c89,
  0xc000c0000cff0cfc8f8c8c8c0000030020202021,
  0xf000c0ffffffffffffccccff00cf00cf8acf8b,
  0xc000c00000ff0000ff000c00ff00ff00ffffffff,
  0xc0c0c0c0ffffffccffeaeeeaff00ff0000000001,
  0xc000c0ffffffcccfcaceca88888b8800000001,
  0xc080c080c8ffc8c8ff88cc88f000c3008c888c89,
  0xc0c0c0c000ff0000ff00ff00ffffffff22ffffff,
  0xf000f0ffffffc8cfc8ccc8f000f300cccccccd,
  0xc0c0c0c0ffff0000ff00fc00ff000300ff00ff01,
  0xc000c000f0ff0000ff000f00ff31ff3100000001,
  0xc000c00000ff0000ff000c00fff0ff00ffffffff,
  0xc000c0ffffffffcfffccfff000f3f08c8c8c8d,
  0xc0c0c0c0aaffaafacfccccccf000f300cccccccd,
  0xc0c0c0c0ffffffccefeaeeeaf000f300cccccccd,
  0xc0c0c0c0eeffeefeffccccccfc00ff00feeefeef,
  0xc000c00000ff0000ff000c000c000f00f0000001,
  0xc080c08000ff00ccff08cc080c080f0822222223,
  0xf0000000ff0000cf00cf00f888cb880c000c01,
  0x4040404033ff33314f444c440000030030003001,
  0xc000c00000ff0000ff000c00f00003000c000c01,
  0xc000c0c0ffc0cc0f080c08f000c3f08c888c89,
  0xf000000cff0cff8f8c8c8c00000300c000c001,
  0x3030303000ff00000f000c00f00033004c444c45,
  0xc0c0c0c000ff00ffff0cfc0c0c0c0f0c00f000f1,
  0xf0000000ccffccc88f888c8800000300c000c001,
  0x3000300003ff03004f404f400003030310101011,
  0x30303030ddffddfdcfcccccc00000300f000f001,
  0xc000c00000ff00000ff00c00f30003000c000c01,
  0xf000f00003ff03f3cfcccccc00000300c0c0c0c1,
  0x3000300003ff03334f444c440000030010101011,
  0x1010101003ff03334f444c440000030030003001,
  0xc0c0c0c0ffffff32cfc4ccc400000300f000f001,
  0xf0000000ff00000f000c00f3000300cc00cc01,
  0x3000300003ff03004f404c400300030011111111,
  0xc000c08cff8cc88f888c88c000c30008080809,
  0x3000300013ff13314f444c440000030010101011,
  0xc0c0c0c000ff00ff8fcc8cfff000f3000c0c0c0d,
  0xc000c00000ff0000ff000c000f000f0000f00001,
  0xc000c0000cff0cff8f8c8c8c0000030000f00001,
  0xf0000000ff00000f000f00f0000300cc00cc01,
  0x3010301000ff0033ff043c040f040f0411111111,
  0xf000300000ff0030cf44cc44f01033100c040c05,
  0xc000c0000cff0cc88f888c880000030080808081,
  0xf000000000ff0000cf00cc00f888cb880c000c01,
  0x3010301000ff00304f444c44f00033000c040c05,
  0xf000f000ddffddfdcfcccccc0000030030303031,
  0x3010301000ff00300f000c00f00033004c444c45,
  0xf000f000ff00ffcfccccccf000f3000c0c0c0d
]

def maskGood (bits : Nat) : Bool :=
  decide (masked bits 0 false false false false false = true) &&
  decide (Permitted (masked bits) 0 false (some ⟨true,true,1⟩)) &&
  decide (Permitted (masked bits) 1 false (some ⟨true,true,2⟩)) &&
  decide (Permitted (masked bits) 2 false (some ⟨false,true,3⟩)) &&
  decide (Permitted (masked bits) 3 false (some ⟨true,false,2⟩))

theorem count : masks.length = 128 := by decide

theorem all_roots_checked : masks.all maskGood = true := by decide +kernel

/-- Uniform genuinely physical NeverHalts certificate for any of the
128 masks and every total machine whose instructions respect that
mask's locally allowed domain. The four Raw34 rows are known admissible. -/
theorem every_mask_never (bits : Nat) (hb : bits ∈ masks)
    (m : Machine)
    (hm : ∀ q c, Permitted (masked bits) q c (m (q,c))) :
    NeverHalts m := by
  have hg : maskGood bits = true :=
    List.all_eq_true.mp all_roots_checked bits hb
  have hs : masked bits 0 false false false false false = true := by
    have h := Bool.and_eq_true.mp hg
    exact h.1
  exact never_of_permitted (masked bits) m hs hm

#print axioms count
#print axioms all_roots_checked
#print axioms every_mask_never
end BB6.Agent50Window5Bank128
