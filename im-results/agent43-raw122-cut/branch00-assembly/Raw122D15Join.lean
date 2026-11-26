import Raw122D15S00
import Raw122D15S01
import Raw122D15S02
import Raw122D15S03
import Raw122D15S04
import Raw122D15S05
import Raw122D15S06
import Raw122D15S07
import Raw122D15S08
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw122DirectGrowth
open BB6Coverage BB6Coverage.Agent31Pump
namespace M15
theorem entryJ0 : run0 table 256 (entryC0) = some (entryC1) := entryS0

theorem entryJ1 : run0 table 512 (entryC0) = some (entryC2) := @join0 table 256 256 (entryC0) (entryC1) (entryC2) (entryJ0) (entryS1)

theorem entryJ2 : run0 table 768 (entryC0) = some (entryC3) := @join0 table 512 256 (entryC0) (entryC2) (entryC3) (entryJ1) (entryS2)

theorem entryJ3 : run0 table 1024 (entryC0) = some (entryC4) := @join0 table 768 256 (entryC0) (entryC3) (entryC4) (entryJ2) (entryS3)

theorem entryJ4 : run0 table 1280 (entryC0) = some (entryC5) := @join0 table 1024 256 (entryC0) (entryC4) (entryC5) (entryJ3) (entryS4)

theorem entryJ5 : run0 table 1536 (entryC0) = some (entryC6) := @join0 table 1280 256 (entryC0) (entryC5) (entryC6) (entryJ4) (entryS5)

theorem entryJ6 : run0 table 1792 (entryC0) = some (entryC7) := @join0 table 1536 256 (entryC0) (entryC6) (entryC7) (entryJ5) (entryS6)

theorem entryJ7 : run0 table 2048 (entryC0) = some (entryC8) := @join0 table 1792 256 (entryC0) (entryC7) (entryC8) (entryJ6) (entryS7)

theorem entryJ8 : run0 table 2304 (entryC0) = some (entryC9) := @join0 table 2048 256 (entryC0) (entryC8) (entryC9) (entryJ7) (entryS8)

theorem entryJ9 : run0 table 2560 (entryC0) = some (entryC10) := @join0 table 2304 256 (entryC0) (entryC9) (entryC10) (entryJ8) (entryS9)

theorem entryJ10 : run0 table 2816 (entryC0) = some (entryC11) := @join0 table 2560 256 (entryC0) (entryC10) (entryC11) (entryJ9) (entryS10)

theorem entryJ11 : run0 table 3072 (entryC0) = some (entryC12) := @join0 table 2816 256 (entryC0) (entryC11) (entryC12) (entryJ10) (entryS11)

theorem entryJ12 : run0 table 3328 (entryC0) = some (entryC13) := @join0 table 3072 256 (entryC0) (entryC12) (entryC13) (entryJ11) (entryS12)

theorem entryJ13 : run0 table 3584 (entryC0) = some (entryC14) := @join0 table 3328 256 (entryC0) (entryC13) (entryC14) (entryJ12) (entryS13)

theorem entryJ14 : run0 table 3840 (entryC0) = some (entryC15) := @join0 table 3584 256 (entryC0) (entryC14) (entryC15) (entryJ13) (entryS14)

theorem entryJ15 : run0 table 4096 (entryC0) = some (entryC16) := @join0 table 3840 256 (entryC0) (entryC15) (entryC16) (entryJ14) (entryS15)

theorem entryJ16 : run0 table 4352 (entryC0) = some (entryC17) := @join0 table 4096 256 (entryC0) (entryC16) (entryC17) (entryJ15) (entryS16)

theorem entryJ17 : run0 table 4608 (entryC0) = some (entryC18) := @join0 table 4352 256 (entryC0) (entryC17) (entryC18) (entryJ16) (entryS17)

theorem entryJ18 : run0 table 4864 (entryC0) = some (entryC19) := @join0 table 4608 256 (entryC0) (entryC18) (entryC19) (entryJ17) (entryS18)

theorem entryJ19 : run0 table 5120 (entryC0) = some (entryC20) := @join0 table 4864 256 (entryC0) (entryC19) (entryC20) (entryJ18) (entryS19)

theorem entryJ20 : run0 table 5376 (entryC0) = some (entryC21) := @join0 table 5120 256 (entryC0) (entryC20) (entryC21) (entryJ19) (entryS20)

theorem entryJ21 : run0 table 5632 (entryC0) = some (entryC22) := @join0 table 5376 256 (entryC0) (entryC21) (entryC22) (entryJ20) (entryS21)

theorem entryJ22 : run0 table 5888 (entryC0) = some (entryC23) := @join0 table 5632 256 (entryC0) (entryC22) (entryC23) (entryJ21) (entryS22)

theorem entryJ23 : run0 table 6144 (entryC0) = some (entryC24) := @join0 table 5888 256 (entryC0) (entryC23) (entryC24) (entryJ22) (entryS23)

theorem entryJ24 : run0 table 6400 (entryC0) = some (entryC25) := @join0 table 6144 256 (entryC0) (entryC24) (entryC25) (entryJ23) (entryS24)

theorem entryJ25 : run0 table 6656 (entryC0) = some (entryC26) := @join0 table 6400 256 (entryC0) (entryC25) (entryC26) (entryJ24) (entryS25)

theorem entryJ26 : run0 table 6912 (entryC0) = some (entryC27) := @join0 table 6656 256 (entryC0) (entryC26) (entryC27) (entryJ25) (entryS26)

theorem entryJ27 : run0 table 7168 (entryC0) = some (entryC28) := @join0 table 6912 256 (entryC0) (entryC27) (entryC28) (entryJ26) (entryS27)

theorem entryJ28 : run0 table 7424 (entryC0) = some (entryC29) := @join0 table 7168 256 (entryC0) (entryC28) (entryC29) (entryJ27) (entryS28)

theorem entryJ29 : run0 table 7680 (entryC0) = some (entryC30) := @join0 table 7424 256 (entryC0) (entryC29) (entryC30) (entryJ28) (entryS29)

theorem entryJ30 : run0 table 7936 (entryC0) = some (entryC31) := @join0 table 7680 256 (entryC0) (entryC30) (entryC31) (entryJ29) (entryS30)

theorem entryJ31 : run0 table 8192 (entryC0) = some (entryC32) := @join0 table 7936 256 (entryC0) (entryC31) (entryC32) (entryJ30) (entryS31)

theorem entryJ32 : run0 table 8448 (entryC0) = some (entryC33) := @join0 table 8192 256 (entryC0) (entryC32) (entryC33) (entryJ31) (entryS32)

theorem entryJ33 : run0 table 8704 (entryC0) = some (entryC34) := @join0 table 8448 256 (entryC0) (entryC33) (entryC34) (entryJ32) (entryS33)

theorem entryJ34 : run0 table 8960 (entryC0) = some (entryC35) := @join0 table 8704 256 (entryC0) (entryC34) (entryC35) (entryJ33) (entryS34)

theorem entryJ35 : run0 table 9216 (entryC0) = some (entryC36) := @join0 table 8960 256 (entryC0) (entryC35) (entryC36) (entryJ34) (entryS35)

theorem entryJ36 : run0 table 9338 (entryC0) = some (entryC37) := @join0 table 9216 122 (entryC0) (entryC36) (entryC37) (entryJ35) (entryS36)

theorem growthJ0 (n : Nat) : run0 table 256 (growthC0 n) = some (growthC1 n) := growthS0 n

theorem growthJ1 (n : Nat) : run0 table 512 (growthC0 n) = some (growthC2 n) := @join0 table 256 256 (growthC0 n) (growthC1 n) (growthC2 n) (growthJ0 n) (growthS1 n)

theorem growthJ2 (n : Nat) : run0 table 768 (growthC0 n) = some (growthC3 n) := @join0 table 512 256 (growthC0 n) (growthC2 n) (growthC3 n) (growthJ1 n) (growthS2 n)

theorem growthJ3 (n : Nat) : run0 table 1024 (growthC0 n) = some (growthC4 n) := @join0 table 768 256 (growthC0 n) (growthC3 n) (growthC4 n) (growthJ2 n) (growthS3 n)

theorem growthJ4 (n : Nat) : run0 table 1134 (growthC0 n) = some (growthC5 n) := @join0 table 1024 110 (growthC0 n) (growthC4 n) (growthC5 n) (growthJ3 n) (growthS4 n)
end M15
end BB6Coverage.Agent31Pump.Raw122DirectGrowth
