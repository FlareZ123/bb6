import Core192All
set_option maxRecDepth 16000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace Agent38M192
open Agent41M192
instance (a k c : Nat) : Decidable (high a k c) := by
  unfold high
  infer_instance
instance (x w: Nat) : Decidable (lowCore x w) := by
  unfold lowCore
  infer_instance

theorem finite_c0 : ∀ r : Fin 192, ∀ s : Fin 192,
  high ((r.val+190)%192) 1 (2*s.val+1) → lowCore r.val s.val := by
  intro ⟨r, hr⟩
  by_cases hm : r < 96
  · by_cases hm : r < 48
    · by_cases hm : r < 24
      · by_cases hm : r < 12
        · by_cases hm : r < 6
          · by_cases hm : r < 3
            · by_cases hm : r < 1
              · have heq : r = 0 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 2
                · have heq : r = 1 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 2 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
            · by_cases hm : r < 4
              · have heq : r = 3 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 5
                · have heq : r = 4 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 5 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
          · by_cases hm : r < 9
            · by_cases hm : r < 7
              · have heq : r = 6 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 8
                · have heq : r = 7 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 8 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
            · by_cases hm : r < 10
              · have heq : r = 9 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 11
                · have heq : r = 10 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 11 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
        · by_cases hm : r < 18
          · by_cases hm : r < 15
            · by_cases hm : r < 13
              · have heq : r = 12 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 14
                · have heq : r = 13 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 14 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
            · by_cases hm : r < 16
              · have heq : r = 15 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 17
                · have heq : r = 16 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 17 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
          · by_cases hm : r < 21
            · by_cases hm : r < 19
              · have heq : r = 18 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 20
                · have heq : r = 19 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 20 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
            · by_cases hm : r < 22
              · have heq : r = 21 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 23
                · have heq : r = 22 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 23 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
      · by_cases hm : r < 36
        · by_cases hm : r < 30
          · by_cases hm : r < 27
            · by_cases hm : r < 25
              · have heq : r = 24 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 26
                · have heq : r = 25 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 26 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
            · by_cases hm : r < 28
              · have heq : r = 27 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 29
                · have heq : r = 28 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 29 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
          · by_cases hm : r < 33
            · by_cases hm : r < 31
              · have heq : r = 30 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 32
                · have heq : r = 31 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 32 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
            · by_cases hm : r < 34
              · have heq : r = 33 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 35
                · have heq : r = 34 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 35 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
        · by_cases hm : r < 42
          · by_cases hm : r < 39
            · by_cases hm : r < 37
              · have heq : r = 36 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 38
                · have heq : r = 37 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 38 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
            · by_cases hm : r < 40
              · have heq : r = 39 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 41
                · have heq : r = 40 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 41 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
          · by_cases hm : r < 45
            · by_cases hm : r < 43
              · have heq : r = 42 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 44
                · have heq : r = 43 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 44 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
            · by_cases hm : r < 46
              · have heq : r = 45 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 47
                · have heq : r = 46 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 47 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
    · by_cases hm : r < 72
      · by_cases hm : r < 60
        · by_cases hm : r < 54
          · by_cases hm : r < 51
            · by_cases hm : r < 49
              · have heq : r = 48 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 50
                · have heq : r = 49 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 50 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
            · by_cases hm : r < 52
              · have heq : r = 51 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 53
                · have heq : r = 52 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 53 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
          · by_cases hm : r < 57
            · by_cases hm : r < 55
              · have heq : r = 54 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 56
                · have heq : r = 55 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 56 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
            · by_cases hm : r < 58
              · have heq : r = 57 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 59
                · have heq : r = 58 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 59 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
        · by_cases hm : r < 66
          · by_cases hm : r < 63
            · by_cases hm : r < 61
              · have heq : r = 60 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 62
                · have heq : r = 61 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 62 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
            · by_cases hm : r < 64
              · have heq : r = 63 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 65
                · have heq : r = 64 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 65 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
          · by_cases hm : r < 69
            · by_cases hm : r < 67
              · have heq : r = 66 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 68
                · have heq : r = 67 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 68 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
            · by_cases hm : r < 70
              · have heq : r = 69 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 71
                · have heq : r = 70 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 71 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
      · by_cases hm : r < 84
        · by_cases hm : r < 78
          · by_cases hm : r < 75
            · by_cases hm : r < 73
              · have heq : r = 72 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 74
                · have heq : r = 73 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 74 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
            · by_cases hm : r < 76
              · have heq : r = 75 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 77
                · have heq : r = 76 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 77 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
          · by_cases hm : r < 81
            · by_cases hm : r < 79
              · have heq : r = 78 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 80
                · have heq : r = 79 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 80 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
            · by_cases hm : r < 82
              · have heq : r = 81 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 83
                · have heq : r = 82 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 83 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
        · by_cases hm : r < 90
          · by_cases hm : r < 87
            · by_cases hm : r < 85
              · have heq : r = 84 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 86
                · have heq : r = 85 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 86 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
            · by_cases hm : r < 88
              · have heq : r = 87 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 89
                · have heq : r = 88 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 89 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
          · by_cases hm : r < 93
            · by_cases hm : r < 91
              · have heq : r = 90 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 92
                · have heq : r = 91 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 92 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
            · by_cases hm : r < 94
              · have heq : r = 93 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 95
                · have heq : r = 94 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 95 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
  · by_cases hm : r < 144
    · by_cases hm : r < 120
      · by_cases hm : r < 108
        · by_cases hm : r < 102
          · by_cases hm : r < 99
            · by_cases hm : r < 97
              · have heq : r = 96 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 98
                · have heq : r = 97 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 98 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
            · by_cases hm : r < 100
              · have heq : r = 99 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 101
                · have heq : r = 100 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 101 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
          · by_cases hm : r < 105
            · by_cases hm : r < 103
              · have heq : r = 102 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 104
                · have heq : r = 103 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 104 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
            · by_cases hm : r < 106
              · have heq : r = 105 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 107
                · have heq : r = 106 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 107 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
        · by_cases hm : r < 114
          · by_cases hm : r < 111
            · by_cases hm : r < 109
              · have heq : r = 108 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 110
                · have heq : r = 109 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 110 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
            · by_cases hm : r < 112
              · have heq : r = 111 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 113
                · have heq : r = 112 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 113 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
          · by_cases hm : r < 117
            · by_cases hm : r < 115
              · have heq : r = 114 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 116
                · have heq : r = 115 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 116 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
            · by_cases hm : r < 118
              · have heq : r = 117 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 119
                · have heq : r = 118 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 119 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
      · by_cases hm : r < 132
        · by_cases hm : r < 126
          · by_cases hm : r < 123
            · by_cases hm : r < 121
              · have heq : r = 120 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 122
                · have heq : r = 121 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 122 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
            · by_cases hm : r < 124
              · have heq : r = 123 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 125
                · have heq : r = 124 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 125 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
          · by_cases hm : r < 129
            · by_cases hm : r < 127
              · have heq : r = 126 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 128
                · have heq : r = 127 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 128 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
            · by_cases hm : r < 130
              · have heq : r = 129 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 131
                · have heq : r = 130 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 131 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
        · by_cases hm : r < 138
          · by_cases hm : r < 135
            · by_cases hm : r < 133
              · have heq : r = 132 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 134
                · have heq : r = 133 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 134 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
            · by_cases hm : r < 136
              · have heq : r = 135 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 137
                · have heq : r = 136 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 137 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
          · by_cases hm : r < 141
            · by_cases hm : r < 139
              · have heq : r = 138 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 140
                · have heq : r = 139 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 140 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
            · by_cases hm : r < 142
              · have heq : r = 141 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 143
                · have heq : r = 142 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 143 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
    · by_cases hm : r < 168
      · by_cases hm : r < 156
        · by_cases hm : r < 150
          · by_cases hm : r < 147
            · by_cases hm : r < 145
              · have heq : r = 144 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 146
                · have heq : r = 145 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 146 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
            · by_cases hm : r < 148
              · have heq : r = 147 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 149
                · have heq : r = 148 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 149 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
          · by_cases hm : r < 153
            · by_cases hm : r < 151
              · have heq : r = 150 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 152
                · have heq : r = 151 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 152 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
            · by_cases hm : r < 154
              · have heq : r = 153 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 155
                · have heq : r = 154 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 155 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
        · by_cases hm : r < 162
          · by_cases hm : r < 159
            · by_cases hm : r < 157
              · have heq : r = 156 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 158
                · have heq : r = 157 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 158 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
            · by_cases hm : r < 160
              · have heq : r = 159 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 161
                · have heq : r = 160 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 161 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
          · by_cases hm : r < 165
            · by_cases hm : r < 163
              · have heq : r = 162 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 164
                · have heq : r = 163 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 164 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
            · by_cases hm : r < 166
              · have heq : r = 165 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 167
                · have heq : r = 166 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 167 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
      · by_cases hm : r < 180
        · by_cases hm : r < 174
          · by_cases hm : r < 171
            · by_cases hm : r < 169
              · have heq : r = 168 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 170
                · have heq : r = 169 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 170 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
            · by_cases hm : r < 172
              · have heq : r = 171 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 173
                · have heq : r = 172 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 173 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
          · by_cases hm : r < 177
            · by_cases hm : r < 175
              · have heq : r = 174 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 176
                · have heq : r = 175 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 176 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
            · by_cases hm : r < 178
              · have heq : r = 177 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 179
                · have heq : r = 178 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 179 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
        · by_cases hm : r < 186
          · by_cases hm : r < 183
            · by_cases hm : r < 181
              · have heq : r = 180 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 182
                · have heq : r = 181 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 182 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
            · by_cases hm : r < 184
              · have heq : r = 183 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 185
                · have heq : r = 184 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 185 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
          · by_cases hm : r < 189
            · by_cases hm : r < 187
              · have heq : r = 186 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 188
                · have heq : r = 187 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 188 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
            · by_cases hm : r < 190
              · have heq : r = 189 := by omega
                subst r
                simp only [Fin.val_mk]
                decide
              · by_cases hm : r < 191
                · have heq : r = 190 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide
                · have heq : r = 191 := by omega
                  subst r
                  simp only [Fin.val_mk]
                  decide

#print axioms finite_c0
end Agent38M192
