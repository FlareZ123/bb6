"""Reproduce the four kernel-checked extended sweep witnesses."""
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "agent10-tnf-multipump"))
import multi

CASES = [
  [
    "360",
    "1RB0LF1RC0RC0RD---1LD1RE1RD1RA0LE1LA",
    [
      20,
      1,
      [
        [
          "0",
          False
        ],
        [
          "11",
          True
        ],
        [
          "111100",
          False
        ],
        [
          "111",
          True
        ],
        [
          "1",
          False
        ]
      ],
      [],
      [
        [
          "011",
          False
        ],
        [
          "11",
          True
        ],
        [
          "111100111",
          False
        ],
        [
          "111",
          True
        ],
        [
          "1",
          False
        ]
      ],
      []
    ]
  ],
  [
    "820",
    "1RB0LF1RC1RE0RD1LA1LD1RE---1RA0LA1LC",
    [
      1,
      1,
      [
        [
          "0",
          False
        ],
        [
          "111111111111",
          True
        ],
        [
          "1",
          False
        ]
      ],
      [],
      [
        [
          "0111111111111",
          False
        ],
        [
          "111111111111",
          True
        ],
        [
          "1",
          False
        ]
      ],
      []
    ]
  ],
  [
    "987",
    "1RB0LF1RC---0RD0RC1LD1RE0RC1RA0LA1LF",
    [
      409,
      1,
      [
        [
          "01110000111100",
          False
        ],
        [
          "0011110011000011",
          True
        ],
        [
          "0011110011000011",
          False
        ]
      ],
      [],
      [
        [
          "011100001111000011110011000011",
          False
        ],
        [
          "0011110011000011",
          True
        ],
        [
          "0011110011000011",
          False
        ]
      ],
      []
    ]
  ],
  [
    "991",
    "1RB0LF1RC---0RD0RC1LD1RE1RC1RA0LA1LF",
    [
      1148,
      1,
      [
        [
          "0111000110000011000110011011000110000",
          False
        ],
        [
          "011000110011",
          True
        ],
        [
          "011000110000001111",
          False
        ]
      ],
      [],
      [
        [
          "0111000110000011000110011011000110000011000110011",
          False
        ],
        [
          "011000110011",
          True
        ],
        [
          "011000110000001111",
          False
        ]
      ],
      []
    ]
  ]
]

def main():
    ns = "BB6.Agent1Raw60A0LFMulti"
    parts = ["import SweepPumping", "set_option maxRecDepth 100000", "set_option maxHeartbeats 0", "set_option linter.unusedVariables false", f"namespace {ns}", "open BB6Coverage BB6Coverage.Agent31Pump"]
    for idx, code, (t, q, L, R, LL, RR) in CASES:
        st = multi.C(q, tuple(map(tuple,L)), tuple(map(tuple,R)))
        tg = multi.C(q, tuple(map(tuple,LL)), tuple(map(tuple,RR)))
        p = multi.parse(code)
        ans = multi.pump(p, st, tg, 1200)
        assert ans, idx
        proof, _ = multi.generate(idx, p, (t, st, tg, ans))
        parts.append(proof)
    parts.append(f"end {ns}")
    (ROOT / "Raw60A0LFMulti.lean").write_text("\n\n".join(parts) + "\n")

if __name__ == "__main__":
    main()
