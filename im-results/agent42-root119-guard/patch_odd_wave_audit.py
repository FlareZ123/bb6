from pathlib import Path

source = Path(__file__).with_name("test-root119-odd-wave-audit.cjs")
text = source.read_text(encoding="utf-8")

replacements = [
    (
        """let previousBit = null;

function bit(x) {""",
        """let previousBit = null;
let predictedB0Intervals = 0;
let predictedB1Checkpoints = 0;

function bit(x) {""",
    ),
    (
        """  for (const prediction of due) {
    assert.equal(q, 'B', `predicted B/0 at time ${time}`);
    assert.equal(head, prediction.head, `predicted head at time ${time}`);
  }
  pending.delete(time);""",
        """  for (const prediction of due) {
    assert.equal(q, 'B', `predicted B state at time ${time}`);
    assert.equal(head, prediction.head, `predicted head at time ${time}`);
  }
  if (due.length > 0 && bit(head) === 1) predictedB1Checkpoints++;
  pending.delete(time);""",
    ),
    (
        """      });
    }

    let leftRun = 0;
    while (tape.has(head - 1 - leftRun)) leftRun++;""",
        """      });
    } else if (previousB0) {
      predictedB0Intervals++;
    }

    let leftRun = 0;
    while (tape.has(head - 1 - leftRun)) leftRun++;""",
    ),
    (
        """  simulatedSteps: LIMIT,
  unmatchedB0Intervals: residuals.length,""",
        """  simulatedSteps: LIMIT,
  completedB0Intervals: residuals.length + predictedB0Intervals,
  predictedB0Intervals,
  predictedB1Checkpoints,
  unmatchedB0Intervals: residuals.length,
  pendingPredictionsAtCutoff: Array.from(pending.entries()),
  lastB0AtCutoff: previousB0 ? { time: previousB0.time, head: previousB0.head } : null,""",
    ),
]

for old, new in replacements:
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"Expected one audit source match, found {count}: {old[:80]!r}")
    text = text.replace(old, new)

source.write_text(text, encoding="utf-8")
print("Patched odd-wave audit: distinguish B/0 returns from B/1 checkpoints and report cutoff coverage.")
