// Reproducible BigInt certificate for the S4 discounted-moment bounds.
// The 9-digit prefix starts at the source-certified return-5457 state and
// repeats after 81,920 P-returns.  This script only evaluates that finite
// prefix cycle and the exact rational upper recurrence described in
// DISCOUNTED-MOMENT-ASYMPTOTIC.md; it does not simulate the full S4 stack.

const K = 9;
const PERIOD = 81920;
const SCALE = 1n << 512n;
const M0 = 5590215n;
const C = [509n, 290n, 219n];

const ROOT18 = [
  283n, 906n, 982n, 3490n, 3734n, 5935n, 13580n, 109210n, 171050n,
  366446n, 435688n, 443554n, 1702180n, 1770018n, 211301n, 281569n,
  35137n, 35134n
];
const ROOT9 = ROOT18.slice(0, K);

function assert(condition, message) {
  if (!condition) throw new Error(message);
}

function hp(a, tail) {
  if (tail.length === 0) {
    return a % 2n === 0n ? [a / 2n + 2n] : [a / 2n];
  }
  const [b, ...rest] = tail;
  if (a % 2n === 0n) return [a / 2n + 2n, b + a / 2n, ...rest];
  return [a / 2n, ...hp(b + a / 2n + 1n, rest)];
}

function gp(c, digits) {
  return digits.length === 0 ? [] : hp(digits[0] + c, digits.slice(1));
}

function weight(digits) {
  let value = 0n;
  let place = 1n;
  for (const digit of digits) {
    value += (digit + 1n) * place;
    place *= 2n;
  }
  return value;
}

function v2cap(value, cap) {
  let r = 0;
  while (r < cap && value % 2n === 0n) {
    value /= 2n;
    r++;
  }
  return r;
}

// BigInt division truncates toward zero.  For positive denominators that is
// ceil(a/b) when a<0, and the usual positive ceiling formula when a>=0.
function ceilDiv(a, b) {
  return a >= 0n ? (a + b - 1n) / b : a / b;
}

function decimal(numerator, denominator = SCALE, places = 9) {
  const unit = 10n ** BigInt(places);
  const q = numerator * unit / denominator;
  const sign = q < 0n ? "-" : "";
  const absolute = q < 0n ? -q : q;
  return sign + String(absolute / unit) + "." +
    String(absolute % unit).padStart(places, "0");
}

function oneScale(s) {
  const p = 1n << BigInt(s);
  const d = 2n * p - 1n;
  const D0 = 2n * p ** BigInt(K + 1);
  assert(SCALE % D0 === 0n, "fixed-point scale does not cover D0");

  function update(R, prefix, c, r) {
    if (r < K) {
      // Exact shallow-gate increment:
      // delta = c + (z-1)/2 * sum(t_i z^i) + (5z^r-z^(r+1))/2,
      // with z=1/p and alpha=3/D0.
      let t = prefix[0] + 1n + c;
      let discountedCarryNumerator = 0n;
      for (let i = 0; i <= r; i++) {
        discountedCarryNumerator += t * p ** BigInt(K - 1 - i);
        if (i < r) {
          assert(t % 2n === 0n, "carry before terminal index is not even");
          t = prefix[i + 1] + 1n + t / 2n;
        }
      }
      const deltaScaled =
        c * D0 +
        (1n - p) * p * discountedCarryNumerator +
        5n * p ** BigInt(K + 1 - r) -
        p ** BigInt(K - r);
      const centeredIncrement = deltaScaled - 3n * (c + 2n);
      return R + centeredIncrement * (SCALE / D0);
    }

    // Deep-gate upper recurrence for R=P(z)-alpha*M:
    // R' <= (p/d)R + h, with h=hNumerator/(d*D0).
    const hNumerator =
      2n * c * p ** BigInt(K + 2) +
      c * (p - 1n) +
      d * (5n * p - 1n) -
      3n * d * (c + 2n);
    const hScaled = ceilDiv(hNumerator * SCALE, d * D0);
    return ceilDiv(p * R, d) + hScaled;
  }

  function simulate(start) {
    let R = start;
    let prefix = ROOT9.slice();
    let deep = 0;
    let shallow = 0;
    let maximum = R;
    let maximumPhase = null;

    for (let ret = 0; ret < PERIOD; ret++) {
      for (let stage = 0; stage < 3; stage++) {
        const c = C[stage];
        const r = v2cap(weight(prefix) + c, K);
        R = update(R, prefix, c, r);
        if (r < K) shallow++;
        else deep++;

        if (R > maximum) {
          maximum = R;
          maximumPhase = { ret, stage, carryDepthAtLeast: r, offset: String(c) };
        }
        prefix = gp(c, prefix);
      }
    }

    return {
      end: R,
      maximum,
      maximumPhase,
      deep,
      shallow,
      closed: prefix.join(",") === ROOT9.join(",")
    };
  }

  // The initial discounted value is exact because SCALE is divisible by
  // every denominator p^i for i<=17 and by D0.
  let initialP = 0n;
  for (let i = 0; i < ROOT18.length; i++) {
    initialP += (ROOT18[i] + 1n) * (SCALE / p ** BigInt(i));
  }
  const initialR = initialP - 3n * M0 * (SCALE / D0);

  // The period map contracts by (p/d)^703.  Since p/d<=2/3 and there are
  // 703 deep gates, its coefficient is <1/2.  If B bounds the period
  // constant from start zero, 2B+1 is a period-start invariant.
  const fromZero = simulate(0n);
  assert(fromZero.deep === 703, "unexpected deep-gate count");
  assert(fromZero.shallow === 245057, "unexpected shallow-gate count");
  assert(fromZero.closed, "nine-digit prefix did not close");
  assert(fromZero.end > 0n, "expected positive period constant");

  const periodStartCap = [
    0n,
    initialR,
    2n * fromZero.end + SCALE
  ].reduce((a, b) => a > b ? a : b);

  const boundedPeriod = simulate(periodStartCap);
  assert(boundedPeriod.closed, "bounded prefix cycle did not close");
  assert(boundedPeriod.end <= periodStartCap,
    "computed period-start invariant failed");

  const globalConstant = ceilDiv(boundedPeriod.maximum, SCALE);
  const asymptoticSlope =
    10 - Math.log(1.5) / (s * Math.log(2));

  return {
    s,
    z: `1/2^${s}`,
    alpha: `3/${D0}`,
    asymptotic_D_over_M_lower_limit: asymptoticSlope,
    deep_gates_per_period: fromZero.deep,
    shallow_gates_per_period: fromZero.shallow,
    initial_centered_value: decimal(initialR),
    period_constant_from_zero: decimal(fromZero.end),
    period_start_cap: decimal(periodStartCap),
    global_centered_cap: decimal(boundedPeriod.maximum),
    integer_C: String(globalConstant),
    period_start_invariant: boundedPeriod.end <= periodStartCap,
    maximum_phase: boundedPeriod.maximumPhase
  };
}

const rootMass = ROOT18.reduce((sum, digit) => sum + digit + 1n, 0n);
assert(rootMass === M0, "return-5457 root mass mismatch");

const results = [];
for (let s = 1; s <= 8; s++) results.push(oneScale(s));
console.log(JSON.stringify(results, null, 2));
