import { Q } from "./quantifiers";
import { BasicDivisionDefinitions } from "./basic-division-definnitions";
import { I } from "./inferences";

function abs(n: number) {
  if (n < 0) {
    return -n;
  } else {
    return n;
  }
}

function ifDevidesTwoThenDevidesTheirCombination(
  d: number,
  x: number,
  y: number,
  r: number,
  s: number,
  a: number,
  b: number
) {
  /// requirements
  if (
    !(
      BasicDivisionDefinitions.divides(d, x) &&
      BasicDivisionDefinitions.divides(d, y)
    )
  ) {
    throw new Error("This is initial conditions");
  }
  /// end of requirements

  I.functionsChain([
    a * x + b * y,
    a * (r * d) + b * (s * d),
    d * (a * r + b * s)
  ]);

  return BasicDivisionDefinitions.divides(d, a * x + b * y) === true;
}

class NotZeroInteger {
  n: number;
  constructor(n: number) {
    I.True(n !== 0);
    this.n = n;
  }
}

class ReductionModulo {
  n: number;
  m: number;
  r: number;
  q: number;
  constructor(n: number, m: number, r: number, q: number) {
    I.True(n === q * m + r && r >= 0 && r <= abs(m));
    this.n = n;
    this.m = m;
    this.r = r;
    this.q = q;
  }
}

const allNumbers: number[] = [];

const existsOnlyOneReductionModulo = (
  n: number,
  mnz: NotZeroInteger
): ReductionModulo => {
  /// proof
  // Proof: Let S be the set of all non-negative integers
  // expressible in the form N − sm for some integer s.
  const m = mnz.n;
  const specialForms: number[] = [];
  const b = n + m;
  const rform = (s: number) => n - s * m;
  allNumbers.forEach((s) => {
    if (rform(s) >= 0) {
      specialForms.push(rform(s));
    }
  });

  // The set S is non-empty
  if (specialForms.length === 0) {
    throw new Error("Can't be empty.");
  }

  // , so by well-ordering has a least element r = N − qm.
  const r = specialForms.sort()[0];
  let q = (n - r) / m;
  // rform(r);

  let existingReductionModulo: ReductionModulo;
  // Claim that r < |m|.
  if (r < abs(m)) {
    existingReductionModulo = new ReductionModulo(n, m, r, q);
  }
  // If not, then
  // still r − |m| ≥ 0,
  else {
    I.logicChain([r >= abs(m), r - abs(m) >= 0]);
    //  and also
    // r − |m| = (N − qm) − |m| = N − (q ± 1)m
    const s1 = q + 1;
    I.functionsChain([
      r - abs(m),
      n - q * m - abs(m),
      m >= 0 ? n - (q + 1) * m : n - (q - 1) * m,
      m >= 0 ? n - s1 * m : n - s1 * m
    ]);

    // const func_r = (n: number, q: number, m: number) => {
    //   return n - q * m;
    // }
    // const someForm = (r: (n: number, q: number, m: number) => number, m:number) => {
    //   return r - mod(m);
    // }

    // (with the sign depending on the sign of m) is still in the set S, contradiction

    const substitution = m >= 0 ? n - (q + 1) * m : n - (q - 1) * m;

    if (specialForms.indexOf(substitution) && substitution < r) {
      throw new Error("Contradiction");
    } else {
      throw new Error("Impossible");
    }
  }

  // For uniqueness, suppose that both N = qm + r and N = q′m + r′. Subtract to find
  // r − r′ = m · (q′ − q)
  // Thus, r − r′is a multiple of m. But since −|m| < r − r′ < |m| we have r = r′. And then q = q′.

  const _r = Q.assume(Q.exist());
  const _q = Q.assume(Q.exist());
  const anotherExistingReductionModule = new ReductionModulo(n, m, _r, _q);

  I.functionsChain([r - _r, m * (_q - q)]);
  I.logicChain([
    0 <= r && r < abs(r) && 0 <= _r && _r < abs(_r),
    -abs(m) < r - _r && r - _r < abs(m),
    -abs(m) < m * (_q - q) && m * (_q - q) < abs(m)
  ]);

  if (m > 0) {
    I.logicChain([
      -abs(m) < m * (_q - q) && m * (_q - q) < abs(m),
      -abs(m) / m < _q - q && _q - q < abs(m) / m,
      -1 < m * (_q - q) && _q - q < 1,
      _q === q
    ]);
  } else {
    I.logicChain([
      -abs(m) < m * (_q - q) && m * (_q - q) < abs(m),
      -abs(m) / m > _q - q && _q - q > abs(m) / m,
      1 > m * (_q - q) && _q - q > -1,
      _q === q
    ]);
  }

  I.logicChain([_q === q, r === _r]);

  return existingReductionModulo;
};

// A positive integer n is prime if and only if it is not divisible by any of the integers
// d with 1 < d ≤ √n.

class PositivePrime {
  p: number;
  constructor(p: number) {
    I.True(BasicDivisionDefinitions.isPrime(p) && p > 0);
    this.p = p;
  }
}

class NotDivisibleWithLessThanRoot {
  p: number;
  constructor(p: number) {
    const d = Q.any();
    I.True(
      1 < d && d <= Math.sqrt(p) && !BasicDivisionDefinitions.divides(d, p)
    );
    this.p = p;
  }
}

function NotDivisibleWithLessThenRootThenPositivePrime(
  notDivisblePositive: NotDivisibleWithLessThanRoot
): PositivePrime {
  // positive integer:
  // divistible  => has  a divisor <= sqrt(n)
  const n = Q.any();
  const d = Q.exist();
  const e = Q.exist();

  if (
    n > 0 &&
    n === d * e &&
    BasicDivisionDefinitions.isProperDivisor(d, n) &&
    BasicDivisionDefinitions.isProperDivisor(e, n) &&
    d <= e
  ) {
    I.functionsChain([
      d === n / e,
      n / e <= n / d,
      d <= n / d,
      Math.pow(d, 2) <= n,
      d <= Math.sqrt(n)
    ]);
    // positive integer:
    //not(divistible) i.e. prime  <= has no divisor <= sqrt(n)
    return new PositivePrime(notDivisblePositive.p);
  } else {
    throw new Error("Bad luck");
  }
}

function IfPositivePrimeThenNotDivisibleWithLessThenRoot(
  prime: PositivePrime
): NotDivisibleWithLessThanRoot {
  // obvious, because of prime
  return new NotDivisibleWithLessThanRoot(prime.p);
}

// check if it's prime
function trialDivisionPrimeTest(n: number): boolean {
  const maxd = Math.sqrt(n);

  for (let i = 2; i <= maxd; i++) {
    if (BasicDivisionDefinitions.divides(i, n)) {
      return false;
    }
  }
  return true;
}

// coprime
// mutually prime
function relativelyPrime(m: number, n: number): boolean {
  const d = Q.exist();
  if (
    BasicDivisionDefinitions.divides(d, m) &&
    BasicDivisionDefinitions.divides(d, n)
  ) {
    if (d === -1 || d === 1) {
      return true;
    } else {
      return false;
    }
  } else {
    return false;
  }
}

// n = 10; m=21
// n = 1o; m= 5;
function relativelyPrime1(m: number, n: number): boolean {
  const d = Q.any(); // d =5
  if (
    BasicDivisionDefinitions.divides(d, m) &&
    BasicDivisionDefinitions.divides(d, n)
  ) {
    if (d === -1 || d === 1) {
      return true;
    } else {
      return false;
    }
  } else {
    return true;
  }
}

function commonDivisor(d: number, n: number[]) {
  for (const ni of n) {
    if (!BasicDivisionDefinitions.divides(d, ni)) {
      return false;
    }
  }

  return true;
}

function commonMultiple(N: number, n: number[]) {
  for (const ni of n) {
    if (!BasicDivisionDefinitions.divides(ni, N)) {
      return false;
    }
  }

  return true;
}

class XYForm {
  n: number;
  m: number;
  x: number;
  y: number;
  d: number;
  constructor(n: number, m: number, x: number, y: number, d: number) {
    I.True(d === x * m + y * n);

    this.n = n;
    this.m = m;
    this.x = x;
    this.y = y;
    this.d = d;
  }
}

function existsOnlyOneTheLeastPositiveXYForm(
  nnz: NotZeroInteger,
  mnz: NotZeroInteger
) {
  const n = nnz.n;
  const m = mnz.n;
  const x1 = Q.any();
  const y1 = Q.any();
  const x = Q.exist();
  const y = Q.exist();
  const d = x * m + y * n;
  I.True(d > 0 && d <= x1 * m + y1 * n);

  return new XYForm(n, m, x, y, d);
}

function existsOnlyOneGreatestCommonDivisorInTheLeastPositiveXYForm(
  nnz: NotZeroInteger,
  mnz: NotZeroInteger
) {
  const n = nnz.n;
  const m = mnz.n;
  const leastPositiveForm = existsOnlyOneTheLeastPositiveXYForm(nnz, mnz);
  const { x, y, d: D } = leastPositiveForm;

  const d = Q.any();
  const m_ = Q.assume(BasicDivisionDefinitions.existsDivision(d, n));
  const n_ = Q.assume(BasicDivisionDefinitions.existsDivision(d, m));

  I.functionsChain([
    D,
    x * m + y * n,
    x * (m_ * d) + y * (n_ * d),
    (x * m_ + y * n_) * d
  ]);

  I.True(BasicDivisionDefinitions.divides(d, D));

  const reductionModule = existsOnlyOneReductionModulo(
    m,
    new NotZeroInteger(D)
  );
  const q = reductionModule.q;
  const r = reductionModule.r;

  I.functionsChain([
    r,
    m - q * D,
    m - q * (x * m + y * n),
    (1 - q * x) * m + -q * y * n
  ]);

  const x_ = 1 - q * x;
  const y_ = -q * y;
  I.True(r === x_ * m + y_ * n);

  I.True(r < D);
  I.True(r === 0);
  I.True(BasicDivisionDefinitions.divides(D, m));

  // similarly
  I.True(BasicDivisionDefinitions.divides(D, n));

  return leastPositiveForm;
  // how to tell that it's unique?
}
