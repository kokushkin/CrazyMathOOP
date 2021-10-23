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

class Prime {
  p: number;
  constructor(p: number) {
    I.True(BasicDivisionDefinitions.isPrime(p));
    this.p = p;
  }
}

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
    I.functionsChain(
      d === n / e,
      n / e <= n / d,
      d <= n / d,
      Math.pow(d, 2) <= n,
      d <= Math.sqrt(n)
    );
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

function existsOnlyOneTheLeastPositiveXYForm(n: number, mnz: NotZeroInteger) {
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
  n: number,
  mnz: NotZeroInteger
) {
  const m = mnz.n;
  const leastPositiveForm = existsOnlyOneTheLeastPositiveXYForm(n, mnz);
  const { x, y, d: D } = leastPositiveForm;

  const d = Q.any();
  const m_ = Q.assume(BasicDivisionDefinitions.existsDivision(d, n));
  const n_ = Q.assume(BasicDivisionDefinitions.existsDivision(d, m));

  I.functionsChain(
    D,
    x * m + y * n,
    x * (m_ * d) + y * (n_ * d),
    (x * m_ + y * n_) * d
  );

  I.True(BasicDivisionDefinitions.divides(d, D));

  const reductionModule = existsOnlyOneReductionModulo(
    m,
    new NotZeroInteger(D)
  );
  const q = reductionModule.q;
  const r = reductionModule.r;

  I.functionsChain(
    r,
    m - q * D,
    m - q * (x * m + y * n),
    (1 - q * x) * m + -q * y * n
  );

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

function existOnlyOneLeastCommonMultiple(n: number, mnz: NotZeroInteger) {
  const m = mnz.n;
  const {
    d: gcd,
    x: a,
    y: b
  } = existsOnlyOneGreatestCommonDivisorInTheLeastPositiveXYForm(n, mnz);
  const n_ = BasicDivisionDefinitions.existsDivision(gcd, n);
  const m_ = BasicDivisionDefinitions.existsDivision(gcd, m);

  I.True(n === n_ * gcd);
  I.True(m === m_ * gcd);
  const L = (n * m) / gcd;
  I.functionsChain(L, (n * m) / gcd, (n_ * gcd * m) / gcd, n_ * m);
  I.functionsChain(L, (n * m) / gcd, (n * m_ * gcd) / gcd, n * m_);
  I.True(L === n_ * m && L === n * m_);

  const M = Q.assume(Q.exist());
  const s = Q.assume(BasicDivisionDefinitions.existsDivision(n, M));
  const r = Q.assume(BasicDivisionDefinitions.existsDivision(m, M));

  I.True(gcd === a * m + b * n);
  I.functionsChain(gcd, a * m + b * n, a * m_ * gcd + b * n_ * gcd);
  I.True(1 === a * m_ + b * n_);
  I.functionsChain(
    M,
    1 * M,
    (a * m_ + b * n_) * M,
    a * m_ * M + b * n_ * M,
    a * m_ * s * n + b * n_ * r * m,
    (a * s + b * r) * L
  );

  I.True(BasicDivisionDefinitions.multiple(M, L));

  return L;
}

function devidesProductIfAndOnlyIfDevidesOneOfThem(
  prime: Prime,
  a: number,
  b: number
) {
  const p = prime.p;

  if (BasicDivisionDefinitions.divides(p, a)) {
    return true;
  } else {
    const {
      d: gcd,
      x: r,
      y: s
    } = existsOnlyOneGreatestCommonDivisorInTheLeastPositiveXYForm(
      p,
      new NotZeroInteger(a)
    );
    I.True(gcd !== p);
    I.True(gcd === 1);
    const k = BasicDivisionDefinitions.existsDivision(p, a * b);
    I.True(k * p === a * b);
    I.functionsChain(
      b,
      b * 1,
      b * (r * p + s * a),
      b * r * p + s * a * b,
      b * r * p + s * k * p,
      p * (r * b + s * k)
    );
    I.True(BasicDivisionDefinitions.divides(p, a));
    return true;
  }
}

class Factorisation {
  n: number;
  primes: number[];
  exponents: number[];
  constructor(n: number, primes: number[], exponents: number[]) {
    // TODO: add check I.True
    this.n = n;
    this.primes = primes;
    this.exponents = exponents;
  }
}

function existFactorisation(n: number): Factorisation {
  if (n === 1) {
    return new Factorisation(1, [1], [1]);
  }

  // n > 1
  const n1 = Q.any();
  Q.assume(I.True(n1 < n));
  Q.assume(existFactorisation(n1) !== undefined);

  const nUniqueFactorisation = existFactorisation(n);
  if (nUniqueFactorisation === undefined) {
    if (BasicDivisionDefinitions.isPrime(n)) {
      const primeUniqueFactorisation = new Factorisation(n, [n], [1]);
      I.True(nUniqueFactorisation !== undefined);
      throw new Error("Contradiction");
    }

    const x = Q.exist();
    const y = Q.exist();
    I.True(
      BasicDivisionDefinitions.isProperDivisor(x, n) &&
        BasicDivisionDefinitions.isProperDivisor(y, n)
    );
    I.True(n === x * y);
    I.True(x < n);
    I.True(y < n);
    const uniqueFactorisationOfX = existFactorisation(x);
    const uniqueFactorisationOfY = existFactorisation(y);
    I.True(
      nUniqueFactorisation === uniqueFactorisationOfX * uniqueFactorisationOfY
    );
    throw new Error("Contradiction");
  }

  I.True(nUniqueFactorisation !== undefined);

  return nUniqueFactorisation;
}

function existUniqueFactorisation(n: number): Factorisation {
  const qFactorisation = existFactorisation(n);
  const pFactorisation = existFactorisation(n);
  Q.assume(qFactorisation !== pFactorisation);

  const q1 = qFactorisation.primes[0];
  I.True(BasicDivisionDefinitions.divides(q1, qFactorisation.n));
  I.True(BasicDivisionDefinitions.divides(q1, pFactorisation.n));

  // devidesProductIfAndOnlyIfDevidesOneOfThem(q1);
}
