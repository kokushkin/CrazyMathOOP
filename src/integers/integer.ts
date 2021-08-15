import { Quantifiers } from "./quantifiers";
import { BasicDivisionDefinitions } from "./basic-division-definnitions";
import { Inferences } from "./inferences";

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

  Inferences.functionsChain([
    a * x + b * y,
    a * (r * d) + b * (s * d),
    d * (a * r + b * s)
  ]);

  return BasicDivisionDefinitions.divides(d, a * x + b * y) === true;
}

class TwoIntegers {
  n: number;
  m: number;
  constructor(n: number, m: number) {
    if (m === 0) {
      throw new Error("m must not be = 0");
    }
    this.n = n;
    this.m = m;
  }
}

class ReductionModuloResult {
  n: number;
  m: number;
  r: number;
  q: number;
  constructor(integers: TwoIntegers, r: number, q: number) {
    if (integers.n === q * integers.m + r && r >= 0 && r <= abs(integers.m)) {
      this.n = integers.n;
      this.m = integers.m;
      this.r = r;
      this.q = q;
    } else {
      throw new Error("Wrong numbers");
    }
  }
}

class Exist<T> {
  obj: T;
  constructor(obj: T) {
    this.obj = obj;
  }
}

class ExistOnlyOne<T> {
  obj: Exist<T>;
  constructor(obj: Exist<T>) {
    this.obj = obj;
  }
}

const allNumbers: number[] = [];

type ReductionModuloTheorem = (
  integers: TwoIntegers
) => ExistOnlyOne<ReductionModuloResult>;

const reductionModuloTheorem: ReductionModuloTheorem = (integers) => {
  const n = integers.n;
  const m = integers.m;

  /// proof
  // Proof: Let S be the set of all non-negative integers
  // expressible in the form N − sm for some integer s.
  const specialForms: number[] = [];
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

  let existingReductionModulo: Exist<ReductionModuloResult>;
  // Claim that r < |m|.
  if (r < abs(m)) {
    existingReductionModulo = new Exist(
      new ReductionModuloResult(integers, r, q)
    );
  }
  // If not, then
  // still r − |m| ≥ 0,
  else {
    Inferences.logicChain([r >= abs(m), r - abs(m) >= 0]);
    //  and also
    // r − |m| = (N − qm) − |m| = N − (q ± 1)m
    const s1 = q + 1;
    Inferences.functionsChain([
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

  const anotherExistingReductionModule = new Exist(
    new ReductionModuloResult(integers, 3, 5)
  );

  const _r = anotherExistingReductionModule.obj.r;
  const _q = anotherExistingReductionModule.obj.q;

  Inferences.functionsChain([r - _r, m * (_q - q)]);
  Inferences.logicChain([
    0 <= r && r < abs(r) && 0 <= _r && _r < abs(_r),
    -abs(m) < r - _r && r - _r < abs(m),
    -abs(m) < m * (_q - q) && m * (_q - q) < abs(m)
  ]);

  if (m > 0) {
    Inferences.logicChain([
      -abs(m) < m * (_q - q) && m * (_q - q) < abs(m),
      -abs(m) / m < _q - q && _q - q < abs(m) / m,
      -1 < m * (_q - q) && _q - q < 1,
      _q === q
    ]);
  } else {
    Inferences.logicChain([
      -abs(m) < m * (_q - q) && m * (_q - q) < abs(m),
      -abs(m) / m > _q - q && _q - q > abs(m) / m,
      1 > m * (_q - q) && _q - q > -1,
      _q === q
    ]);
  }

  Inferences.logicChain([_q === q, r === _r]);

  return new ExistOnlyOne(existingReductionModulo);
};

// A positive integer n is prime if and only if it is not divisible by any of the integers
// d with 1 < d ≤ √n.

class PositivePrime {
  p: number;
  constructor(p: number) {
    if (BasicDivisionDefinitions.isPrime(p) && p > 0) {
      this.p = p;
    } else {
      throw new Error("Wrong numbers");
    }
  }
}

class NotDivisibleWithLessThanRoot {
  p: number;
  constructor(p: number) {
    const d = Quantifiers.any();
    if (1 < d && d <= Math.sqrt(p) && !BasicDivisionDefinitions.divides(d, p)) {
      this.p = p;
    } else {
      throw new Error("Bad luck");
    }
  }
}

function NotDivisibleWithLessThenRootThenPositivePrime(
  notDivisblePositive: NotDivisibleWithLessThanRoot
): PositivePrime {
  // positive integer:
  // divistible  => has  a divisor <= sqrt(n)
  const n = Quantifiers.any();
  const d = Quantifiers.exist();
  const e = Quantifiers.exist();

  if (
    n > 0 &&
    n === d * e &&
    BasicDivisionDefinitions.isProperDivisor(d, n) &&
    BasicDivisionDefinitions.isProperDivisor(e, n) &&
    d <= e
  ) {
    Inferences.functionsChain([
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
  const d = Quantifiers.any();
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
    throw new Error("Bad luck");
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

class NotZero {
  n: number;
  constructor(n: number) {
    if (n > 0) {
      this.n = n;
    } else {
      throw new Error("Bad luck");
    }
  }
}

class PairNotZero {
  n: NotZero;
  m: NotZero;
  constructor(n: NotZero, m: NotZero) {
    this.n = n;
    this.m = m;
  }
}

//gcd(m, n).
class GreatestCommonDevisior {
  pair: PairNotZero;
  d: number;
  constructor(pair: PairNotZero, d: number) {
    const e = Quantifiers.any();
    if (
      BasicDivisionDefinitions.divides(d, pair.n.n) &&
      BasicDivisionDefinitions.divides(d, pair.n.n) &&
      d > 0 &&
      BasicDivisionDefinitions.divides(e, pair.n.n) &&
      BasicDivisionDefinitions.divides(e, pair.m.n) &&
      BasicDivisionDefinitions.divides(e, d)
    ) {
      this.pair = pair;
      this.d = d;
    } else {
      throw new Error("Bad luck");
    }
  }
}

class LeastPositiveIntegerOfTheXYForm {
  pair: PairNotZero;
  d: number;
  constructor(pair: PairNotZero, d: number) {
    const n = pair.n.n;
    const m = pair.m.n;
    const x = Quantifiers.any();
    const y = Quantifiers.any();
    const d1 = Quantifiers.any();

    Inferences.True(
      d > 0 && d1 > 0 && d === x * m + y * n && d1 === x * m + y * n && d <= d1
    );

    this.pair = pair;
    this.d = d;
  }
}

class GreatestCommonDevisiorAndLeastPositiveIntegerOfTheXYForm {
  gcd: GreatestCommonDevisior;
  least: LeastPositiveIntegerOfTheXYForm;
  constructor(pair: PairNotZero, d: number) {
    this.gcd = new GreatestCommonDevisior(pair, d);
    this.least = new LeastPositiveIntegerOfTheXYForm(pair, d);
  }
}

function greatesCommonDivisorTheorem(
  pair: PairNotZero
): GreatestCommonDevisiorAndLeastPositiveIntegerOfTheXYForm {
  const n = pair.n.n;
  const m = pair.m.n;
  const D = Quantifiers.exist();
  const leastPositiveInteger = new LeastPositiveIntegerOfTheXYForm(pair, D);
  const x0 = Quantifiers.exist();
  const y0 = Quantifiers.exist();

  Inferences.True(D === x0 * m + y0 * n);

  const d = Quantifiers.any();
  Inferences.True(
    BasicDivisionDefinitions.divides(d, n) &&
      BasicDivisionDefinitions.divides(d, m)
  );

  const m_ = Quantifiers.exist();
  const n_ = Quantifiers.exist();
  Inferences.True(n === n_ * d && m === m_ * d);

  Inferences.functionsChain([
    D,
    x0 * m + y0 * n,
    x0 * (m_ * d) + y0 * (n_ * d),
    (x0 * m_ + y0 * n_) * d
  ]);

  Inferences.True(BasicDivisionDefinitions.divides(d, D));

  const reductionModule = reductionModuloTheorem(new TwoIntegers(m, D));
  const q = reductionModule.obj.obj.q;
  const r = reductionModule.obj.obj.r;
  Inferences.True(0 <= r && r < D);

  Inferences.functionsChain([
    r,
    m - q * D,
    m - q * (x0 * m + y0 * n),
    (1 - q * x0) * m + -q * y0 * n
  ]);

  const x_ = 1 - q * x0;
  const y_ = -q * y0;
  Inferences.True(r === x_ * m + y_ * n);

  Inferences.logicChain([
    r < D && D === leastPositiveInteger.d,
    r === 0,
    BasicDivisionDefinitions.divides(D, m)
  ]);
  Inferences.True(BasicDivisionDefinitions.divides(D, n));

  return new GreatestCommonDevisiorAndLeastPositiveIntegerOfTheXYForm(pair, D);
  // how to tell that it's unique?
}
