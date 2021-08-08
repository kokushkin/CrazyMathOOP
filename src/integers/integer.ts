function logicChain(predicates: any[]) {
  for (let pred in predicates) {
    if (!pred) {
      throw new Error("Wrong conclusion");
    }
  }
  return true;
}

function functionsChain(functions: any[]) {
  let i = 0;
  while (i < functions.length - 1) {
    if (functions[i] !== functions[i + 1]) {
      throw new Error("Wrong sequence");
    }
  }
  return true;
}

function mod(n: number) {
  if (n < 0) {
    return -n;
  } else {
    return n;
  }
}

function divides(
  divedend: number, // 4
  devisor: number // 8
) {
  const oneMore = any(); // 56
  if (devisor === divedend * oneMore) {
    return true;
  }
  return devisor === divedend * oneMore;
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
  if (!(divides(d, x, r) && divides(d, y, s))) {
    throw new Error("This is initial conditions");
  }
  /// end of requirements

  functionsChain([
    a * x + b * y,
    a * (r * d) + b * (s * d),
    d * (a * r + b * s)
  ]);

  return divides(d, a * x + b * y, a * r + b * s) === true;
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
    if (integers.n === q * integers.m + r && r >= 0 && r <= mod(integers.m)) {
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
  if (r < mod(m)) {
    existingReductionModulo = new Exist(
      new ReductionModuloResult(integers, r, q)
    );
  }
  // If not, then
  // still r − |m| ≥ 0,
  else {
    logicChain([r >= mod(m), r - mod(m) >= 0]);
    //  and also
    // r − |m| = (N − qm) − |m| = N − (q ± 1)m
    const s1 = q + 1;
    functionsChain([
      r - mod(m),
      n - q * m - mod(m),
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

  functionsChain([r - _r, m * (_q - q)]);
  logicChain([
    0 <= r && r < mod(r) && 0 <= _r && _r < mod(_r),
    -mod(m) < r - _r && r - _r < mod(m),
    -mod(m) < m * (_q - q) && m * (_q - q) < mod(m)
  ]);

  if (m > 0) {
    logicChain([
      -mod(m) < m * (_q - q) && m * (_q - q) < mod(m),
      -mod(m) / m < _q - q && _q - q < mod(m) / m,
      -1 < m * (_q - q) && _q - q < 1,
      _q === q
    ]);
  } else {
    logicChain([
      -mod(m) < m * (_q - q) && m * (_q - q) < mod(m),
      -mod(m) / m > _q - q && _q - q > mod(m) / m,
      1 > m * (_q - q) && _q - q > -1,
      _q === q
    ]);
  }

  logicChain([_q === q, r === _r]);

  return new ExistOnlyOne(existingReductionModulo);
};

function any(): number {
  return Math.floor(Math.random() * 1000000);
}



function isPrime(p: number) {
  const divisor = any();
  return p > 1 && !isProperDivisor(divisor, p);
}

// A positive integer n is prime if and only if it is not divisible by any of the integers
// d with 1 < d ≤ √n.

class PositivePrime {
  p: number;
  constructor(p: number) {
    if (isPrime(p) && p > 0) {
      this.p = p;
    } else {
      throw new Error("Wrong numbers");
    }
  }
}

class NotDivisibleWithLessThanRoot {
  p: number;
  constructor(p: number) {
    const d = any();
    if (1 < d && d <= Math.sqrt(p) && !divides(d, p)) {
      this.p = p;
    } else {
      throw new Error("Bad luck");
    }
  }
}

function isProperDivisor(d: number, n: number) {
  return d !== n && d !== -n && d !== 1 && d !== -1 && divides(d, n);
}

function IfPositivePrimeThenNotDivisibleWithLessThenRoot(
  prime: PositivePrime
): NotDivisibleWithLessThanRoot {

  ///sdfsdfsdf
  ///dsfsdfsdf
  ///sf sdf 
  /// to be continued....
  const d = exist();
  const e = exist();
  if (n === d * e && isProperDivisor(d, n) && isProperDivisor(e, n) && d <= e) {
    functionsChain([
      d === n / e,
      n / e <= n / d,
      d <= n / d,
      Math.pow(d, 2) <= n,
      d <= Math.sqrt(n)
    ]);
    return new NotDivisibleWithLessThanRoot(prime.p);
  } else {
    throw new Error("Bad luck");
  }
}

function NotDivisibleWithLessThenRoot IfPositivePrimeThen(
  prime: PositivePrime
): NotDivisibleWithLessThanRoot {



