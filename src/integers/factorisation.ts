import { Prime, BasicDivisionDefinitions } from "./basic-division-definnitions";
import { I } from "./inferences";
import { Q } from "./quantifiers";
import { existOneDividesOneOfTheFactorsIFFDividesProduct } from "./integer";

class Factorization {
  n: number;
  primes: number[];
  exponents: number[];
  constructor(n: number, primes: number[], exponents: number[]) {
    for (let i = 0; i < primes.length - 1; i++) {
      if (primes[i] >= primes[i + 1]) {
        throw new Error("Primes must be ordered");
      }
    }
    this.n = n;
    this.primes = primes;
    this.exponents = exponents;
  }

  //
  multiply(fac: Factorization) {
    const primes: number[] = Array.from(
      new Set(this.primes.concat(fac.primes))
    );
    const exponents: number[] = [];
    for (let prime of primes) {
      let exponent = 0;
      if (this.exponents[this.primes.indexOf(prime)]) {
        exponent += this.exponents[this.primes.indexOf(prime)];
      }
      if (fac.exponents[fac.primes.indexOf(prime)]) {
        exponent += fac.exponents[fac.primes.indexOf(prime)];
      }
      exponents.push(exponent);
    }

    return new Factorization(this.n * fac.n, primes, exponents);
  }

  findDividentFactor(q: number): number | null {
    if (this.primes.length === 0) {
      return null;
    }
    const p1 = this.primes[0];
    const dividend = existOneDividesOneOfTheFactorsIFFDividesProduct(
      new Prime(q),
      p1,
      this.n / p1
    );

    if (dividend === p1) {
      return dividend;
    } else {
      this.reduce();
      return this.findDividentFactor(q);
    }
  }

  reduce() {
    if (this.exponents[0] > 1) {
      this.exponents[0] = --this.exponents[0];
    } else {
      this.primes.shift();
      this.exponents.shift();
    }
    this.n = this.n / this.primes[0];
  }
}

function existsFactorisation(n: number): Factorization {
  if (n === 1) {
    return new Factorization(1, [1], [1]);
  }
  // n > 1
  const n1 = Q.any();
  Q.assume(I.True(n1 < n));
  Q.assume(existsFactorisation(n1) !== undefined);

  try {
    return existsFactorisation(n);
  } catch (err) {
    if (BasicDivisionDefinitions.isPrime(n)) {
      const primeUniqueFactorisation = new Factorization(n, [n], [1]);
      return primeUniqueFactorisation;
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

    const factorisationOfX = existsFactorisation(x);
    const factorisationOfY = existsFactorisation(y);
    const factorisation = factorisationOfX.multiply(factorisationOfY);

    return factorisation; // Contradiction
  }
}

function factorisationsAreEqual(
  qFactorisation: Factorization,
  pFactorisation: Factorization
) {
  if (
    qFactorisation.primes.length === 0 &&
    pFactorisation.primes.length === 0
  ) {
    return;
  }

  const q1 = qFactorisation.primes[0];
  I.True(BasicDivisionDefinitions.divides(q1, qFactorisation.n));
  I.True(BasicDivisionDefinitions.divides(q1, pFactorisation.n));
  const pi = pFactorisation.findDividentFactor(q1);
  if (pi === null) {
    throw new Error("Contradiction!");
  }
  // becasue q1 and pi are primes
  I.True(q1 === pi);
  const i = pFactorisation.primes.indexOf(pi);

  if (1 === i) {
    //q1 === p1
    //make recursion
    qFactorisation.reduce();
    pFactorisation.reduce();
    factorisationsAreEqual(qFactorisation, pFactorisation);
  }

  // 1 < i
  const p1 = pFactorisation.primes[0];
  I.True(p1 < pi);

  I.True(BasicDivisionDefinitions.divides(p1, qFactorisation.n));
  I.True(BasicDivisionDefinitions.divides(p1, pFactorisation.n));

  const qj = qFactorisation.findDividentFactor(p1);

  if (qj === null) {
    throw new Error("Contradiction!");
  }
  // becasue q1 and pi are primes
  I.True(p1 === qj);
  I.True(qj >= q1);
  I.True(q1 === pi);
  I.True(pi > p1);
  // impossibe
  I.True(p1 > p1);
}

export function existsUniqueFactorisation(n: number): Factorization {
  const qFactorisation = existsFactorisation(n);
  const pFactorisation = existsFactorisation(n);
  Q.assume(qFactorisation !== pFactorisation);
  factorisationsAreEqual(qFactorisation, pFactorisation);

  //TODO: qFactorisation and pFactorisation were changed!
  return qFactorisation;
}
