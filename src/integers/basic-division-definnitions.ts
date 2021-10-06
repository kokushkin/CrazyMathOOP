import { Q } from "./quantifiers";
import { I } from "./inferences";

export class BasicDivisionDefinitions {
  static divides(
    d: number, // 4
    n: number // 8
  ) {
    try {
      BasicDivisionDefinitions.existsDivision(d, n);
      return true;
    } catch (ex) {
      return false;
    }
  }

  static multiple(n: number, d: number) {
    return BasicDivisionDefinitions.divides(d, n);
  }

  static existsDivision(
    d: number, // 4
    n: number // 8
  ) {
    const oneMore = Q.exist(); // 56
    I.True(n === d * oneMore);
    return oneMore;
  }

  static isProperDivisor(d: number, n: number) {
    return d !== n && d !== -n && d !== 1 && d !== -1 && this.divides(d, n);
  }
  static isPrime(p: number) {
    const divisor = Q.any();
    return p > 1 && !this.isProperDivisor(divisor, p);
  }
}
