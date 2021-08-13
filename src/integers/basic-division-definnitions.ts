import { Quantifiers } from "./quantifiers";

export class BasicDivisionDefinitions {
  static divides(
    divedend: number, // 4
    devisor: number // 8
  ) {
    const oneMore = Quantifiers.exist(); // 56
    if (devisor === divedend * oneMore) {
      return true;
    } else {
      return false;
    }
  }

  static isProperDivisor(d: number, n: number) {
    return d !== n && d !== -n && d !== 1 && d !== -1 && this.divides(d, n);
  }
  static isPrime(p: number) {
    const divisor = Quantifiers.any();
    return p > 1 && !this.isProperDivisor(divisor, p);
  }
}
