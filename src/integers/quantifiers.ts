export class Quantifiers {
  static any(): number {
    return Math.floor(Math.random() * 1000000);
  }

  static exist() {
    return Math.floor(Math.random() * 1000000);
  }

  // static existq(quatifier: (...params: number[]) => unknown) {
  //   return quatifier;
  // }

  // static anyq(quatifier: (...params: number[]) => unknown) {
  //   return quatifier;
  // }
}
