export class Q {
  static any(): number {
    return Math.floor(Math.random() * 1000000);
  }

  static exist() {
    return Math.floor(Math.random() * 1000000);
  }

  static assume<T>(x: T) {
    return x;
  }

  // static existq(quatifier: (...params: number[]) => unknown) {
  //   return quatifier;
  // }

  // static anyq(quatifier: (...params: number[]) => unknown) {
  //   return quatifier;
  // }
}
