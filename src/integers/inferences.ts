export class I {
  static logicChain(predicates: any[]) {
    for (let pred in predicates) {
      if (!pred) {
        throw new Error("Wrong conclusion");
      }
    }
    return true;
  }

  static functionsChain(functions: any[]) {
    let i = 0;
    while (i < functions.length - 1) {
      this.True(functions[i] === functions[i + 1]);
    }
  }

  static True(predicate: boolean) {
    if (!predicate) {
      throw new Error("It must be True");
    }
  }
}
