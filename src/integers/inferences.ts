export class Inferences {
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
      if (functions[i] !== functions[i + 1]) {
        throw new Error("Wrong sequence");
      }
    }
    return true;
  }
}
