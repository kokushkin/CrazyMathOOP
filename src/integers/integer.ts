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
  oneInteger: number,
  anotherInteger: number,
  OneAnotherInteger: number
) {
  return anotherInteger === oneInteger * OneAnotherInteger;
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

  functionsChain([a * x + b * y, a * r * d + b * s * d, d * (a * r + b * s)]);

  return divides(d, a * x + b * y, a * r + b * s) === true;
}

function theorem1_1_1(n: number, m: number, all: number[]) {
  /// requirements
  if (m === 0) {
    throw new Error("m must be more then 0");
  }
  /// end of requirements

  /// proof
  const specialForms: number[] = [];
  all.forEach((s) => {
    const form = n - s * m;
    if (form >= 0) {
      specialForms.push(form);
    }
  });

  if (specialForms.length === 0) {
    throw new Error("Can't be empty. WHY??");
  }

  const r = specialForms.sort()[0];
  const q = -(r - n) / m;
  logicChain([r === n - q * m]);

  if (!(r < mod(m))) {
    logicChain([r >= mod(m), r - mod(m) >= 0]);

    functionsChain([
      r - mod(m),
      n - q * m - mod(m),
      q >= 0 ? n - (q + 1) * m : n - (q - 1) * m
    ]);

    const substitution2 = q >= 0 ? n - (q + 1) * m : n - (q - 1) * m;

    if (specialForms.indexOf(substitution2) && substitution2 < r) {
      throw new Error("Contradiction");
    }

    return false;
  }
  //(r < mod(m))
  else {
    // results
    logicChain([n === q * m + r && r > 0 && r <= mod(m)]);
    return true;
  }
}
