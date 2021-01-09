function flch(expression: boolean) {
  if (!expression) {
    throw new Error("Math doesn't work");
  }
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

  flch(
    a * x + b * y === a * r * d + b * s * d &&
      a * r * d + b * s * d === d * (a * r + b * s)
  );

  return divides(d, a * x + b * y, a * r + b * s) === true;
}

function theorem1_1_1(n: number, m: number, all: number[]) {
  /// requirements
  if (!(m > 0)) {
    throw new Error("m must be more then 0");
  }
  /// end of requirements

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
  flch(r === n - q * m);

  if (!(r < mod(m))) {
    flch(r >= mod(m) && r - mod(m) >= 0);

    flch(
      r - mod(m) === n - q * m - mod(m) &&
        n - q * m - mod(m) === n - (q - 1) * m
    );
  }

  return {};
}
