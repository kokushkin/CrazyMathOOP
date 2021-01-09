export class Integer {
  public integer: number;

  constructor(integer: number) {
    this.integer = integer;
  }

  public plus(anotherInt: Integer) {
    return new Integer(this.integer + anotherInt.integer);
  }

  public times(anotherInt: Integer) {
    return new Integer(this.integer * anotherInt.integer);
  }

  public equal(anotherInt: Integer) {
    return this.integer === anotherInt.integer;
  }

  public divides(anotherInteger: Integer, anotherOneInteger: Integer) {
    return anotherInteger.equal(this.times(anotherOneInteger));
  }

  public IfIntegerDividesTwoOthersThemItDividesTheCombination(
    d: Integer,
    x: Integer,
    y: Integer,
    r: Integer,
    s: Integer,
    a: Integer,
    b: Integer
  ) {
    const combinations = a.plus(x).plus(b.times(y));
    const regroup = a.times(r.times(d)).plus(b.times(s.times(d)));
    const dDivideSum = d.times(a.times(r).plus(b.times(s)));

    if (d.divides(x, r) && d.divides(y, s)) {
      return combinations === regroup && regroup === dDivideSum;
    }
    return false;
  }

  public theorem1_1_1(n: Integer, m: Integer, allIntegers: Integer[]) {
    if (m.integer === 0) {
      return;
    }

    const getNotNegativeIntegerInForm = (s: Integer) => {
      const form = n.integer - s.integer * m.integer;
      if (form < 0) {
        return;
      }
      return form;
    };
    const setOfIntegersInFrom = allIntegers.map((integer) =>
      getNotNegativeIntegerInForm(integer)
    );

    return {};
  }
}

export class ReductionModulo {
  public n: Integer;
  public q: Integer;
  public m: Integer;
  public r: Integer;

  constructor(n: Integer, q: Integer, m: Integer, r: Integer) {
    this.n = n;
    this.q = q;
    this.m = m;
    this.r = r;
  }

  public definition() {
    return this.n.integer === this.q.integer * this.m.integer + this.r.integer;
  }
}
