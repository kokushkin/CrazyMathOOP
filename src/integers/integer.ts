export class Integer {
  public integer: number;

  constructor(integer: number) {
    this.integer = integer;
  }

  public plus(anotherInt: Integer) {
    return new Integer(this.integer + anotherInt.integer);
  }

  public minus(anotherInt: Integer) {
    return new Integer(this.integer - anotherInt.integer);
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

  public more(anotherInt: Integer) {
    return this.integer > anotherInt.integer;
  }

  public less(anotherInt: Integer) {
    return this.integer < anotherInt.integer;
  }

  public mod() {
    if (this.less(new Integer(0))) return new Integer(0).minus(this);
    return this;
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

  public theorem1_1_1(n: Integer, m: Integer, all: Integer[]) {
    if (!m.more(new Integer(0))) {
      throw new Error("m must be more then 0");
    }

    const specialForms: Integer[] = [];
    all.forEach((s) => {
      const form = n.minus(s.times(m));
      if (!form.less(new Integer(0))) {
        specialForms.push(form);
      }
    });

    if (specialForms.length === 0) {
      throw new Error("Can't be empty. WHY??");
    }

    const r = specialForms.sort()[0];

    if (!r.less(m.mod())) {
      if (
        !(
          r.minus(m.mod()).more(new Integer(0)) ||
          r.minus(m.mod()).equal(new Integer(0))
        )
      ) {
        throw new Error("Impossible");
      }
    }

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
