// Well-Behaved (Co)algebraic Semantics of Regular Expressions in Dafny
// Based on: S. Zetzsche and W. Rozowski (arXiv:2409.09889v1)

/*** Section 2.1: Regular Expressions as Datatype ***/

datatype Exp<A> = Zero | One | Char(A) | Plus(Exp, Exp) | Comp(Exp, Exp) | Star(Exp)

/*** Section 2.2: Formal Languages as Codatatype ***/

codatatype Lang<!A> = Alpha(eps: bool, delta: A -> Lang<A>)

/*** Section 2.3: An Algebra of Formal Languages ***/

module Languages {
  codatatype Lang<!A> = Alpha(eps: bool, delta: A -> Lang<A>)

  function Zero<A>(): Lang {
    Alpha(false, (a: A) => Zero())
  }

  function One<A>(): Lang {
    Alpha(true, (a: A) => Zero())
  }

  function Singleton<A(==)>(a: A): Lang {
    Alpha(false, (b: A) => if a == b then One() else Zero())
  }

  function {:abstemious} Plus<A>(L1: Lang, L2: Lang): Lang {
    Alpha(L1.eps || L2.eps, (a: A) => Plus(L1.delta(a), L2.delta(a)))
  }

  function {:abstemious} Comp<A>(L1: Lang, L2: Lang): Lang {
    Alpha(L1.eps && L2.eps,
          (a: A) => Plus(Comp(L1.delta(a), L2),
                         Comp(if L1.eps then One() else Zero(), L2.delta(a))))
  }

  function {:abstemious} Star<A>(L: Lang): Lang {
    Alpha(true, (a: A) => Comp(L.delta(a), Star(L)))
  }
}

/*** Section 2.4: Denotational Semantics as Induced Morphism ***/

function Denotational<A(==)>(e: Exp): Languages.Lang {
  match e
  case Zero => Languages.Zero()
  case One => Languages.One()
  case Char(a) => Languages.Singleton(a)
  case Plus(e1, e2) => Languages.Plus(Denotational(e1), Denotational(e2))
  case Comp(e1, e2) => Languages.Comp(Denotational(e1), Denotational(e2))
  case Star(e1) => Languages.Star(Denotational(e1))
}

/*** Section 2.5: Bisimilarity and Coinduction ***/

greatest predicate Bisimilar<A(!new)>[nat](L1: Languages.Lang, L2: Languages.Lang) {
  && (L1.eps == L2.eps)
  && (forall a :: Bisimilar(L1.delta(a), L2.delta(a)))
}

greatest lemma BisimilarityIsReflexive<A(!new)>[nat](L: Languages.Lang)
  ensures Bisimilar(L, L)
{}

/*** Section 2.6: Denotational Semantics as Algebra Homomorphism ***/

ghost predicate IsAlgebraHomomorphism<A(!new)>(f: Exp -> Languages.Lang) {
  forall e :: IsAlgebraHomomorphismPointwise(f, e)
}

ghost predicate IsAlgebraHomomorphismPointwise<A(!new)>
  (f: Exp -> Languages.Lang, e: Exp) {
  Bisimilar<A>(
    f(e),
    match e
    case Zero => Languages.Zero()
    case One => Languages.One()
    case Char(a) => Languages.Singleton(a)
    case Plus(e1, e2) => Languages.Plus(f(e1), f(e2))
    case Comp(e1, e2) => Languages.Comp(f(e1), f(e2))
    case Star(e1) => Languages.Star(f(e1))
  )
}

lemma DenotationalIsAlgebraHomomorphism<A(!new)>()
  ensures IsAlgebraHomomorphism<A>(Denotational)
{
  forall e ensures IsAlgebraHomomorphismPointwise<A>(Denotational, e) {
    BisimilarityIsReflexive<A>(Denotational(e));
  }
}

/*** Section 3.1: A Coalgebra of Regular Expressions ***/

function Eps<A>(e: Exp): bool {
  match e
  case Zero => false
  case One => true
  case Char(a) => false
  case Plus(e1, e2) => Eps(e1) || Eps(e2)
  case Comp(e1, e2) => Eps(e1) && Eps(e2)
  case Star(e1) => true
}

function Delta<A(==)>(e: Exp): A -> Exp {
  (a: A) =>
    match e
    case Zero => Zero
    case One => Zero
    case Char(b) => if a == b then One else Zero
    case Plus(e1, e2) => Plus(Delta(e1)(a), Delta(e2)(a))
    case Comp(e1, e2) =>
      Plus(Comp(Delta(e1)(a), e2), Comp(if Eps(e1) then One else Zero, Delta(e2)(a)))
    case Star(e1) => Comp(Delta(e1)(a), Star(e1))
}

/*** Section 3.2: Operational Semantics as Induced Morphism ***/

function Operational<A(==)>(e: Exp): Languages.Lang {
  Languages.Alpha(Eps(e), (a: A) => Operational(Delta(e)(a)))
}

/*** Section 3.3: Operational Semantics as Coalgebra Homomorphism ***/

ghost predicate IsCoalgebraHomomorphism<A(!new)>(f: Exp -> Languages.Lang) {
  && (forall e :: f(e).eps == Eps(e))
  && (forall e, a :: Bisimilar(f(e).delta(a), f(Delta(e)(a))))
}

lemma OperationalIsCoalgebraHomomorphism<A(!new)>()
  ensures IsCoalgebraHomomorphism<A>(Operational)
{
  forall e, a ensures Bisimilar<A>(Operational(e).delta(a), Operational(Delta(e)(a))) {
    BisimilarityIsReflexive(Operational(e).delta(a));
  }
}

/*** Section 4.1: Denotational Semantics as Coalgebra Homomorphism ***/

lemma BisimilarMonotone<A(!new)>(j: nat, k: nat, L1: Languages.Lang, L2: Languages.Lang)
  requires j <= k
  requires Bisimilar#[k](L1, L2)
  ensures Bisimilar#[j](L1, L2)
  decreases j
{
  if j != 0 {
    forall a ensures Bisimilar#[j-1](L1.delta(a), L2.delta(a)) {
      BisimilarMonotone(j-1, k-1, L1.delta(a), L2.delta(a));
    }
  }
}

lemma PlusCongruencePointwise<A(!new)>(k: nat,
  L1a: Languages.Lang, L1b: Languages.Lang, L2a: Languages.Lang, L2b: Languages.Lang)
  requires Bisimilar#[k](L1a, L1b)
  requires Bisimilar#[k](L2a, L2b)
  ensures Bisimilar#[k](Languages.Plus(L1a, L2a), Languages.Plus(L1b, L2b))
  decreases k
{
  if k != 0 {
    forall a ensures Bisimilar#[k-1](Languages.Plus(L1a, L2a).delta(a),
                                     Languages.Plus(L1b, L2b).delta(a)) {
      PlusCongruencePointwise(k-1, L1a.delta(a), L1b.delta(a), L2a.delta(a), L2b.delta(a));
    }
  }
}

lemma CompCongruencePointwise<A(!new)>(k: nat,
  L1a: Languages.Lang, L1b: Languages.Lang, L2a: Languages.Lang, L2b: Languages.Lang)
  requires Bisimilar(L1a, L1b)
  requires Bisimilar#[k](L2a, L2b)
  ensures Bisimilar#[k](Languages.Comp(L1a, L2a), Languages.Comp(L1b, L2b))
  decreases k
{
  if k != 0 {
    assert L1a.eps == L1b.eps;
    forall a ensures Bisimilar#[k-1](Languages.Comp(L1a, L2a).delta(a),
                                     Languages.Comp(L1b, L2b).delta(a)) {
      BisimilarMonotone(k-1, k, L2a, L2b);
      CompCongruencePointwise(k-1, L1a.delta(a), L1b.delta(a), L2a, L2b);

      var cond := if L1a.eps then Languages.One<A>() else Languages.Zero<A>();
      BisimilarityIsReflexive(cond);
      CompCongruencePointwise(k-1, cond, cond, L2a.delta(a), L2b.delta(a));

      PlusCongruencePointwise(k-1,
        Languages.Comp(L1a.delta(a), L2a), Languages.Comp(L1b.delta(a), L2b),
        Languages.Comp(cond, L2a.delta(a)), Languages.Comp(cond, L2b.delta(a)));
    }
  }
}

lemma DenotationalEps<A(!new)>(e: Exp)
  ensures Denotational(e).eps == Eps(e)
{}

lemma DenotationalDelta<A(!new)>(e: Exp, a: A)
  ensures Bisimilar<A>(Denotational(e).delta(a), Denotational(Delta(e)(a)))
  decreases e, 1
{
  match e {
    case Zero =>
      BisimilarityIsReflexive<A>(Denotational<A>(Zero).delta(a));
    case One =>
      BisimilarityIsReflexive<A>(Denotational<A>(One).delta(a));
    case Char(b) =>
      BisimilarityIsReflexive<A>(Denotational<A>(Char(b)).delta(a));
    case Plus(e1, e2) =>
      DenotationalDeltaPlus(e1, e2, a);
    case Comp(e1, e2) =>
      DenotationalDeltaComp(e1, e2, a);
    case Star(e1) =>
      DenotationalDeltaStar(e1, a);
  }
}

lemma DenotationalDeltaPlus<A(!new)>(e1: Exp, e2: Exp, a: A)
  ensures Bisimilar<A>(Denotational<A>(Plus(e1, e2)).delta(a),
                       Denotational(Delta<A>(Plus(e1, e2))(a)))
  decreases Plus(e1, e2), 0
{
  DenotationalDelta(e1, a);
  DenotationalDelta(e2, a);
  PlusCongruence(Denotational(e1).delta(a), Denotational(Delta(e1)(a)),
                 Denotational(e2).delta(a), Denotational(Delta(e2)(a)));
}

lemma DenotationalDeltaComp<A(!new)>(e1: Exp, e2: Exp, a: A)
  ensures Bisimilar<A>(Denotational<A>(Comp(e1, e2)).delta(a),
                       Denotational(Delta<A>(Comp(e1, e2))(a)))
  decreases Comp(e1, e2), 0
{
  DenotationalEps(e1);
  var D1 := Denotational(e1);
  var D2 := Denotational(e2);
  var D1a := Denotational(Delta(e1)(a));
  var D2a := Denotational(Delta(e2)(a));
  var cond := if Eps(e1) then Languages.One<A>() else Languages.Zero<A>();
  assert cond == if D1.eps then Languages.One<A>() else Languages.Zero<A>();

  DenotationalDelta(e1, a);
  assert Bisimilar(D1.delta(a), D1a);

  DenotationalDelta(e2, a);
  assert Bisimilar(D2.delta(a), D2a);

  BisimilarityIsReflexive(D2);
  DenotationalDeltaCompPart1(D1.delta(a), D1a, D2);
  DenotationalDeltaCompPart2(cond, D2.delta(a), D2a);
  DenotationalDeltaCompCombine(D1.delta(a), D1a, cond, D2, D2.delta(a), D2a);
}

lemma DenotationalDeltaCompPart1<A(!new)>(
  L1a: Languages.Lang, L1b: Languages.Lang, L2: Languages.Lang)
  requires Bisimilar(L1a, L1b)
  requires Bisimilar(L2, L2)
  ensures Bisimilar(Languages.Comp(L1a, L2), Languages.Comp(L1b, L2))
{
  CompCongruence(L1a, L1b, L2, L2);
}

lemma DenotationalDeltaCompPart2<A(!new)>(
  cond: Languages.Lang, L2a: Languages.Lang, L2b: Languages.Lang)
  requires Bisimilar(L2a, L2b)
  ensures Bisimilar(Languages.Comp(cond, L2a), Languages.Comp(cond, L2b))
{
  BisimilarityIsReflexive(cond);
  CompCongruence(cond, cond, L2a, L2b);
}

lemma DenotationalDeltaCompCombine<A(!new)>(
  D1da: Languages.Lang, D1a: Languages.Lang, cond: Languages.Lang,
  D2: Languages.Lang, D2da: Languages.Lang, D2a: Languages.Lang)
  requires Bisimilar(Languages.Comp(D1da, D2), Languages.Comp(D1a, D2))
  requires Bisimilar(Languages.Comp(cond, D2da), Languages.Comp(cond, D2a))
  ensures Bisimilar(
    Languages.Plus(Languages.Comp(D1da, D2), Languages.Comp(cond, D2da)),
    Languages.Plus(Languages.Comp(D1a, D2), Languages.Comp(cond, D2a)))
{
  PlusCongruence(
    Languages.Comp(D1da, D2), Languages.Comp(D1a, D2),
    Languages.Comp(cond, D2da), Languages.Comp(cond, D2a));
}

lemma DenotationalDeltaStar<A(!new)>(e1: Exp, a: A)
  ensures Bisimilar<A>(Denotational<A>(Star(e1)).delta(a),
                       Denotational(Delta<A>(Star(e1))(a)))
  decreases Star(e1), 0
{
  DenotationalDelta(e1, a);
  BisimilarityIsReflexive(Languages.Star(Denotational(e1)));
  CompCongruence(Denotational(e1).delta(a), Denotational(Delta(e1)(a)),
                 Languages.Star(Denotational(e1)), Languages.Star(Denotational(e1)));
}

lemma DenotationalIsCoalgebraHomomorphism<A(!new)>()
  ensures IsCoalgebraHomomorphism<A>(Denotational)
{
  forall e ensures Denotational<A>(e).eps == Eps<A>(e) {
    DenotationalEps(e);
  }
  forall e, a ensures Bisimilar<A>(Denotational<A>(e).delta(a), Denotational(Delta<A>(e)(a))) {
    DenotationalDelta(e, a);
  }
}

greatest lemma PlusCongruence<A(!new)>[nat]
  (L1a: Languages.Lang, L1b: Languages.Lang, L2a: Languages.Lang, L2b: Languages.Lang)
  requires Bisimilar(L1a, L1b)
  requires Bisimilar(L2a, L2b)
  ensures Bisimilar(Languages.Plus(L1a, L2a), Languages.Plus(L1b, L2b))
{}

lemma CompCongruence<A(!new)>(L1a: Languages.Lang, L1b: Languages.Lang,
  L2a: Languages.Lang, L2b: Languages.Lang)
  requires Bisimilar(L1a, L1b)
  requires Bisimilar(L2a, L2b)
  ensures Bisimilar(Languages.Comp(L1a, L2a), Languages.Comp(L1b, L2b))
{
  forall k: nat ensures Bisimilar#[k](Languages.Comp(L1a, L2a), Languages.Comp(L1b, L2b)) {
    CompCongruencePointwise(k, L1a, L1b, L2a, L2b);
  }
}

/*** Section 4.2: Coalgebra Homomorphisms Are Unique ***/

lemma UniqueCoalgebraHomomorphism<A(!new)>(f: Exp -> Languages.Lang,
  g: Exp -> Languages.Lang, e: Exp)
  requires IsCoalgebraHomomorphism(f)
  requires IsCoalgebraHomomorphism(g)
  ensures Bisimilar(f(e), g(e))
{
  forall k: nat ensures Bisimilar#[k](f(e), g(e)) {
    BisimilarityIsReflexive(f(e));
    BisimilarityIsReflexive(g(e));
    UniqueCoalgebraHomomorphismHelperPointwise(k, f, g, f(e), g(e));
  }
}

greatest lemma BisimilarityIsTransitive<A(!new)>[nat](L1: Languages.Lang,
  L2: Languages.Lang, L3: Languages.Lang)
  requires Bisimilar(L1, L2) && Bisimilar(L2, L3)
  ensures Bisimilar(L1, L3)
{}

lemma UniqueCoalgebraHomomorphismHelperPointwise<A(!new)>
  (k: nat, f: Exp -> Languages.Lang, g: Exp -> Languages.Lang,
   L1: Languages.Lang, L2: Languages.Lang)
  requires IsCoalgebraHomomorphism(f)
  requires IsCoalgebraHomomorphism(g)
  requires exists e :: Bisimilar#[k](L1, f(e)) && Bisimilar#[k](L2, g(e))
  ensures Bisimilar#[k](L1, L2)
{
  var e :| Bisimilar#[k](L1, f(e)) && Bisimilar#[k](L2, g(e));
  if k != 0 {
    forall a ensures Bisimilar#[k-1](L1.delta(a), L2.delta(a)) {
      BisimilarityIsTransitivePointwise(
        k-1, L1.delta(a), f(e).delta(a), f(Delta(e)(a))
      );
      BisimilarityIsTransitivePointwise(
        k-1, L2.delta(a), g(e).delta(a), g(Delta(e)(a))
      );
      UniqueCoalgebraHomomorphismHelperPointwise(
        k-1, f, g, L1.delta(a), L2.delta(a)
      );
    }
  }
}

lemma BisimilarityIsTransitivePointwise<A(!new)>(k: nat,
  L1: Languages.Lang, L2: Languages.Lang, L3: Languages.Lang)
  ensures Bisimilar#[k](L1, L2) && Bisimilar#[k](L2, L3) ==> Bisimilar#[k](L1, L3)
{
  if k != 0 {
    if Bisimilar#[k](L1, L2) && Bisimilar#[k](L2, L3) {
      assert Bisimilar#[k](L1, L3) by {
        forall a ensures Bisimilar#[k-1](L1.delta(a), L3.delta(a)) {
          BisimilarityIsTransitivePointwise(k-1, L1.delta(a), L2.delta(a), L3.delta(a));
        }
      }
    }
  }
}

/*** Section 4.3: Denotational and Operational Semantics Are Bisimilar ***/

lemma OperationalAndDenotationalAreBisimilar<A(!new)>(e: Exp)
  ensures Bisimilar<A>(Operational(e), Denotational(e))
{
  OperationalIsCoalgebraHomomorphism<A>();
  DenotationalIsCoalgebraHomomorphism<A>();
  UniqueCoalgebraHomomorphism<A>(Operational, Denotational, e);
}

/*** Section 4.4: Operational Semantics as Algebra Homomorphism ***/

greatest lemma BisimilarityIsSymmetric<A(!new)>[nat](L1: Languages.Lang,
  L2: Languages.Lang)
  ensures Bisimilar(L1, L2) ==> Bisimilar(L2, L1)
  ensures Bisimilar(L1, L2) <== Bisimilar(L2, L1)
{}

lemma StarCongruencePointwise<A(!new)>(k: nat,
  L1: Languages.Lang, L2: Languages.Lang)
  requires Bisimilar(L1, L2)
  ensures Bisimilar#[k](Languages.Star(L1), Languages.Star(L2))
  decreases k
{
  if k != 0 {
    forall a ensures Bisimilar#[k-1](Languages.Star(L1).delta(a),
                                     Languages.Star(L2).delta(a)) {
      StarCongruencePointwise(k-1, L1, L2);
      CompCongruencePointwise(k-1, L1.delta(a), L2.delta(a),
                              Languages.Star(L1), Languages.Star(L2));
    }
  }
}

lemma StarCongruence<A(!new)>(L1: Languages.Lang, L2: Languages.Lang)
  requires Bisimilar(L1, L2)
  ensures Bisimilar(Languages.Star(L1), Languages.Star(L2))
{
  forall k: nat ensures Bisimilar#[k](Languages.Star(L1), Languages.Star(L2)) {
    StarCongruencePointwise(k, L1, L2);
  }
}

lemma OperationalIsAlgebraHomomorphism<A(!new)>()
  ensures IsAlgebraHomomorphism<A>(Operational)
{
  forall e ensures IsAlgebraHomomorphismPointwise<A>(Operational, e) {
    OperationalIsAlgebraHomomorphismPointwise(e);
  }
}

lemma OperationalIsAlgebraHomomorphismPointwise<A(!new)>(e: Exp)
  ensures IsAlgebraHomomorphismPointwise<A>(Operational, e)
{
  OperationalAndDenotationalAreBisimilar<A>(e);
  match e {
    case Zero =>
      BisimilarityIsReflexive<A>(Languages.Zero<A>());
      BisimilarityIsTransitive(Operational<A>(Zero), Denotational<A>(Zero),
                               Languages.Zero<A>());
    case One =>
      BisimilarityIsReflexive<A>(Languages.One<A>());
      BisimilarityIsTransitive(Operational<A>(One), Denotational<A>(One),
                               Languages.One<A>());
    case Char(c) =>
      BisimilarityIsReflexive<A>(Languages.Singleton(c));
      BisimilarityIsTransitive(Operational(Char(c)), Denotational(Char(c)),
                               Languages.Singleton(c));
    case Plus(e1, e2) =>
      OperationalAndDenotationalAreBisimilar(e1);
      OperationalAndDenotationalAreBisimilar(e2);
      BisimilarityIsSymmetric(Operational(e1), Denotational(e1));
      BisimilarityIsSymmetric(Operational(e2), Denotational(e2));
      PlusCongruence(Denotational(e1), Operational(e1),
                     Denotational(e2), Operational(e2));
      BisimilarityIsTransitive(Operational(Plus(e1, e2)),
                               Denotational(Plus(e1, e2)),
                               Languages.Plus(Operational(e1), Operational(e2)));
    case Comp(e1, e2) =>
      OperationalAndDenotationalAreBisimilar(e1);
      OperationalAndDenotationalAreBisimilar(e2);
      BisimilarityIsSymmetric(Operational(e1), Denotational(e1));
      BisimilarityIsSymmetric(Operational(e2), Denotational(e2));
      CompCongruence(Denotational(e1), Operational(e1),
                     Denotational(e2), Operational(e2));
      BisimilarityIsTransitive(Operational(Comp(e1, e2)),
                               Denotational(Comp(e1, e2)),
                               Languages.Comp(Operational(e1), Operational(e2)));
    case Star(e1) =>
      OperationalAndDenotationalAreBisimilar(e1);
      BisimilarityIsSymmetric(Operational(e1), Denotational(e1));
      StarCongruence(Denotational(e1), Operational(e1));
      BisimilarityIsTransitive(Operational(Star(e1)),
                               Denotational(Star(e1)),
                               Languages.Star(Operational(e1)));
  }
}
