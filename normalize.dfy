// Expression normalization for Brzozowski derivatives.
// Normalizes modulo identity/annihilator laws and idempotence of Plus.
// Ensures: Bisimilar(Denotational(Normalize(e)), Denotational(e))

include "re.dfy"

/** Normalize an expression, applying algebraic simplifications bottom-up. */
function Normalize<A(==)>(e: Exp<A>): Exp<A> {
  match e
  case Zero => Zero
  case One => One
  case Char(a) => Char(a)
  case Plus(e1, e2) => NormPlus(Normalize(e1), Normalize(e2))
  case Comp(e1, e2) => NormComp(Normalize(e1), Normalize(e2))
  case Star(e1) => NormStar(Normalize(e1))
}

/** Smart constructor for Plus: identity and idempotence. */
function NormPlus<A(==)>(e1: Exp<A>, e2: Exp<A>): Exp<A> {
  if e1 == Zero then e2
  else if e2 == Zero then e1
  else if e1 == e2 then e1
  else Plus(e1, e2)
}

/** Smart constructor for Comp: annihilator and left identity. */
function NormComp<A(==)>(e1: Exp<A>, e2: Exp<A>): Exp<A> {
  if e1 == Zero then Zero
  else if e2 == Zero then Zero
  else if e1 == One then e2
  else Comp(e1, e2)
}

/** Smart constructor for Star: absorption of Zero and One. */
function NormStar<A(==)>(e: Exp<A>): Exp<A> {
  match e
  case Zero => One
  case One => One
  case _ => Star(e)
}

/** Normalized derivative: Delta then Normalize. */
function NDelta<A(==)>(e: Exp<A>, a: A): Exp<A> {
  Normalize(Delta(e, a))
}

/** Fold normalized derivatives over a string. */
function FoldNDelta<A(==)>(e: Exp<A>, s: seq<A>): Exp<A>
  decreases |s|
{
  if |s| == 0 then e else FoldNDelta(NDelta(e, s[0]), s[1..])
}

/*============================================================================
  Prefix-level helpers for bisimilarity reasoning.
  ============================================================================*/

/** Plus(X, Y) ~#[k] Z  when  X ~#[k] Z  and  Y ~#[k] Zero. */
lemma PlusBisimRightZero<A(!new)>(k: nat,
  X: Languages.Lang, Y: Languages.Lang, Z: Languages.Lang)
  requires Bisimilar#[k](X, Z)
  requires Bisimilar#[k](Y, Languages.Zero<A>())
  ensures Bisimilar#[k](Languages.Plus(X, Y), Z)
  decreases k
{
  if k != 0 {
    forall a ensures Bisimilar#[k-1](Languages.Plus(X, Y).delta(a), Z.delta(a)) {
      PlusBisimRightZero(k-1, X.delta(a), Y.delta(a), Z.delta(a));
    }
  }
}

/** Plus(X, Y) ~#[k] Z  when  X ~#[k] Zero  and  Y ~#[k] Z. */
lemma PlusBisimLeftZero<A(!new)>(k: nat,
  X: Languages.Lang, Y: Languages.Lang, Z: Languages.Lang)
  requires Bisimilar#[k](X, Languages.Zero<A>())
  requires Bisimilar#[k](Y, Z)
  ensures Bisimilar#[k](Languages.Plus(X, Y), Z)
  decreases k
{
  if k != 0 {
    forall a ensures Bisimilar#[k-1](Languages.Plus(X, Y).delta(a), Z.delta(a)) {
      PlusBisimLeftZero(k-1, X.delta(a), Y.delta(a), Z.delta(a));
    }
  }
}

/** Plus(X, Y) ~#[k] Zero when both X and Y are ~#[k] Zero. */
lemma PlusBisimBothZero<A(!new)>(k: nat, X: Languages.Lang, Y: Languages.Lang)
  requires Bisimilar#[k](X, Languages.Zero<A>())
  requires Bisimilar#[k](Y, Languages.Zero<A>())
  ensures Bisimilar#[k](Languages.Plus(X, Y), Languages.Zero<A>())
  decreases k
{
  PlusBisimRightZero(k, X, Y, Languages.Zero<A>());
}

/*============================================================================
  Algebraic laws on languages, proved at prefix level.
  ============================================================================*/

/** Plus(L, Zero) ~ L */
greatest lemma PlusZeroRight<A(!new)>[nat](L: Languages.Lang)
  ensures Bisimilar(Languages.Plus(L, Languages.Zero()), L)
{}

greatest lemma PlusZeroLeft<A(!new)>[nat](L: Languages.Lang)
  ensures Bisimilar(Languages.Plus(Languages.Zero(), L), L)
{}

greatest lemma PlusIdem<A(!new)>[nat](L: Languages.Lang)
  ensures Bisimilar(Languages.Plus(L, L), L)
{}

/** Plus(L1, L2) ~ Plus(L2, L1) */
greatest lemma PlusComm<A(!new)>[nat](L1: Languages.Lang, L2: Languages.Lang)
  ensures Bisimilar(Languages.Plus(L1, L2), Languages.Plus(L2, L1))
{}

/** Plus(Plus(L1, L2), L3) ~ Plus(L1, Plus(L2, L3)) */
greatest lemma PlusAssoc<A(!new)>[nat](L1: Languages.Lang, L2: Languages.Lang, L3: Languages.Lang)
  ensures Bisimilar(Languages.Plus(Languages.Plus(L1, L2), L3),
                    Languages.Plus(L1, Languages.Plus(L2, L3)))
{}

/** Comp(Zero, L) ~ Zero */
lemma CompZeroLeftPrefix<A(!new)>(k: nat, L: Languages.Lang)
  ensures Bisimilar#[k](Languages.Comp(Languages.Zero(), L), Languages.Zero<A>())
  decreases k
{
  if k != 0 {
    forall a ensures Bisimilar#[k-1](
        Languages.Comp(Languages.Zero(), L).delta(a), Languages.Zero<A>().delta(a)) {
      CompZeroLeftPrefix(k-1, L);
      CompZeroLeftPrefix(k-1, L.delta(a));
      PlusBisimBothZero(k-1,
        Languages.Comp(Languages.Zero<A>(), L),
        Languages.Comp(Languages.Zero<A>(), L.delta(a)));
    }
  }
}

lemma CompZeroLeft<A(!new)>(L: Languages.Lang)
  ensures Bisimilar(Languages.Comp(Languages.Zero(), L), Languages.Zero<A>())
{
  forall k: nat { CompZeroLeftPrefix(k, L); }
}

/** Comp(L, Zero) ~ Zero */
lemma {:isolate_assertions} CompZeroRightPrefix<A(!new)>(k: nat, L: Languages.Lang)
  ensures Bisimilar#[k](Languages.Comp(L, Languages.Zero()), Languages.Zero<A>())
  decreases k
{
  if k != 0 {
    var Z := Languages.Zero<A>();
    var cond := if L.eps then Languages.One<A>() else Languages.Zero<A>();
    forall a ensures Bisimilar#[k-1](
        Languages.Comp(L, Z).delta(a), Z.delta(a)) {
      CompZeroRightPrefix(k-1, L.delta(a));
      CompZeroRightPrefix(k-1, cond);
      PlusBisimBothZero(k-1,
        Languages.Comp(L.delta(a), Z),
        Languages.Comp(cond, Z));
    }
  }
}

lemma CompZeroRight<A(!new)>(L: Languages.Lang)
  ensures Bisimilar(Languages.Comp(L, Languages.Zero()), Languages.Zero<A>())
{
  forall k: nat { CompZeroRightPrefix(k, L); }
}

/** Comp(One, L) ~ L */
lemma CompOneLeftPrefix<A(!new)>(k: nat, L: Languages.Lang)
  ensures Bisimilar#[k](Languages.Comp(Languages.One(), L), L)
  decreases k
{
  if k != 0 {
    forall a ensures Bisimilar#[k-1](
        Languages.Comp(Languages.One(), L).delta(a), L.delta(a)) {
      CompZeroLeftPrefix(k-1, L);
      CompOneLeftPrefix(k-1, L.delta(a));
      PlusBisimLeftZero(k-1,
        Languages.Comp(Languages.Zero<A>(), L),
        Languages.Comp(Languages.One(), L.delta(a)),
        L.delta(a));
    }
  }
}

lemma CompOneLeft<A(!new)>(L: Languages.Lang)
  ensures Bisimilar(Languages.Comp(Languages.One(), L), L)
{
  forall k: nat { CompOneLeftPrefix(k, L); }
}

/** Star(Zero) ~ One */
greatest lemma StarZero<A(!new)>[nat]()
  ensures Bisimilar<A>(Languages.Star(Languages.Zero()), Languages.One())
{
  forall a ensures Bisimilar(Languages.Star(Languages.Zero<A>()).delta(a),
                             Languages.One<A>().delta(a)) {
    CompZeroLeft(Languages.Star(Languages.Zero<A>()));
  }
}

/** Star(One) ~ One */
greatest lemma StarOne<A(!new)>[nat]()
  ensures Bisimilar<A>(Languages.Star(Languages.One()), Languages.One())
{
  forall a ensures Bisimilar(Languages.Star(Languages.One<A>()).delta(a),
                             Languages.One<A>().delta(a)) {
    CompZeroLeft(Languages.Star(Languages.One<A>()));
  }
}

/*============================================================================
  Smart constructor correctness.
  ============================================================================*/

lemma NormPlusCorrect<A(!new)>(e1: Exp, e2: Exp)
  ensures Bisimilar<A>(Denotational(NormPlus(e1, e2)),
                       Languages.Plus(Denotational(e1), Denotational(e2)))
{
  if e1 == Zero {
    PlusZeroLeft(Denotational(e2));
    BisimilarityIsSymmetric(Languages.Plus(Denotational<A>(e1), Denotational(e2)),
                            Denotational(e2));
  } else if e2 == Zero {
    PlusZeroRight(Denotational(e1));
    BisimilarityIsSymmetric(Languages.Plus(Denotational<A>(e1), Denotational(e2)),
                            Denotational(e1));
  } else if e1 == e2 {
    PlusIdem(Denotational(e1));
    BisimilarityIsSymmetric(Languages.Plus(Denotational<A>(e1), Denotational(e1)),
                            Denotational(e1));
  } else {
    BisimilarityIsReflexive(Denotational(Plus(e1, e2)));
  }
}

lemma NormCompCorrect<A(!new)>(e1: Exp, e2: Exp)
  ensures Bisimilar<A>(Denotational(NormComp(e1, e2)),
                       Languages.Comp(Denotational(e1), Denotational(e2)))
{
  var D1 := Denotational<A>(e1);
  var D2 := Denotational<A>(e2);
  if e1 == Zero {
    assert D1 == Denotational<A>(Zero);
    CompZeroLeft<A>(D2);
    BisimilarityIsSymmetric<A>(Languages.Comp(D1, D2), Languages.Zero());
  } else if e2 == Zero {
    assert D2 == Denotational<A>(Zero);
    CompZeroRight<A>(D1);
    BisimilarityIsSymmetric<A>(Languages.Comp(D1, D2), Languages.Zero());
  } else if e1 == One {
    assert D1 == Denotational<A>(One);
    CompOneLeft<A>(D2);
    BisimilarityIsSymmetric<A>(Languages.Comp(D1, D2), D2);
  } else {
    BisimilarityIsReflexive<A>(Denotational(Comp(e1, e2)));
  }
}

lemma NormStarCorrect<A(!new)>(e: Exp)
  ensures Bisimilar<A>(Denotational(NormStar(e)),
                       Languages.Star(Denotational(e)))
{
  match e {
    case Zero =>
      StarZero<A>();
      BisimilarityIsSymmetric(Languages.Star(Denotational<A>(Zero)),
                              Languages.One<A>());
    case One =>
      StarOne<A>();
      BisimilarityIsSymmetric(Languages.Star(Denotational<A>(One)),
                              Languages.One<A>());
    case _ =>
      BisimilarityIsReflexive(Denotational(Star(e)));
  }
}

/*============================================================================
  Main theorem: Normalize preserves denotational semantics.
  ============================================================================*/

lemma NormalizeCorrect<A(!new)>(e: Exp)
  ensures Bisimilar<A>(Denotational(Normalize(e)), Denotational(e))
{
  match e {
    case Zero => BisimilarityIsReflexive<A>(Denotational<A>(Zero));
    case One => BisimilarityIsReflexive<A>(Denotational<A>(One));
    case Char(a) => BisimilarityIsReflexive<A>(Denotational(Char(a)));
    case Plus(e1, e2) =>
      NormalizeCorrect(e1);
      NormalizeCorrect(e2);
      PlusCongruence(Denotational(Normalize(e1)), Denotational(e1),
                     Denotational(Normalize(e2)), Denotational(e2));
      NormPlusCorrect<A>(Normalize(e1), Normalize(e2));
      BisimilarityIsTransitive(
        Denotational(Normalize(Plus(e1, e2))),
        Languages.Plus(Denotational(Normalize(e1)), Denotational(Normalize(e2))),
        Languages.Plus(Denotational(e1), Denotational(e2)));
    case Comp(e1, e2) =>
      NormalizeCorrect(e1);
      NormalizeCorrect(e2);
      CompCongruence(Denotational(Normalize(e1)), Denotational(e1),
                     Denotational(Normalize(e2)), Denotational(e2));
      NormCompCorrect<A>(Normalize(e1), Normalize(e2));
      BisimilarityIsTransitive(
        Denotational(Normalize(Comp(e1, e2))),
        Languages.Comp(Denotational(Normalize(e1)), Denotational(Normalize(e2))),
        Languages.Comp(Denotational(e1), Denotational(e2)));
    case Star(e1) =>
      NormalizeCorrect(e1);
      StarCongruence(Denotational(Normalize(e1)), Denotational(e1));
      NormStarCorrect<A>(Normalize(e1));
      BisimilarityIsTransitive(
        Denotational(Normalize(Star(e1))),
        Languages.Star(Denotational(Normalize(e1))),
        Languages.Star(Denotational(e1)));
  }
}
