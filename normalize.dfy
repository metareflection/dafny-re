// Expression normalization for Brzozowski derivatives.
// Normalizes modulo identity/annihilator laws and idempotence of Plus.
// Ensures: Bisimilar(Denotational(Normalize(e)), Denotational(e))

include "re.dfy"

/** Normalize an expression, applying algebraic simplifications bottom-up.
    The normPlus parameter controls how Plus is normalized:
    - NormPlus: generic, right-association + head dedup
    - NormPlusChar: full ACI canonicalization with sorted operands */
function Normalize<A(==)>(e: Exp<A>, normPlus: (Exp<A>, Exp<A>) -> Exp<A>): Exp<A> {
  match e
  case Zero => Zero
  case One => One
  case Char(a) => Char(a)
  case Plus(e1, e2) => normPlus(Normalize(e1, normPlus), Normalize(e2, normPlus))
  case Comp(e1, e2) => NormComp(Normalize(e1, normPlus), Normalize(e2, normPlus))
  case Star(e1) => NormStar(Normalize(e1, normPlus))
}

/** Smart constructor for Plus: identity, idempotence, right-association.
    Normalizes Plus(Plus(a, b), c) to Plus(a, Plus(b, c)) and deduplicates. */
function NormPlus<A(==)>(e1: Exp<A>, e2: Exp<A>): Exp<A>
  decreases e1, 1
{
  if e1 == Zero then e2
  else if e2 == Zero then e1
  else if e1 == e2 then e1
  else match e1
    case Plus(a, b) => NormPlus(a, NormPlus(b, e2))  // right-associate
    case _ =>
      // e1 is not Plus; check if e1 is the head of e2
      match e2
      case Plus(c, d) => if e1 == c then e2 else Plus(e1, e2)
      case _ => Plus(e1, e2)
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
function NDelta<A(==)>(e: Exp<A>, a: A, normPlus: (Exp<A>, Exp<A>) -> Exp<A>): Exp<A> {
  Normalize(Delta(e, a), normPlus)
}

/** Fold normalized derivatives over a string. */
function FoldNDelta<A(==)>(e: Exp<A>, s: seq<A>, normPlus: (Exp<A>, Exp<A>) -> Exp<A>): Exp<A>
  decreases |s|
{
  if |s| == 0 then e else FoldNDelta(NDelta(e, s[0], normPlus), s[1..], normPlus)
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

/** A normPlus function is correct if it preserves Plus semantics. */
ghost predicate NormPlusSpec<A(!new)>(normPlus: (Exp<A>, Exp<A>) -> Exp<A>) {
  forall e1: Exp<A>, e2: Exp<A> ::
    Bisimilar<A>(Denotational(normPlus(e1, e2)),
                 Languages.Plus(Denotational(e1), Denotational(e2)))
}

lemma NormPlusCorrect<A(!new)>(e1: Exp, e2: Exp)
  ensures Bisimilar<A>(Denotational(NormPlus(e1, e2)),
                       Languages.Plus(Denotational(e1), Denotational(e2)))
  decreases e1, 1
{
  var D1 := Denotational<A>(e1);
  var D2 := Denotational<A>(e2);
  if e1 == Zero {
    PlusZeroLeft<A>(D2);
    BisimilarityIsSymmetric(Languages.Plus(D1, D2), D2);
  } else if e2 == Zero {
    PlusZeroRight<A>(D1);
    BisimilarityIsSymmetric(Languages.Plus(D1, D2), D1);
  } else if e1 == e2 {
    PlusIdem<A>(D1);
    BisimilarityIsSymmetric(Languages.Plus(D1, D1), D1);
  } else {
    match e1 {
      case Plus(a, b) =>
        NormPlusCorrect<A>(b, e2);
        NormPlusCorrect<A>(a, NormPlus(b, e2));
        var Da := Denotational<A>(a);
        var Db := Denotational<A>(b);
        // Step 1: D(NormPlus(a, NormPlus(b, e2))) ~ Plus(Da, D(NormPlus(b, e2)))
        // Step 2: D(NormPlus(b, e2)) ~ Plus(Db, D2)
        // So: ~ Plus(Da, Plus(Db, D2))
        BisimilarityIsReflexive<A>(Da);
        PlusCongruence<A>(Da, Da,
                     Denotational(NormPlus(b, e2)),
                     Languages.Plus(Db, D2));
        BisimilarityIsTransitive(
          Denotational(NormPlus(a, NormPlus(b, e2))),
          Languages.Plus(Da, Denotational(NormPlus(b, e2))),
          Languages.Plus(Da, Languages.Plus(Db, D2)));
        // Step 3: Plus(Da, Plus(Db, D2)) ~ Plus(Plus(Da, Db), D2)
        PlusAssoc<A>(Da, Db, D2);
        BisimilarityIsSymmetric(
          Languages.Plus(Languages.Plus(Da, Db), D2),
          Languages.Plus(Da, Languages.Plus(Db, D2)));
        BisimilarityIsTransitive(
          Denotational(NormPlus(a, NormPlus(b, e2))),
          Languages.Plus(Da, Languages.Plus(Db, D2)),
          Languages.Plus(Languages.Plus(Da, Db), D2));
      case _ =>
        match e2 {
          case Plus(c, d) =>
            if e1 == c {
              var Dc := Denotational<A>(c);
              var Dd := Denotational<A>(d);
              assert D1 == Dc;
              // Need: D(e2) ~ Plus(D1, D(e2))
              // D(e2) = Plus(Dc, Dd), Plus(D1, D(e2)) = Plus(Dc, Plus(Dc, Dd))
              // Plus(Dc, Plus(Dc, Dd)) ~ Plus(Plus(Dc, Dc), Dd) ~ Plus(Dc, Dd)
              PlusAssoc<A>(Dc, Dc, Dd);
              PlusIdem<A>(Dc);
              BisimilarityIsReflexive<A>(Dd);
              PlusCongruence<A>(Languages.Plus(Dc, Dc), Dc, Dd, Dd);
              BisimilarityIsSymmetric(
                Languages.Plus(Languages.Plus(Dc, Dc), Dd),
                Languages.Plus(Dc, Languages.Plus(Dc, Dd)));
              BisimilarityIsTransitive(
                Languages.Plus(Dc, Languages.Plus(Dc, Dd)),
                Languages.Plus(Languages.Plus(Dc, Dc), Dd),
                Languages.Plus(Dc, Dd));
              BisimilarityIsSymmetric(
                Languages.Plus(Dc, Languages.Plus(Dc, Dd)),
                Languages.Plus(Dc, Dd));
            } else {
              BisimilarityIsReflexive<A>(Denotational(Plus(e1, e2)));
            }
          case _ =>
            BisimilarityIsReflexive<A>(Denotational(Plus(e1, e2)));
        }
    }
  }
}

lemma NormPlusSatisfiesSpec<A(!new)>()
  ensures NormPlusSpec<A>(NormPlus)
{
  forall e1: Exp<A>, e2: Exp<A>
    ensures Bisimilar<A>(Denotational(NormPlus(e1, e2)),
                         Languages.Plus(Denotational(e1), Denotational(e2)))
  {
    NormPlusCorrect<A>(e1, e2);
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

lemma NormalizeCorrect<A(!new)>(e: Exp, normPlus: (Exp<A>, Exp<A>) -> Exp<A>)
  requires NormPlusSpec<A>(normPlus)
  ensures Bisimilar<A>(Denotational(Normalize(e, normPlus)), Denotational(e))
{
  match e {
    case Zero => BisimilarityIsReflexive<A>(Denotational<A>(Zero));
    case One => BisimilarityIsReflexive<A>(Denotational<A>(One));
    case Char(a) => BisimilarityIsReflexive<A>(Denotational(Char(a)));
    case Plus(e1, e2) =>
      NormalizeCorrect(e1, normPlus);
      NormalizeCorrect(e2, normPlus);
      PlusCongruence(Denotational(Normalize(e1, normPlus)), Denotational(e1),
                     Denotational(Normalize(e2, normPlus)), Denotational(e2));
      assert Bisimilar<A>(Denotational(normPlus(Normalize(e1, normPlus), Normalize(e2, normPlus))),
                          Languages.Plus(Denotational(Normalize(e1, normPlus)), Denotational(Normalize(e2, normPlus))));
      BisimilarityIsTransitive(
        Denotational(Normalize(Plus(e1, e2), normPlus)),
        Languages.Plus(Denotational(Normalize(e1, normPlus)), Denotational(Normalize(e2, normPlus))),
        Languages.Plus(Denotational(e1), Denotational(e2)));
    case Comp(e1, e2) =>
      NormalizeCorrect(e1, normPlus);
      NormalizeCorrect(e2, normPlus);
      CompCongruence(Denotational(Normalize(e1, normPlus)), Denotational(e1),
                     Denotational(Normalize(e2, normPlus)), Denotational(e2));
      NormCompCorrect<A>(Normalize(e1, normPlus), Normalize(e2, normPlus));
      BisimilarityIsTransitive(
        Denotational(Normalize(Comp(e1, e2), normPlus)),
        Languages.Comp(Denotational(Normalize(e1, normPlus)), Denotational(Normalize(e2, normPlus))),
        Languages.Comp(Denotational(e1), Denotational(e2)));
    case Star(e1) =>
      NormalizeCorrect(e1, normPlus);
      StarCongruence(Denotational(Normalize(e1, normPlus)), Denotational(e1));
      NormStarCorrect<A>(Normalize(e1, normPlus));
      BisimilarityIsTransitive(
        Denotational(Normalize(Star(e1), normPlus)),
        Languages.Star(Denotational(Normalize(e1, normPlus))),
        Languages.Star(Denotational(e1)));
  }
}

/*============================================================================
  Full ACI canonicalization for Exp<char>: total order + sorted NormPlus.
  ============================================================================*/

/*-- Total order on Exp<char>. --*/

function ExpTag(e: Exp<char>): nat {
  match e
  case Zero => 0  case One => 1  case Char(_) => 2
  case Plus(_, _) => 3  case Comp(_, _) => 4  case Star(_) => 5
}

predicate ExpLt(e1: Exp<char>, e2: Exp<char>)
  decreases e1, e2
{
  if ExpTag(e1) != ExpTag(e2) then ExpTag(e1) < ExpTag(e2)
  else match (e1, e2)
    case (Char(a), Char(b)) => a < b
    case (Plus(a1, a2), Plus(b1, b2)) =>
      ExpLt(a1, b1) || (a1 == b1 && ExpLt(a2, b2))
    case (Comp(a1, a2), Comp(b1, b2)) =>
      ExpLt(a1, b1) || (a1 == b1 && ExpLt(a2, b2))
    case (Star(a), Star(b)) => ExpLt(a, b)
    case _ => false
}

predicate ExpLe(e1: Exp<char>, e2: Exp<char>) { e1 == e2 || ExpLt(e1, e2) }

/*-- Sorted insert into a right-associated Plus chain (no duplicates). --*/

function SortedInsert(e: Exp<char>, rest: Exp<char>): Exp<char>
  decreases rest
{
  match rest
  case Zero => e
  case Plus(h, t) =>
    if e == h then rest                          // dedup
    else if ExpLt(e, h) then Plus(e, rest)       // insert before
    else Plus(h, SortedInsert(e, t))             // keep going
  case _ =>
    if e == rest then rest                       // dedup
    else if ExpLt(e, rest) then Plus(e, rest)
    else Plus(rest, e)
}

/*-- Flatten + sorted rebuild for Exp<char>. --*/

function FlattenInto(e: Exp<char>, acc: Exp<char>): Exp<char>
  decreases e
{
  match e
  case Zero => acc
  case Plus(e1, e2) => FlattenInto(e1, FlattenInto(e2, acc))
  case _ => SortedInsert(e, acc)
}

/** Fully canonicalizing Plus for Exp<char>. */
function NormPlusChar(e1: Exp<char>, e2: Exp<char>): Exp<char> {
  FlattenInto(e1, FlattenInto(e2, Zero))
}

/*-- Correctness of SortedInsert. --*/

lemma SortedInsertCorrect(e: Exp<char>, rest: Exp<char>)
  ensures Bisimilar<char>(Denotational(SortedInsert(e, rest)),
                          Languages.Plus(Denotational(e), Denotational(rest)))
  decreases rest
{
  var De := Denotational<char>(e);
  var Dr := Denotational<char>(rest);
  match rest {
    case Zero =>
      PlusZeroRight<char>(De);
      BisimilarityIsSymmetric(Languages.Plus(De, Dr), De);
    case Plus(h, t) =>
      var Dh := Denotational<char>(h);
      var Dt := Denotational<char>(t);
      if e == h {
        // SortedInsert = rest = Plus(h, t)
        // Need: D(Plus(h,t)) ~ Plus(De, D(Plus(h,t)))
        // i.e. Plus(Dh, Dt) ~ Plus(Dh, Plus(Dh, Dt))  since e == h
        PlusAssoc<char>(Dh, Dh, Dt);
        PlusIdem<char>(Dh);
        BisimilarityIsReflexive<char>(Dt);
        PlusCongruence<char>(Languages.Plus(Dh, Dh), Dh, Dt, Dt);
        BisimilarityIsSymmetric(
          Languages.Plus(Languages.Plus(Dh, Dh), Dt),
          Languages.Plus(Dh, Languages.Plus(Dh, Dt)));
        BisimilarityIsTransitive(
          Languages.Plus(Dh, Languages.Plus(Dh, Dt)),
          Languages.Plus(Languages.Plus(Dh, Dh), Dt),
          Languages.Plus(Dh, Dt));
        BisimilarityIsSymmetric(
          Languages.Plus(Dh, Languages.Plus(Dh, Dt)),
          Languages.Plus(Dh, Dt));
      } else if ExpLt(e, h) {
        // SortedInsert = Plus(e, rest) — identity
        BisimilarityIsReflexive<char>(Denotational(Plus(e, rest)));
      } else {
        // SortedInsert = Plus(h, SortedInsert(e, t))
        SortedInsertCorrect(e, t);
        // D(SortedInsert(e, t)) ~ Plus(De, Dt)
        BisimilarityIsReflexive<char>(Dh);
        PlusCongruence<char>(Dh, Dh,
                        Denotational(SortedInsert(e, t)),
                        Languages.Plus(De, Dt));
        // Plus(Dh, Plus(De, Dt)) ~ Plus(De, Plus(Dh, Dt)) by ACI
        PlusAssoc<char>(Dh, De, Dt);
        PlusComm<char>(Dh, De);
        BisimilarityIsReflexive<char>(Dt);
        PlusCongruence<char>(Languages.Plus(Dh, De),
                        Languages.Plus(De, Dh), Dt, Dt);
        PlusAssoc<char>(De, Dh, Dt);
        BisimilarityIsSymmetric(
          Languages.Plus(Languages.Plus(De, Dh), Dt),
          Languages.Plus(De, Languages.Plus(Dh, Dt)));
        BisimilarityIsTransitive(
          Languages.Plus(Languages.Plus(Dh, De), Dt),
          Languages.Plus(Languages.Plus(De, Dh), Dt),
          Languages.Plus(De, Languages.Plus(Dh, Dt)));
        BisimilarityIsSymmetric(
          Languages.Plus(Dh, Languages.Plus(De, Dt)),
          Languages.Plus(Languages.Plus(Dh, De), Dt));
        BisimilarityIsTransitive(
          Languages.Plus(Dh, Languages.Plus(De, Dt)),
          Languages.Plus(Languages.Plus(Dh, De), Dt),
          Languages.Plus(De, Languages.Plus(Dh, Dt)));
        // Chain everything
        BisimilarityIsTransitive(
          Denotational(Plus(h, SortedInsert(e, t))),
          Languages.Plus(Dh, Languages.Plus(De, Dt)),
          Languages.Plus(De, Languages.Plus(Dh, Dt)));
      }
    case _ =>
      if e == rest {
        PlusIdem<char>(De);
        BisimilarityIsSymmetric(Languages.Plus(De, De), De);
      } else if ExpLt(e, rest) {
        BisimilarityIsReflexive<char>(Denotational(Plus(e, rest)));
      } else {
        PlusComm<char>(Dr, De);
        BisimilarityIsSymmetric(Languages.Plus(Dr, De), Languages.Plus(De, Dr));
      }
  }
}

/*-- Correctness of FlattenInto. --*/

lemma FlattenIntoCorrect(e: Exp<char>, acc: Exp<char>)
  ensures Bisimilar<char>(Denotational(FlattenInto(e, acc)),
                          Languages.Plus(Denotational(e), Denotational(acc)))
  decreases e
{
  var De := Denotational<char>(e);
  var Da := Denotational<char>(acc);
  match e {
    case Zero =>
      PlusZeroLeft<char>(Da);
      BisimilarityIsSymmetric(Languages.Plus(De, Da), Da);
    case Plus(e1, e2) =>
      // FlattenInto(Plus(e1,e2), acc) = FlattenInto(e1, FlattenInto(e2, acc))
      FlattenIntoCorrect(e2, acc);
      FlattenIntoCorrect(e1, FlattenInto(e2, acc));
      var D1 := Denotational<char>(e1);
      var D2 := Denotational<char>(e2);
      // D(FlattenInto(e1, FlattenInto(e2, acc))) ~ Plus(D1, D(FlattenInto(e2, acc)))
      // D(FlattenInto(e2, acc)) ~ Plus(D2, Da)
      BisimilarityIsReflexive<char>(D1);
      PlusCongruence<char>(D1, D1,
                      Denotational(FlattenInto(e2, acc)),
                      Languages.Plus(D2, Da));
      BisimilarityIsTransitive(
        Denotational(FlattenInto(e1, FlattenInto(e2, acc))),
        Languages.Plus(D1, Denotational(FlattenInto(e2, acc))),
        Languages.Plus(D1, Languages.Plus(D2, Da)));
      // Plus(D1, Plus(D2, Da)) ~ Plus(Plus(D1, D2), Da)
      PlusAssoc<char>(D1, D2, Da);
      BisimilarityIsSymmetric(
        Languages.Plus(Languages.Plus(D1, D2), Da),
        Languages.Plus(D1, Languages.Plus(D2, Da)));
      BisimilarityIsTransitive(
        Denotational(FlattenInto(e1, FlattenInto(e2, acc))),
        Languages.Plus(D1, Languages.Plus(D2, Da)),
        Languages.Plus(Languages.Plus(D1, D2), Da));
    case _ =>
      SortedInsertCorrect(e, acc);
  }
}

/*-- NormPlusChar satisfies NormPlusSpec. --*/

lemma NormPlusCharCorrect(e1: Exp<char>, e2: Exp<char>)
  ensures Bisimilar<char>(Denotational(NormPlusChar(e1, e2)),
                          Languages.Plus(Denotational(e1), Denotational(e2)))
{
  var D1 := Denotational<char>(e1);
  var D2 := Denotational<char>(e2);
  FlattenIntoCorrect(e2, Zero);
  FlattenIntoCorrect(e1, FlattenInto(e2, Zero));
  // D(FlattenInto(e2, Zero)) ~ Plus(D2, D(Zero)) ~ D2
  PlusZeroRight<char>(D2);
  BisimilarityIsTransitive(
    Denotational(FlattenInto(e2, Zero)),
    Languages.Plus(D2, Languages.Zero()),
    D2);
  // D(FlattenInto(e1, FlattenInto(e2, Zero))) ~ Plus(D1, D(FlattenInto(e2, Zero)))
  BisimilarityIsReflexive<char>(D1);
  PlusCongruence<char>(D1, D1,
                  Denotational(FlattenInto(e2, Zero)), D2);
  BisimilarityIsTransitive(
    Denotational(NormPlusChar(e1, e2)),
    Languages.Plus(D1, Denotational(FlattenInto(e2, Zero))),
    Languages.Plus(D1, D2));
}

lemma NormPlusCharSatisfiesSpec()
  ensures NormPlusSpec<char>(NormPlusChar)
{
  forall e1: Exp<char>, e2: Exp<char>
    ensures Bisimilar<char>(Denotational(NormPlusChar(e1, e2)),
                            Languages.Plus(Denotational(e1), Denotational(e2)))
  {
    NormPlusCharCorrect(e1, e2);
  }
}

/*============================================================================
  Char-specialized wrappers: fix normPlus = NormPlusChar.
  ============================================================================*/

function NormalizeC(e: Exp<char>): Exp<char> {
  match e
  case Zero => Zero
  case One => One
  case Char(a) => Char(a)
  case Plus(e1, e2) => NormPlusChar(NormalizeC(e1), NormalizeC(e2))
  case Comp(e1, e2) => NormComp(NormalizeC(e1), NormalizeC(e2))
  case Star(e1) => NormStar(NormalizeC(e1))
}

function NDeltaC(e: Exp<char>, a: char): Exp<char> {
  NormalizeC(Delta(e, a))
}

function FoldNDeltaC(e: Exp<char>, s: seq<char>): Exp<char>
  decreases |s|
{
  if |s| == 0 then e else FoldNDeltaC(NDeltaC(e, s[0]), s[1..])
}

lemma NormalizeCIsNormalize(e: Exp<char>)
  ensures NormalizeC(e) == Normalize(e, NormPlusChar)
{
  match e {
    case Zero =>
    case One =>
    case Char(_) =>
    case Plus(e1, e2) =>
      NormalizeCIsNormalize(e1);
      NormalizeCIsNormalize(e2);
    case Comp(e1, e2) =>
      NormalizeCIsNormalize(e1);
      NormalizeCIsNormalize(e2);
    case Star(e1) =>
      NormalizeCIsNormalize(e1);
  }
}

lemma FoldNDeltaCIsFoldNDelta(e: Exp<char>, s: seq<char>)
  ensures FoldNDeltaC(e, s) == FoldNDelta(e, s, NormPlusChar)
  decreases |s|
{
  if |s| != 0 {
    NormalizeCIsNormalize(Delta(e, s[0]));
    FoldNDeltaCIsFoldNDelta(NDeltaC(e, s[0]), s[1..]);
  }
}

lemma NormalizeCCorrect(e: Exp<char>)
  ensures Bisimilar<char>(Denotational(NormalizeC(e)), Denotational(e))
{
  NormalizeCIsNormalize(e);
  NormPlusCharSatisfiesSpec();
  NormalizeCorrect<char>(e, NormPlusChar);
}
