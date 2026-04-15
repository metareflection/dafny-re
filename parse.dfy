// Recursive descent regex parser producing Exp<char>.

include "re.dfy"

datatype ParseResult = Success(e: Exp<char>, rest: string) | Failure(msg: string)

method ParseChar(s: string) returns (r: ParseResult)
  ensures r.Success? ==> |r.rest| < |s|
{
  if |s| == 0 { return Failure("unexpected end of input"); }
  if s[0] == '\\' {
    if |s| < 2 { return Failure("trailing backslash"); }
    return Success(Char(s[1]), s[2..]);
  }
  if s[0] == '(' || s[0] == ')' || s[0] == '|' || s[0] == '[' || s[0] == ']' {
    return Failure("unexpected '" + [s[0]] + "'");
  }
  return Success(Char(s[0]), s[1..]);
}

method ParseClassChar(s: string) returns (r: ParseResult)
  ensures r.Success? ==> |r.rest| < |s|
{
  if |s| == 0 { return Failure("unexpected end of input in class"); }
  if s[0] == '\\' {
    if |s| < 2 { return Failure("trailing backslash in class"); }
    return Success(Char(s[1]), s[2..]);
  }
  if s[0] == ']' { return Failure("unexpected ']'"); }
  return Success(Char(s[0]), s[1..]);
}

method ParseClass(s: string) returns (r: ParseResult)
  ensures r.Success? ==> |r.rest| < |s|
{
  if |s| == 0 { return Failure("unexpected end of input in class"); }
  if s[0] == ']' { return Failure("empty character class"); }
  var first := ParseClassChar(s);
  match first {
    case Failure(m) => return Failure(m);
    case Success(e, rest) => {
      var acc := e;
      var cur := rest;
      while |cur| > 0 && cur[0] != ']'
        invariant |cur| < |s|
        decreases |cur|
      {
        var next := ParseClassChar(cur);
        match next {
          case Failure(m) => return Failure(m);
          case Success(e2, rest2) => { acc := Plus(acc, e2); cur := rest2; }
        }
      }
      if |cur| == 0 { return Failure("unterminated character class"); }
      return Success(acc, cur[1..]);
    }
  }
}

method ParseAtom(s: string) returns (r: ParseResult)
  ensures r.Success? ==> |r.rest| < |s|
  decreases |s|, 0
{
  if |s| == 0 { return Failure("unexpected end of input"); }
  if s[0] == '(' {
    var inner := ParseAlt(s[1..]);
    match inner {
      case Failure(m) => return Failure(m);
      case Success(e, rest) => {
        if |rest| == 0 || rest[0] != ')' { return Failure("expected ')'"); }
        return Success(e, rest[1..]);
      }
    }
  } else if s[0] == '[' {
    r := ParseClass(s[1..]);
  } else {
    r := ParseChar(s);
  }
}

method ApplyPostfix(e0: Exp<char>, s: string) returns (r: ParseResult)
  ensures r.Success? ==> |r.rest| <= |s|
{
  var e := e0;
  var cur := s;
  while |cur| > 0 && (cur[0] == '*' || cur[0] == '+' || cur[0] == '?')
    decreases |cur|
  {
    if cur[0] == '*' { e := Star(e); }
    else if cur[0] == '+' { e := Comp(e, Star(e)); }
    else { e := Plus(e, One); }
    cur := cur[1..];
  }
  return Success(e, cur);
}

predicate IsAtomStart(s: string) {
  |s| > 0 && s[0] != ')' && s[0] != '|' && s[0] != ']' && s[0] != '*' && s[0] != '+' && s[0] != '?'
}

method ParseConcat(s: string) returns (r: ParseResult)
  ensures r.Success? ==> |r.rest| < |s|
  decreases |s|, 1
{
  var a := ParseAtom(s);
  match a {
    case Failure(m) => return Failure(m);
    case Success(e, rest) => {
      var p := ApplyPostfix(e, rest);
      match p {
        case Failure(m) => return Failure(m);
        case Success(e2, rest2) => {
          var acc := e2;
          var cur := rest2;
          while IsAtomStart(cur)
            invariant |cur| < |s|
            decreases |cur|
          {
            var a2 := ParseAtom(cur);
            match a2 {
              case Failure(m) => return Failure(m);
              case Success(e3, rest3) => {
                var p2 := ApplyPostfix(e3, rest3);
                match p2 {
                  case Failure(m) => return Failure(m);
                  case Success(e4, rest4) => { acc := Comp(acc, e4); cur := rest4; }
                }
              }
            }
          }
          return Success(acc, cur);
        }
      }
    }
  }
}

method ParseAlt(s: string) returns (r: ParseResult)
  ensures r.Success? ==> |r.rest| < |s|
  decreases |s|, 2
{
  var first := ParseConcat(s);
  match first {
    case Failure(m) => return Failure(m);
    case Success(e, rest) => {
      var acc := e;
      var cur := rest;
      while |cur| > 0 && cur[0] == '|'
        invariant |cur| < |s|
        decreases |cur|
      {
        var next := ParseConcat(cur[1..]);
        match next {
          case Failure(m) => return Failure(m);
          case Success(e2, rest2) => { acc := Plus(acc, e2); cur := rest2; }
        }
      }
      return Success(acc, cur);
    }
  }
}

method ParseRegex(s: string) returns (r: ParseResult) {
  if |s| == 0 { return Success(One, ""); }
  var res := ParseAlt(s);
  match res {
    case Failure(m) => return Failure(m);
    case Success(e, rest) => {
      if |rest| != 0 { return Failure("unexpected trailing input: '" + rest + "'"); }
      return Success(e, rest);
    }
  }
}
