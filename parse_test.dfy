// Tests for the regex parser: parse strings, then match against inputs.

include "parse.dfy"
include "match.dfy"

method TestParse(pattern: string, input: string, expected: bool)
  decreases *
{
  var pr := ParseRegex(pattern);
  match pr {
    case Failure(m) => print "PARSE FAIL /", pattern, "/: ", m, "\n";
    case Success(e, _) => {
      var ok := Match(e, input);
      var status := if ok == expected then "PASS" else "FAIL";
      print status, "  /", pattern, "/  \"", input, "\"  => ", ok, "\n";
    }
  }
}

method Main()
  decreases *
{
  print "=== Literals & concatenation ===\n";
  TestParse("a",    "a",   true);
  TestParse("a",    "b",   false);
  TestParse("ab",   "ab",  true);
  TestParse("ab",   "a",   false);
  TestParse("ab",   "abc", false);

  print "\n=== Alternation ===\n";
  TestParse("a|b",  "a",   true);
  TestParse("a|b",  "b",   true);
  TestParse("a|b",  "c",   false);

  print "\n=== Kleene star ===\n";
  TestParse("a*",   "",    true);
  TestParse("a*",   "a",   true);
  TestParse("a*",   "aaa", true);
  TestParse("a*",   "b",   false);

  print "\n=== Plus ===\n";
  TestParse("a+",   "",    false);
  TestParse("a+",   "a",   true);
  TestParse("a+",   "aa",  true);

  print "\n=== Optional ===\n";
  TestParse("a?",   "",    true);
  TestParse("a?",   "a",   true);
  TestParse("a?",   "aa",  false);

  print "\n=== Grouping ===\n";
  TestParse("(ab)*",  "",     true);
  TestParse("(ab)*",  "ab",   true);
  TestParse("(ab)*",  "abab", true);
  TestParse("(ab)*",  "aba",  false);

  print "\n=== Character classes ===\n";
  TestParse("[abc]",  "a",  true);
  TestParse("[abc]",  "b",  true);
  TestParse("[abc]",  "c",  true);
  TestParse("[abc]",  "d",  false);

  print "\n=== Escape sequences ===\n";
  TestParse("\\(",   "(",  true);
  TestParse("\\*",   "*",  true);
  TestParse("\\\\",  "\\", true);
  TestParse("\\|",   "|",  true);

  print "\n=== Precedence ===\n";
  TestParse("ab|c",  "ab", true);
  TestParse("ab|c",  "c",  true);
  TestParse("ab|c",  "ac", false);
  TestParse("ab*",   "a",  true);
  TestParse("ab*",   "abbb", true);

  print "\n=== Complex ===\n";
  TestParse("(a|b)*a", "a",    true);
  TestParse("(a|b)*a", "ba",   true);
  TestParse("(a|b)*a", "ab",   false);
  TestParse("(a|b)*a", "abba", true);

  print "\n=== Empty regex ===\n";
  TestParse("",  "",  true);
  TestParse("",  "a", false);
}
