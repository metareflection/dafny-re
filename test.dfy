// Smoke tests for both the derivative matcher and the compiled DFA.

include "match.dfy"
include "compile.dfy"

method Main()
  decreases *
{
  // Expression: (a|b)*a — strings over {a,b} ending in 'a'
  var a := Char('a');
  var b := Char('b');
  var ab_star := Star(Plus(a, b));
  var expr := Comp(ab_star, a);
  var alpha := {'a', 'b'};

  print "=== Derivative matcher ===\n";
  var r1 := Match(expr, "a");     print "(a|b)*a  \"a\"    => ", r1, "\n";
  var r2 := Match(expr, "ba");    print "(a|b)*a  \"ba\"   => ", r2, "\n";
  var r3 := Match(expr, "ab");    print "(a|b)*a  \"ab\"   => ", r3, "\n";
  var r4 := Match(expr, "abba");  print "(a|b)*a  \"abba\" => ", r4, "\n";
  var r5 := Match(expr, "");      print "(a|b)*a  \"\"     => ", r5, "\n";

  print "\n=== Compiled DFA ===\n";
  var dfa := Compile(expr, alpha);
  print "DFA states: ", dfa.nStates, "\n";

  var d1 := DFAMatch(dfa, "a", alpha);     print "(a|b)*a  \"a\"    => ", d1, "\n";
  var d2 := DFAMatch(dfa, "ba", alpha);    print "(a|b)*a  \"ba\"   => ", d2, "\n";
  var d3 := DFAMatch(dfa, "ab", alpha);    print "(a|b)*a  \"ab\"   => ", d3, "\n";
  var d4 := DFAMatch(dfa, "abba", alpha);  print "(a|b)*a  \"abba\" => ", d4, "\n";
  var d5 := DFAMatch(dfa, "", alpha);      print "(a|b)*a  \"\"     => ", d5, "\n";

  // Second expression: a(a|b)
  var expr2 := Comp(a, Plus(a, b));
  print "\n=== a(a|b) via DFA ===\n";
  var dfa2 := Compile(expr2, alpha);
  print "DFA states: ", dfa2.nStates, "\n";
  var d6 := DFAMatch(dfa2, "ab", alpha);  print "a(a|b)  \"ab\" => ", d6, "\n";
  var d7 := DFAMatch(dfa2, "ba", alpha);  print "a(a|b)  \"ba\" => ", d7, "\n";
  var d8 := DFAMatch(dfa2, "aa", alpha);  print "a(a|b)  \"aa\" => ", d8, "\n";
  var d9 := DFAMatch(dfa2, "a", alpha);   print "a(a|b)  \"a\"  => ", d9, "\n";
}
