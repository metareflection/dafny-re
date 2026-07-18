// Runnable demo for the auto-generated (a|b)*a matcher.
// Kept separate so gen_star_ab_a.dfy stays verbatim generator output.
//   dafny run demo_star_ab_a.dfy
include "gen_star_ab_a.dfy"

method Main() {
  var r1 := MatchSpecialized("a");     print "(a|b)*a  \"a\"    => ", r1, "\n";
  var r2 := MatchSpecialized("ba");    print "(a|b)*a  \"ba\"   => ", r2, "\n";
  var r3 := MatchSpecialized("ab");    print "(a|b)*a  \"ab\"   => ", r3, "\n";
  var r4 := MatchSpecialized("abba");  print "(a|b)*a  \"abba\" => ", r4, "\n";
  var r5 := MatchSpecialized("");      print "(a|b)*a  \"\"     => ", r5, "\n";
}
