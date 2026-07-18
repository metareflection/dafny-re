// Regenerates gen_star_ab_a.dfy — the self-certifying matcher for (a|b)*a.
// Build the native binary and run it (clean stdout, no verifier banner):
//
//   dafny build --no-verify run_gen_star_ab_a.dfy && ./run_gen_star_ab_a > gen_star_ab_a.dfy
//   dafny verify gen_star_ab_a.dfy      # confirm the artifact verifies on its own
//
include "codegen.dfy"

method Main()
  decreases *
{
  var expr := Comp(Star(Plus(Char('a'), Char('b'))), Char('a'));  // (a|b)*a
  var code := Codegen(expr, {'a', 'b'});
  print code;
}
