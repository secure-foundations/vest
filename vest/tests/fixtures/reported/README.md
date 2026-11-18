# Reported compiler regressions

These files preserve the reproducing inputs from
[#58](https://github.com/secure-foundations/vest/issues/58),
[#59](https://github.com/secure-foundations/vest/issues/59), and
[#60](https://github.com/secure-foundations/vest/issues/60). The suffix is
the case number in the corresponding report.

`cargo test -p vest --test diagnostics` checks that each input either
produces a diagnostic without writing output or generates a module. The
test has a subprocess deadline, so a compiler loop fails the test rather
than hanging CI. Supported code-generation cases also have representative
fixtures in `vest_tests/src/compiler_regressions.vest` that are compiled
and verified. A well-typed length expression can still need bounds on its
operands to discharge Verus's overflow checks.
