# Revision history for telomare

## Unreleased

* EAL certification now terminates by construction in every phase: each
  DeferRef occurrence instantiates its body once (let-polymorphism over the
  DeferMap DAG) and carries the instance's interface with its tag, so dispatch
  only unifies and is bounded by sites times tags. The dispatch depth cap,
  polyvariance cap and variable budget are gone. Self-application is rejected
  as a cycle through an interface's argument half (the occurs check of arrow
  types), with the cycle named in the error; cycles through captures remain
  regular closure shapes. An abort that really aborts now has a bottom type
  instead of being read as the identity, so sized recursion chains type
  through their dead base. Numeral-of-numeral composition and the previously
  pinned same-arity gate join certify.
* The box constraints are solved exactly (presolve, sparse Gaussian elimination,
  exact dual simplex from the slack basis); the level cap, the round budgets and
  `EALSolverGaveUp` are gone, and an unsatisfiable system names the rows that
  cannot hold together. The objective is total leaf depth. Depths are cumulative
  per node, so equations have at most three terms.
* A closed data tree under a pair constructor is one data leaf in the analysis
  (one level of pair structure kept), not a node per pair: data is level-free,
  and the per-component view bangs were what every instance copied.
* The box constraints are solved once, in the global pass, and per-body levels
  and env bangs are read off it. The standalone per-body passes run only when
  main fails, to localize the failure: a certified main has certified every
  body's instances, and a body's own constraints are a subset of its
  instance's, so no body can fail on its own under a certified main. The
  forced identity reading of an unresolved abort could previously fail a body
  standalone and reject main through the dependency gate even though main's
  own derivation certified; that false rejection is gone with the gate.
* The box discipline is faithful EAL: occurrences sit exactly as deep as the
  bangs they open, boxes pass through applications, projections and gate
  switches instead of vanishing, a duplicated capture is contracted outside
  its closure's box (the reading that types Church numerals), and data stays
  level-free. Reported levels are now proof-net depths.
* Reorganized the library into compiler-stage modules: `Telomare.Parse`,
  `Telomare.Expand`, `Telomare.Desugar`, `Telomare.Resolve`,
  `Telomare.TypeCheck`, `Telomare.Size` (+ `.IR`) with the shared
  `Telomare.Machine` step algebra, `Telomare.Eval.Reference` /
  `Telomare.Eval.Meter`, and `Telomare.Driver`. The IR vocabulary moved
  to `Telomare.IR.*` and the error types to `Telomare.Error`.
* Parser APIs now expose an explicit parse-then-expand pipeline. Each surface
  phase has its own term type: the parser produces `ParsedSurfaceTerm` (base
  functor `ParsedTermF` = `UnprocessedParsedTermF` plus the `SugarTermF`
  fragment), and `Telomare.Expand` removes the sugar fragment, returning
  `ExpandedSurfaceTerm` — so expanded trees structurally cannot contain raw
  sugar forms. `Telomare.Desugar` then returns `DesugaredSurfaceTerm`, whose
  case capability is uninhabited, and only that type enters name resolution.
  Module syntax uses `ModuleItem`/`ImportDecl`; expansion retains imports as
  typed `ExpandedModuleItem` values instead of encoding them as arbitrary
  terms. Complete expression runners reject trailing input. The old
  parse-time expansion APIs and `Telomare.Parse.Sugar` module were removed.
* Fixed parser and elaboration correctness issues around oversized naturals,
  keyword boundaries, empty list definitions, generated-pattern capture, UDT
  arity truncation, import failures/cycles, and shadowed builtin rewrites.
* Removed dead code: the unbuildable benchmarks, the C serializer FFI
  (`cbits/`, `ctest/`), the commented-out HVM/LLVM/Chez backends,
  `Telomare.Decompiler`, and orphaned fixture files.
* Removed the `telomare-evaluare` executable and its flake app; its
  interactive evaluation functionality lives in the LSP app now.
* Fixed every GHC `-Wall` warning across the library, executables, and test
  suites (unused imports, name shadowing, incomplete patterns, missing
  signatures, orphan instances, type defaults), and enabled `-Wall`
  permanently for every component in `telomare.cabal`. Orphan instances moved to
  their proper homes: `MonadFail (Either ResolverError)` to `Telomare.Error`,
  `TelomareLike CompiledExpr` to `Telomare.IR.Core`, and the
  `PrettyPrintable` `Char`/`FunctionIndex` instances to
  `Telomare.PrettyPrint`.
* Removed a further ~1,100 lines of dead code across the library, the
  executables and the test suites, including the unused `super*`/`indexed*`
  step family in `Telomare.Machine` and test scaffolding reachable from nothing
  live. Every component now also carries `-Wunused-packages`, and the
  build is warning-free under it.
* Consolidated duplicated logic behind shared abstractions: `Telomare.Util`
  (one `debugTrace`, `padRight` and `plural` where there were six, four and
  two), `Telomare.Lexical` (reserved words, identifier character classes and
  comment delimiters, now read by both the parser and the language server),
  `traverseScoped` in `Telomare.IR.Surface` (one binding-aware traversal of the
  surface functor replacing five hand-written scope walks), and `purely` in
  `Telomare.Machine` (the pure step functions are derived from the monadic ones
  rather than written out a second time).
* Fixed three drifts between the language server's lexer and the parser, all of
  which came from the lexer restating parser facts: `where` was highlighted as
  a keyword though the language does not reserve it, identifiers could only
  start with an ASCII letter, and `{- -}` block comments were never lexed.
* Added `test/ConformanceTests.hs`, a corpus-driven check that the sized
  evaluator, the step meter and the fast runtime agree on the programs they can
  all run.
* Fixed `topologicalSort` in `Telomare.Resolve`, which existed twice with the
  two copies returning opposite orders.
* Fixed the nix build, which had stopped compiling the test suites: it builds
  from `cabal sdist` output, and the Telomare programs the tests read at run
  time were no longer declared in `telomare.cabal`.
* Fixed `nix run .#push-cachix`, which aborted before pushing anything: it named
  the shell apps' closures by evaluating `apps.<system>.<name>.program`, which
  computes a store path without building it, and `nix path-info` rejects a path
  that does not exist. The apps are now build inputs of the script.
* Moved to GHC 9.10.3 and `cabal-version` 3.12, and updated every flake input.

## 0.1.0.0 -- YYYY-mm-dd

* First version. Released on an unsuspecting world.
