# Telomare — High-Level Design

> Status: DRAFT. First version reverse-engineered from the implementation 

## How to read this document

Every item carries one of five tags:

- **[commitment]** — a load-bearing, deliberate choice. Changing it changes what
  Telomare is. There are very few of these, and they are all in Part I.
- **[heuristic]** — a design rule of thumb the project follows because it has paid
  off, not because the language requires it. Contributions should follow it by
  default and may argue for exceptions.
- **[decision]** — how the current code serves a commitment. There were alternatives,
  the code picked one, and revisiting it is a legitimate contribution. Each decision
  names the commitment(s) it **serves**, gives its **rationale**, and where known lists
  the **alternatives** it was chosen over. A proposal to replace a decision should
  argue against the rationale recorded here, not against the code.
- **[direction]** — a speculative future path the maintainer has floated. Not
  implemented, not promised; recorded so contributions can aim at it.
- **[open]** — a known tension or unresolved question. The code embodies a stopgap or
  carries pinned tests documenting the problem. These are good places to contribute.

Appendix A lists things found in the tree that appear to be *incidental* — historical
residue, drift, or scaffolding — and are explicitly **not** design.

---

# Part I — Commitments

These are the only fixed points. Everything in Part II is negotiable against them.

## C1. The core grammar is as simple as possible

**[commitment]** Telomare has a small core grammar, and the commitment is to its
*simplicity*, not to its current shape. None of the specific forms in §2 are fixed.

This is one leg of a broader commitment set out in
[The Semantic Trinity](https://sfultong.blogspot.com/2019/06/the-semantic-trinity.html):
compilation is a translation from semantics ergonomic for humans (the surface grammar)
to semantics ergonomic for machines (the runtime), through a middle layer that should
be grounded in mathematical principle rather than in any particular language paradigm,
and should be stable enough to outlive both the surface languages above it and the
machines below it. The vision for Telomare's core is that it be

> the simplest possible denotational semantics that carries the essential concerns of
> the surface grammar and has a clear path to optimal operational semantics of the
> runtime.

Consequences used as tests of proposed core changes:

- A change to the core is justified by making it *simpler* while still carrying the
  surface language's essential concerns, or by shortening the path to an optimal
  runtime. "More expressive" is not by itself a justification.
- Every static analysis (sizing, certification, runtime compilation) should have to
  handle only a handful of forms. Growth in the number of forms is a cost to be argued
  for.

## C2. Telomare is total, in some form

**[commitment]** Every program that compiles terminates. Turing-completeness is given
up so that the compiler can bound a program's work before running it.

The commitment is to *some* form of totality. The specific mechanism — the
`{test, recursion, last}` triple, symbolic sizing, EAL certification — is a set of
decisions (§4, §5) and is explicitly not fixed; the maintainer's own view is that the
recursion triple is not as elegant as it could be.

## C3. Resource use is a first-class output of compilation

**[commitment]** The bounds inferred to make a program total are reported, not
discarded, and runs can be measured. Totality machinery is the means; a language whose
compiler can tell you what a program will cost is the end. (The original design notes
name the goals as *finding recursion limits* and *finding resource use*.)

## C4. Eventually, exactly one runtime

**[commitment]** The end state has a single runtime, which is the operational leg of
the trinity in C1: the core should have a clear path to *optimal* operational
semantics, and one optimal runtime is the target. The current assumption is that it
will be interaction-combinator based (§7), but that is a decision, not the commitment.

While that runtime is being developed, having a second, simple runtime to validate its
semantics against is a deliberate transitional arrangement (§6), not a design feature
to preserve.

## C5. Abort exists to validate static invariants, and is erased from the runtime

**[commitment]** The purpose of the abort instruction is to let programs state
invariants that can be validated statically, in the manner of refinement typing.
Abort is a *surface-level* concept; in the ideal pipeline it never reaches the final
runtime. See §10 for the current state and the intended split of abort-containing
code into statically evaluable, runtime-only, and abort-free parts.

---

# Design heuristics

Not commitments: the language would still be Telomare without them. They are recorded
because they have consistently paid off, and contributions are expected to follow them
unless there is a specific reason not to.

**[heuristic] H1. Make eliminated forms unrepresentable.** Each elaboration stage
hands the next a term type in which the previous stage's sugar is structurally
impossible. New sugar is added to the parsed type and *removed by type* at the
appropriate stage. Internal errors that cannot be made unrepresentable get their own
constructor rather than a catch-all.
- Why: a stage cannot mishandle a form it cannot receive, so the pipeline's invariants
  are checked by the compiler instead of by tests or discipline.

---

# Part II — Decisions

Each decision names what it serves. "Serves: C1" means the decision is the current
answer to C1's demand and may be replaced by a better one.

## 1. What Telomare looks like

**[decision] The surface language is a small, conventional-looking functional language**
(lambdas, `let`, `case`, `if`, modules/imports) that elaborates completely away.
- Serves: C1 (the surface carries the human-facing concerns; nothing in the core
  depends on it).
- Rationale: familiarity lowers the cost of trying the language; a surface that
  elaborates fully away keeps the core free to change.
- The surface grammar is documented in README.md.

**[decision] No native numeric representation in the core.** There is one atom (`Zero`)
and one constructor (`Pair`); numbers, lists, strings, booleans, and user-defined types
are all encodings.
- Serves: C1.
- Rationale: one atom and one constructor is the smallest data vocabulary that still
  carries every surface data type; every analysis handles only these two forms.
- Alternatives: native naturals would make arithmetic cheap but add forms every
  analysis must understand and give the middle layer a paradigm bias.

## 2. The core grammar

The executable core (`Telomare.IR.Base`, `Telomare.IR.Core`) is an *environment
machine*, not a lambda calculus.

**[decision] Eight machine forms plus abort.**

| form | meaning |
|---|---|
| `Zero` | the single atom |
| `Pair a b` | the single data constructor |
| `Env` | the current environment |
| `SetEnv x` | `x` evaluates to `(Defer body, env)`; run `body` with `Env := env` |
| `Defer body` | code as a value: an unevaluated body whose **only free variable is `Env`** |
| `Gate` | primitive two-way branch: applied to `Zero` selects left, to a pair selects right |
| `Left x` / `Right x` | pair projections (`Left Zero = Zero`, `Right Zero = Zero`) |
| `Abort` | applied to `Zero` = identity; applied to a pair = abort carrying that pair as message |

- Serves: C1.
- Rationale: this is the current best guess at "simplest denotational semantics with a
  clear path to an optimal runtime". It is not a commitment; a smaller or cleaner core
  that still carries the surface concerns would replace it.
- Note the tension with C5: `Abort` is currently a core form, whereas the commitment
  says abort is surface-level and erased (§10).

**[decision] There are no binders in the core.** A closure is literally the pair
`(Defer body, env)`; a function value *is* that pair; application is `SetEnv` after a
small env-rearranging "twiddle" step. `Env` is a right-nested tuple acting as a de
Bruijn spine.
- Serves: C1, C4.
- Rationale: with no binders there is no capture analysis anywhere. Defer bodies are
  closed over `Env` alone, so code can be content-addressed and shared (§8); the
  environment is the single sharing point, so evaluators share the env value across
  all its occurrences (§6) and the IC runtime can treat a body's env interface as a
  single wire (§7).
- Alternatives: a de Bruijn lambda calculus is the conventional choice; it would need
  substitution or closure conversion in every backend and would make the IC mapping
  less direct.

**[decision] `SetEnv` is the sole elimination form.** Function application, gate
dispatch, and abort triggering are all `SetEnv` of a pair.
- Serves: C1.
- Rationale: analyses need exactly one apply rule.

**[decision] Standard data encodings.** Naturals are left-nested unary pairs
(`n = (n-1, 0)`); lists are right-nested pairs ending in `Zero`; strings are lists of
character codes; `Zero` is false and any pair is true. Abort messages are data with
tagged prefixes distinguishing user aborts, recursion-budget aborts, and unsizeable
aborts.
- Serves: C1 (encodings live above the core).

**[decision] Church numerals are a separate, explicit surface literal (`$n`)**, built
as plain nested applications (`\f x -> f (f … x)`) — an *iterator value*, deliberately
distinct from the data encoding. `Prelude.tel`'s `d2c`/`c2d` bridge the two, and the
Prelude maintains parallel arithmetic families (`dPlus`/`plus`, …) for each.
- Serves: C2, C3.
- Rationale: data numbers are cheap to store and pattern-match; Church numbers are how
  you iterate, and iteration is exactly what the totality machinery must see and bound.
- Alternatives: a single numeric representation with iteration derived from it would
  be simpler for users but would hide the iteration structure sizing needs.

**[decision] Compiler-minted closures use reserved negative `FunctionIndex`es**, and
defer equality is by index (one body per index is an invariant, not a checked
property).
- Serves: implementation convenience only; see Appendix A for the places this
  invariant is hand-violated.

## 3. Elaboration pipeline

Stage-by-stage, what each type guarantees (this is H1 applied):

| stage | output | eliminated by construction |
|---|---|---|
| Parse | `ParsedSurfaceTerm` | — (raw sugar present) |
| Expand | `ExpandedSurfaceTerm` | multi-pattern lambdas, let-sugar, list definitions, UDT sugar |
| Desugar | `DesugaredSurfaceTerm` | `case` (lowered to nested conditionals), unbound builtins |
| Resolve | `Term1` → `Term2` → `Term3` | names (de Bruijn), then all lambda-calculus structure |
| Size | `CompiledExpr` | sizing holes and refinement wrappers — the runnable core |

**[decision] Lambda lifting with capture trimming happens at `splitExpr` (Term2→Term3).**
An open lambda captures a fresh tuple of exactly the outer variables its body uses, not
the whole ambient env.
- Serves: C2 (via EAL certification, §5).
- Rationale: closure creation becomes disjoint path projections, so duplication is
  charged only for genuinely duplicated variables. Capturing the whole env would make
  every closure a duplication of everything in scope.

**[decision] UDT identity is a structural hash.** `# expr` hashes the de Bruijn-ized,
location-stripped subterm (SHA-256, truncated); the UDT expansion applies the type's
wrapper to the hash *of that wrapper*, and the generated validator checks the tag.
- Serves: C1, C5.
- Rationale: nominal typing with no nominal machinery in the core; α-equivalent
  definitions get equal tags, stable across reformatting. The validator is an abort-
  based invariant check in the sense of C5.

**[decision] UDT surface convention:** `[T, ctor, …] = \h -> [ … ]` is recognized as a
UDT definition when the first name is uppercase and the body is a lambda, with exactly
one more name than body slot (the extra name is the generated validator). This is an
elaboration-level convention, not parser behavior.
- Serves: C1 (keeps UDTs out of the core entirely).

**[open] The certified term is not the executed term.** `compileMainReporting` resolves
the program twice: a `let`-inlined build (`main2Term3`) is EAL-certified and discarded,
while a `let`-as-application build (`main2Term3let`) is what actually gets sized and
run. The two are believed equivalent, but nothing checks it per-program. Unifying the
two pipelines (or certifying the executed build) is a known destination — the
DeferMap-native pipeline work (lifting, `linkDefers`, the parity harness) is
scaffolding toward it.

## 4. Totality: recursion and sizing

Everything here is the *current* answer to C2. None of it is fixed.

**[decision] The only recursion is the `{test, recursion, last}` triple.** There is
no fixpoint combinator; general recursion is unrepresentable at the surface. A triple
means: while `test` holds of the argument, apply `recursion` (which receives the
recursive call as a parameter); otherwise apply `last`.
- Serves: C2.
- Rationale: a recursion form that syntactically separates the continue-test from the
  step gives the sizer something to bound; it cannot be written without a test.
- Known cost: it is less elegant than it could be, and it forces users to restructure
  ordinary recursive definitions.

**[direction] General recursion in the surface grammar, compiled down to a recursion
triple (or something else).** The surface would accept ordinary recursive definitions;
elaboration would attempt to recover a triple (test / step / base) and report an error
when no base case can be found or the conversion otherwise fails. This keeps C2 while
moving the awkwardness out of the user's hands. Whether the target should remain the
triple is itself open.

**[decision] Iteration counts are inferred, not annotated and not searched.** The
sizing pass abstractly interprets the program over a *symbolic* input (unknown input
paths become indexed variables; gates on unknowns fork into superpositions with
env-filtering keeping each branch consistent). Each recursion site unrolls lazily —
one layer per demand, only while its test can still pass — and when a test provably
stops, the depth at which it stopped is recorded. The worst case across all explored
paths becomes the site's count. A program whose counts cannot be found does not compile.
- Serves: C2, C3.
- Rationale: inference means the user writes no bounds and the bounds are still
  available as a report (C3). Annotation would push the proof burden onto the user;
  searching (e.g. SMT) was tried and abandoned (Appendix A), but could be resurrected.

**[decision] Sizing failures split into exactly two kinds because the advice differs:**
`FuelExhausted` (the unrolling budget — default 65536 — was too small; raising it may
help) and `UnboundedInput` (no budget can help; the fix is to bound the input with a
refinement or `assert` before recursing). Errors name the recursion site and which kind
occurred.
- Serves: C2 (usability of the totality discipline).

**[decision] Unbounded input is tamed at the boundary by refinements.** `x : v`
annotations are checks (`v` applied to the value; a pair result aborts with that
message), and the sizing pass additionally *reads* refinements on the input to learn
which input paths are bounded. This is the idiom that makes interactive programs
(tictactoe) sizeable.
- Serves: C2, C5.
- Rationale: this is the C5 mechanism doing its intended job — an abort-based
  invariant that the static pipeline can consume.

**[decision] One sizing oracle per recursion *use site*.** Each syntactic use of a
recursive binding gets its own token, so the same function sizes independently at each
call site.
- Serves: C2, C3.
- Rationale: different call sites may need different depths; a per-definition bound
  would be the max over all sites and would over-report cost at cheap ones.

**[decision] Sized recursion is baked in as an approximant chain** — `step^n(abort)`
built by iterating a closure link, with one link of slack over the observed depth, and
a runtime abort at the bottom as the safety net (it fires only if the certificate was
somehow wrong).
- Serves: C2, C4.
- Rationale: this replaced an earlier self-applying repeat frame *specifically because
  self-application is outside the EAL fragment* (§5); the chain, and the Church literal
  encoding, were rewritten to be EAL-typable so that sized programs are admissible to
  the IC runtime.
- Tension with C5: the bottom abort is a runtime abort in compiled code (§10).

**[decision] The chain uses the strict conditional shape deliberately.**
- Serves: C4 (EAL admissibility).
- Rationale: lazy branch closures would capture the whole env and cost an EAL box per
  link, making levels grow with the count. See the strict-vs-lazy `if` question (§11).

**[decision] Sizing is engineered to be paid once.** It is input-independent (symbolic
input), so its cost (~70s for tictactoe) can be amortized via `.telc` artifacts (§9).
- Serves: C3 (makes the inferred bounds a stable artifact of the program).

**[decision] `uncurryRecursions`:** multi-argument recursion triples are rewritten
pre-resolution to recurse on a single right-nested data tuple. A companion
whole-program `uncurryBindings` pass normalizes saturated calls.
- Serves: C4 (EAL admissibility).
- Rationale: data is level-free in EAL while curried accumulator closures would demand
  unbounded box towers.

## 5. Certification: EAL instead of a type checker

None of this is a commitment. EAL certification is currently the chosen way to
*simultaneously* ensure totality (C2) and ensure the program can be fed to an optimal
runtime (C4). The hard part is making every program that feels semantically sound in
the surface grammar actually certify (§11).

**[decision] There is no conventional type system; the static discipline is
Elementary Affine Logic decoration inference** (`Telomare.EAL`). Its only claim is
*termination within an elementary bound* — every rejection is phrased as "this
program's work could not be bounded", never as a data-shape complaint. It replaced the
old unification type checker outright (commit a952626); the REPL's `:t` prints an EAL
verdict. The one shape check retained: a `main` that is data through and through is
rejected — a program must be a function of its input.
- Serves: C2, C4, C1.
- Rationale: one analysis does double duty (termination bound and sharing-graph
  admissibility), and an affine discipline fits a core with no binders and a single
  sharing point. A conventional type system would answer a question (data shape) the
  core does not ask.
- Alternatives: keep a type checker alongside; a different light logic (LAL, SLL)
  with a different bound/expressiveness trade-off.

**[decision] EAL certification gates every production compile path** (both sized and
`--fast`), pre-sizing. Separately, it is the admission certificate for the IC runtime
(§7), post-sizing: the IC net's *correctness* — not merely performance — depends on
the program being EAL-typable, so `admitIC` re-certifies the compiled expression once
per program.
- Serves: C2, C4.

**[decision] Every analysis phase terminates by construction, not by budget.** The
walk instantiates each DeferRef occurrence once (finite because the DeferMap is a
DAG); dispatch only unifies, so its fixpoint is bounded by sites times tags;
unification merges a finite number of classes. No phase has a depth cap, variable
budget or polyvariance cap, and a rejection is a fact about the program (a type
cycle, a box conflict), never "the analysis got tired".
- Serves: C2 (a certificate's negative side must mean something), C1.
- Rationale: a cap conflates "the program is bad" with "the analysis is lost", which
  is how a false rejection was pinned for a month without anyone being able to tell
  which it was.

**[decision] The box constraints are solved exactly.** The system is homogeneous
(sums of variables equal a variable, no constants) with zero-forcings and lower
bounds, so a rational solution scales to a natural one and rational feasibility
decides natural feasibility. Three stages, none with a budget: a presolve that draws
the arithmetic-free consequences (zeros propagate both ways, a total equal to one
summand merges the classes, a cycle of `summand <= total` edges makes its members
equal and its other summands zero, lower bounds add up) and reports a boxed/unboxed
clash as `EALBoxConflict` with both blames; sparse Gaussian elimination that keeps
nonnegativity, leaving inequalities over the free variables only, with vacuous rows
dropped; and an exact dual simplex. The slack basis is dual feasible from the start
(every weight is positive) and primal infeasible only on the rows a lower bound made
negative, so each pivot repairs one such row; Bland's rule makes it terminate, and a
row with no negative entry names the origins that cannot hold together
(`EALUnsatisfiable`). The objective is total leaf depth, so the reported levels are
a shallowest decoration in aggregate, not a canonical least one. Depths are
cumulative, one variable per node (`depth = parent + edge`), so every equation has
at most three terms. The level cap, the round budgets and `EALSolverGaveUp` are
gone. A residual with equality rows (which elimination never leaves) falls back to
a two-phase primal simplex.
- Serves: C2 (a rejection is a fact about the program), C3 (levels that mean
  something).
- Rationale: the greedy repair could not tell "no solution" from "stopped looking",
  and the per-occurrence skeleton produces zero-weight equation cycles it pumped
  forever.

**[decision] Appliable values are code tags carrying an interface.** A defer body is
a code tag (its content hash); tag sets *union* at joins instead of unifying, and
captures ride per-tag. Each DeferRef *occurrence* instantiates its body once (a fresh
copy of the body's constraints, served from a per-body template that includes the
nested instances), and the occurrence's tag carries that instance's interface: the
env it consumes and the value it yields. Every `SetEnv` registers an apply site, and
the dispatch fixpoint unifies the site's operand and result with the interface of
every tag that reaches it. This is let-polymorphism over the DeferMap. A code class
reachable from the *argument half* of its own env, or from its result, is
self-application and is rejected outright (the occurs check of arrow types, stated on
interfaces); a cycle through the *capture half* is a regular closure shape (a partial
whose captured function is another such partial, a sized recursion chain) and is
allowed, just as captures never appear in a simple type. Cycles through pair structure
alone collapse to data. The result of an abort that really aborts (a pair message) is
bottom, a value that never exists and absorbs every unification, so the dead base of a
recursion chain joins with its live links.
- Serves: C1 (the analysis mirrors the binder-free core), C2, C4.
- Rationale: per-site-per-tag re-derivation (the previous design) was an unboundedly
  polyvariant flow analysis — it effectively unfolded the program's evaluation at the
  type level, needed a depth cap to terminate on self-application, and could not
  distinguish a Church tower from omega except by how long it ran. Interfaces give
  the finite skeleton that standard EAL inference assumes, and rank-1 is enough for
  the corpus: numeral-of-numeral composition and the curried recursion family certify
  with per-occurrence instances. The price is HM's: a λ-bound function used at two
  incompatible shapes is monomorphic.
- Alternatives: operand-keyed memoization of derivations (does not terminate on
  self-application through fresh capture classes, and any finite abstraction of
  operands conflates some Church tower with omega); a full occurs check through
  captures (rejects sized recursion chains).

**[decision] The box discipline is faithful EAL, read onto the compiled form.**
Levels are proof-net depths, and the certificate's negative side means "no EAL
decoration exists under these readings":
- An env occurrence at a projection path sits exactly as deep as the bangs it opens:
  the env's top bang plus the bangs of every component along the path. No slack: an
  unopened box above a variable is not weakening, it is a use at the wrong level.
- Contraction is charged at the duplicated prefix, to that component's bang; using
  `Left Env` and `Right Env` once each is linear destructuring.
- Boxes pass through, they never vanish. An application whose function carries `k`
  boxes (on the applied pair and on the function) runs inside them: the operand must
  carry at least `k` and the result gains `k`. This is the implicit `let !g = f in
  !^k(g a)` the compiler never writes; without it a boxed result applied directly
  (`$3 $2 succ 0`) is a dereliction. A projection adds the pair's boxes to the
  component (`!(A x B) |- !A`), and a gate switch adds the branch pair's boxes to the
  taken branch.
- A capture that a closure body duplicates is contracted *outside the closure's box*,
  one copy per door, exactly as `\g. !(\x. g (g x))` types Church numerals as
  `!(A -o A) -o !(A -o A)`. The component's bang splits into one door (bounded by the
  analysis-wide unit, so "exactly one" survives the homogeneous scaling) and the part
  the body still opens, and every package built with that code carries its own bang,
  which bounds the doors: the closure is born in the box its copies enter. Argument
  duplication is contracted inside the body as usual.
- Data is level-free: a component of a data tree keeps a free bang and a gate
  scrutinee may sit under any boxes. Copying data is bounded work.
- An abort that really aborts yields bottom (see above).
- Serves: C2, C3, C4.
- Rationale: the previous "pairs are passive conduits" rule let projections and
  applications open boxes silently, so the levels meant "some assignment" and the
  verdict meant "EAL-like". Under the faithful rules every corpus program that
  certified before still certifies, with levels that are now depths.
- Runtime caveat: the door reading places the fan inside the body instance where the
  runtime places it, while the EAL proof places it outside the box. Whether that is
  the invariant the pointer/fresh-label net needs is the unwritten correctness
  argument (§7, §11).

**[decision] Applying data is tolerated** (stuckness is a value until demanded,
matching the call-by-need reference evaluator and the IC runtime's stuck-value
discipline).
- Serves: C4 (consistency with the runtime's discipline).

**[decision] The certificate includes a *virtual application of main* to symbolic
data input**, because divergence hiding under main's outermost lambda is invisible to
a body-local analysis. One virtual application is sound because an iteration's result
must be a data pair; it is also what lets one IC admission cover a whole session.
- Serves: C2, C4.

**[decision] EAL emits advisory runtime guidance** (`CodeGuidance` per body hash: env
usage paths, env bang, max level, speculatability, capture layouts). The contract:
guidance may *only* choose where an optimization is attempted; materialization checks
decide whether it applies. Wrong or stale guidance costs performance, never meaning.
- Serves: C3, C4.
- Rationale: the long-term direction is for certification plus sizing to produce
  guidance rich enough for performance estimation and optimization, without the
  runtime's correctness ever depending on it.

**[decision] Blame is part of the error design.** `EALBoxConflict` names both the
duplication that requires boxing and the site that forbids it.
- Serves: C2 (usability), and the direction of automatic affine-repair transforms,
  for which this is deliberately shaped as the input.

## 6. Execution: runtimes during the transition

Per C4 there should eventually be one runtime. The current plurality is a development
arrangement: a simple reference runtime exists to validate the IC runtime's semantics
against while it is being built, and the other evaluators (fast, meter, partial,
static-check, sizing) are stacks over the same step algebra.

**[decision] All runtimes interpret the same `CompiledExpr` core, and observable
parity between them is enforced by test suites**, not assumed: fast-vs-sized
transcripts, meter-vs-reference values, IC-vs-reference over a compiled corpus.
- Serves: C4 (the reference runtime's only job is to be the oracle the single future
  runtime is checked against).
- Rationale: a second runtime is only worth having if it is observably *the same
  interpreter*; once the IC runtime is trusted, the others become removable.

**[decision] Evaluators are assembled from a shared step algebra**
(`Telomare.Machine`): per-functor step handlers, each taking a "handle everything
else" continuation, composed into stacks. The reference evaluator, the partial
evaluator, the static-check evaluator, and the entire sizing interpreter are different
stacks over different carrier IRs. (The meter and Fast are deliberate hand-written
mirrors instead — see Appendix A for the duplication this causes.)
- Serves: C1 (few forms make a shared algebra practical).

**[decision] Environments are shared, not copied.** Beta-reduction computes the env
value once and splices the same value at every `Env` occurrence, making residual
terms DAGs.
- Serves: C1, C4 (the env is the single sharing point the IC runtime also relies on).
- Consequence: the meter deliberately reports **no memory figure** — counting the term
  as a tree overstates a run by orders of magnitude (~1.2TB vs a few GB on tictactoe),
  and an honest figure needs reachability over distinct nodes, which is consciously
  left unimplemented rather than reported wrong (C3: never report a dishonest number).

**[decision] The IO model is an iterated pure `main`.** Per iteration: input is `0`
(first) or `(inputString, oldState)`; output is `0` (abort) or `(displayString,
nextState)`, with `nextState = 0` ending the session. All runtimes share one driver
loop (`evalLoopCore`) parameterized by evaluator and by a monoidal measurement.
- Serves: C2.
- Rationale: the *unbounded* part of an interactive session — how many turns — lives
  in the impure host loop; each turn is a total function call, so totality never has
  to reason about the session.
- Alternatives: an effect system or stream type in the language would move
  unboundedness inside the language and require the totality story to cover it.

**[decision] `--fast` skips sizing, not certification.** It compiles recursion sites
to an unmaterialized approximant-chain *limit* that unrolls one layer per demand,
charges fuel per unroll/apply (default 2^24 **per main iteration**, so long sessions
don't exhaust it; `--fuel 0` uncaps), and consequently proves nothing about
termination — which is why it is a flag and sizing is the default. It also runs
programs the sizer rejects, and it is the only mode that can report *per-site* unroll
totals (after sizing, the sites no longer exist to attribute costs to).
- Serves: C3 (measurement of programs the sizer cannot yet handle) and development
  of C2 (it is the escape hatch that shows what sizing is failing to prove).

**[decision] In Fast, aborts are discardable values**: only an abort surviving into
the iteration result ends the run, matching the laziness of the reference evaluator.
- Serves: parity (§6, first decision).

## 7. The interaction-combinator runtime (in flight)

**[decision] The single runtime of C4 is assumed to be the "abstract algorithm" flavor
of sharing-graph reduction** — no boxes or brackets at runtime, dup labels minted fresh
per instantiation — which is unsound in general; **EAL typability is the classical
sufficient condition**, hence the admission gate.
- Serves: C4, C1 (this is the "clear path to optimal operational semantics" the core
  is meant to have).
- Rationale: optimal reduction is the strongest known operational target; the
  abstract algorithm is its cheapest form and the price (needing EAL) is one the
  certification story (§5) already pays for totality.
- Alternatives: full Lamping/BOHM with oracle nodes (sound without EAL, much more
  runtime bookkeeping); a conventional graph-reduction machine (no optimality).

Design points the implementation commits to:

- **Telomare maps onto nets unusually cleanly because the core has no binders**: a
  compiled defer body is a static net template with a single env wire.
- **Code is a pointer** (`ICRef` into a template table, keyed by the same content-hash
  namespace as the DeferMap and EAL guidance), so copying code is a leaf duplication.
- **Env delivery is a splitter tree**: disjoint projection paths are routed, never
  copied; fans appear only where a path is genuinely used more than once. The compiler
  side (`envWiring`) and the analyzer side (`cgUsage`) compute the same usage map, and
  a test pins their agreement.
- **Stuckness is a value** (`ICStuckV`): the net fires every redex it instantiates,
  and compiled sizing machinery legitimately leaves ill-shaped applications in dead
  branches; stuck values are erased if undemanded and only fail at readback if
  demanded.
- **Eager speculation is accepted**: bounded dead code costs interactions; diverging
  dead code becomes fuel exhaustion. Termination of live code is EAL's promise.
- **Guided duplication and erasure** consume the advisory capture layouts
  (dup-closure/era-closure bulk operations with generic fans/erasers at the frontier),
  under the advisory-only contract from §5.

**[open] The IC runtime is mid-landing.** The `--ic` CLI mode, the admission driver
(`Telomare.Eval.IC`), and guided erasure are uncommitted; known ceiling: guidance is
keyed by code hash, so discarded *data* (no code head) can't benefit from layout
guidance — era-pair cascades dominate on gate-heavy programs. Identified-but-unbuilt
guidance uses: speculation scheduling from `cgSpeculatable`, call-site env
pre-splitting from `cgUsage`.

## 8. Content-addressed code (DeferMap)

**[decision] Every defer body is content-addressable.** `deferLift` replaces bodies
with SHA-256 references over annotation-stripped structure, collecting them in a map
that is a DAG by construction (nested defers lift first) and dedupes structurally
equal bodies. EAL inference and the IC template table both consume this form, and
share the hash namespace by construction.
- Serves: C1, C4.
- Rationale: the binder-free core makes this free of capture analysis; a program
  representation that is structurally free of static recursion is explicitly wanted
  for both the analysis and the runtime.

**[open] DeferMap-native compilation is a destination, not the present.** Today the
executed pipeline is still let-inlining (`letsToApps`); the lifted form is derived for
analysis. Making the lifted, hash-keyed form the primary representation (with the
analyzer deciding where bodies need level-instances) is the standing "B-plan", gated
on EAL polyvariance being strong enough.

## 9. Artifacts and reports

Nothing here is a commitment; these are the current means of delivering C3.

**[decision] Compile once: `.telc`.** An artifact stores the sized expression, the
sizing report, the *rendered* certificate text, the entry module, and a source hash —
so running it skips parse/certify/size entirely and `--certificate` prints instantly
with no sources present.
- Serves: C3 (the bounds are a durable output), and the pay-once sizing decision (§4).

**[decision] Staleness warns; version mismatch refuses.** An artifact is expected to
outlive the checkout it came from: changed sources produce a note and the run
continues. A format-version mismatch refuses with "recompile it from source" —
invalidate rather than misread. The codec is a hand-written tag-per-node binary format
(deliberately not derived: `Show`/`Read` don't round-trip the term type, and derived
orphan instances were rejected on principle).
- Serves: C3.

**[decision] Two user-facing reports, with disjoint epistemic status.**
`--certificate` says what the compiler *knows without running* (the inferred
per-instantiation counts — which assert nothing new, being the numbers already baked
into the program — plus a cheap structural nesting/duplication-pressure reading that
indexes differently and is explicitly not merged into one table). `--meter` says what
*one run cost* (measurements, not predictions).
- Serves: C3.
- Rationale: prediction and measurement answer different questions and should not be
  blurred in one table; and no number known to be dishonest is reported (see the
  memory figure, §6).

**[decision] Error taxonomy mirrors the pipeline.** One `EvalError` union with a
constructor per stage (resolve / certification / sizing / static check / runtime),
each rendered as user-actionable prose; the driver returns errors as text, never
throws.
- Serves: H1 (one constructor per failure kind, no catch-all).

## 10. The abort system

C5 says what abort is *for*: stating invariants that can be validated statically, in
the manner of refinement typing. This section records how far the code is from that.

**Where abort appears today.**
- User aborts: `x : v` refinements and `assert`-style checks lower to `Abort` applied
  to a validator's result (§4).
- UDT validators: the generated tag check is an abort (§3).
- Recursion-budget aborts: the approximant chain's bottom link (§4).
- Unsizeable aborts: sizing's own failure signalling.
- `Abort` is a core machine form (§2), and every runtime (reference, fast, meter, IC)
  implements it; in Fast and the reference evaluator aborts are lazy, discardable
  values.

**[direction] Split every program into three parts by abort content.** The ideal
compilation pipeline classifies code into:

1. abort-containing sections that can be evaluated *statically* — these are the
   refinement-typing use case; the compiler discharges them and they vanish;
2. abort-containing sections that can only be evaluated at *runtime* — residual
   dynamic checks, which should be the exception and visible as such;
3. sections containing no aborts at all.

With that split, abort becomes purely a surface-level instruction that is erased in
the final runtime: the optimal runtime of C4 never has to implement it.

**[open] Abort is currently a core form and a runtime concern.** The direction above
conflicts with the present state in three places: `Abort` is one of the core machine
forms; the sized approximant chain relies on a runtime abort as its safety net; and
the IC runtime implements abort and abort-message readback. Resolving this means
either discharging those aborts statically (the chain's bottom abort is provably dead
if the certificate is right, so it is a candidate for part 1) or making a principled
argument for a residual runtime abort (part 2) with a smaller footprint than a core
form.

---

# Part III — Open questions and tensions

## 11. The live frontier

Collected here so contributors see it in one place.

1. **Getting all semantically sound surface code to EAL-certify.** This is the central
   difficulty of the §5 approach: known false rejections are terminating programs that
   fall outside the rank-1 fragment (a λ-bound function used at two incompatible
   shapes; `(\f -> f f) id`, which HM also rejects). Numeral-of-numeral composition
   and the same-arity gate join, the two former frontier programs, certify under the
   per-occurrence skeleton with the faithful box discipline and the exact solver.
   Certification cost rose with exactness: a sized `listEqual` takes about 33
   seconds end to end and `tictactoe.tel` about 11 minutes. The box constraints
   are solved once, in the global pass; the standalone per-body passes do only the
   structural work (walk, dispatch, presolve), which is where type cycles and
   boxed/unboxed clashes are found and localized, and per-body levels are read off
   the global solve. The remaining cost is the standalone walks themselves, which
   instantiate each body's subtree once per ancestor (tictactoe has 3,054 bodies
   and 30,123 instances in its main pass alone); an infeasibility only the solver
   can see is reported on main rather than on the body. Interface
   projection was tried and reverted: the type structure mirrors the term's pair
   structure, so almost no bang variable is interior and nothing projects away.
2. **Gate joins in EAL** — one pinned test: arms of disagreeing arity are rejected
   (would need a real data⊔code lattice join at result positions; also blame should
   name the gate, not the deep build site).
3. **Strict vs lazy `if`.** Two conditionals coexist: user-facing `if` lowers to the
   *strict* gate shape only because sizing's input-restriction extraction can currently
   only see through that shape; the lazy form exists and is what recursion unrolling
   depends on; the sized chain deliberately reverts to strict for EAL level-flatness;
   and the IC runtime speculates strict branches (a pinned test shows it fuel-dying on
   a strict dead branch the reference evaluator skips). A coherent single story is
   wanted.
4. **Certified term ≠ executed term** (§3). Two resolutions of the same source; parity
   is assumed, not checked per-program.
5. **Elegance of the recursion form** (§4). The triple is the current answer to C2 and
   is acknowledged to be inelegant; the general-recursion-in-surface direction is one
   candidate replacement, and the target form is itself open.
6. **Abort as a core form vs. abort as erased surface instruction** (§10).
7. **`trace` is currently a no-op** (dropped to identity at `splitExpr`) — restore or
   remove.
8. **The Levels (nesting/`!!`) report is approximate by design** (unknown
   function-parameter summaries contribute offset 0) and this is disclosed; whether it
   should grow toward soundness or stay a cheap heuristic is open.
9. **Guidance for data** — hash-keyed layouts cannot help discarded data values (§7);
   would need branch-shape guidance.
10. **`main` input validation** relies on the refinement idiom (`truncate`, validators)
    by convention; there is no enforced boundary discipline. Under C5 this is the
    intended mechanism, but nothing makes it mandatory.
11. **When does the transitional multi-runtime arrangement end?** (§6, C4). No
    criterion is recorded for when the IC runtime is trusted enough to retire the
    reference evaluator and the hand-mirrored Fast and Meter interpreters.

---

## Appendix A: Incidental inventory (not design)

Things in the tree that appear historical, vestigial, or drifted. Deleting or fixing
any of these should require no design discussion beyond this list; if one is actually
load-bearing, promote it into the body.

**Stale docs / names**
- README still lists a `Telomare.TypeCheck` pipeline stage (module deleted; EAL
  replaced it) and documents neither `--ic` nor the IC modules.
- Comments referencing `Telomare.Resolver` (module is `Resolve`) and the deleted
  `IExpr` type (`funWrap` error strings, `eval2IExpr`).
- `Show1` instances print pre-rename constructor names (`VarUPF`, `UnsizedRecursionUPF`, …).
- `src/SIL/` is an empty directory left from the "Stand In Language" rename;
  `src/Telomare/*.hs.~undo-tree~` are ~2.5MB of Emacs undo files for deleted modules;
  `src/Telomare/dist-newstyle/` is a stray build dir.

**Dead code**
- `Telomare.IR.Types` (`PartialTypeF` etc.) is orphaned by the type-checker removal
  (only pretty-printer instances remain; `Driver` imports it for nothing).
- `SizingOption.NoSizing` is marked deprecated but still implemented (and uses the old
  church-tower encoding that no longer matches the runtime).
- Unreferenced Machine step variants (`superStep`, `unsizedStep`, `zeroedInputStepM`,
  `indexedInputStep'` — a byte-identical copy — and friends); `basicEval`;
  `Driver.runMain`/`compileMain`; `MonoidList`; commented-out SBV imports in two files
  (abandoned SMT sizing attempt).
- The REPL's `--haskell` backend flag selects the only backend that exists.
- `renderStaticReport`'s source-hash parameter is always `Nothing` (the mechanism for
  printing an artifact's hash exists but is never fed).

**Drift / duplication (maintenance hazards, kept honest only by parity tests)**
- The approximant step body exists twice (Machine and Fast), hand-mirrored.
- Lazy gate selection is implemented three different ways (implicit laziness /
  explicit case / syntactic pattern), plus the IC's speculation non-implementation.
- Abort-message truncation ×4 and find-surviving-abort ×4 across the runtimes.
- The Meter is a whole second interpreter whose header names a parity pin that appears
  to have drifted.
- Five hand-copied `debug = False` / `debugTrace` idioms (Machine, Size, Size.IR, IC,
  Reference), plus leftover per-function-id debug switches and `debugIC` ("temporary").
- EAL's `deepShowTau` leaking analyzer-internal ids into user-visible mismatch errors
  is diagnostic scaffolding from the current debugging round, not settled UX.

**Latent bugs / asymmetries noticed in passing**
- `PairTypeP` show instance prints its second component twice.
- `Eq1 UnsizedRecursionF` only handles one constructor; its `Show1` errors on three.
- `Eq1 StuckF` compares defers by index only (correct per the invariant, but the
  invariant is unchecked and hand-violated in two places with re-minted indices).
- `Term3CheckingWrapper` carries a `LocTag` that always duplicates its node annotation.
- The unannotated pattern-synonym builders stamp every node
  `GeneratedLoc "…Cofree instance"`, so terms built through them lose source locations
  (self-labeled "placeholder design") — EAL blame then points at the instance.
- Case desugaring generates references to magic `__case_*` names, and the binding
  pruner hard-codes the unprefixed names to avoid pruning them — a hidden cross-module
  coupling.
- `annotateUnsizedCount` fabricates `:`-prefixed variable names, relying on their
  unparseability (self-described `-- HACK`).
- `unsizedStepM'''`'s name and unused parameters are residue of a vanished iteration
  series.
