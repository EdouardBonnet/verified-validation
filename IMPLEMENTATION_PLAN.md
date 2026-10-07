# Connecting the verified core to Lax validation

This plan extends the proved core in this folder toward the code that Lax
actually runs. The first deliverable is a verified axiom inspection component
used by the Lean inspector. Later milestones connect it to acceptance,
proof-network classification, and publication of the checked artifact.
These are proposed changes; this document adds no new proofs or production code.

The immediate security objective is precise: an accepted dependency report
cannot omit an axiom reachable through the inspected declarations. Combined
with the validation and proof-network results, this prevents a hidden
assumption from being silently treated as discharged. Relating those syntactic
dependencies to everything Lean's kernel needs is a separate, explicit obligation.

## What the current evidence establishes

The inspected Lax source is commit
[`c730f816ca1ac97fffb4960a62d13656b9bbd254`](https://github.com/lax-archive/lax/tree/c730f816ca1ac97fffb4960a62d13656b9bbd254),
with Lean 4.33.0. The local source and GitHub main matched when checked on
3 October 2026. That identifies the reviewed source, not the deployed binary.

The experiments in [lax-755887](https://laxarchive.org/lax-755887/index.html)
distinguish false interface assumptions, circular proofs, and missing imported
axiom reports. Its recorded tests reject the hidden-dependency probes and leave
false application claims open. They do not demonstrate a successful attack on
current Lax. The related
[Lean issue](https://github.com/leanprover/lean4/issues/15226) describes incomplete
dependency results being cached during recursive traversal and exported for
later use. It concerns axiom reporting rather than kernel acceptance of a false
proof without assumptions.

The current inspector already has important defenses. It ignores Lean's
exported axiom cache, traverses declaration types and bodies, and separates
completed cached results from declarations whose traversal is still open.
Replay and inspection use the captured artifacts, and the publisher checks
capture provenance and dependency identities. The next work should prove and
connect these protections rather than assume they are absent.

Two source details need direct attention:

- [`collectAxiomsCached`](https://github.com/lax-archive/lax/blob/c730f816ca1ac97fffb4960a62d13656b9bbd254/src/submission-validation/lean/inspector/Main.lean)
  is a partial recursive function. Its handling of cycles and shared cache
  entries has regression coverage but no correctness proof in this project.
  Missing declarations and a missing root cache entry can currently produce an
  empty result; the verified interface should make these explicit errors.
- Its expression traversal calls `Lean.Expr.getUsedConstants`. In
  [Lean 4.33.0's source](https://github.com/leanprover/lean4/blob/v4.33.0/src/Lean/Util/FoldConsts.lean),
  the underlying `foldConsts` has an unsafe runtime replacement through
  `implemented_by`. A theorem about the current abstract graph does not verify
  that executable traversal. This is a correspondence gap, not evidence of an
  exploit.

The existing 26 proved statements remain useful: they establish graph
reachability, validation rules, finite proof derivations, and controller
properties for the supplied records. They do not establish how those records
were obtained from real artifacts.

## First milestone inspect real Lean declarations

Define executable, total functions over the pinned toolchain's actual
`Lean.Expr` and `Lean.ConstantInfo` types. Use the same definitions in the
inspector and in the theorem statements. Avoid an unverified runtime
replacement for these new functions.

Write an independent occurrence relation and prove that the expression walker
finds exactly its references. Cover every expression constructor. At the
declaration level, include references in types and available bodies, including
the types of axioms themselves. Audit inductive families, constructors,
recursors, projections, opaque declarations, and quotient primitives against
the kernel's rules; specify required structural links explicitly. Generated
and private names must receive the same security treatment as public names.
The existing graph filtered to package-local helpers is for editorial warnings
and must not become the security dependency graph.

Unknown references, unavailable required bodies, unsupported declaration
forms, or exhausted resource bounds must prevent approval. A missing lookup
must never mean that a declaration has no dependencies. Keep declaration names
structural internally; verify any identifier assignment or serialization before
using it for security decisions.

Completion requires constructor coverage, occurrence theorems, and an inspector
adapter calling the proved functions on the actual checked declarations.
Document the remaining primitive observation boundary: loading a captured
environment and retrieving its kernel-checked declarations.

## Second milestone certify the collector results

The recommended first implementation uses a small proved checker to validate
results supplied by a fast collector. The collector may keep its current cache
optimization. Its output alone will no longer authorize a dependency report.

For a queried declaration, a certificate lists a proposed reachable set and
paths witnessing membership. The checker verifies that the root is present,
each listed declaration is reached from it, and every direct dependency of
every listed declaration is also present. Crucially, the checker obtains these
direct dependencies from the real declarations using the first milestone's
extractor; it does not trust an edge list supplied by the producer. It then
checks that the reported axiom set is exactly the axioms in this reachable set.

The main theorem should have this shape, with all well-formedness requirements
stated explicitly:

```text
checkDependencies(E, root, certificate) = success(A)
  implies
  a belongs to A iff a is an axiom reachable from root in E.
```

Here reachability uses the declared dependency relation. This is exact graph
dependency, not a claim that every reported axiom is logically indispensable.

Prove certificate existence for every finite complete input, as well as
soundness for arbitrary certificates. Derive that all successful answers for
one environment and root agree, regardless of query order, cache contents,
declaration enumeration, or certificate producer. Also prove invariance under
consistent renaming and irrelevance of imported axiom-cache payloads when the
checked declarations are unchanged. A corrupt producer can cause rejection;
it cannot obtain approval for an omitted reachable axiom.

Initially use a simple traversal to produce certificates and compare its
results with the existing collector. Benchmark whole submissions and realistic
Mathlib dependency graphs. Avoid repeatedly expanding the entire library for
every declaration. If necessary, add shared certificates or reuse previously
certified closures, with proofs that reuse is valid only for the same immutable
environment. Proving the current cache algorithm as a refinement is another
possible optimization; it is not required for the initial safety theorem.

This milestone covers arbitrary finite dependency cycles, including nested
mutual inductives. It is substantially stronger than testing a fixed collection
of names that happen to trigger a cache bug.

## Third milestone connect dependencies to kernel checking

A correct traversal of an incomplete dependency relation would still be
insufficient. Establish a kernel support result: checking a declaration needs
only declarations in its dependency closure, together with the specified
built-in rules. One formulation is preservation of the relevant typing and
conversion judgments when declarations outside that closure are removed.

This requires an explicit account of inductive and recursor rules, projections,
quotient primitives, and environment well-formedness. The dependency relation
may conservatively include additional structural references where necessary.
The proof must explain why its axiom leaves cover the unchecked assumptions
used by a checked theorem.

This is the hardest mathematical bridge. First audit an available formalization
of Lean's typing rules for compatibility with the pinned toolchain and for its
own assumptions. A theorem about those rules still needs an explicit connection
to the trusted checker implementation. Do not silently rename this obligation
to “faithful extraction,” or claim that a syntax-walking theorem proves it.

The first two milestones can be completed and submitted independently with an
explicit kernel-support hypothesis. This third milestone reduces that
hypothesis. Full verification of Lean's kernel, loader, compiler, and runtime
is outside this plan.

## Fourth milestone connect real inspection to validation rules

Build the input to the existing core from certified dependency results and
authenticated package data. Check the source of each fact currently represented
by a Boolean or identifier: declaration kind, proposition status, declaration
origin, direct concept requirements, background axioms, and the kernel comparison
between an annotated theorem's type and its stated conclusion.

Move the mathematical decisions currently in
[`judgeInspection`](https://github.com/lax-archive/lax/blob/c730f816ca1ac97fffb4960a62d13656b9bbd254/src/submission-validation/phases/inspect.ts)
to calls to the proved Lean entry points. Keep editorial checks separately
identified. User-provided assumption lists remain assertions to verify, never
the source of the computed dependency set.

Prove the adapter's refinement of the existing `Snapshot` interface, including
injective identifiers, exact relevant inventories, and preservation of
dependencies and origins. For serialized data, prove properties of the actual
encoder and decoder where possible, and reject malformed or ambiguous input.
Keep the kernel operations and authenticated package observations that remain
trusted explicit.

Compose with the existing validation and closure theorems. The resulting claim
should say that each proof records all permitted statement assumptions, and
an unconditional proved label has a finite derivation whose assumptions have
all been discharged. False contracts remain open until independently proved;
self-reference and mutual support cannot create a starting proof.

## Fifth milestone bind approval to the artifact that is published

The existing controller checks matching receipt fields. Receiving matching
strings does not establish that checks actually ran on the same files.
Trace and constrain the real path through capture, replay, inspection,
[`artifact-schema.ts`](https://github.com/lax-archive/lax/blob/c730f816ca1ac97fffb4960a62d13656b9bbd254/src/submission-validation/artifact-schema.ts), and
[`submit-publisher.ts`](https://github.com/lax-archive/lax/blob/c730f816ca1ac97fffb4960a62d13656b9bbd254/src/shared/submit-publisher.ts).

Bind the source revision, concept and proof captures, dependency captures,
Lean environment, inspector/core revision, and validation scope to one run.
Require replay and inspection to resolve the same immutable declarations and
publish only the approved capture. Reject stale reports, changed dependencies,
failed stages, malformed results, and partial validation scopes on the full
publication path. Ensure that a checker crash or timeout cannot become success.

Implement the decision and transition logic using the proved controller;
connect actual stage results to its events. Authenticate those results at the
wrapper boundary. Receipt authenticity, filesystem isolation, hashing, and
process execution remain stated infrastructure assumptions unless separately
verified. Tests of the TypeScript wrapper supplement these assumptions; they
do not prove the wrapper correct.

Have the archive's proof-network computation and displayed status consume the
verified classification, or supply a certificate to the existing proved
network checker. This connects the guarantee to what users actually see.

## Validation and delivery

Preserve the lax-755887 probes and add generated cases covering type-only
dependencies, opaque bodies, references in axiom types, long chains, mutual
families, shared subexpressions, and changing query order and names. Deliberately
delete an edge, substitute a stale environment, or supply an incomplete cached
answer and check that certification fails. Add integration cases for mismatched
captures, forged reports, altered assumptions, and failure paths. These tests
exercise integration; the universal collector claim comes from the proofs.

Deliver in stages:

1. A follow-up submission for real declaration extraction and certified axiom
   collection, with a working inspector integration and measured performance.
   Keep the kernel-support boundary explicit.
2. An extension covering the adapter, actual acceptance entry points, and their
   composition with the existing validation and proof-network results.
3. Production integration with artifact binding, comparison against existing
   decisions, and an audit of every publication and displayed-status path.
   Pursue the kernel-support proof as a distinct obligation with its own scope.

Keep concept files readable and free of tactic blocks. Put proofs separately,
import earlier concept statements to expose the proof network, and check that
executable validation functions use none of the submission's statement axioms.
Every claimed completed stage needs replayed proofs, integration checks, and a
record of the exact source and toolchain used.

## The security claim we should ultimately make

For adversarial submission code, annotations, imported cache payloads, and
collector certificates, an unconditional proved label has a finite grounded
derivation using only the permitted background axioms, provided the specified
kernel, artifact-authentication, and execution assumptions hold. This excludes
hidden-dependency and circular-justification attacks within the formalized
input model, including arbitrary instances of the cache failure pattern.

The first collector deliverable alone proves the narrower no-omission result;
the broader claim requires the subsequent connections. None of these milestones
proves that arbitrary attacks on the operating system, GitHub, native memory
safety, or the trusted Lean implementation are impossible. Nor do they certify
that a formal statement expresses the mathematics its author intended.
