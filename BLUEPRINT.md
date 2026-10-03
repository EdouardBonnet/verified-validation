# A verified Lean core for Lax validation

This blueprint describes a replacement for the mathematical decision code in
Lax's validation pipeline. The intended production implementation is the Lean
code in this concept package. We will prove properties of these same functions,
then have the pipeline invoke them. A separately maintained handwritten
translation into TypeScript would reintroduce the correspondence gap that this
project is meant to remove.

The current deliverable is a type-checked design with executable reference
implementations and open theorem statements. It is not a proof that Lax's
current TypeScript implementation is correct, and it is not deployed.

## The guarantee

The headline statement is `Production.production_sound`. If
`Production.validateAndProve` returns a classification, every statement in its
result holds under the explicit `RelativeSoundness.KernelContract` for the
approved input. The unconditional entry point fixes the initial assumption set
to empty. The more general `validateAndClassify` preserves its assumptions in
the output, so a conditional result cannot silently become an unconditional
proved label at this interface.

The kernel contract has three clauses: checked theorem declarations follow
from their actual axiom dependencies; successful kernel type comparisons
preserve the meaning of the type; and the permitted background axioms hold.
The validator must derive sound network rules from these declaration-level
facts. Soundness of every recorded network edge is a theorem goal, not an
assumption of the headline theorem.

The guarantee is relative. Applying it to a real execution also requires that
the declaration graph, origin information, comparisons, and receipts faithfully
represent the checked artifacts. None of those facts is established merely by
putting a Boolean or a digest string in an input record.

## The concrete core

| Component | Executable function | Independent specification or theorem goal |
|---|---|---|
| Declaration dependencies | `Dependencies.axiomsUsed` | `UsesAxiom`, defined by finite paths |
| Mathematical acceptance | `Validation.validate` | `Validation.Valid` |
| Proof-network closure | `ProofNetworks.closure` | `ProofNetworks.Derivable` |
| Whole-network certificate | `Certificates.check` | Exactly the finite derivations from the stated assumptions |
| Pipeline controller | `Pipeline.run` and `approvedInput` | `Pipeline.EvidenceComplete` |
| Combined entry points | `Production.validateAndClassify` and `validateAndProve` | Exact classification and relative soundness |

The independent descriptions use predicates, quantifiers, and finite
derivations. They do not simply define correctness as the executable function
returning `true`. Small record tests, such as matching a conclusion identifier
to a successful kernel comparison, are shared named predicates.

All algorithms terminate by ordinary structural recursion over a fixed number
of rounds or a finite list. Identifiers are natural numbers assigned uniquely
to actual constants and packages. The declaration names are also retained and
checked for uniqueness. The input represents one compatible Lean environment;
combining different archive environments is not supported by this core.

The reference implementations favor readability. Repeated finite-list scans
are not yet suitable evidence of production performance on a full Mathlib
environment. The implementation phase must benchmark representative extracted
inputs. Faster indexed tables or worklists will require a proved refinement of
these semantics before adoption. No machine-model running-time claim is made.

## A running example

Suppose the archive has statements P and Q. One proof establishes P without
statement assumptions; another establishes Q assuming P. The closure is
{P, Q}. A certificate lists the proof of P first and the proof of Q second.

Now remove the assumption-free proof and instead provide P from Q and Q from
P. Both are admissible conditional proofs, so mathematical validation may
accept them. The unconditional closure is empty. An empty witness list is an
exact certificate: neither rule can start. If P is explicitly assumed, both
statements become derivable relative to that assumption.

If a helper used in the proof of Q depends on P, the dependency collector must
still report P. An author-supplied empty assumptions list is rejected. If that
helper instead depends on an unapproved axiom, the proof package is rejected.
These cases are executable examples in [checks/Examples.lean](checks/Examples.lean).

## Why the certificates establish the exact answer

The checker reads proof witnesses in order. A witness can add a statement only
when its recorded rule has all its assumptions among the already established
statements. The list therefore supplies a finite derivation for every added
statement and cannot justify itself through a cycle.

After checking the witnesses, the checker scans every rule. Whenever all
assumptions are in the result, its conclusion must be there too. This closure
condition ensures that no finite derivation has been omitted. The witness and
closure checks together determine the entire least closed set.

An arbitrary program may produce the certificate. Correctness is required of
the checker. A rejected certificate does not establish that its proposed
conclusion is false or unprovable; an accepted exact certificate can establish
that a statement is not derivable from the rules in this particular snapshot.

## The source correspondence requirement

Production must link or import the exact definitions proved in this package.
The build should expose a stable entry point calling
`Production.validateAndProve` for unconditional labels. It should not copy the
body into a different language and rely on matching examples as an equivalence
proof. A source change requires rechecking the relevant proofs.

Pin the core source revision, Lean environment, adapter revision, and build
procedure in each release. A source hash identifies the code; it does not prove
that a compiler preserved its semantics. Executing the compiled Lean program
therefore retains compiler and runtime assumptions. Kernel checking of a
computation certificate is a possible later way to reduce that execution
assumption, but no such deployment mechanism is implemented here.

The source-level claims concern the concrete functions in this folder. The
correspondence to the deployed Lax service begins only once the service calls
them, supplies the specified inputs, and respects their outputs.

## Boundaries that remain to be implemented or trusted

| Boundary | Required behavior | Status in this blueprint |
|---|---|---|
| Source and dependency acquisition | Fetch the pinned source and authentic immutable dependency captures | Existing infrastructure remains outside the proof |
| Lean replay | Check the actual captured declarations against the pinned environment | Explicit kernel and execution boundary |
| Declaration extraction | Supply every relevant declaration, references in types and bodies, structural links to inductive constructors, canonical origins, and actual comparison results | Adapter not implemented or verified here |
| Package metadata | Authenticate direct requirements, registration state, and environment identity | Input contract; list consistency is checked by the core |
| Input decoding | Reject malformed data and faithfully construct the typed input records | Decoder not implemented here |
| Runner receipts | Emit successful events only after the corresponding checks on the named immutable artifact | External runner contract |
| Artifact identity | Bind inspection data to the exact capture and dependency snapshot identified in receipts | Strings are compared here; authenticity and hashing are external |
| Native execution | Execute the proved Lean definitions according to their source semantics | Compiler and runtime remain trusted |
| Publication | Honor rejection and publish precisely the approved artifact | Publisher integration is not implemented here |
| Human interpretation | Confirm that the specification and displayed statements express the intended mathematics | Human review remains necessary |

The controller deliberately takes untrusted-looking data types: any Lean
program can construct an `Event`. The controller proves consequences of a
sequence of events; it does not authenticate those events. Similarly,
`KernelContract` is a named mathematical hypothesis, not an implemented report
verifier or a theorem about Lean's C++ kernel.

The wrapper should stay small enough to review separately. It must distinguish
an ordinary mathematical rejection from a crashed checker, treat both as
non-approval, and never offer a publication path that bypasses the core. Any
future theorem covering the wrapper must formalize these behaviors rather than
hide them in the word "faithful".

## Relationship to the existing implementation

The reference implementation inspected for this design is the local Lax
repository at commit `c730f816ca1ac97fffb4960a62d13656b9bbd254`.

| Existing source | Proposed responsibility |
|---|---|
| `src/submission-validation/lean/inspector/Main.lean`, including `collectAxiomsCached` | Extract primitive declaration facts; replace dependency collection with proved code, or prove the optimization correct |
| `src/submission-validation/phases/inspect.ts`, `judgeInspection` | Route mathematical acceptance to `Validation.validate`; retain separately identified editorial checks |
| `src/submission-validation/phases/replay.ts` | Produce authenticated receipts for the captured artifacts actually replayed |
| `src/submission-validation/pipeline.ts` | Integrate the proved controller and retain its exact input and output binding |
| `src/submission-validation/artifact-schema.ts` and `src/shared/submit-publisher.ts` | Authenticate reports and publish only the artifact approved by the core |
| `src/cli/prooftree.ts` and the website's network computation | Produce witnesses or consume the verified classification |

This is a proposed factoring of responsibilities, not an equivalence claim
about those files. The prototype does not implement namespace restrictions,
layout checks, annotation parsing, paper validation, ownership authorization,
or artifact security. Acceptance by this mathematical core alone is not enough
to publish a Lax submission.

## Proof plan

1. Prove the dependency collector correct. Relate list expansion to bounded
   paths and show that a reachable vertex has a path without repeated vertices.
   This establishes the finite round bound, including graphs with cycles.
2. Prove `validate_exact`. Establish table-check equivalences first, use the
   collector theorem for declaration and claim checks, then combine the finite
   Boolean checks. Derive network well-formedness and exact recorded assumptions.
3. Prove closure soundness and completeness. Induct on rounds for soundness,
   establish saturation within the number of statements, and induct on finite
   derivations for completeness. Cover networks with no initial grounding rule.
4. Prove certificate soundness by an invariant over the witness list. Use final
   closure to obtain completeness. Construct a bounded certificate by ordering
   statements according to when closure first establishes them.
5. Prove the relative soundness chain. Partition each theorem's axiom dependencies
   into permitted background axioms and recorded statement assumptions. Apply
   the kernel contract and the checked conclusion comparison, then compose rules
   by induction on derivations.
6. Prove the preservation results for added rules, discharged assumptions,
   rule reordering, injective renaming, and idempotent closure.
7. Prove controller invariants by induction on the event list. Track the origin
   key of each receipt and show that failure is permanent within a run. Combine
   these invariants with validation and certificate correctness for the public
   entry points.

These proofs belong in `proofs/`, with Lax annotations linking each proof to its
concept statement. No production definition may depend on a concept axiom.
All current theorem statements remain open; none should be treated as a
verified guarantee until a closed proof has been supplied and checked.

## Completion criteria

The mathematical submission is complete when every stated obligation has a
closed, replayed proof, the executable functions have no dependency on those
statement axioms, and the human-readable concepts have been reviewed for the
intended meaning. Regression examples are useful but do not replace proofs.

The source-level production milestone additionally requires a real decoder and
inspector adapter, a benchmarked executable using these functions, documented
input authenticity and execution assumptions, fail-closed publisher integration,
and review showing that the deployed acceptance path cannot bypass the core.
Only then should the project describe Lax's production decision core as verified.

The full deployed pipeline has a broader correctness claim than either milestone.
This blueprint does not claim to verify the operating system, containers, GitHub,
cryptographic primitives, or the Lean kernel itself.
