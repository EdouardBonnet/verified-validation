# A verified Lean core for Lax validation

This folder contains a Lax submission for a proposed production validator
written in Lean. Its functions are executable, and all **26 theorem statements
have proofs** in the separate proof package. The current Lax service does not
use this code.

Start with [BLUEPRINT.md](BLUEPRINT.md) for the exact scope, trust boundaries,
proof structure, and production adoption criteria. The main formal guarantee is
[`Production.production_sound`](concepts/Lax796640/Production.lean).
Its [proof](proofs/Lax796640Proofs/Production.lean) applies to the concrete Lean
entry point under the explicit kernel and input contract. It does not verify
the current TypeScript pipeline or its surrounding infrastructure.

[IMPLEMENTATION_PLAN.md](IMPLEMENTATION_PLAN.md) sets out the next stages:
certified axiom collection from real Lean declarations, connection to the
validation rules, and binding approval to the artifacts used in production.

The source is arranged for readers in this order:

1. [Declarations](concepts/Lax796640/Declarations.lean): the input records and what their fields mean.
2. [Dependencies](concepts/Lax796640/Dependencies.lean): which axioms a declaration uses.
3. [ProofNetworks](concepts/Lax796640/ProofNetworks.lean): finite derivations and closure.
4. [Validation](concepts/Lax796640/Validation.lean): an independent specification and a concrete checker.
5. [Certificates](concepts/Lax796640/Certificates.lean): exact proved and unproved classifications.
6. [RelativeSoundness](concepts/Lax796640/RelativeSoundness.lean): the explicit kernel contract.
7. [Stability](concepts/Lax796640/Stability.lean): extension, substitution of assumptions, and renaming.
8. [Pipeline](concepts/Lax796640/Pipeline.lean): stage receipts, artifact identity, and failure handling.
9. [Production](concepts/Lax796640/Production.lean): the intended public entry points.

The concept files contain no tactic blocks, `sorry`, or noncomputable
algorithms. Lax keeps statements declared with `axiom` in the concept package
and their proofs in [proofs/](proofs/Lax796640Proofs.lean). Proofs of later results
use the corresponding concept statements, so the proof network displays their
dependencies. Every required statement has a proof, and the network closes
without cycles. Shared technical helpers are kept separate from these submitted
results. No executable function uses the statement axioms.

From the parent directory, build and replay both packages with:

```sh
lax build verified-validation --replay
node complexity/scripts/audit-proof-closure.mjs verified-validation
```

After building, run the executable regression examples from `concepts/`:

```sh
lake env lean ../checks/Examples.lean
```

The replay checks the proof terms, and the closure audit checks that all 26
statements have closed proofs. The executable examples check representative
accepted and rejected inputs; they supplement the general proofs. The package
uses the existing Lax Mathlib cache and has no RAM or other submission dependency.
