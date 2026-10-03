# Verified Lean validation blueprint

This folder contains a local Lax concept package for a proposed production
validator written in Lean. Its functions are executable. Its 26 theorem
statements are **open proof obligations**, and the current Lax service does
not use this code.

Start with [BLUEPRINT.md](BLUEPRINT.md) for the exact scope, trust boundaries,
proof plan, and production adoption criteria. The main formal guarantee is
[`Production.production_sound`](concepts/Lax796640/Production.lean).

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
algorithms. The declaration `axiom` is Lax's notation for a statement awaiting
a proof in a separate proof package. No executable function uses those axioms.
The proof package is deliberately empty at this stage.

From the parent directory, check the concepts with:

```sh
lax build verified-validation --only concepts --replay
```

After building, run the executable regression examples from `concepts/`:

```sh
lake env lean ../checks/Examples.lean
```

These checks establish that the blueprint compiles and that the examples behave
as expected. They do not discharge the open theorem statements. The package
uses the existing Lax Mathlib cache and has no RAM or other submission dependency.
