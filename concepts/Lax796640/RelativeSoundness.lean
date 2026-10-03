import Lax796640.Validation
import Lax796640.Certificates

/-!
---
title: What acceptance guarantees under the kernel contract
type: theorem
---
Give each declaration identifier the proposition expressed by its type.
The kernel contract below specifies the facts supplied by the trusted Lean
boundary: a checked theorem follows from its actual axiom dependencies,
successful type comparisons preserve meaning, and the permitted background
axioms hold in the chosen interpretation.

These are explicit hypotheses. This submission does not prove Lean's kernel
sound, or establish that an arbitrary JSON report came from that kernel.
Faithful extraction of declaration references and comparisons is necessary
to apply the contract to the real archive.

The important intermediate claim is derived rather than assumed: validation
turns these declaration-level facts into sound proof-network rules. Finite
derivations then compose those rules. A valid conditional proof may still
have unproved assumptions; acceptance alone does not discharge them.
-/

namespace Lax796640.RelativeSoundness

open Declarations Dependencies ProofNetworks Validation Certificates

/-- The explicit logical interface to replay and faithful inspection.
`meaning id` denotes the proposition expressed by the declaration's type;
the contract is used only for theorems and their axiom dependencies.
-/
structure KernelContract (s : Snapshot) (meaning : Nat → Prop) : Prop where
  /-- Kernel-checked theorem bodies establish their types from their axiom leaves. -/
  theoremSound : ∀ d ∈ s.declarations, d.kind = .theoremDecl →
    (∀ a, UsesAxiom s d.id a → meaning a) → meaning d.id
  /-- Conversion compares the actual types, rather than their printed text. -/
  comparisonSound : ∀ f ∈ s.comparisons, f.sameType = true →
    (meaning f.theoremId ↔ meaning f.statementId)
  /-- The three permitted background axioms hold in the chosen interpretation. -/
  backgroundSound : ∀ a, backgroundAxiom s a = true → meaning a

/-- Each recorded rule preserves truth when all of its assumptions hold. -/
def RulesSound (n : Network) (meaning : Nat → Prop) : Prop :=
  ∀ r ∈ n.rules, (∀ a ∈ r.assumptions, meaning a) → meaning r.conclusion

/-- The validator's acceptance rules justify the edges it records. -/
axiom validation_rules_sound (s : Snapshot) (meaning : Nat → Prop)
    (kernel : KernelContract s meaning) (accepted : validate s = true) :
    RulesSound (network s) meaning

/-- Finite derivations compose sound rules without introducing new assumptions. -/
axiom derivation_sound (n : Network) (meaning : Nat → Prop)
    (rules : RulesSound n meaning) (initial : List Nat)
    (assumptions : ∀ a ∈ initial, meaning a) (a : Nat)
    (derived : Derivable n initial a) : meaning a

/-- Main mathematical guarantee for the computed closure of accepted records. -/
axiom established_sound (s : Snapshot) (meaning : Nat → Prop)
    (kernel : KernelContract s meaning) (accepted : validate s = true)
    (initial : List Nat) (admitted : ∀ a ∈ initial, a ∈ (network s).statements)
    (assumptions : ∀ a ∈ initial, meaning a) (a : Nat)
    (established : a ∈ closure (network s) initial) : meaning a

/-- The same guarantee holds when an arbitrary producer supplies a certificate. -/
axiom certificate_sound (s : Snapshot) (meaning : Nat → Prop)
    (kernel : KernelContract s meaning) (accepted : validate s = true)
    (initial : List Nat) (admitted : ∀ a ∈ initial, a ∈ (network s).statements)
    (assumptions : ∀ a ∈ initial, meaning a) (steps : List Step)
    (known : List Nat) (certificate : check (network s) initial steps = some known)
    (a : Nat) (established : a ∈ known) : meaning a

end Lax796640.RelativeSoundness
