import Lax796640.RelativeSoundness
import Lax796640Proofs.Common

namespace Lax796640Proofs.RelativeSoundness

open Lax796640.Declarations Lax796640.Dependencies Lax796640.ProofNetworks
open Lax796640.Validation Lax796640.Certificates Lax796640.RelativeSoundness

/--
---
conclusion: Lax796640.RelativeSoundness.validation_rules_sound
assumptions:
  - Lax796640.Validation.recorded_assumptions_exact
  - Lax796640.Validation.validate_exact
---
Partition a theorem's actual axiom dependencies into background axioms and
recorded assumptions. The kernel contract establishes the theorem, and its
successful type comparison transfers that meaning to the claimed conclusion.
-/
theorem validation_rules_sound (s : Snapshot) (meaning : Nat → Prop)
    (kernel : KernelContract s meaning) (accepted : validate s = true) :
    RulesSound (network s) meaning := by
  have valid := (Lax796640.Validation.validate_exact s).1 accepted
  intro r hr assumptions
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
  obtain ⟨d, hd, did, kind, _, _, compared, _⟩ := valid.2.2.2 c hc
  have theoremTrue : meaning c.theoremId := by
    rw [← did]
    apply kernel.theoremSound d hd kind
    intro a used
    by_cases background : backgroundAxiom s a = true
    · exact kernel.backgroundSound a background
    · apply assumptions a
      apply (Lax796640.Validation.recorded_assumptions_exact s accepted c hc a).2
      exact ⟨did ▸ used, by simpa using background⟩
  simp only [comparisonAgrees, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at compared
  obtain ⟨comparison, present, ⟨⟨theoremId, statementId⟩, sameType⟩, _⟩ := compared
  have comparisonTrue := kernel.comparisonSound comparison present sameType
  rw [theoremId, statementId] at comparisonTrue
  exact comparisonTrue.mp theoremTrue

/--
---
conclusion: Lax796640.RelativeSoundness.derivation_sound
assumptions:
---
Induction on a finite derivation composes truth-preserving rules.
-/
theorem derivation_sound (n : Network) (meaning : Nat → Prop)
    (rules : RulesSound n meaning) (initial : List Nat)
    (assumptions : ∀ a ∈ initial, meaning a) (a : Nat)
    (derived : Derivable n initial a) : meaning a := by
  induction derived with
  | assumption ha => exact assumptions _ ha
  | apply hr _ ih => exact rules _ hr ih

/--
---
conclusion: Lax796640.RelativeSoundness.established_sound
assumptions:
  - Lax796640.ProofNetworks.closure_exact
  - Lax796640.RelativeSoundness.derivation_sound
  - Lax796640.RelativeSoundness.validation_rules_sound
  - Lax796640.Validation.accepted_network_wellFormed
---
The concrete closure algorithm produces finite derivations, whose rules are
sound under the explicit kernel contract.
-/
theorem established_sound (s : Snapshot) (meaning : Nat → Prop)
    (kernel : KernelContract s meaning) (accepted : validate s = true)
    (initial : List Nat) (admitted : ∀ a ∈ initial, a ∈ (network s).statements)
    (assumptions : ∀ a ∈ initial, meaning a) (a : Nat)
    (established : a ∈ closure (network s) initial) : meaning a := by
  apply Lax796640.RelativeSoundness.derivation_sound (network s) meaning
    (Lax796640.RelativeSoundness.validation_rules_sound s meaning kernel accepted)
    initial assumptions a
  exact (Lax796640.ProofNetworks.closure_exact (network s)
    (Lax796640.Validation.accepted_network_wellFormed s accepted) initial admitted a).1 established

/--
---
conclusion: Lax796640.RelativeSoundness.certificate_sound
assumptions:
  - Lax796640.Certificates.check_exact
  - Lax796640.RelativeSoundness.derivation_sound
  - Lax796640.RelativeSoundness.validation_rules_sound
  - Lax796640.Validation.accepted_network_wellFormed
---
The certificate checker supplies the same finite derivations without trusting
the program that produced the certificate.
-/
theorem certificate_sound (s : Snapshot) (meaning : Nat → Prop)
    (kernel : KernelContract s meaning) (accepted : validate s = true)
    (initial : List Nat) (admitted : ∀ a ∈ initial, a ∈ (network s).statements)
    (assumptions : ∀ a ∈ initial, meaning a) (steps : List Step)
    (known : List Nat) (certificate : check (network s) initial steps = some known)
    (a : Nat) (established : a ∈ known) : meaning a := by
  apply Lax796640.RelativeSoundness.derivation_sound (network s) meaning
    (Lax796640.RelativeSoundness.validation_rules_sound s meaning kernel accepted)
    initial assumptions a
  exact (Lax796640.Certificates.check_exact (network s)
    (Lax796640.Validation.accepted_network_wellFormed s accepted) initial admitted steps known certificate a).1 established

end Lax796640Proofs.RelativeSoundness
