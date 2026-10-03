import Lax796640.Production
import Lax796640Proofs.Pipeline
import Lax796640Proofs.RelativeSoundness

namespace Lax796640Proofs.Production

open Lax796640.Declarations Lax796640.ProofNetworks Lax796640.Certificates
open Lax796640.Validation Lax796640.RelativeSoundness Lax796640.Pipeline
open Lax796640.Production

/--
---
conclusion: Lax796640.Production.classification_exact
assumptions:
---
Successful execution identifies the very inspected snapshot that passed the
controller and validator. The certificate result is exact for that network,
and the returned assumptions are precisely the supplied assumptions.
-/
theorem classification_exact (key : ArtifactKey) (events : List Event)
    (initial : List Nat) (certificate : List Step) (result : Classification)
    (accepted : validateAndClassify key events initial certificate = some result) :
    result.assumed = initial.eraseDups ∧
    ∃ data, approvedInput key events = some data ∧ Valid data ∧
      ∀ a, a ∈ result.established ↔ Derivable (network data) initial a := by
  unfold validateAndClassify at accepted
  cases approved : approvedInput key events with
  | none => simp [approved] at accepted
  | some data =>
      simp only [approved] at accepted
      split at accepted
      next admitted =>
        cases checked : check (network data) initial certificate with
        | none => simp [checked] at accepted
        | some known =>
            have resultEq : { assumed := initial.eraseDups, established := known : Classification } = result := by
              simpa [checked] using accepted
            subst result
            have evidence := Pipeline.approval_requires_evidence key events data approved
            have valid := evidence.2.2.2.2.2
            refine ⟨rfl, data, rfl, valid, ?_⟩
            intro a
            exact Certificates.check_exact (network data)
              (Validation.accepted_network_wellFormed data ((Validation.validate_exact data).2 valid))
              initial ((includes_iff _ _).1 admitted) certificate known checked a
      next => simp at accepted

/--
---
conclusion: Lax796640.Production.production_sound
assumptions:
---
The unconditional entry point supplies no assumptions. Exact classification
therefore gives a finite derivation from sound rules for every proved label,
under the kernel contract for the actual approved snapshot.
-/
theorem production_sound (key : ArtifactKey) (events : List Event)
    (certificate : List Step) (result : Classification) (meaning : Nat → Prop)
    (trusted : ∀ data, approvedInput key events = some data → KernelContract data meaning)
    (accepted : validateAndProve key events certificate = some result) :
    result.assumed = [] ∧ ∀ a ∈ result.established, meaning a := by
  obtain ⟨assumed, data, approved, valid, exactResult⟩ :=
    classification_exact key events [] certificate result accepted
  refine ⟨assumed, ?_⟩
  intro a ha
  exact RelativeSoundness.derivation_sound (network data) meaning
    (RelativeSoundness.validation_rules_sound data meaning (trusted data approved)
      ((Validation.validate_exact data).2 valid)) [] (by simp) a ((exactResult a).1 ha)

/--
---
conclusion: Lax796640.Production.production_rejects_failure
assumptions:
---
The final entry point immediately rejects whenever the controller records a
failure, regardless of the proposed assumptions or certificate.
-/
theorem production_rejects_failure (key : ArtifactKey) (events : List Event)
    (failed : Event.failed ∈ events) (initial : List Nat) (certificate : List Step) :
    validateAndClassify key events initial certificate = none := by
  simp [validateAndClassify, Pipeline.failure_blocks_approval key events failed]

end Lax796640Proofs.Production
