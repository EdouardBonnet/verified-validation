import Lax796640.Pipeline
import Lax796640.RelativeSoundness

/-!
---
title: The proposed production entry points and their guarantees
type: theorem
---
The functions in this file combine the controller, validation rules, and
certificate checker. The implementation to deploy is these same Lean
definitions, not a separately handwritten translation of them.

The general entry point reports the assumptions under which its results hold.
The entry point for ordinary proved labels always supplies an empty assumption
list. This prevents a conditional classification from silently being
presented as an unconditional proof.

All theorem declarations in this package are currently open obligations.
Compiling this blueprint checks their types, not their truth. Even after
proving them, deployment still requires faithful input extraction, authentic
runner receipts, correct execution, and a publisher that respects rejection
and publishes the very artifact identified by the approved run.
-/

namespace Lax796640.Production

open Declarations ProofNetworks Certificates Validation RelativeSoundness Pipeline

/-- A classification retains the assumptions on which it depends. -/
structure Classification where
  assumed : List Nat
  established : List Nat
  deriving DecidableEq, BEq, Repr

/-- Proposed production entry point for classification relative to assumptions. -/
def validateAndClassify (key : ArtifactKey) (events : List Event)
    (initial : List Nat) (certificate : List Step) : Option Classification :=
  match approvedInput key events with
  | none => none
  | some data =>
      let n := network data
      if includes n.statements initial then
        (check n initial certificate).map (fun known =>
          { assumed := initial.eraseDups, established := known })
      else none

/-- Proposed entry point for unconditional proved labels. -/
def validateAndProve (key : ArtifactKey) (events : List Event)
    (certificate : List Step) : Option Classification :=
  validateAndClassify key events [] certificate

/-- The final result is exact for the very snapshot approved by the controller. -/
axiom classification_exact (key : ArtifactKey) (events : List Event)
    (initial : List Nat) (certificate : List Step) (result : Classification)
    (accepted : validateAndClassify key events initial certificate = some result) :
    result.assumed = initial.eraseDups ∧
    ∃ data, approvedInput key events = some data ∧ Valid data ∧
      ∀ a, a ∈ result.established ↔ Derivable (network data) initial a

/-- Main proposed production guarantee. The runner/kernel contract applies to
the actual approved input, not to an unrelated model or an arbitrary network. -/
axiom production_sound (key : ArtifactKey) (events : List Event)
    (certificate : List Step) (result : Classification) (meaning : Nat → Prop)
    (trusted : ∀ data, approvedInput key events = some data → KernelContract data meaning)
    (accepted : validateAndProve key events certificate = some result) :
    result.assumed = [] ∧ ∀ a ∈ result.established, meaning a

/-- A failure in the runner cannot yield a successful final classification. -/
axiom production_rejects_failure (key : ArtifactKey) (events : List Event)
    (failed : Event.failed ∈ events) (initial : List Nat) (certificate : List Step) :
    validateAndClassify key events initial certificate = none

end Lax796640.Production
