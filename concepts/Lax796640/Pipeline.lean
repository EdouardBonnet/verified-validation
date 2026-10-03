import Lax796640.Validation

/-!
---
title: Requiring the right checks before approval
type: theorem
---
The proposed controller records successful concept replay, successful proof
replay, and inspection for one identified artifact. Receipts for another
artifact are ignored. Any failure blocks approval for the rest of this run.
A new artifact begins a new run with no inherited receipts.

Artifact identifiers include the source commit, environment, captured files,
and dependency snapshot. Equality of these strings is the controller's check;
computing authentic digests and keeping the represented files immutable are
obligations of the external runner. Similarly, a replay event is a receipt
from the runner, not a formal proof of kernel execution.

The functions here are intended to be used by the production controller.
The stated guarantees are about these exact functions. Their adoption by the
current Node pipeline is still planned work.
-/

namespace Lax796640.Pipeline

open Declarations Validation

/-- The identity shared by replay, inspection, and the eventual publication. -/
structure ArtifactKey where
  sourceCommit : String
  environment : String
  captureDigest : String
  dependencyDigest : String
  deriving DecidableEq, BEq, Repr

/-- Reports from the external runner. Authenticating them is outside this controller. -/
inductive Event where
  | conceptsReplayed (key : ArtifactKey)
  | proofsReplayed (key : ArtifactKey)
  | inspected (key : ArtifactKey) (data : Snapshot)
  | failed
  deriving DecidableEq, BEq, Repr

/-- Accumulated evidence for one artifact. -/
structure State where
  key : ArtifactKey
  conceptsReplayed : Bool
  proofsReplayed : Bool
  inspection : Option Snapshot
  failed : Bool
  deriving DecidableEq, BEq, Repr

/-- Starting a run clears every receipt, even if another run just succeeded. -/
def start (key : ArtifactKey) : State :=
  { key, conceptsReplayed := false, proofsReplayed := false,
    inspection := none, failed := false }

/-- Advance the controller. A failure is permanent within this run. -/
def step (state : State) (event : Event) : State :=
  if state.failed then state else
  match event with
  | .failed => { state with failed := true }
  | .conceptsReplayed key =>
      if key == state.key then { state with conceptsReplayed := true } else state
  | .proofsReplayed key =>
      if key == state.key then { state with proofsReplayed := true } else state
  | .inspected key data =>
      if key == state.key then { state with inspection := some data } else state

/-- Execute a finite sequence of runner events. -/
def run (key : ArtifactKey) (events : List Event) : State :=
  events.foldl step (start key)

/-- Approval requires both replays, an inspection in this environment,
and acceptance by the concrete mathematical validator. -/
def approve (state : State) : Bool :=
  !state.failed && state.conceptsReplayed && state.proofsReplayed &&
    state.inspection.any (fun data =>
      data.environment == state.key.environment && validate data)

/-- The exact inspected input approved at the end of this run, if any. -/
def approvedInput (key : ArtifactKey) (events : List Event) : Option Snapshot :=
  let state := run key events
  if approve state then state.inspection else none

/-- A declarative record of the required successful stages. -/
def EvidenceComplete (key : ArtifactKey) (events : List Event) (data : Snapshot) : Prop :=
  Event.conceptsReplayed key ∈ events ∧ Event.proofsReplayed key ∈ events ∧
  Event.inspected key data ∈ events ∧ Event.failed ∉ events ∧
  data.environment = key.environment ∧ Valid data

/-- An approved input has all required evidence for the same artifact. -/
axiom approval_requires_evidence (key : ArtifactKey) (events : List Event)
    (data : Snapshot) (accepted : approvedInput key events = some data) :
    EvidenceComplete key events data

/-- A failed stage can never be repaired merely by later success receipts. -/
axiom failure_blocks_approval (key : ArtifactKey) (events : List Event)
    (failed : Event.failed ∈ events) : approvedInput key events = none

/-- Starting a new run carries no approval from a previous artifact. -/
axiom fresh_run_unapproved (key : ArtifactKey) : approve (start key) = false

end Lax796640.Pipeline
