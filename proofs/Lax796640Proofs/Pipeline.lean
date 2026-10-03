import Lax796640.Pipeline
import Lax796640Proofs.Validation

namespace Lax796640Proofs.Pipeline

open Lax796640.Declarations Lax796640.Validation Lax796640.Pipeline

deriving instance ReflBEq, LawfulBEq for ArtifactKey

/-- Each receipt retained by the controller has a matching event in this run.
The failure flag records exactly whether any stage has failed. -/
def Tracks (key : ArtifactKey) (events : List Event) (state : State) : Prop :=
  state.key = key ∧
  (state.conceptsReplayed = true → Event.conceptsReplayed key ∈ events) ∧
  (state.proofsReplayed = true → Event.proofsReplayed key ∈ events) ∧
  (∀ data, state.inspection = some data → Event.inspected key data ∈ events) ∧
  (state.failed = true ↔ Event.failed ∈ events)

theorem tracks_start (key : ArtifactKey) : Tracks key [] (start key) := by
  simp [Tracks, start]

theorem tracks_step (key : ArtifactKey) (events : List Event) (state : State)
    (tracked : Tracks key events state) (event : Event) :
    Tracks key (events ++ [event]) (step state event) := by
  rcases state with ⟨stateKey, concepts, proofs, inspection, failed⟩
  rcases tracked with ⟨rfl, hc, hp, hi, hf⟩
  cases failed <;> cases event <;>
    simp_all [Tracks, step, List.mem_append] <;>
    split_ifs <;> simp_all

theorem run_tracks (key : ArtifactKey) (events : List Event) :
    Tracks key events (run key events) := by
  induction events using List.reverseRecOn with
  | nil => exact tracks_start key
  | append_singleton events event ih =>
      simpa only [run, List.foldl_append, List.foldl_cons, List.foldl_nil] using
        tracks_step key events (run key events) ih event

/--
---
conclusion: Lax796640.Pipeline.approval_requires_evidence
assumptions:
---
The controller invariant links every accepted receipt to this artifact and
this run. Approval additionally supplies the environment and validation checks.
-/
theorem approval_requires_evidence (key : ArtifactKey) (events : List Event)
    (data : Snapshot) (accepted : approvedInput key events = some data) :
    EvidenceComplete key events data := by
  have tracked := run_tracks key events
  dsimp only [approvedInput] at accepted
  split at accepted
  next approved =>
    rcases tracked with ⟨keyEq, concepts, proofs, inspection, failure⟩
    have facts := approved
    simp only [approve, Bool.and_eq_true, accepted, Option.any_some,
      beq_iff_eq] at facts
    rcases facts with ⟨⟨⟨notFailed, conceptsOk⟩, proofsOk⟩, environment, validated⟩
    refine ⟨concepts conceptsOk, proofs proofsOk, inspection data accepted, ?_, ?_,
      (Validation.validate_exact data).1 validated⟩
    · intro failed
      have := failure.mpr failed
      simp [this] at notFailed
    · exact environment.trans (congrArg ArtifactKey.environment keyEq)
  next => simp at accepted

/--
---
conclusion: Lax796640.Pipeline.failure_blocks_approval
assumptions:
---
Failure is recorded permanently; later successful receipts cannot clear it.
-/
theorem failure_blocks_approval (key : ArtifactKey) (events : List Event)
    (failed : Event.failed ∈ events) : approvedInput key events = none := by
  have failure := (run_tracks key events).2.2.2.2.mpr failed
  simp [approvedInput, approve, failure]

/--
---
conclusion: Lax796640.Pipeline.fresh_run_unapproved
assumptions:
---
A fresh controller state has none of the receipts required for approval.
-/
theorem fresh_run_unapproved (key : ArtifactKey) : approve (start key) = false := by
  rfl

end Lax796640Proofs.Pipeline
