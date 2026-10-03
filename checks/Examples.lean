import Lax796640

/-!
Executable regression examples for the proposed core. These are synthetic
inspector inputs, not evidence that the named theorem declarations exist in
a real Lean environment. No KernelContract is asserted for these fixtures.
The checks exercise computations; they do not discharge the concept axioms.
-/

open Lax796640
open Declarations Dependencies ProofNetworks Validation Certificates Pipeline Production

namespace BlueprintChecks

def basic : Snapshot where
  environment := "example-environment"
  localPackages := [1, 2]
  packages :=
    [{ id := 0, role := .background, environment := "example-environment",
       registered := true, requires := [] },
     { id := 1, role := .concepts, environment := "example-environment",
       registered := false, requires := [] },
     { id := 2, role := .proofs, environment := "example-environment",
       registered := false, requires := [1] }]
  declarations :=
    [{ id := 0, name := "propext", package := 0, kind := .axiomDecl,
       isProposition := true, references := [] },
     { id := 1, name := "Example.P", package := 1, kind := .axiomDecl,
       isProposition := true, references := [] },
     { id := 2, name := "Example.Q", package := 1, kind := .axiomDecl,
       isProposition := true, references := [] },
     { id := 10, name := "ExampleProofs.p", package := 2, kind := .theoremDecl,
       isProposition := true, references := [] },
     { id := 11, name := "ExampleProofs.q", package := 2, kind := .theoremDecl,
       isProposition := true, references := [1] },
     { id := 12, name := "ExampleProofs.helper", package := 2, kind := .other,
       isProposition := false, references := [11] },
     { id := 13, name := "ExampleProofs.viaHelper", package := 2, kind := .theoremDecl,
       isProposition := true, references := [12] }]
  comparisons :=
    [{ theoremId := 10, statementId := 1, sameType := true, conclusionImported := true },
     { theoremId := 11, statementId := 2, sameType := true, conclusionImported := true },
     { theoremId := 13, statementId := 2, sameType := true, conclusionImported := true }]
  claims :=
    [{ theoremId := 10, statementId := 1, claimedAssumptions := none },
     { theoremId := 11, statementId := 2, claimedAssumptions := some [1] }]

def fullCertificate : List Step :=
  [{ statement := 1, proofId := 10 }, { statement := 2, proofId := 11 }]

#guard validate basic
#guard axiomsUsed basic 13 == [1]
#guard closure (network basic) [] == [1, 2]
#guard check (network basic) [] fullCertificate == some [1, 2]

-- A witness cannot use an assumption before establishing it.
#guard (check (network basic) [] fullCertificate.reverse).isNone
-- The result must include enabled conclusions, not merely justify its own members.
#guard (check (network basic) [] (fullCertificate.take 1)).isNone

def hiddenAssumption : Snapshot :=
  { basic with claims :=
      [{ theoremId := 13, statementId := 2, claimedAssumptions := some [] }] }
#guard !validate hiddenAssumption

def documentedHelper : Snapshot :=
  { hiddenAssumption with claims :=
      [{ theoremId := 13, statementId := 2, claimedAssumptions := some [1, 1] }] }
#guard validate documentedHelper

def cyclicHelpers : Snapshot :=
  { basic with declarations := basic.declarations.map (fun d =>
      if d.id == 12 then { d with references := [13, 1] } else d) }
#guard axiomsUsed cyclicHelpers 13 == [1]
#guard validate cyclicHelpers

def cycle : Snapshot :=
  { basic with declarations := basic.declarations.map (fun d =>
      if d.id == 10 then { d with references := [2] } else d) }
#guard validate cycle
#guard closure (network cycle) [] == []
#guard check (network cycle) [] [] == some []
#guard closure (network cycle) [1] == [1, 2]

def forbidden : Snapshot :=
  { basic with declarations :=
      { id := 50, name := "unapprovedAxiom", package := 0, kind := .axiomDecl,
        isProposition := true, references := [] } ::
      basic.declarations.map (fun d =>
        if d.id == 12 then { d with references := [50] } else d) }
#guard axiomsUsed forbidden 13 == [50]
#guard !validate forbidden

def wrongConclusion : Snapshot :=
  { basic with comparisons := basic.comparisons.map (fun f => { f with sameType := false }) }
#guard !validate wrongConclusion

def dangling : Snapshot :=
  { basic with declarations := basic.declarations.map (fun d =>
      if d.id == 10 then { d with references := [999] } else d) }
#guard !validate dangling

def duplicate : Snapshot :=
  { basic with declarations := basic.declarations ++ basic.declarations }
#guard !validate duplicate

def conceptUsesStatement : Snapshot :=
  { basic with declarations := basic.declarations.map (fun d =>
      if d.id == 2 then { d with references := [1] } else d) }
#guard !validate conceptUsesStatement

def undeclaredRequirement : Snapshot :=
  { basic with packages := basic.packages.map (fun p =>
      if p.id == 2 then { p with requires := [] } else p) }
#guard !validate undeclaredRequirement

def mixedEnvironment : Snapshot :=
  { basic with packages := basic.packages.map (fun p =>
      if p.id == 1 then { p with environment := "another-environment" } else p) }
#guard !validate mixedEnvironment

def draftDependency : Snapshot := { basic with localPackages := [2] }
#guard !validate draftDependency

def key : ArtifactKey :=
  { sourceCommit := "source-A", environment := "example-environment",
    captureDigest := "capture-A", dependencyDigest := "dependencies-A" }

def otherKey : ArtifactKey := { key with captureDigest := "capture-B" }

def successful : List Event :=
  [.conceptsReplayed key, .proofsReplayed key, .inspected key basic]

#guard approve (run key successful)
#guard !(approve (run otherKey successful))
#guard !(approve (run key [.conceptsReplayed otherKey, .proofsReplayed key, .inspected key basic]))
#guard !(approve (run key [.inspected key basic]))
#guard !(approve (run key (successful ++ [.failed])))
#guard !(approve (run key (.failed :: successful)))
#guard !(approve (start key))
#guard validateAndProve key successful fullCertificate ==
  some { assumed := [], established := [1, 2] }
#guard (validateAndClassify key successful [999] []).isNone
#guard (validateAndProve key (successful ++ [.failed]) fullCertificate).isNone

-- These executable functions must not use any of the open theorem obligations.
#print axioms Lax796640.Validation.validate
#print axioms Lax796640.Production.validateAndProve

end BlueprintChecks
