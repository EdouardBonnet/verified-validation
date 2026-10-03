import Lax796640.ProofNetworks

/-!
---
title: Certificates for the exact set of established statements
type: theorem
---
A certificate is a list of statements paired with their chosen proofs, in
dependency order. Each proof must use only initial assumptions or statements
already established earlier in the list. A final check requires the resulting
set to be closed under every rule in the network.

The ordered witnesses show that nothing was falsely added. The closure check
shows that nothing derivable was omitted. Thus one certificate can justify
both the proved and unproved classifications for an entire snapshot.
Unproved here means not derivable from the available rules; it does not mean
that the mathematical statement is false.
-/

namespace Lax796640.Certificates

open Declarations ProofNetworks

/-- A step names the statement being established and the proof rule used. -/
structure Step where
  statement : Nat
  proofId : Nat
  deriving DecidableEq, BEq, Repr

/-- Check witnesses in order; each new statement must have a grounded proof. -/
def checkSteps (n : Network) : List Nat → List Step → Option (List Nat)
  | known, [] => some known.eraseDups
  | known, step :: rest =>
      if !known.contains step.statement && n.rules.any (fun r =>
          r.proofId == step.proofId && r.conclusion == step.statement &&
          includes known r.assumptions) then
        checkSteps n (known ++ [step.statement]) rest
      else none

/-- Check that every enabled proof rule has its conclusion in the result. -/
def checkClosed (n : Network) (known : List Nat) : Bool :=
  n.rules.all (fun r => !(includes known r.assumptions) || known.contains r.conclusion)

/-- Proposed production entry point for checking an entire classification. -/
def check (n : Network) (initial : List Nat) (steps : List Step) : Option (List Nat) :=
  match checkSteps n initial steps with
  | none => none
  | some known => if checkClosed n known then some known else none

/-- An accepted certificate describes precisely all derivable statements. -/
axiom check_exact (n : Network) (h : WellFormed n) (initial : List Nat)
    (admitted : ∀ a ∈ initial, a ∈ n.statements) (steps : List Step)
    (known : List Nat) (accepted : check n initial steps = some known) (a : Nat) :
    a ∈ known ↔ Derivable n initial a

/-- Every well-formed finite network has a certificate of at most one step
per statement. The producer is not assumed to be correct or trusted. -/
axiom certificate_exists (n : Network) (h : WellFormed n) (initial : List Nat)
    (admitted : ∀ a ∈ initial, a ∈ n.statements) :
    ∃ steps known, steps.length ≤ n.statements.length ∧
      check n initial steps = some known

/-- A statement excluded by an accepted certificate has no finite derivation
in this network from these initial assumptions. -/
axiom unproved_certificate (n : Network) (h : WellFormed n) (initial : List Nat)
    (admitted : ∀ a ∈ initial, a ∈ n.statements) (steps : List Step)
    (known : List Nat) (accepted : check n initial steps = some known)
    (a : Nat) (excluded : a ∉ known) : ¬ Derivable n initial a

end Lax796640.Certificates
