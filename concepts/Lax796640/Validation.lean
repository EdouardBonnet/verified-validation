import Lax796640.Dependencies
import Lax796640.ProofNetworks

/-!
---
title: The executable mathematical validation rules
type: theorem
---
Validation has two descriptions here. `Valid` states the requirements using
quantifiers and graph reachability. `validate` is a concrete Boolean program
using finite lists and the executable axiom collector. The central obligation
is that these descriptions agree on every input.

Only `propext`, `Classical.choice`, and `Quot.sound` are permitted background
axioms. A concept may state an axiom but may not use another statement as an
assumption. Proof declarations may use background axioms and statements from
directly required concept packages. A proof claim must name a theorem with
the same type as its imported conclusion.

These are mathematical acceptance rules. Source fetching, declaration
extraction, namespaces, documentation, paper rendering, and ownership checks
are outside this function. Package roles and kernel comparisons must be
authenticated by the surrounding pipeline; their presence in this data
structure is not authentication.
-/

namespace Lax796640.Validation

open Declarations Dependencies ProofNetworks

/-- The fixed background axiom policy of the intended Lax environment. -/
def backgroundNames : List String :=
  ["propext", "Classical.choice", "Quot.sound"]

/-- A background axiom must have both the right name and a background origin. -/
def backgroundAxiom (s : Snapshot) (id : Nat) : Bool :=
  (declaration s id).any (fun d =>
    d.kind == .axiomDecl && backgroundNames.contains d.name &&
    (package s d.package).any (fun p => p.role == .background))

/-- An admissible statement is a propositional axiom of a concept package. -/
def isStatement (s : Snapshot) (id : Nat) : Bool :=
  (declaration s id).any (fun d =>
    d.kind == .axiomDecl && d.isProposition &&
    (package s d.package).any (fun p => p.role == .concepts))

/-- A proof package may assume statements only from directly required concepts. -/
def allowedStatement (s : Snapshot) (proofPackage statement : Nat) : Bool :=
  isStatement s statement &&
    (package s proofPackage).any (fun p =>
      (declaration s statement).any (fun d => p.requires.contains d.package))

/-- An explicit successful comparison for this particular theorem and conclusion. -/
def comparisonAgrees (s : Snapshot) (c : Claim) : Bool :=
  s.comparisons.any (fun f => f.theoremId == c.theoremId &&
    f.statementId == c.statementId && f.sameType && f.conclusionImported)

/-- Statements used by a theorem, after removing permitted background axioms. -/
def assumptionsOf (s : Snapshot) (theoremId : Nat) : List Nat :=
  (axiomsUsed s theoremId).filter (fun a => !(backgroundAxiom s a))

/-- Declarative requirements on identifiers, package relationships, and references. -/
def TablesValid (s : Snapshot) : Prop :=
  ReferencesWellFormed s ∧
  (s.declarations.map Declaration.name).Nodup ∧
  (s.packages.map Package.id).Nodup ∧ s.localPackages.Nodup ∧
  (∀ id ∈ s.localPackages, ∃ p ∈ s.packages, p.id = id) ∧
  (∀ d ∈ s.declarations, ∃ p ∈ s.packages, p.id = d.package) ∧
  (∀ p ∈ s.packages,
    p.environment = s.environment ∧
    (p.role = .background ∨ p.id ∈ s.localPackages ∨ p.registered = true) ∧
    (∀ id ∈ p.requires, ∃ q ∈ s.packages, q.id = id) ∧
    (p.role = .concepts → ∀ id ∈ p.requires,
      ∀ q ∈ s.packages, q.id = id → q.role ≠ .proofs)) ∧
  (∀ f ∈ s.comparisons,
    (∃ d ∈ s.declarations, d.id = f.theoremId) ∧
    (∃ d ∈ s.declarations, d.id = f.statementId))

/-- The axiom policy for one declaration, stated without the collector program. -/
def DeclarationValid (s : Snapshot) (d : Declaration) : Prop :=
  ∃ p ∈ s.packages, p.id = d.package ∧
    match p.role with
    | .background => True
    | .concepts =>
        (d.kind = .axiomDecl → d.isProposition = true) ∧
        ∀ a, UsesAxiom s d.id a →
          backgroundAxiom s a = true ∨ (d.kind = .axiomDecl ∧ a = d.id)
    | .proofs =>
        ∀ a, UsesAxiom s d.id a →
          backgroundAxiom s a = true ∨ allowedStatement s d.package a = true

/-- A proof claim agrees with declaration facts and with its actual dependencies. -/
def ClaimValid (s : Snapshot) (c : Claim) : Prop :=
  ∃ d ∈ s.declarations, d.id = c.theoremId ∧ d.kind = .theoremDecl ∧
    (package s d.package).any (fun p => p.role == .proofs) = true ∧
    allowedStatement s d.package c.statementId = true ∧
    comparisonAgrees s c = true ∧
    ∀ claimed, c.claimedAssumptions = some claimed →
      ∀ a, a ∈ claimed ↔ UsesAxiom s c.theoremId a ∧ backgroundAxiom s a = false

/-- The independent mathematical specification of acceptance. -/
def Valid (s : Snapshot) : Prop :=
  TablesValid s ∧ (∀ d ∈ s.declarations, DeclarationValid s d) ∧
  (s.claims.map Claim.theoremId).Nodup ∧ (∀ c ∈ s.claims, ClaimValid s c)

/-- Check finite table integrity before relying on lookups. -/
def checkTables (s : Snapshot) : Bool :=
  let declIds := s.declarations.map Declaration.id
  let declNames := s.declarations.map Declaration.name
  let packageIds := s.packages.map Package.id
  declIds.eraseDups.length == declIds.length &&
  declNames.eraseDups.length == declNames.length &&
  packageIds.eraseDups.length == packageIds.length &&
  s.localPackages.eraseDups.length == s.localPackages.length &&
  includes packageIds s.localPackages &&
  s.declarations.all (fun d => packageIds.contains d.package &&
    includes declIds d.references) &&
  s.packages.all (fun p => p.environment == s.environment &&
    (p.role == .background || s.localPackages.contains p.id || p.registered) &&
    includes packageIds p.requires &&
    (p.role != .concepts || p.requires.all (fun id =>
      (package s id).any (fun q => q.role != .proofs)))) &&
  s.comparisons.all (fun f => declIds.contains f.theoremId &&
    declIds.contains f.statementId)

/-- Check the declaration policy using computed axiom dependencies. -/
def checkDeclaration (s : Snapshot) (d : Declaration) : Bool :=
  match package s d.package with
  | none => false
  | some p =>
      match p.role with
      | .background => true
      | .concepts =>
          (d.kind != .axiomDecl || d.isProposition) &&
          (axiomsUsed s d.id).all (fun a => backgroundAxiom s a ||
            (d.kind == .axiomDecl && a == d.id))
      | .proofs =>
          (axiomsUsed s d.id).all (fun a => backgroundAxiom s a ||
            allowedStatement s d.package a)

/-- Check a proof claim; author-supplied assumptions can never hide a dependency. -/
def checkClaim (s : Snapshot) (c : Claim) : Bool :=
  (declaration s c.theoremId).any (fun d =>
    d.kind == .theoremDecl &&
    (package s d.package).any (fun p => p.role == .proofs) &&
    allowedStatement s d.package c.statementId && comparisonAgrees s c &&
    match c.claimedAssumptions with
    | none => true
    | some claimed => sameMembers claimed (assumptionsOf s c.theoremId))

/-- Proposed production entry point for mathematical validation.
This function is executable; it does not call any stated proof obligation. -/
def validate (s : Snapshot) : Bool :=
  checkTables s && s.declarations.all (checkDeclaration s) &&
  (s.claims.map Claim.theoremId).eraseDups.length == s.claims.length &&
  s.claims.all (checkClaim s)

/-- The network recorded after acceptance, built from recomputed assumptions. -/
def network (s : Snapshot) : Network where
  statements := (s.declarations.map Declaration.id).filter (isStatement s)
  rules := s.claims.map (fun c =>
    { proofId := c.theoremId, assumptions := assumptionsOf s c.theoremId,
      conclusion := c.statementId })

/-- No network is returned when the mathematical rules fail. -/
def acceptedNetwork (s : Snapshot) : Option Network :=
  if validate s then some (network s) else none

/-- Exact agreement between the executable validator and its specification. -/
axiom validate_exact (s : Snapshot) : validate s = true ↔ Valid s

/-- Accepted records produce a network with no dangling or duplicate identities. -/
axiom accepted_network_wellFormed (s : Snapshot) (accepted : validate s = true) :
    WellFormed (network s)

/-- Every recorded assumption is an actual, non-background axiom dependency. -/
axiom recorded_assumptions_exact (s : Snapshot) (accepted : validate s = true)
    (c : Claim) (present : c ∈ s.claims) (a : Nat) :
    a ∈ assumptionsOf s c.theoremId ↔
      UsesAxiom s c.theoremId a ∧ backgroundAxiom s a = false

end Lax796640.Validation
