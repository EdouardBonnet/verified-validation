import Mathlib.Data.List.Basic

/-!
---
title: The finite input to the validator
type: definition
---
The validator receives a finite table of packages and Lean declarations.
A declaration is a named constant, such as a definition, an axiom, or a
theorem. Its references include constants used in both its type and its body,
and structural links such as an inductive declaration's constructors.

Natural numbers are internal identifiers. Names are retained for readers and
for identifying the three permitted background axioms. Distinct declarations
must have distinct identifiers and names; the validation rules check this.

This is the proposed interface of a production Lean component. An adapter
must obtain these facts from the same artifacts that passed kernel replay.
An input record containing `true` does not itself establish that fact.
-/

namespace Lax796640.Declarations

/-- Background packages are the pinned Lean and Mathlib environment. -/
inductive PackageRole where
  | background
  | concepts
  | proofs
  deriving DecidableEq, BEq, Repr

/-- Only the distinctions needed for the mathematical validation rules. -/
inductive DeclarationKind where
  | axiomDecl
  | theoremDecl
  | other
  deriving DecidableEq, BEq, Repr

/-- A package and the packages it directly requires. -/
structure Package where
  id : Nat
  role : PackageRole
  environment : String
  registered : Bool
  requires : List Nat
  deriving DecidableEq, BEq, Repr

/-- Facts extracted from one kernel-checked declaration. -/
structure Declaration where
  id : Nat
  name : String
  package : Nat
  kind : DeclarationKind
  /-- Whether the declared type itself has type `Prop`. -/
  isProposition : Bool
  /-- References from types, bodies, and structural links to constructors. -/
  references : List Nat
  deriving DecidableEq, BEq, Repr

/-- A kernel comparison and an import check for a proposed conclusion. -/
structure Comparison where
  theoremId : Nat
  statementId : Nat
  sameType : Bool
  conclusionImported : Bool
  deriving DecidableEq, BEq, Repr

/-- An author's request to record a theorem as a proof of a statement. -/
structure Claim where
  theoremId : Nat
  statementId : Nat
  /-- Optional documentation, cross-checked against computed dependencies. -/
  claimedAssumptions : Option (List Nat)
  deriving DecidableEq, BEq, Repr

/-- One environment and its complete relevant declaration table.
`localPackages` are being validated now; other non-background packages must
already be registered. Imported packages still have their declarations here.
-/
structure Snapshot where
  environment : String
  localPackages : List Nat
  packages : List Package
  declarations : List Declaration
  comparisons : List Comparison
  claims : List Claim
  deriving DecidableEq, BEq, Repr

/-- Find a declaration. Duplicate identifiers are rejected before acceptance. -/
def declaration (s : Snapshot) (id : Nat) : Option Declaration :=
  s.declarations.find? (fun d => d.id == id)

/-- Find a package by its identifier. -/
def package (s : Snapshot) (id : Nat) : Option Package :=
  s.packages.find? (fun p => p.id == id)

/-- Every requested identifier belongs to the supplied list. -/
def includes (available requested : List Nat) : Bool :=
  requested.all available.contains

/-- Set equality ignores order and repeated identifiers. -/
def sameMembers (left right : List Nat) : Bool :=
  includes left right && includes right left

/-- The graph conditions needed for bounded dependency traversal. -/
def ReferencesWellFormed (s : Snapshot) : Prop :=
  (s.declarations.map Declaration.id).Nodup ∧
  ∀ d ∈ s.declarations, ∀ id ∈ d.references,
    ∃ target ∈ s.declarations, target.id = id

end Lax796640.Declarations
