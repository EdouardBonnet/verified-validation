import Lax796640.Declarations

/-!
---
title: Finding every axiom used by a declaration
type: theorem
---
A declaration depends on an axiom when following constant references can
reach that axiom. We include a path of length zero: an axiom uses itself.
References in types matter as well as references in proof bodies.

The executable collector expands the set of reachable declarations once per
round. There are at most as many necessary rounds as declarations. This
handles cycles without relying on recursive calls through the graph.

The two statements below are proof obligations. They concern the concrete
functions in this file, given a complete finite reference table. Establishing
that an inspector supplies that table is a separate integration obligation.
-/

namespace Lax796640.Dependencies

open Declarations

/-- The direct references of a declaration; absent entries have no references.
Missing referenced declarations are nevertheless rejected by validation. -/
def references (s : Snapshot) (id : Nat) : List Nat :=
  ((declaration s id).map Declaration.references).getD []

/-- A finite path in the graph of constant references. -/
inductive Reaches (s : Snapshot) : Nat → Nat → Prop where
  | self (id : Nat) : Reaches s id id
  | next {start middle finish : Nat} :
      Reaches s start middle → finish ∈ references s middle →
      Reaches s start finish

/-- One round retains known declarations and adds their direct references. -/
def expand (s : Snapshot) (known : List Nat) : List Nat :=
  (known ++ known.flatMap (references s)).eraseDups

/-- Run a fixed number of rounds, using ordinary recursion on a natural number. -/
def expandFor (s : Snapshot) : Nat → List Nat → List Nat
  | 0, known => known
  | rounds + 1, known => expandFor s rounds (expand s known)

/-- The proposed executable collector, with its finite bound built in. -/
def reachable (s : Snapshot) (start : Nat) : List Nat :=
  expandFor s s.declarations.length [start]

/-- Test the recorded kind of a declaration. -/
def isAxiom (s : Snapshot) (id : Nat) : Bool :=
  (declaration s id).any (fun d => d.kind == .axiomDecl)

/-- The specification of an axiom dependency uses finite paths. -/
def UsesAxiom (s : Snapshot) (start axiomId : Nat) : Prop :=
  Reaches s start axiomId ∧ isAxiom s axiomId = true

/-- Compute dependencies from references, never from an author's claimed list. -/
def axiomsUsed (s : Snapshot) (start : Nat) : List Nat :=
  (reachable s start).filter (isAxiom s)

/-- The bounded traversal finds exactly the reachable declarations. -/
axiom reachable_exact (s : Snapshot) (h : ReferencesWellFormed s)
    (start : Nat) (existsStart : ∃ d ∈ s.declarations, d.id = start) (id : Nat) :
    id ∈ reachable s start ↔ Reaches s start id

/-- No used axiom is omitted, and no unrelated axiom is reported. -/
axiom axiomsUsed_exact (s : Snapshot) (h : ReferencesWellFormed s)
    (start : Nat) (existsStart : ∃ d ∈ s.declarations, d.id = start) (id : Nat) :
    id ∈ axiomsUsed s start ↔ UsesAxiom s start id

end Lax796640.Dependencies
