import Lax796640.ProofNetworks

/-!
---
title: Adding proofs, discharging assumptions, and renaming statements
type: theorem
---
Several archive operations should preserve existing derivations. Adding
available proofs cannot invalidate one. Assumptions can be replaced by their
own derivations. Reordering the available rules does not change what follows.
Renaming identifiers consistently also preserves the result, provided the
renaming does not merge distinct statements.

These statements concern immutable mathematical networks. Replacing an
archived submission is covered only when the replacement satisfies the
stated network relationship; a successor label alone is not such a proof.
-/

namespace Lax796640.Stability

open ProofNetworks

/-- Every original rule remains available in an extension. -/
def Extends (original extended : Network) : Prop :=
  ∀ r ∈ original.rules, r ∈ extended.rules

/-- Rename statement identifiers in assumptions and conclusions. Proof ids stay fixed. -/
def rename (f : Nat → Nat) (n : Network) : Network where
  statements := n.statements.map f
  rules := n.rules.map (fun r =>
    { r with assumptions := r.assumptions.map f, conclusion := f r.conclusion })

/-- Adding rules preserves all existing finite derivations. -/
axiom extension_preserves (n larger : Network) (extension : Extends n larger)
    (initial : List Nat) (a : Nat) :
    Derivable n initial a → Derivable larger initial a

/-- Derivations of the assumptions can be substituted into a derivation. -/
axiom discharge_assumptions (n : Network) (initial replacement : List Nat)
    (discharge : ∀ a ∈ initial, Derivable n replacement a) (a : Nat) :
    Derivable n initial a → Derivable n replacement a

/-- The order and multiplicity of identical proof rules have no semantic effect. -/
axiom rules_order_irrelevant (left right : Network)
    (sameRules : ∀ r, r ∈ left.rules ↔ r ∈ right.rules)
    (initial : List Nat) (a : Nat) :
    Derivable left initial a ↔ Derivable right initial a

/-- An injective renaming preserves and reflects derivability. -/
axiom renaming_exact (n : Network) (f : Nat → Nat) (injective : Function.Injective f)
    (initial : List Nat) (a : Nat) :
    Derivable (rename f n) (initial.map f) (f a) ↔ Derivable n initial a

/-- Recomputing closure from an already closed result changes no membership. -/
axiom closure_idempotent (n : Network) (h : WellFormed n) (initial : List Nat)
    (admitted : ∀ a ∈ initial, a ∈ n.statements) (a : Nat) :
    a ∈ closure n (closure n initial) ↔ a ∈ closure n initial

end Lax796640.Stability
