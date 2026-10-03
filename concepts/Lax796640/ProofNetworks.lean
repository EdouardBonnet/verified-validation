import Lax796640.Declarations

/-!
---
title: Finite derivations in a proof network
type: theorem
---
A proof rule says that its conclusion follows if all its assumptions have
been established. Several rules may have the same conclusion. A derivation
is a finite tree of rule applications, with designated assumptions at its
leaves. A rule with no assumptions supplies a starting point.

The closure algorithm repeatedly applies all available rules. Its result is
specified by finite derivability, independently of the algorithm. The target
equivalence concerns the rules in this snapshot, not all possible Lean proofs.
-/

namespace Lax796640.ProofNetworks

open Declarations

/-- One conditional proof, identified by its theorem declaration. -/
structure Rule where
  proofId : Nat
  assumptions : List Nat
  conclusion : Nat
  deriving DecidableEq, BEq, Repr

/-- Statements and the available rules for establishing them. -/
structure Network where
  statements : List Nat
  rules : List Rule
  deriving DecidableEq, BEq, Repr

/-- Rules refer to existing statements and have distinct proof identifiers. -/
def WellFormed (n : Network) : Prop :=
  n.statements.Nodup ∧ (n.rules.map Rule.proofId).Nodup ∧
  ∀ r ∈ n.rules, r.conclusion ∈ n.statements ∧
    ∀ a ∈ r.assumptions, a ∈ n.statements

/-- Establish a statement from designated assumptions using finitely many rules. -/
inductive Derivable (n : Network) (initial : List Nat) : Nat → Prop where
  | assumption {statement : Nat} :
      statement ∈ initial → Derivable n initial statement
  | apply {r : Rule} : r ∈ n.rules →
      (∀ a ∈ r.assumptions, Derivable n initial a) →
      Derivable n initial r.conclusion

/-- A set is closed when every rule whose assumptions it contains stays in it. -/
def Closed (n : Network) (known : List Nat) : Prop :=
  ∀ r ∈ n.rules, (∀ a ∈ r.assumptions, a ∈ known) → r.conclusion ∈ known

/-- One round of the executable closure algorithm. -/
def advance (n : Network) (known : List Nat) : List Nat :=
  (known ++ (n.rules.filter (fun r => includes known r.assumptions)).map
    Rule.conclusion).eraseDups

/-- Each recursive call consumes one round. -/
def closeFor (n : Network) : Nat → List Nat → List Nat
  | 0, known => known.eraseDups
  | rounds + 1, known => closeFor n rounds (advance n known)

/-- At most one round per statement suffices, even in a cyclic network. -/
def closure (n : Network) (initial : List Nat) : List Nat :=
  closeFor n n.statements.length initial

/-- The computed set is exactly the set of finite derivations. -/
axiom closure_exact (n : Network) (h : WellFormed n) (initial : List Nat)
    (admitted : ∀ a ∈ initial, a ∈ n.statements) (statement : Nat) :
    statement ∈ closure n initial ↔ Derivable n initial statement

/-- The bound built into the algorithm reaches a fixed point. -/
axiom closure_closed (n : Network) (h : WellFormed n) (initial : List Nat)
    (admitted : ∀ a ∈ initial, a ∈ n.statements) :
    Closed n (closure n initial)

/-- Without initial assumptions or a rule with no assumptions, nothing starts. -/
axiom no_ungrounded_proof (n : Network)
    (noStart : ∀ r ∈ n.rules, r.assumptions ≠ []) (statement : Nat) :
    ¬ Derivable n [] statement

end Lax796640.ProofNetworks
