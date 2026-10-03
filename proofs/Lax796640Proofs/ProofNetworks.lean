import Lax796640.ProofNetworks
import Lax796640Proofs.FiniteSaturation

/-! The list algorithm reaches its least fixed point after at most one round
per statement. Cardinality supplies the termination bound; induction on finite
derivations supplies the independent specification. -/

namespace Lax796640Proofs.ProofNetworks

open Lax796640.Declarations Lax796640.ProofNetworks

theorem derivable_within (n : Network) (h : WellFormed n) (initial : List Nat)
    (admitted : ∀ a ∈ initial, a ∈ n.statements) (a : Nat)
    (derived : Derivable n initial a) : a ∈ n.statements := by
  cases derived with
  | assumption ha => exact admitted a ha
  | apply hr _ => exact (h.2.2 _ hr).1

@[simp] theorem mem_advance (n : Network) (known : List Nat) (a : Nat) :
    a ∈ advance n known ↔ a ∈ known ∨
      ∃ r ∈ n.rules, (∀ b ∈ r.assumptions, b ∈ known) ∧ r.conclusion = a := by
  simp [advance, includes_iff, and_assoc]

noncomputable def nextSet (n : Network) (known : Finset Nat) : Finset Nat :=
  (advance n known.toList).toFinset

@[simp] theorem mem_nextSet (n : Network) (known : Finset Nat) (a : Nat) :
    a ∈ nextSet n known ↔ a ∈ known ∨
      ∃ r ∈ n.rules, (∀ b ∈ r.assumptions, b ∈ known) ∧ r.conclusion = a := by
  simp [nextSet]

theorem advance_toFinset (n : Network) (known : List Nat) :
    (advance n known).toFinset = nextSet n known.toFinset := by
  ext a
  simp

theorem closeFor_toFinset (n : Network) (rounds : Nat) (known : List Nat) :
    (closeFor n rounds known).toFinset = (nextSet n)^[rounds] known.toFinset := by
  induction rounds generalizing known with
  | zero => simp [closeFor]
  | succ rounds ih =>
      simp only [closeFor, ih, advance_toFinset, Function.iterate_succ_apply]

theorem nextSet_grows (n : Network) (known : Finset Nat) :
    known ⊆ nextSet n known := by
  intro a ha
  exact (mem_nextSet n known a).2 (Or.inl ha)

theorem nextSet_preserves (n : Network) (h : WellFormed n) (known : Finset Nat)
    (within : known ⊆ n.statements.toFinset) :
    nextSet n known ⊆ n.statements.toFinset := by
  intro a ha
  rcases (mem_nextSet n known a).1 ha with ha | ⟨r, hr, _, rfl⟩
  · exact within ha
  · simpa using (h.2.2 r hr).1

theorem closure_fixed (n : Network) (h : WellFormed n) (initial : List Nat)
    (admitted : ∀ a ∈ initial, a ∈ n.statements) :
    nextSet n (closure n initial).toFinset = (closure n initial).toFinset := by
  change nextSet n (closeFor n n.statements.length initial).toFinset =
    (closeFor n n.statements.length initial).toFinset
  rw [closeFor_toFinset]
  apply finite_saturation n.statements.toFinset (nextSet n)
    (nextSet_grows n) (nextSet_preserves n h)
  · intro a ha
    simpa using admitted a (by simpa using ha)
  · have bound := List.toFinset_card_le n.statements
    omega

theorem closeFor_initial (n : Network) (rounds : Nat) (known : List Nat)
    (a : Nat) (ha : a ∈ known) : a ∈ closeFor n rounds known := by
  induction rounds generalizing known with
  | zero => simpa [closeFor] using ha
  | succ rounds ih => exact ih (advance n known) ((mem_advance n known a).2 (.inl ha))

theorem closeFor_sound (n : Network) (initial known : List Nat)
    (sound : ∀ a ∈ known, Derivable n initial a) (rounds : Nat) :
    ∀ a ∈ closeFor n rounds known, Derivable n initial a := by
  induction rounds generalizing known with
  | zero => simpa [closeFor] using sound
  | succ rounds ih =>
      apply ih (advance n known)
      intro a ha
      rcases (mem_advance n known a).1 ha with ha | ⟨r, hr, enabled, rfl⟩
      · exact sound a ha
      · exact Derivable.apply hr (fun b hb => sound b (enabled b hb))

/--
---
conclusion: Lax796640.ProofNetworks.closure_closed
assumptions:
---
If another round could add a statement, the strictly growing finite set would
already have exceeded the number of statements in the network.
-/
theorem closure_closed (n : Network) (h : WellFormed n) (initial : List Nat)
    (admitted : ∀ a ∈ initial, a ∈ n.statements) :
    Closed n (closure n initial) := by
  intro r hr enabled
  have member : r.conclusion ∈ nextSet n (closure n initial).toFinset := by
    apply (mem_nextSet _ _ _).2
    exact .inr ⟨r, hr, (by simpa using enabled), rfl⟩
  rw [closure_fixed n h initial admitted] at member
  simpa using member

/--
---
conclusion: Lax796640.ProofNetworks.closure_exact
assumptions:
---
Each round only adds valid rule conclusions. Conversely, the fixed point
contains the leaves and is closed under every rule in a finite derivation.
-/
theorem closure_exact (n : Network) (h : WellFormed n) (initial : List Nat)
    (admitted : ∀ a ∈ initial, a ∈ n.statements) (statement : Nat) :
    statement ∈ closure n initial ↔ Derivable n initial statement := by
  constructor
  · exact closeFor_sound n initial initial (fun _ ha => .assumption ha) _ statement
  · intro derived
    induction derived with
    | assumption ha => exact closeFor_initial n _ initial _ ha
    | apply hr _ ih => exact closure_closed n h initial admitted _ hr ih

/--
---
conclusion: Lax796640.ProofNetworks.no_ungrounded_proof
assumptions:
---
A finite derivation must have a leaf. With no assumptions and no rule without
premises, even a cycle cannot supply one.
-/
theorem no_ungrounded_proof (n : Network)
    (noStart : ∀ r ∈ n.rules, r.assumptions ≠ []) (statement : Nat) :
    ¬ Derivable n [] statement := by
  intro derived
  induction derived with
  | assumption ha => simp at ha
  | @apply r hr _ ih =>
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ (noStart r hr)
      exact ih a ha

end Lax796640Proofs.ProofNetworks
