import Lax796640.Stability
import Lax796640Proofs.Common

namespace Lax796640Proofs.Stability

open Lax796640.ProofNetworks Lax796640.Stability

/--
---
conclusion: Lax796640.Stability.extension_preserves
assumptions:
---
Reuse the same finite derivation in the larger network.
-/
theorem extension_preserves (n larger : Network) (extension : Extends n larger)
    (initial : List Nat) (a : Nat) :
    Derivable n initial a → Derivable larger initial a := by
  intro derived
  induction derived with
  | assumption ha => exact .assumption ha
  | apply hr _ ih => exact .apply (extension _ hr) ih

/--
---
conclusion: Lax796640.Stability.discharge_assumptions
assumptions:
---
Replace each assumption leaf with its supplied derivation.
-/
theorem discharge_assumptions (n : Network) (initial replacement : List Nat)
    (discharge : ∀ a ∈ initial, Derivable n replacement a) (a : Nat) :
    Derivable n initial a → Derivable n replacement a := by
  intro derived
  induction derived with
  | assumption ha => exact discharge _ ha
  | apply hr _ ih => exact .apply hr ih

/--
---
conclusion: Lax796640.Stability.rules_order_irrelevant
assumptions:
  - Lax796640.Stability.extension_preserves
---
Rule membership is the only feature of the rule list used by derivations.
-/
theorem rules_order_irrelevant (left right : Network)
    (sameRules : ∀ r, r ∈ left.rules ↔ r ∈ right.rules)
    (initial : List Nat) (a : Nat) :
    Derivable left initial a ↔ Derivable right initial a :=
  ⟨Lax796640.Stability.extension_preserves left right (fun r hr => (sameRules r).1 hr) initial a,
   Lax796640.Stability.extension_preserves right left (fun r hr => (sameRules r).2 hr) initial a⟩

theorem rename_forward (n : Network) (f : Nat → Nat) (initial : List Nat)
    (a : Nat) (derived : Derivable n initial a) :
    Derivable (rename f n) (initial.map f) (f a) := by
  induction derived with
  | assumption ha => exact .assumption (List.mem_map.mpr ⟨_, ha, rfl⟩)
  | @apply r hr _ ih =>
      apply Derivable.apply (r := { r with assumptions := r.assumptions.map f, conclusion := f r.conclusion })
      · exact List.mem_map.mpr ⟨r, hr, rfl⟩
      · intro b hb
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
        exact ih a ha

theorem rename_backward (n : Network) (f : Nat → Nat) (injective : Function.Injective f)
    (initial : List Nat) (b : Nat)
    (derived : Derivable (rename f n) (initial.map f) b) :
    ∀ a, b = f a → Derivable n initial a := by
  induction derived with
  | assumption hb =>
      intro a eq
      obtain ⟨a', ha', mapped⟩ := List.mem_map.mp hb
      have : a' = a := injective (mapped.trans eq)
      exact .assumption (this ▸ ha')
  | @apply r hr _ ih =>
      intro a eq
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp hr
      have : original.conclusion = a := injective eq
      subst a
      apply Derivable.apply present
      intro b hb
      exact ih (f b) (List.mem_map.mpr ⟨b, hb, rfl⟩) b rfl

/--
---
conclusion: Lax796640.Stability.renaming_exact
assumptions:
---
Map the derivation in one direction. Injectivity permits each mapped rule and
assumption to be recovered in the other direction.
-/
theorem renaming_exact (n : Network) (f : Nat → Nat) (injective : Function.Injective f)
    (initial : List Nat) (a : Nat) :
    Derivable (rename f n) (initial.map f) (f a) ↔ Derivable n initial a :=
  ⟨fun h => rename_backward n f injective initial (f a) h a rfl,
   rename_forward n f initial a⟩

/--
---
conclusion: Lax796640.Stability.closure_idempotent
assumptions:
  - Lax796640.ProofNetworks.closure_exact
  - Lax796640.Stability.discharge_assumptions
---
An assumption in the first closure already has a derivation from the original
assumptions. Substituting those derivations makes a second closure redundant.
-/
theorem closure_idempotent (n : Network) (h : WellFormed n) (initial : List Nat)
    (admitted : ∀ a ∈ initial, a ∈ n.statements) (a : Nat) :
    a ∈ closure n (closure n initial) ↔ a ∈ closure n initial := by
  have exactFirst := Lax796640.ProofNetworks.closure_exact n h initial admitted
  have inNetwork : ∀ b ∈ closure n initial, b ∈ n.statements := by
    intro b hb
    cases (exactFirst b).1 hb with
    | assumption hi => exact admitted b hi
    | apply hr _ => exact (h.2.2 _ hr).1
  rw [Lax796640.ProofNetworks.closure_exact n h (closure n initial) inNetwork]
  constructor
  · intro derived
    apply (exactFirst a).2
    exact Lax796640.Stability.discharge_assumptions n (closure n initial) initial
      (fun b hb => (exactFirst b).1 hb) a derived
  · exact Derivable.assumption

end Lax796640Proofs.Stability
