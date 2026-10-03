import Lax796640.Dependencies
import Lax796640Proofs.FiniteSaturation

/-! Dependency collection is reachability in the finite reference table.
The proof includes references through cycles and the length-zero path. -/

namespace Lax796640Proofs.Dependencies

open Lax796640.Declarations Lax796640.Dependencies

theorem references_within (s : Snapshot) (h : ReferencesWellFormed s)
    (id a : Nat) (ha : a ∈ references s id) :
    a ∈ s.declarations.map Declaration.id := by
  cases found : declaration s id with
  | none => simp [references, found] at ha
  | some d =>
      have hd := (declaration_exact s h.1 id d).1 found
      have href : a ∈ d.references := by simpa [references, found] using ha
      obtain ⟨target, ht, eq⟩ := h.2 d hd.1 a href
      exact List.mem_map.mpr ⟨target, ht, eq⟩

@[simp] theorem mem_expand (s : Snapshot) (known : List Nat) (a : Nat) :
    a ∈ expand s known ↔ a ∈ known ∨ ∃ b ∈ known, a ∈ references s b := by
  simp [expand]

noncomputable def nextSet (s : Snapshot) (known : Finset Nat) : Finset Nat :=
  (expand s known.toList).toFinset

@[simp] theorem mem_nextSet (s : Snapshot) (known : Finset Nat) (a : Nat) :
    a ∈ nextSet s known ↔ a ∈ known ∨ ∃ b ∈ known, a ∈ references s b := by
  simp [nextSet]

theorem expand_toFinset (s : Snapshot) (known : List Nat) :
    (expand s known).toFinset = nextSet s known.toFinset := by
  ext a
  simp

theorem expandFor_toFinset (s : Snapshot) (rounds : Nat) (known : List Nat) :
    (expandFor s rounds known).toFinset = (nextSet s)^[rounds] known.toFinset := by
  induction rounds generalizing known with
  | zero => rfl
  | succ rounds ih =>
      simp only [expandFor, ih, expand_toFinset, Function.iterate_succ_apply]

theorem reachable_fixed (s : Snapshot) (h : ReferencesWellFormed s)
    (start : Nat) (existsStart : ∃ d ∈ s.declarations, d.id = start) :
    nextSet s (reachable s start).toFinset = (reachable s start).toFinset := by
  unfold reachable
  rw [expandFor_toFinset]
  apply finite_saturation (s.declarations.map Declaration.id).toFinset (nextSet s)
  · intro known a ha
    exact (mem_nextSet _ _ _).2 (.inl ha)
  · intro known within a ha
    rcases (mem_nextSet _ _ _).1 ha with ha | ⟨b, _, href⟩
    · exact within ha
    · simpa using references_within s h b a href
  · simpa using List.mem_map.mpr existsStart
  · have bound := List.toFinset_card_le (s.declarations.map Declaration.id)
    simp only [List.length_map] at bound
    simpa using Nat.le_trans bound (Nat.le_add_left s.declarations.length 1)

theorem expandFor_initial (s : Snapshot) (rounds : Nat) (known : List Nat)
    (a : Nat) (ha : a ∈ known) : a ∈ expandFor s rounds known := by
  induction rounds generalizing known with
  | zero => exact ha
  | succ rounds ih => exact ih (expand s known) ((mem_expand _ _ _).2 (.inl ha))

theorem expandFor_sound (s : Snapshot) (start : Nat) (known : List Nat)
    (sound : ∀ a ∈ known, Reaches s start a) (rounds : Nat) :
    ∀ a ∈ expandFor s rounds known, Reaches s start a := by
  induction rounds generalizing known with
  | zero => exact sound
  | succ rounds ih =>
      apply ih (expand s known)
      intro a ha
      rcases (mem_expand _ _ _).1 ha with ha | ⟨b, hb, href⟩
      · exact sound a ha
      · exact .next (sound b hb) href

/--
---
conclusion: Lax796640.Dependencies.reachable_exact
assumptions:
---
The finite bound saturates the reference graph. Every added reference extends
a path, and every finite path lies in the saturated set.
-/
theorem reachable_exact (s : Snapshot) (h : ReferencesWellFormed s)
    (start : Nat) (existsStart : ∃ d ∈ s.declarations, d.id = start) (id : Nat) :
    id ∈ reachable s start ↔ Reaches s start id := by
  constructor
  · apply expandFor_sound s start [start]
    intro a ha
    have : a = start := by simpa using ha
    subst a
    exact .self start
  · intro path
    induction path with
    | self => exact expandFor_initial s _ [start] start (by simp)
    | @next middle finish path href ih =>
        have member : finish ∈ nextSet s (reachable s start).toFinset := by
          apply (mem_nextSet _ _ _).2
          exact .inr ⟨middle, by simpa using ih, href⟩
        rw [reachable_fixed s h start existsStart] at member
        simpa using member

/--
---
conclusion: Lax796640.Dependencies.axiomsUsed_exact
assumptions:
  - Lax796640.Dependencies.reachable_exact
---
Filtering the exact reachability result by declaration kind gives exactly the
used axioms, including an axiom's dependency on itself.
-/
theorem axiomsUsed_exact (s : Snapshot) (h : ReferencesWellFormed s)
    (start : Nat) (existsStart : ∃ d ∈ s.declarations, d.id = start) (id : Nat) :
    id ∈ axiomsUsed s start ↔ UsesAxiom s start id := by
  simp [axiomsUsed, UsesAxiom, Lax796640.Dependencies.reachable_exact s h start existsStart id]

end Lax796640Proofs.Dependencies
