import Lax796640.Declarations
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

namespace Lax796640Proofs

open Lax796640.Declarations

@[simp] theorem eraseDups_toFinset (xs : List Nat) :
    xs.eraseDups.toFinset = xs.toFinset := by
  ext a
  simp

@[simp] theorem includes_iff (available requested : List Nat) :
    includes available requested = true ↔ ∀ a ∈ requested, a ∈ available := by
  simp [includes, List.all_eq_true]

@[simp] theorem sameMembers_iff (left right : List Nat) :
    sameMembers left right = true ↔ ∀ a, a ∈ left ↔ a ∈ right := by
  simp only [sameMembers, Bool.and_eq_true, includes_iff]
  aesop

theorem finite_saturation (ambient : Finset Nat) (next : Finset Nat → Finset Nat)
    (grows : ∀ set, set ⊆ next set)
    (preserves : ∀ set, set ⊆ ambient → next set ⊆ ambient)
    (rounds : Nat) (initial : Finset Nat) (within : initial ⊆ ambient)
    (enough : ambient.card ≤ initial.card + rounds) :
    next (next^[rounds] initial) = next^[rounds] initial := by
  induction rounds generalizing initial with
  | zero =>
      have equal : initial = ambient :=
        Finset.eq_of_subset_of_card_le within (by simpa using enough)
      subst initial
      exact Finset.Subset.antisymm (preserves ambient (Finset.Subset.refl _)) (grows ambient)
  | succ rounds ih =>
      by_cases fixed : next initial = initial
      · rw [Function.iterate_fixed fixed]
        exact fixed
      · have strict : initial.card < (next initial).card := by
          by_contra notStrict
          have equal := Finset.eq_of_subset_of_card_le (grows initial)
            (Nat.le_of_not_gt notStrict)
          exact fixed equal.symm
        rw [Function.iterate_succ_apply]
        exact ih (next initial) (preserves initial within) (by omega)

end Lax796640Proofs
