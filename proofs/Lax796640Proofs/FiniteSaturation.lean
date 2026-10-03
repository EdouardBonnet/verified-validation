import Lax796640Proofs.Common
import Mathlib.Logic.Function.Iterate

namespace Lax796640Proofs

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
