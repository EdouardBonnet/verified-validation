import Lax796640.Declarations
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! Shared facts about lists, Boolean tests, and unique table lookups.
This module contains no annotated submission proofs. Dependencies between the
main results are expressed through their concept statements instead. -/

namespace Lax796640Proofs

open Lax796640.Declarations

instance : LawfulBEq PackageRole where
  eq_of_beq := by intro a b; cases a <;> cases b <;> decide
  rfl := by intro a; cases a <;> rfl

instance : LawfulBEq DeclarationKind where
  eq_of_beq := by intro a b; cases a <;> cases b <;> decide
  rfl := by intro a; cases a <;> rfl

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

theorem find_id_exact {α : Type} (xs : List α) (id : α → Nat)
    (unique : (xs.map id).Nodup) (key : Nat) (x : α) :
    xs.find? (fun d => id d == key) = some x ↔ x ∈ xs ∧ id x = key := by
  constructor
  · intro found
    exact ⟨List.mem_of_find?_eq_some found, by simpa using List.find?_some found⟩
  · rintro ⟨hx, keyEq⟩
    cases found : xs.find? (fun d => id d == key) with
    | none =>
        have missing := List.find?_eq_none.mp found x hx
        simp [keyEq] at missing
    | some y =>
        have hy := List.mem_of_find?_eq_some found
        have ykey : id y = key := by simpa using List.find?_some found
        have same : y = x := List.inj_on_of_nodup_map unique hy hx (ykey.trans keyEq.symm)
        simp [same]

theorem declaration_exact (s : Snapshot) (unique : (s.declarations.map Declaration.id).Nodup)
    (id : Nat) (d : Declaration) :
    declaration s id = some d ↔ d ∈ s.declarations ∧ d.id = id :=
  find_id_exact _ _ unique id d

end Lax796640Proofs
