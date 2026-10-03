import Lax796640.Certificates
import Lax796640Proofs.ProofNetworks

namespace Lax796640Proofs.Certificates

open Lax796640.Declarations Lax796640.ProofNetworks Lax796640.Certificates

@[simp] theorem checkClosed_iff (n : Network) (known : List Nat) :
    checkClosed n known = true ↔ Closed n known := by
  simp [checkClosed, Closed, includes_iff, or_iff_not_imp_left]

theorem check_eq_some (n : Network) (initial : List Nat) (steps : List Step)
    (known : List Nat) :
    check n initial steps = some known ↔
      checkSteps n initial steps = some known ∧ Closed n known := by
  unfold check
  cases found : checkSteps n initial steps with
  | none => simp
  | some result =>
      by_cases closed : checkClosed n result = true
      · simp_all
        rintro rfl
        exact closed
      · simp_all
        rintro rfl
        exact closed

@[simp] theorem step_enabled_iff (n : Network) (known : List Nat) (step : Step) :
    (!known.contains step.statement && n.rules.any (fun r =>
      r.proofId == step.proofId && r.conclusion == step.statement &&
      includes known r.assumptions)) = true ↔
    step.statement ∉ known ∧ ∃ r ∈ n.rules, r.proofId = step.proofId ∧
      r.conclusion = step.statement ∧ ∀ a ∈ r.assumptions, a ∈ known := by
  simp [includes_iff, and_assoc]

theorem checkSteps_invariant (n : Network) (initial : List Nat) (steps : List Step)
    (current : List Nat) (sound : ∀ a ∈ current, Derivable n initial a)
    (known : List Nat) (accepted : checkSteps n current steps = some known) :
    (∀ a ∈ current, a ∈ known) ∧ (∀ a ∈ known, Derivable n initial a) := by
  induction steps generalizing current with
  | nil =>
      have eq : current.eraseDups = known := by simpa [checkSteps] using accepted
      subst known
      simpa using sound
  | cons step rest ih =>
      simp only [checkSteps] at accepted
      split at accepted
      next enabled =>
        obtain ⟨_, r, hr, _, conclusion, premises⟩ := (step_enabled_iff _ _ _).1 enabled
        have newSound : Derivable n initial step.statement := by
          rw [← conclusion]
          exact .apply hr (fun a ha => sound a (premises a ha))
        have soundNext : ∀ a ∈ current ++ [step.statement], Derivable n initial a := by
          intro a ha
          simp only [List.mem_append, List.mem_singleton] at ha
          rcases ha with ha | rfl
          · exact sound a ha
          · exact newSound
        obtain ⟨retained, resultSound⟩ := ih (current ++ [step.statement]) soundNext accepted
        exact ⟨fun a ha => retained a (List.mem_append_left _ ha), resultSound⟩
      next => simp at accepted

/--
---
conclusion: Lax796640.Certificates.check_exact
assumptions:
---
Ordered witnesses justify every added statement. The final closure check then
contains every finite derivation, so no derivable statement is omitted.
-/
theorem check_exact (n : Network) (_h : WellFormed n) (initial : List Nat)
    (_admitted : ∀ a ∈ initial, a ∈ n.statements) (steps : List Step)
    (known : List Nat) (accepted : check n initial steps = some known) (a : Nat) :
    a ∈ known ↔ Derivable n initial a := by
  obtain ⟨checked, closed⟩ := (check_eq_some _ _ _ _).1 accepted
  obtain ⟨retained, sound⟩ := checkSteps_invariant n initial steps initial
    (fun _ ha => .assumption ha) known checked
  constructor
  · exact sound a
  · intro derived
    induction derived with
    | assumption ha => exact retained _ ha
    | apply hr _ ih => exact closed _ hr ih

theorem certificate_with_budget (n : Network) (h : WellFormed n) (budget : Nat)
    (initial : List Nat) (admitted : ∀ a ∈ initial, a ∈ n.statements)
    (enough : n.statements.toFinset.card ≤ initial.toFinset.card + budget) :
    ∃ steps known, steps.length ≤ budget ∧ check n initial steps = some known := by
  classical
  induction budget generalizing initial with
  | zero =>
      have equal : initial.toFinset = n.statements.toFinset := by
        apply Finset.eq_of_subset_of_card_le
        · intro a ha
          simpa using admitted a (by simpa using ha)
        · simpa using enough
      have closed : Closed n initial.eraseDups := by
        intro r hr _
        have : r.conclusion ∈ initial.toFinset := by
          rw [equal]
          simpa using (h.2.2 r hr).1
        simpa using this
      exact ⟨[], initial.eraseDups, by simp,
        (check_eq_some _ _ _ _).2 ⟨rfl, closed⟩⟩
  | succ budget ih =>
      by_cases closed : Closed n initial
      · exact ⟨[], initial.eraseDups, by simp,
          (check_eq_some _ _ _ _).2 ⟨rfl, by simpa [Closed] using closed⟩⟩
      · obtain ⟨r, hr, premises, missing⟩ :
          ∃ r ∈ n.rules, (∀ a ∈ r.assumptions, a ∈ initial) ∧ r.conclusion ∉ initial := by
          unfold Closed at closed
          push Not at closed
          exact closed
        let step : Step := ⟨r.conclusion, r.proofId⟩
        have nextAdmitted : ∀ a ∈ initial ++ [r.conclusion], a ∈ n.statements := by
          intro a ha
          simp only [List.mem_append, List.mem_singleton] at ha
          rcases ha with ha | rfl
          · exact admitted a ha
          · exact (h.2.2 r hr).1
        have size : (initial ++ [r.conclusion]).toFinset.card = initial.toFinset.card + 1 := by
          simp [List.toFinset_append, Finset.union_singleton, missing]
        obtain ⟨rest, known, length, checked⟩ := ih (initial ++ [r.conclusion])
          nextAdmitted (by omega)
        refine ⟨step :: rest, known, by simpa using Nat.succ_le_succ length, ?_⟩
        obtain ⟨checkedSteps, resultClosed⟩ := (check_eq_some _ _ _ _).1 checked
        apply (check_eq_some _ _ _ _).2
        refine ⟨?_, resultClosed⟩
        have enabled : (!initial.contains step.statement && n.rules.any (fun rule =>
            rule.proofId == step.proofId && rule.conclusion == step.statement &&
            includes initial rule.assumptions)) = true :=
          (step_enabled_iff _ _ _).2 ⟨missing, r, hr, rfl, rfl, premises⟩
        simpa only [checkSteps, enabled, ↓reduceIte] using checkedSteps

/--
---
conclusion: Lax796640.Certificates.certificate_exists
assumptions:
---
Keep adding an enabled conclusion that is still missing. Each step consumes a
distinct statement, so the process reaches closure within the stated bound.
-/
theorem certificate_exists (n : Network) (h : WellFormed n) (initial : List Nat)
    (admitted : ∀ a ∈ initial, a ∈ n.statements) :
    ∃ steps known, steps.length ≤ n.statements.length ∧
      check n initial steps = some known := by
  apply certificate_with_budget n h n.statements.length initial admitted
  have bound := List.toFinset_card_le n.statements
  omega

/--
---
conclusion: Lax796640.Certificates.unproved_certificate
assumptions:
---
Exactness turns an omitted statement into a certificate of non-derivability
from the available rules, without asserting that the statement is false.
-/
theorem unproved_certificate (n : Network) (h : WellFormed n) (initial : List Nat)
    (admitted : ∀ a ∈ initial, a ∈ n.statements) (steps : List Step)
    (known : List Nat) (accepted : check n initial steps = some known)
    (a : Nat) (excluded : a ∉ known) : ¬ Derivable n initial a :=
  fun derived => excluded ((check_exact n h initial admitted steps known accepted a).2 derived)

end Lax796640Proofs.Certificates
