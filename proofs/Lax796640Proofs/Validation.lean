import Lax796640.Validation
import Lax796640Proofs.Dependencies
import Lax796640Proofs.ProofNetworks

namespace Lax796640Proofs.Validation

open Lax796640.Declarations Lax796640.Dependencies Lax796640.ProofNetworks
open Lax796640.Validation

instance : LawfulBEq PackageRole where
  eq_of_beq := by intro a b; cases a <;> cases b <;> decide
  rfl := by intro a; cases a <;> rfl

instance : LawfulBEq DeclarationKind where
  eq_of_beq := by intro a b; cases a <;> cases b <;> decide
  rfl := by intro a; cases a <;> rfl

theorem eraseDups_length_le {α : Type} [BEq α] [LawfulBEq α] (xs : List α) :
    xs.eraseDups.length ≤ xs.length := by
  induction xs using List.reverseRecOn with
  | nil => simp
  | append_singleton xs a ih =>
      rw [List.eraseDups_append]
      by_cases member : a ∈ xs <;>
        simp [List.removeAll, List.eraseDups_cons, member] <;> omega

@[simp] theorem eraseDups_length_eq_iff {α : Type} [BEq α] [LawfulBEq α] (xs : List α) :
    xs.eraseDups.length = xs.length ↔ xs.Nodup := by
  induction xs using List.reverseRecOn with
  | nil => simp
  | append_singleton xs a ih =>
      have nodup : (xs ++ [a]).Nodup ↔ a ∉ xs ∧ xs.Nodup := by
        simpa only [List.concat_eq_append] using List.nodup_concat xs a
      rw [nodup]
      rw [List.eraseDups_append]
      by_cases member : a ∈ xs
      · have bound := eraseDups_length_le xs
        simp [List.removeAll, member]
        omega
      · simpa [List.removeAll, List.eraseDups_cons, member] using ih

theorem package_exact (s : Snapshot) (unique : (s.packages.map Package.id).Nodup)
    (id : Nat) (p : Package) :
    package s id = some p ↔ p ∈ s.packages ∧ p.id = id :=
  Dependencies.find_id_exact _ _ unique id p

theorem declaration_any (s : Snapshot) (unique : (s.declarations.map Declaration.id).Nodup)
    (id : Nat) (test : Declaration → Bool) :
    (declaration s id).any test = true ↔
      ∃ d ∈ s.declarations, d.id = id ∧ test d = true := by
  simp only [Option.any_eq_true, Dependencies.declaration_exact s unique]
  aesop

theorem package_role_check (s : Snapshot) (unique : (s.packages.map Package.id).Nodup)
    (id : Nat) (existsPackage : ∃ p ∈ s.packages, p.id = id) :
    (package s id).any (fun q => q.role != .proofs) = true ↔
      ∀ q ∈ s.packages, q.id = id → q.role ≠ .proofs := by
  obtain ⟨p, hp, eq⟩ := existsPackage
  rw [(package_exact s unique id p).2 ⟨hp, eq⟩]
  simp only [Option.any_some, bne_iff_ne]
  constructor
  · intro good q hq qid
    have same : q = p := List.inj_on_of_nodup_map unique hq hp (qid.trans eq.symm)
    simpa [same] using good
  · intro good
    exact good p hp eq

theorem required_concepts_exact (s : Snapshot) (unique : (s.packages.map Package.id).Nodup)
    (p : Package) (existsRequired : ∀ id ∈ p.requires, ∃ q ∈ s.packages, q.id = id) :
    (p.role != .concepts || p.requires.all (fun id =>
      (package s id).any (fun q => q.role != .proofs))) = true ↔
    (p.role = .concepts → ∀ id ∈ p.requires,
      ∀ q ∈ s.packages, q.id = id → q.role ≠ .proofs) := by
  simp only [Bool.or_eq_true, bne_iff_ne, List.all_eq_true]
  have allEq : (∀ id ∈ p.requires, (package s id).any (fun q => q.role != .proofs) = true) ↔
      (∀ id ∈ p.requires, ∀ q ∈ s.packages, q.id = id → q.role ≠ .proofs) := by
    apply forall_congr'
    intro id
    apply forall_congr'
    intro present
    exact package_role_check s unique id (existsRequired id present)
  rw [allEq]
  tauto

theorem package_checks (s : Snapshot) (unique : (s.packages.map Package.id).Nodup)
    (p : Package) :
    (p.environment == s.environment &&
      (p.role == .background || s.localPackages.contains p.id || p.registered) &&
      includes (s.packages.map Package.id) p.requires &&
      (p.role != .concepts || p.requires.all (fun id =>
        (package s id).any (fun q => q.role != .proofs)))) = true ↔
    p.environment = s.environment ∧
    (p.role = .background ∨ p.id ∈ s.localPackages ∨ p.registered = true) ∧
    (∀ id ∈ p.requires, ∃ q ∈ s.packages, q.id = id) ∧
    (p.role = .concepts → ∀ id ∈ p.requires,
      ∀ q ∈ s.packages, q.id = id → q.role ≠ .proofs) := by
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, List.contains_iff_mem,
    includes_iff, List.mem_map, and_assoc, or_assoc]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro existsRequired
  simpa only [Bool.or_eq_true] using required_concepts_exact s unique p existsRequired

theorem checkTables_exact (s : Snapshot) : checkTables s = true ↔ TablesValid s := by
  by_cases unique : (s.packages.map Package.id).Nodup
  · simp only [checkTables, Bool.and_eq_true]
    simp only [beq_iff_eq, eraseDups_length_eq_iff, includes_iff, List.all_eq_true,
      package_checks s unique, List.contains_iff_mem, List.mem_map, Bool.and_eq_true]
    unfold TablesValid ReferencesWellFormed
    constructor
    · rintro ⟨⟨⟨⟨⟨⟨⟨ids, names⟩, packages⟩, locals⟩, localRefs⟩, declarations⟩, packagesValid⟩, comparisons⟩
      exact ⟨⟨ids, fun d hd => (declarations d hd).2⟩, names, packages, locals,
        localRefs, (fun d hd => (declarations d hd).1), packagesValid, comparisons⟩
    · rintro ⟨⟨ids, refs⟩, names, packages, locals, localRefs, declarations, packagesValid, comparisons⟩
      exact ⟨⟨⟨⟨⟨⟨⟨ids, names⟩, packages⟩, locals⟩, localRefs⟩,
        fun d hd => ⟨declarations d hd, refs d hd⟩⟩, packagesValid⟩, comparisons⟩
  · simp only [checkTables, Bool.and_eq_true, beq_iff_eq, eraseDups_length_eq_iff,
      unique, and_false, false_and, TablesValid]

theorem checkDeclaration_exact (s : Snapshot) (tables : TablesValid s)
    (d : Declaration) (present : d ∈ s.declarations) :
    checkDeclaration s d = true ↔ DeclarationValid s d := by
  rcases tables with ⟨refs, _, unique, _, _, packageExists, _, _⟩
  obtain ⟨p, hp, pid⟩ := packageExists d present
  have found := (package_exact s unique d.package p).2 ⟨hp, pid⟩
  have depends := Dependencies.axiomsUsed_exact s refs d.id ⟨d, present, rfl⟩
  unfold checkDeclaration DeclarationValid
  rw [found]
  simp only [← and_assoc, ← package_exact s unique, found, Option.some.injEq]
  cases role : p.role <;>
    simp [role, Bool.and_eq_true, List.all_eq_true, depends, or_iff_not_imp_left]

theorem assumptionsOf_exact (s : Snapshot) (refs : ReferencesWellFormed s)
    (id : Nat) (existsDeclaration : ∃ d ∈ s.declarations, d.id = id) (a : Nat) :
    a ∈ assumptionsOf s id ↔ UsesAxiom s id a ∧ backgroundAxiom s a = false := by
  simp [assumptionsOf, Dependencies.axiomsUsed_exact s refs id existsDeclaration]

theorem checkClaim_exact (s : Snapshot) (tables : TablesValid s) (c : Claim) :
    checkClaim s c = true ↔ ClaimValid s c := by
  rw [checkClaim, declaration_any s tables.1.1]
  unfold ClaimValid
  apply exists_congr
  intro d
  apply and_congr_right
  intro present
  apply and_congr_right
  intro did
  have depends := assumptionsOf_exact s tables.1 c.theoremId ⟨d, present, did⟩
  cases c.claimedAssumptions <;>
    simp [Bool.and_eq_true, and_assoc, sameMembers_iff, depends]

/--
---
conclusion: Lax796640.Validation.validate_exact
assumptions:
---
Unique table identifiers make lookups exact. The dependency collector is exact
as well, so each Boolean check is equivalent to its declarative requirement.
-/
theorem validate_exact (s : Snapshot) : validate s = true ↔ Valid s := by
  have claimIds : ((s.claims.map Claim.theoremId).eraseDups.length == s.claims.length) = true ↔
      (s.claims.map Claim.theoremId).Nodup := by
    simpa only [beq_iff_eq, List.length_map] using
      eraseDups_length_eq_iff (s.claims.map Claim.theoremId)
  by_cases tables : TablesValid s
  · simp +contextual only [validate, Valid, Bool.and_eq_true, checkTables_exact, tables,
      List.all_eq_true, checkDeclaration_exact s tables, checkClaim_exact s tables,
      claimIds, true_and, and_assoc]
  · simp [validate, Valid, Bool.and_eq_true, checkTables_exact, tables]

/--
---
conclusion: Lax796640.Validation.recorded_assumptions_exact
assumptions:
---
The stored assumptions come from the actual dependency traversal, with exactly
the permitted background axioms removed.
-/
theorem recorded_assumptions_exact (s : Snapshot) (accepted : validate s = true)
    (c : Claim) (present : c ∈ s.claims) (a : Nat) :
    a ∈ assumptionsOf s c.theoremId ↔
      UsesAxiom s c.theoremId a ∧ backgroundAxiom s a = false := by
  have valid := (validate_exact s).1 accepted
  obtain ⟨d, hd, did, _⟩ := valid.2.2.2 c present
  exact assumptionsOf_exact s valid.1.1 c.theoremId ⟨d, hd, did⟩ a

theorem statement_in_network (s : Snapshot) (a : Nat) (statement : isStatement s a = true) :
    a ∈ (network s).statements := by
  have details := statement
  simp only [isStatement, Option.any_eq_true] at details
  obtain ⟨d, found, _⟩ := details
  have present := List.mem_of_find?_eq_some found
  have id : d.id = a := by simpa using List.find?_some found
  exact List.mem_filter.mpr ⟨List.mem_map.mpr ⟨d, present, id⟩, statement⟩

theorem allowed_isStatement (s : Snapshot) (proofPackage a : Nat)
    (allowed : allowedStatement s proofPackage a = true) : isStatement s a = true := by
  simp only [allowedStatement, Bool.and_eq_true] at allowed
  exact allowed.1

theorem claim_assumptions_allowed (s : Snapshot) (valid : Valid s)
    (c : Claim) (present : c ∈ s.claims) (a : Nat)
    (used : UsesAxiom s c.theoremId a) (notBackground : backgroundAxiom s a = false) :
    ∃ proofPackage, allowedStatement s proofPackage a = true := by
  obtain ⟨d, hd, did, _, proofRole, _⟩ := valid.2.2.2 c present
  obtain ⟨p, hp, pid, policy⟩ := valid.2.1 d hd
  have found := (package_exact s valid.1.2.2.1 d.package p).2 ⟨hp, pid⟩
  have role : p.role = .proofs := by simpa [found] using proofRole
  rw [role] at policy
  have allowed := policy a (did.symm ▸ used)
  simp only [notBackground, Bool.false_eq_true, false_or] at allowed
  exact ⟨d.package, allowed⟩

/--
---
conclusion: Lax796640.Validation.accepted_network_wellFormed
assumptions:
---
Validation supplies unique statement and proof identifiers. Every conclusion
and recomputed assumption is an admitted concept statement in the table.
-/
theorem accepted_network_wellFormed (s : Snapshot) (accepted : validate s = true) :
    WellFormed (network s) := by
  have valid := (validate_exact s).1 accepted
  refine ⟨valid.1.1.1.filter _, ?_, ?_⟩
  · simpa [network, List.map_map, Function.comp_def] using valid.2.2.1
  · intro r hr
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
    obtain ⟨d, _, _, _, _, conclusion, _⟩ := valid.2.2.2 c hc
    constructor
    · exact statement_in_network s c.statementId (allowed_isStatement s _ _ conclusion)
    · intro a ha
      obtain ⟨used, notBackground⟩ := (recorded_assumptions_exact s accepted c hc a).1 ha
      obtain ⟨proofPackage, allowed⟩ := claim_assumptions_allowed s valid c hc a used notBackground
      exact statement_in_network s a (allowed_isStatement s _ _ allowed)

end Lax796640Proofs.Validation
