# A verified Lean core for Lax validation

Lax records proofs that may depend on statements not yet proved. To determine
which statements are established, it must follow these dependencies without
treating circular reasoning as a proof. We implement a validation core in Lean
and prove its main guarantees.

The core finds every axiom used by a declaration, checks the mathematical
validation rules, and computes exactly the statements that follow from the
available proofs and declared assumptions. We also verify a certificate checker:
an accepted certificate accounts for every derivable statement, and every
well-formed network has such a certificate with at most one step per statement.
A controller requires matching reports of successful replay and inspection for
the same identified artifact, and any failed stage prevents approval.

The main theorem shows that every unconditional proved label returned by the
combined entry point is sound under an explicit contract for Lean's kernel and
faithful inspection. All 26 theorem statements have kernel-replayed proofs,
with their dependencies recorded in the proof network. These guarantees concern
the executable Lean functions defined here. Using them in the live Lax service
still requires integration with source acquisition, input extraction, authentic
runner reports, execution, and publication.
