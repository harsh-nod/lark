# Proof-provider protocol

The provider is a locally selected command, invoked without a shell. The CLI
splits `--provider` into arguments using shell-style quoting, then passes a
single JSON object on stdin. The command must write one JSON object to stdout;
diagnostics belong on stderr. Network access and credentials are the provider's
responsibility, and no model endpoint is contacted by the verifier itself.

The first attempt uses the deterministic default proposal or `--proposal FILE`.
After a failed check, the provider receives:

```json
{
  "stage": "segmentation-and-equivalence",
  "task": {},
  "program": [],
  "spec": [],
  "proposal": {},
  "lean_source": "the complete pinned model and fixed theorem source",
  "lean_errors": "diagnostics from the previous attempt",
  "instruction": "Return JSON with segments and the three proof slots; statements are immutable."
}
```

It returns:

```json
{
  "segments": [
    {"seq": [{"op": 0}, {"op": 1}, {"op": 2}]}
  ],
  "proofs": {
    "segmentation_data": "by simp [flatten, flattenSegment, segments, program]",
    "race_free": "by exact ⟨_, rfl, rfl⟩",
    "segment_equivalence": "by\n  intro input outside\n  rw [segmentation_data]\n  exact ⟨_, rfl, rfl, rfl⟩"
  }
}
```

This illustrative proposal assumes a three-instruction program; the actual
default equivalence proof also normalizes the access trace for shared-memory
kernels. The request includes the current working proposal so providers can
patch it rather than reconstruct it.

Segment forms are `{"op": instruction_index}`, `{"seq": [segments...]}`, and
`{"repeat": {"count": n, "body": [instruction_indices...]}}`. Repetition is
syntactic expansion of absolute flat instructions, not relocation of branch
targets. Flattening must reproduce the entire original program exactly.

The three proof slots are tactic proofs beginning with `by`. The generator
fixes the surrounding declarations. Forbidden features include admissions,
new declarations, metaprogram execution, unchecked native evaluation, and
modifying checker options. Every attempt also requires an axiom audit of the
end-to-end theorem, regardless of the textual filter.

`--attempts` bounds the total checks, including the first. `--timeout` bounds
each Lean check and each provider invocation independently. Failures produce
an `unproved` report with no acceptance claim. The logs preserve each Lean
attempt. No failure analyst's label can override a failed theorem.

`tools/http_prover.py` is an optional adapter for a chat-completions-compatible
endpoint. Configure the complete URL, model identifier, and optional bearer
credential via `LARK_PROVER_URL`, `LARK_PROVER_MODEL`, and `LARK_PROVER_API_KEY`.
For example, the command can target a model server you already operate. The
adapter sends the full Lean model and diagnostics; choose an endpoint suitable
for your source code. It is not invoked unless explicitly passed as a provider.
