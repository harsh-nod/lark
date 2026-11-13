import Lean
import Std

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

open Lean Elab Command

namespace LarkProofSyntax

elab "lark_check_proof_terms" : command => do
  let raw ← liftIO <| IO.FS.readFile "ProofTerms.json"
  let input ← match Json.parse raw with
    | .ok value => pure value
    | .error message => throwError "Invalid proof-term JSON: {message}"
  let proofs ← match input.getArr? with
    | .ok values => pure values
    | .error message => throwError "Expected proof-term array: {message}"
  unless 0 < proofs.size && proofs.size ≤ 16 do
    throwError "Expected one to sixteen bounded proof terms"
  let env ← getEnv
  for value in proofs do
    let text ← match value.getStr? with
      | .ok text => pure text
      | .error message => throwError "Expected proof string: {message}"
    unless text.length ≤ 20000 do
      throwError "Proof term exceeds the fixed length bound"
    match Parser.runParserCategory env `term text "<proof-slot>" with
    | .error message => throwError "Proof must be exactly one term: {message}"
    | .ok stx =>
      unless stx.getKind == ``Lean.Parser.Term.byTactic do
        throwError "Proof must be one by tactic term"
  logInfo m!"LARK_PROOF_TERMS_OK {proofs.size}"

end LarkProofSyntax
