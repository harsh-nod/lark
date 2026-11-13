import BenchmarkRealAudit
import LarkReal.BenchmarkReferenceImports

/-! Numerical evidence only: instantiate the actual polymorphic reference with
checked Float64 scalar operations. No certificates or error theorems are made. -/
namespace LarkBenchmarkFloatAudit
open Lean Meta Elab
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

abbrev Checked := Except String Float
abbrev Inputs := LarkBenchmarkRealAudit.Inputs

def finite (value : Float) : Checked :=
  if value.isNaN || value.isInf then .error "reference-audit non-finite intermediate"
  else .ok value

def binary (operation : Float → Float → Checked) (a b : Checked) : Checked := do
  operation (← a) (← b)

def unary (operation : Float → Checked) (a : Checked) : Checked := do
  operation (← a)

def divide (a b : Float) : Checked :=
  if b == 0 then .error "reference-audit zero denominator" else finite (a/b)

def inverseSqrt (value : Float) : Checked := do
  if value < 0 then throw "reference-audit negative square-root input"
  divide 1 (← finite value.sqrt)

def integerFloat (value : Int) : Float :=
  match value with
  | .ofNat n => Float.ofNat n
  | .negSucc n => -(Float.ofNat (n+1))

def ops : LarkNonlinear.Ops Checked where
  literal := fun numerator denominator => divide (integerFloat numerator) (Float.ofNat denominator)
  add := binary (fun a b => finite (a+b))
  sub := binary (fun a b => finite (a-b))
  mul := binary (fun a b => finite (a*b))
  max := binary (fun a b => finite (max a b))
  div := binary divide
  exp := unary (fun x => finite x.exp)
  tanh := unary (fun x => finite x.tanh)
  rsqrt := unary inverseSqrt
  fromHalf := id
  toHalf := id

def checkedInput (inputs : Inputs) (buffer offset : Nat) : Checked := do
  if buffer >= inputs.size || offset >= inputs[buffer]!.size then
    throw "reference-audit input index out of bounds"
  finite ((inputs[buffer]!)[offset]!)

def ownedName (name : Name) : Bool :=
  [`LarkPointwise, `LarkReduction, `LarkDot, `LarkDotMap, `LarkBias,
   `LarkMatrix, `LarkConvolution, `LarkRotary, `LarkNonlinear,
   `LarkNormalization, `LarkUnaryMap, `LarkFoldPhase, `LarkRowPhase,
   `LarkRowSoftmax, `LarkAttention, `LarkPipeline, `LarkFeedForward,
   `LarkSwiGLU, `LarkSwiPointwise, `LarkPairMap].any (·.isPrefixOf name)

-- Pure checked collection; List.foldl is a compiled Core loop. Every score
-- is evaluated by the imported source scoreValue function, at the full shape.
def materialize (count : Nat) (function : Nat → Checked) : Except String (Array Float) :=
  (List.range count).foldl (fun state index => do
    let values ← state
    let value ← function index
    return values.push value) (.ok #[])

def scoreAt (values : Array Float) (index : Nat) : Checked :=
  if index >= values.size then .error "reference-audit materialized score index out of bounds"
  else finite values[index]!


def validateClosure (expression : Expr) : MetaM (Array String) := do
  let environment ← getEnv
  let mut pending := expression.getUsedConstants
  let mut seen : Std.HashSet Name := {}
  let mut names : Array String := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    names := names.push name.toString
    if [``Checked, ``Inputs, ``LarkBenchmarkRealAudit.Inputs, ``ops, ``checkedInput, ``materialize, ``scoreAt].contains name then
      continue
    let information ← getConstInfo name
    if information.isUnsafe then throwError "reference-audit unsafe declaration: {name}"
    match information with
    | .thmInfo _ => continue -- Kernel-checked proof fields are erased by evaluation.
    | .axiomInfo _ => throwError "reference-audit unsupported computational axiom: {name}"
    | _ => pure ()
    if (`Classical).isPrefixOf name || ((`Float).isPrefixOf name && name != ``Float) then
      throwError "reference-audit unsupported declaration: {name}"
    let owner := (environment.getModuleIdxFor? name).map fun index =>
      environment.header.moduleNames[index.toNat]!
    if owner.any (fun module => (`Init).isPrefixOf module || (`Std).isPrefixOf module) then
      continue
    let ownImported := owner.any (fun module => (`Lark).isPrefixOf module) &&
      ownedName ((privateToUserName? name).getD name)
    let ownMain := owner.isNone && (`LarkCertificate).isPrefixOf name
    if !ownImported && !ownMain then
      throwError "reference-audit unsupported declaration owner: {name}"
    match information with
    | .defnInfo definition => pending := pending ++ definition.value.getUsedConstants
    | .ctorInfo _ | .inductInfo _ | .recInfo _ => pure ()
    | _ => throwError "reference-audit unsupported declaration kind: {name}"
  return names

def deltaSource (expression : Expr) (name : Name) : MetaM Expr := do
  let .defnInfo information ← getConstInfo name
    | throwError "reference-audit expected source definition: {name}"
  if information.safety != .safe then throwError "reference-audit unsafe source definition: {name}"
  return expression.replace fun node => do
    let .const actual levels := node.getAppFn | none
    if actual != name then none else
      some ((mkAppN (information.value.instantiateLevelParams information.levelParams levels)
        node.getAppArgs).headBeta)

def replaceScores (original shape inputFunction scoreVariable : Expr) : MetaM Expr := do
  let first ← deltaSource original ``LarkAttention.valueInput
  let second ← deltaSource first ``LarkAttention.probability
  let expanded ← deltaSource second ``LarkAttention.softInput
  if !expanded.getUsedConstants.contains ``LarkAttention.scoreValue then
    throwError "reference-audit unsupported attention materialization source"
  let expectedPrefix := mkAppN (mkConst ``LarkAttention.scoreValue)
    #[mkConst ``Checked,shape,mkConst ``ops,inputFunction]
  let rewritten := expanded.replace fun node => do
    if !node.getAppFn.isConstOf ``LarkAttention.scoreValue then return ← none
    let arguments := node.getAppArgs
    if arguments.size != 5 then return ← none
    let callPrefix := mkAppN node.getAppFn (arguments.extract 0 4)
    if callPrefix != expectedPrefix then return ← none
    return mkApp2 (mkConst ``scoreAt) scoreVariable arguments[4]!
  if rewritten.getUsedConstants.contains ``LarkAttention.scoreValue then
    throwError "reference-audit unsupported score call for materialization"
  return rewritten

def prepareScores (declarations : Array String) (inputVariable : Expr) (inputs : Inputs) :
    TermElabM (Option (Expr × Array Float)) := do
  if !declarations.contains "LarkAttention.spec" then return none
  let shape := mkConst `LarkCertificate.shape
  unless ← isDefEq (← inferType shape) (mkConst ``LarkAttention.Shape) do
    throwError "reference-audit unsupported attention shape"
  let (count,_) ← (LarkBenchmarkRealAudit.natural
    (mkApp (mkConst ``LarkAttention.scores) shape)).run #[] |>.run {}
  let sourceFunction := mkAppN (mkConst ``LarkAttention.scoreValue)
    #[mkConst ``Checked,shape,mkConst ``ops,mkApp (mkConst ``checkedInput) inputVariable]
  let expression := mkApp2 (mkConst ``materialize) (mkRawNatLit count) sourceFunction
  let function ← mkLambdaFVars #[inputVariable] expression
  let _ ← validateClosure function
  let expectedType ← Term.elabType (← `(Inputs → Except String (Array Float)))
  Core.checkMaxHeartbeats "reference-audit"
  let evaluator ← unsafe evalExpr (Inputs → Except String (Array Float))
    expectedType function (safety := .safe)
  LarkBenchmarkRealAudit.traceStage s!"MATERIALIZE_BEGIN count={count}"
  let values ← match evaluator inputs with
    | .ok values => pure values
    | .error reason => throwError reason
  Core.checkMaxHeartbeats "reference-audit"
  LarkBenchmarkRealAudit.traceStage s!"MATERIALIZE_VALUES_COMPLETE count={values.size}"
  if values.size != count then throwError "reference-audit materialized score shape mismatch"
  LarkBenchmarkRealAudit.traceStage "MATERIALIZE_SERIALIZATION_BEGIN"
  let evidence := Json.mkObj [
    ("schema",toJson (1 : Nat)),
    ("method",toJson "actual-source-scoreValue-materialization"),
    ("count",toJson count),
    ("compiled_source_function",toJson (← ppExpr function).pretty),
    ("float64_bits",toJson (values.map fun value => toString value.toBits.toNat))]
  IO.FS.writeFile "MaterializedScores.json" (evidence.compress++"\n")
  LarkBenchmarkRealAudit.traceStage "MATERIALIZE_FILE_COMPLETE"
  return some (shape,values)


elab "benchmark_audit_float " term:term " from " file:str " at " "[" indices:num,* "]" : command => do
  let inputs ← LarkBenchmarkRealAudit.readInputs file.getString
  let outputIndices := indices.getElems.map (fun index => index.getNat)
  if outputIndices.isEmpty then throwError "reference-audit empty output selection"
  let mut seen : Array Nat := #[]
  for index in outputIndices do
    if seen.contains index then throwError "reference-audit duplicate output index"
    seen := seen.push index
  Command.liftTermElabM do
    let unresolved ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing
    let reference ← instantiateMVars unresolved
    if reference.hasMVar then throwError "reference-audit unresolved elaboration metavariables"
    let expected ← Term.elabType (← `(∀ {α : Type}, LarkNonlinear.Ops α → (Nat → Nat → α) → List α))
    unless ← isDefEq (← inferType reference) expected do
      throwError "reference-audit expected polymorphic Ops reference"
    if reference.getAppNumArgs != 0 || !reference.isConstOf `LarkCertificate.spec then
      throwError "reference-audit unsupported reference entrypoint"
    let referenceDeclarations ← validateClosure reference
    let realExpression := mkAppN reference
      #[mkConst ``Real, mkConst ``LarkReal.ops, mkConst ``LarkBenchmarkRealAudit.input]
    let realType ← inferType realExpression
    let expectedRealType ← Term.elabType (← `(List ℝ))
    unless ← isDefEq realType expectedRealType do
      throwError "reference-audit expected List Real"
    let functionType ← Term.elabType (← `(Inputs → Checked))
    withLocalDeclD `buffers (mkConst ``Inputs) fun inputVariable => do
      let floatExpression := mkAppN reference
        #[mkConst ``Checked, mkConst ``ops, mkApp (mkConst ``checkedInput) inputVariable]
      let (count,_) ← (LarkBenchmarkRealAudit.listLength floatExpression).run #[] |>.run {}
      let materialized ← prepareScores referenceDeclarations inputVariable inputs
      for index in outputIndices do
        if index >= count then throwError "reference-audit output index out of bounds"
        let (selected,_) ← (LarkBenchmarkRealAudit.listAt floatExpression index).run #[] |>.run {}
        let (value,function,declarations,strategy) ← match materialized with
          | none => do
            let function ← mkLambdaFVars #[inputVariable] selected
            if function.hasMVar || function.hasLooseBVars || function.hasFVar then
              throwError "reference-audit unresolved compiled scalar"
            let declarations ← validateClosure function
            Core.checkMaxHeartbeats "reference-audit"
            let evaluator ← unsafe evalExpr (Inputs → Checked) functionType function (safety := .safe)
            let value ← match evaluator inputs with
              | .ok value => pure value
              | .error reason => throwError reason
            Core.checkMaxHeartbeats "reference-audit"
            pure (value,function,declarations,"direct-source-evaluation")
          | some (shape,scores) => do
            let scoreType ← Term.elabType (← `(Array Float))
            withLocalDeclD `scores scoreType fun scoreVariable => do
              let inputFunction := mkApp (mkConst ``checkedInput) inputVariable
              let rewritten ← replaceScores selected shape inputFunction scoreVariable
              let function ← instantiateMVars (← mkLambdaFVars #[inputVariable,scoreVariable] rewritten)
              if function.hasMVar || function.hasLooseBVars || function.hasFVar then
                throwError "reference-audit unresolved compiled scalar"
              let declarations ← validateClosure function
              let expected ← Term.elabType (← `(Inputs → Array Float → Checked))
              Core.checkMaxHeartbeats "reference-audit"
              let evaluator ← unsafe evalExpr (Inputs → Array Float → Checked) expected function
                (safety := .safe)
              let value ← match evaluator inputs scores with
                | .ok value => pure value
                | .error reason => throwError reason
              Core.checkMaxHeartbeats "reference-audit"
              pure (value,function,declarations,"source-scoreValue-materialization")
        let (realSelected,_) ← (LarkBenchmarkRealAudit.listAt realExpression index).run #[] |>.run {}
        let record := Json.mkObj [
          ("method",toJson "actual-polymorphic-reference-checked-float64"),
          ("evaluation_strategy",toJson strategy),
          ("index",toJson index), ("output_count",toJson count),
          ("float64_bits",toJson (toString value.toBits.toNat)),
          ("elaborated_real_type",toJson (← ppExpr realType).pretty),
          ("elaborated_real_expression",toJson (← ppExpr realExpression).pretty),
          ("elaborated_real_scalar",toJson (← ppExpr realSelected).pretty),
          ("source_float64_scalar",toJson (← ppExpr (← mkLambdaFVars #[inputVariable] selected)).pretty),
          ("compiled_float64_scalar",toJson (← ppExpr function).pretty),
          ("validated_reference_declarations",toJson referenceDeclarations),
          ("validated_declarations",toJson declarations)]
        logInfo m!"LARK_SPEC_AUDIT {record.compress}"

end LarkBenchmarkFloatAudit
