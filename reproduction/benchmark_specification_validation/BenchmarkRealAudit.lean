import Lean
import LarkReal.Ops

/-! Numerical evidence for elaborated reference expressions. This module does
not produce certificates or establish floating-point equivalence. Only named
reference definitions and explicitly supported mathematical constructs unfold.
-/
namespace LarkBenchmarkRealAudit
open Lean Meta Elab
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

-- An expression marker interpreted by the numerical evaluator, never by a proof.
noncomputable def input (_buffer _offset : Nat) : ℝ := 0
noncomputable def intermediate (_offset : Nat) : ℝ := 0

def numericMarker (e : Expr) : Bool := e.isConstOf ``input || e.isConstOf ``intermediate

abbrev Inputs := Array (Array Float)

inductive ArgumentKind where
  | other | natural | real | constructor
  deriving Inhabited

structure ArgumentPlan where
  function : Expr
  dependencies : Array Expr
  kinds : Array ArgumentKind

structure EquationRule where
  theoremName : Name
  parameters : Nat
  left : Expr
  right : Expr
  deriving Inhabited

structure Statistics where
  equationRules : Std.HashMap Expr (Array EquationRule) := {}
  nodes : Nat := 0
  sumTerms : Nat := 0
  definitions : Array String := #[]
  checkedPrimitives : Array Expr := #[]
  intermediates : Array Float := #[]
  valuesByBits : Std.HashMap UInt64 Nat := {}
  valueCache : Std.HashMap Expr Nat := {}
  signatures : Array (Expr × FunInfo) := #[]
  argumentPlans : Array ArgumentPlan := #[]
  foldUnfolds : Nat := 0
  deriving Inhabited

abbrev AuditM := ReaderT Inputs (StateRefT Statistics MetaM)

def tick : AuditM Unit := modify fun s => { s with nodes := s.nodes+1 }

def traceStage (message : String) : IO Unit := do
  IO.FS.withFile "Progress.log" .append fun stream => do
    stream.putStrLn message
    stream.flush

-- Accept only raw Nat literals and Lean's canonical Nat numeral instance.
def naturalLiteral? (expression : Expr) : Option Nat := do
  let e := expression.consumeMData
  if let .lit (.natVal n) := e then return n
  if !e.isAppOfArity ``OfNat.ofNat 3 then return ← none
  let a := e.getAppArgs
  if !a[0]!.isConstOf ``Nat then return ← none
  let .lit (.natVal n) := a[1]! | none
  let numeralInstance := a[2]!
  if !numeralInstance.isAppOfArity ``instOfNatNat 1 || numeralInstance.getAppArgs[0]! != a[1]! then
    return ← none
  return n

def natural (e : Expr) : AuditM Nat := do
  if let some n := naturalLiteral? e then return n
  if (e.find? fun node => numericMarker node).isSome then
    throwError "reference-audit unsupported data-dependent natural expression: {e}"
  let normalized ← withTransparency .all (reduce e)
  let some n ← getNatValue? normalized
    | throwError "reference-audit unsupported natural expression: {e}"
  return n

def finite (x : Float) : AuditM Float := do
  if x.isNaN || x.isInf then throwError "reference-audit non-finite intermediate"
  return x

def checkPrimitive (e : Expr) (explicitArguments : Nat) : AuditM Unit := do
  let a := e.getAppArgs
  if a.size < explicitArguments then throwError "reference-audit primitive arity"
  let operationHead := mkAppN e.getAppFn (a.extract 0 (a.size-explicitArguments))
  if (← get).checkedPrimitives.contains operationHead then return
  let info ← getFunInfo e.getAppFn
  for i in [:min a.size info.paramInfo.size] do
    if info.paramInfo[i]!.binderInfo.isInstImplicit then
      let canonical ← synthInstance (← inferType a[i]!)
      unless ← isDefEq a[i]! canonical do
        throwError "reference-audit unsupported primitive instance: {e.getAppFn}"
  modify fun s => { s with checkedPrimitives := s.checkedPrimitives.push operationHead }

def remember (value : Float) : AuditM Expr := do
  let value ← finite value
  if let some offset := (← get).valuesByBits[value.toBits]? then
    return mkApp (mkConst ``intermediate) (mkRawNatLit offset)
  let offset := (← get).intermediates.size
  modify fun s => { s with intermediates := s.intermediates.push value, valuesByBits := s.valuesByBits.insert value.toBits offset }
  return mkApp (mkConst ``intermediate) (mkRawNatLit offset)

def argumentPlan (expression : Expr) : AuditM (Array ArgumentKind) := do
  let fn := expression.getAppFn
  let args := expression.getAppArgs
  if (← get).nodes < 40 then
    traceStage s!"LARK_SPEC_ARGUMENTS nodes={(← get).nodes} name={fn.constName?.map Name.toString |>.getD "projection"} arity={args.size}"
  let information ← match (← get).signatures.find? (fun pair => pair.1 == fn) with
    | some (_, info) => pure info
    | none => do
      let info ← getFunInfo fn
      modify fun s => { s with signatures := s.signatures.push (fn,info) }
      pure info
  let mut dependencies : Array Expr := #[]
  for i in [:min args.size information.paramInfo.size] do
    if information.paramInfo[i]!.hasFwdDeps then dependencies := dependencies.push args[i]!
  if let some plan := (← get).argumentPlans.find? (fun plan =>
      plan.function == fn && plan.dependencies == dependencies && plan.kinds.size == args.size) then
    return plan.kinds
  let mut kinds := #[]
  for argument in args do
    let type ← inferType argument
    if ← isDefEq type (mkConst ``Nat) then kinds := kinds.push .natural
    else if ← isDefEq type (mkConst ``Real) then kinds := kinds.push .real
    else if [`LarkPointwise.Scalar, `LarkFoldPhase.Term, `LarkNormalization.Kind,
        `LarkNonlinear.Binary, `LarkNonlinear.Unary, ``Bool].contains type.getAppFn.constName then
      kinds := kinds.push .constructor
    else kinds := kinds.push .other
  if fn.isConstOf `LarkFoldPhase.folded then
    traceStage s!"LARK_SPEC_PLAN function={fn} dependencies={dependencies.size} args={args.size} cacheplans={(← get).argumentPlans.size}"
  modify fun s => { s with argumentPlans := s.argumentPlans.push ⟨fn,dependencies,kinds⟩ }
  return kinds

def referenceDefinition (name : Name) : Bool :=
  [`LarkReal, `LarkNativeRope, `LarkSilu, `LarkNonlinear.Ops, `LarkPointwise, `LarkReduction, `LarkDot, `LarkCertificate, `LarkNormalization, `LarkFoldPhase, `LarkUnaryMap, `LarkDotMap, `LarkBias, `LarkMatrix, `LarkConvolution, `LarkRotary, `LarkPipeline, `LarkFeedForward, `LarkSwiGLU, `LarkSwiPointwise, `LarkPairMap, `LarkRowPhase, `LarkRowSoftmax, `LarkAttention].any (·.isPrefixOf name) ||
    [`LarkNonlinear.applyUnary, `LarkNonlinear.applyBinary].contains name

-- Match the first-order left sides of imported, kernel-checked equation
-- theorems. The only arithmetic matching rule is Nat.succ against a literal.
-- No unification may unfold the real-valued numerical marker definitions.
partial def matchEquationPattern (pattern value : Expr)
    (bindings : Array (Option Expr)) : Option (Array (Option Expr)) := do
  let pattern := pattern.consumeMData
  let value := value.consumeMData
  if let some n := naturalLiteral? pattern then
    if naturalLiteral? value == some n then return bindings
    return ← none
  match pattern with
  | .bvar index =>
    if index >= bindings.size || value.hasLooseBVars || value.hasMVar then none
    else match bindings[index]! with
      | none => some (bindings.set! index (some value))
      | some previous => if previous == value then some bindings else none
  | .app fn argument =>
    if fn.isConstOf ``Nat.succ then
      if let some n := naturalLiteral? value then
        if n == 0 then return ← none
        return ← matchEquationPattern argument (.lit (.natVal (n-1))) bindings
    let .app valueFn valueArgument := value | none
    let bindings ← matchEquationPattern fn valueFn bindings
    matchEquationPattern argument valueArgument bindings
  | .proj structName index object =>
    let .proj actualStructure actualIndex actualObject := value | none
    if structName != actualStructure || index != actualIndex then none
    else matchEquationPattern object actualObject bindings
  | .const _ _ | .sort _ | .lit _ =>
    if pattern == value then some bindings else none
  | _ =>
    -- Binder patterns require a binder-aware matcher; decline them explicitly.
    if !pattern.hasLooseBVars && pattern == value then some bindings else none

def loadEquationRules (fn : Expr) : MetaM (Array EquationRule) := do
  let .const name levels := fn | return #[]
  let some names ← getEqnsFor? name | return #[]
  let mut rules := #[]
  for theoremName in names do
    let information ← getConstInfo theoremName
    if information.levelParams.length != levels.length then
      throwError "reference-audit equation universe arity: {theoremName}"
    let mut body := information.type.instantiateLevelParams information.levelParams levels
    let mut parameters := 0
    while body.isForall do
      parameters := parameters+1
      body := body.bindingBody!
    if !body.isAppOfArity ``Eq 3 then
      throwError "reference-audit expected equation theorem: {theoremName}"
    let arguments := body.getAppArgs
    rules := rules.push ⟨theoremName,parameters,arguments[1]!,arguments[2]!⟩
  return rules

def cachedEquationStep (expression : Expr) : AuditM (Option Expr) := do
  let fn := expression.getAppFn
  let rules ← match (← get).equationRules[fn]? with
    | some rules => pure rules
    | none => do
      let rules ← loadEquationRules fn
      modify fun s => {s with equationRules := s.equationRules.insert fn rules}
      pure rules
  if rules.isEmpty then return none
  for rule in rules do
    if let some bindings := matchEquationPattern rule.left expression
        (Array.replicate rule.parameters none) then
      if bindings.all Option.isSome then
        let substitution := bindings.map (fun value => value.getD (mkConst ``False))
        let value := rule.right.instantiate substitution
        if value.hasLooseBVars || value.hasMVar || value == expression then
          throwError "reference-audit malformed instantiated equation: {rule.theoremName}"
        return some value
  -- Projection and wildcard equations may need constructor normalization.
  -- Decline matching; the guarded definition/matcher path handles those.
  return none


def expand (e : Expr) : AuditM Expr := do
  let e := e.consumeMData.headBeta
  if (← get).nodes < 40 then
    traceStage s!"LARK_SPEC_EXPAND nodes={(← get).nodes} name={e.getAppFn.constName?.map Name.toString |>.getD "projection"}"
  if let .letE _ _ value body _ := e then return body.instantiate1 value
  if let .proj struct index value := e.getAppFn then
    if !([``LarkNonlinear.Ops, `LarkReal.OnlineSoftmax.Entry, `LarkUnaryMap.Profile, `LarkFoldPhase.Phase, ``PProd, ``Prod].contains struct) then
      throwError "reference-audit unsupported scalar projection: {struct}"
    let value ← whnf value
    let fields := value.getAppArgs
    let .const constructor _ := value.getAppFn
      | throwError "reference-audit unsupported constructor for {struct}"
    let .ctorInfo info ← getConstInfo constructor
      | throwError "reference-audit expected constructor for {struct}"
    if index >= info.numFields || fields.size != info.numParams + info.numFields then
      throwError "reference-audit unsupported constructor arity for {struct}"
    return (mkAppN fields[info.numParams+index]! e.getAppArgs).headBeta
  if let some matcher ← matchMatcherApp? e true then
    for discriminator in matcher.discrs do
      if (discriminator.find? numericMarker).isSome then
        throwError "reference-audit unsupported data-dependent constructor match"
      let discriminatorType ← whnf (← inferType discriminator)
      if !([``Nat, ``Int, ``Bool, `LarkPointwise.Scalar,
          `LarkNonlinear.Binary, `LarkNonlinear.Unary, `LarkNormalization.Kind, `LarkFoldPhase.Term].contains discriminatorType.getAppFn.constName) then
        throwError "reference-audit unsupported constructor discriminator: {discriminatorType}"
    if let some reduced ← reduceRecMatcher? e then
      if reduced == e then throwError "reference-audit unchanged constructor match"
      return reduced
    throwError "reference-audit constructor match did not reduce"
  let .const name _ := e.getAppFn | throwError "reference-audit unsupported expression: {e}"
  if !referenceDefinition name then throwError "reference-audit unsupported declaration: {name}"
  if let some unfolded ← cachedEquationStep e then
    if [`LarkFoldPhase.folded, `LarkRowPhase.folded, `LarkDot.folded, `LarkDotMap.folded].contains name then
      modify fun s => { s with foldUnfolds := s.foldUnfolds+1 }
      if (← get).foldUnfolds % 1024 == 0 then
        traceStage s!"LARK_SPEC_EQUATION_PROGRESS folds={(← get).foldUnfolds} nodes={(← get).nodes}"
    modify fun s => { s with definitions := if s.definitions.contains name.toString
      then s.definitions else s.definitions.push name.toString }
    return unfolded
  let .defnInfo definition ← getConstInfo name
    | throwError "reference-audit unsupported declaration kind: {name}"
  let .const _ levels := e.getAppFn
    | throwError "reference-audit expected constant head"
  let body := definition.value.instantiateLevelParams definition.levelParams levels
  let unfolded := (mkAppN body e.getAppArgs).headBeta
  if unfolded == e then throwError "reference-audit unchanged declaration: {name}"
  if [`LarkFoldPhase.folded, `LarkRowPhase.folded, `LarkDot.folded, `LarkDotMap.folded].contains name then
    modify fun s => { s with foldUnfolds := s.foldUnfolds+1 }
    let statistics ← get
    if statistics.foldUnfolds % 256 == 0 then
      traceStage s!"LARK_SPEC_PROGRESS folds={statistics.foldUnfolds} nodes={statistics.nodes} values={statistics.intermediates.size} cached={statistics.valueCache.size} plans={statistics.argumentPlans.size}"
  modify fun s => { s with definitions := if s.definitions.contains name.toString
    then s.definitions else s.definitions.push name.toString }
  return unfolded

mutual
  partial def listLength (expression : Expr) : AuditM Nat := do
    tick
    let e := expression.consumeMData.headBeta
    let name := e.getAppFn.constName?
    let a := e.getAppArgs
    if name == some ``HAppend.hAppend || name == some ``Append.append then checkPrimitive e 2
    if name == some ``List.range then return ← natural a.back!
    if name == some ``List.range' then return ← natural a[1]!
    if name == some ``List.map then return ← listLength a.back!
    if name == some ``List.append || name == some ``HAppend.hAppend || name == some ``Append.append then
      return (← listLength a[a.size-2]!) + (← listLength a.back!)
    if name == some ``List.nil then return 0
    if name == some ``List.cons then return 1 + (← listLength a.back!)
    listLength (← expand e)

  partial def listAt (expression : Expr) (index : Nat) : AuditM Expr := do
    tick
    let e := expression.consumeMData.headBeta
    let name := e.getAppFn.constName?
    let a := e.getAppArgs
    if name == some ``HAppend.hAppend || name == some ``Append.append then checkPrimitive e 2
    if name == some ``List.range then
      if index >= (← natural a.back!) then throwError "reference-audit list index out of bounds"
      return mkRawNatLit index
    if name == some ``List.range' then
      if index >= (← natural a[1]!) then throwError "reference-audit list index out of bounds"
      return mkRawNatLit ((← natural a[0]!) + index * (← natural a[2]!))
    if name == some ``List.map then
      return (mkApp a[a.size-2]! (← listAt a.back! index)).headBeta
    if name == some ``List.append || name == some ``HAppend.hAppend || name == some ``Append.append then
      let n ← listLength a[a.size-2]!
      if index < n then return ← listAt a[a.size-2]! index
      return ← listAt a.back! (index-n)
    if name == some ``List.cons then
      if index == 0 then return a[a.size-2]!
      return ← listAt a.back! (index-1)
    listAt (← expand e) index

end

inductive UnaryPrimitive where
  | negate | inverse | exponential | hyperbolicTangent | squareRoot
  deriving Inhabited

inductive BinaryPrimitive where
  | add | subtract | multiply | divide | maximum
  deriving Inhabited

-- Continuations are explicit data. Evaluating a fold's scalar arguments must
-- not leave one Lean VM call frame per recurrence step.
inductive ScalarTask where
  | evaluate (expression : Expr)
  | unary (operation : UnaryPrimitive)
  | binary (operation : BinaryPrimitive)
  | power (exponent : Nat)
  | arguments (fn : Expr) (args : Array Expr) (kinds : Array ArgumentKind) (next : Nat)
  | storeArgument (fn : Expr) (args : Array Expr) (kinds : Array ArgumentKind)
      (index : Nat) (original : Expr)
  | sum (values : Expr) (remaining : Nat)
  | sumAdd
  | fold (fn values : Expr) (index count : Nat)
  deriving Inhabited

def takeScalarValue (values : Array Float) : AuditM (Float × Array Float) := do
  if values.isEmpty then throwError "reference-audit scalar machine missing value"
  return (values.back!,values.pop)

def unaryValue (operation : UnaryPrimitive) (value : Float) : AuditM Float := do
  match operation with
  | .negate => finite (-value)
  | .inverse =>
    if value == 0 then throwError "reference-audit zero denominator"
    finite (1/value)
  | .exponential => finite value.exp
  | .hyperbolicTangent => finite value.tanh
  | .squareRoot =>
    if value < 0 then throwError "reference-audit negative square-root input"
    finite value.sqrt

def binaryValue (operation : BinaryPrimitive) (left right : Float) : AuditM Float := do
  match operation with
  | .add => finite (left+right)
  | .subtract => finite (left-right)
  | .multiply => finite (left*right)
  | .divide =>
    if right == 0 then throwError "reference-audit zero denominator"
    finite (left/right)
  | .maximum => finite (max left right)

partial def scalarChunk (initialTasks : Array ScalarTask) (initialValues : Array Float) :
    AuditM (Array ScalarTask × Array Float) := do
  let mut tasks := initialTasks
  let mut values := initialValues
  for _ in [:64] do
    if tasks.isEmpty then break
    let task := tasks.back!
    tasks := tasks.pop
    match task with
    | .unary operation =>
      let (value,rest) ← takeScalarValue values
      values := rest.push (← unaryValue operation value)
    | .binary operation =>
      let (right,rest) ← takeScalarValue values
      let (left,rest) ← takeScalarValue rest
      values := rest.push (← binaryValue operation left right)
    | .power exponent =>
      let (base,rest) ← takeScalarValue values
      let mut value : Float := 1
      for _ in [:exponent] do value ← finite (value*base)
      values := rest.push value
    | .storeArgument fn args kinds index original =>
      let (value,rest) ← takeScalarValue values
      values := rest
      let normalized ← remember value
      let some offset ← getNatValue? normalized.getAppArgs.back!
        | throwError "reference-audit malformed intermediate marker"
      modify fun s => {s with valueCache := s.valueCache.insert original offset}
      tasks := tasks.push (.arguments fn (args.set! index normalized) kinds (index+1))
    | .arguments fn originalArgs kinds next =>
      let mut args := originalArgs
      let mut index := next
      let mut suspended := false
      while index < args.size && !suspended do
        match kinds[index]! with
        | .other => pure ()
        | .natural => args := args.set! index (mkRawNatLit (← natural args[index]!))
        | .constructor =>
          if (args[index]!.find? numericMarker).isSome then
            throwError "reference-audit unsupported data-dependent constructor argument"
          args := args.set! index (← withTransparency .all (whnf args[index]!))
        | .real =>
          let argument := args[index]!
          if !argument.isAppOf ``intermediate then
            if let some offset := (← get).valueCache[argument]? then
              args := args.set! index (mkApp (mkConst ``intermediate) (mkRawNatLit offset))
            else
              tasks := tasks.push (.storeArgument fn args kinds index argument)
              tasks := tasks.push (.evaluate argument)
              suspended := true
        index := index+1
      if !suspended then tasks := tasks.push (.evaluate (← expand (mkAppN fn args)))
    | .sum list remaining =>
      if remaining > 0 then
        tasks := tasks.push (.sum list (remaining-1))
        tasks := tasks.push .sumAdd
        tasks := tasks.push (.evaluate (← listAt list (remaining-1)))
    | .sumAdd =>
      let (item,rest) ← takeScalarValue values
      let (total,rest) ← takeScalarValue rest
      values := rest.push (← finite (item+total))
    | .fold fn list index count =>
      if index < count then
        let (accumulator,rest) ← takeScalarValue values
        values := rest
        let accumulatorExpression ← remember accumulator
        let item ← listAt list index
        tasks := tasks.push (.fold fn list (index+1) count)
        tasks := tasks.push (.evaluate ((mkAppN fn #[accumulatorExpression,item]).headBeta))
    | .evaluate expression =>
      tick
      let e := expression.consumeMData.headBeta
      let name := e.getAppFn.constName?
      let a := e.getAppArgs
      if name == some ``OfNat.ofNat then checkPrimitive e 0
      if name == some ``Nat.cast || name == some ``Int.cast || name == some ``Neg.neg ||
          name == some ``Inv.inv || name == some ``List.sum then checkPrimitive e 1
      if name == some ``HAdd.hAdd || name == some ``HSub.hSub || name == some ``HMul.hMul ||
          name == some ``HDiv.hDiv || name == some ``HPow.hPow || name == some ``max then
        checkPrimitive e 2
      if name == some ``id then
        tasks := tasks.push (.evaluate a.back!)
      else if name == some ``intermediate then
        let index ← natural a.back!
        let intermediates := (← get).intermediates
        if index >= intermediates.size then throwError "reference-audit intermediate index out of bounds"
        values := values.push intermediates[index]!
      else if name == some ``input then
        let buffer ← natural a[0]!
        let index ← natural a[1]!
        let inputs ← read
        if buffer >= inputs.size || index >= inputs[buffer]!.size then
          throwError "reference-audit input index out of bounds: buffer={buffer}, offset={index}"
        values := values.push ((inputs[buffer]!)[index]!)
      else if name == some ``OfNat.ofNat then
        values := values.push (← finite (Float.ofNat (← natural a[1]!)))
      else if name == some ``Nat.cast then
        values := values.push (← finite (Float.ofNat (← natural a.back!)))
      else if name == some ``Int.cast then
        let normalized ← withTransparency .all (reduce a.back!)
        let value ← if normalized.isAppOf ``Int.ofNat then
            finite (Float.ofNat (← natural normalized.getAppArgs.back!))
          else if normalized.isAppOf ``Int.negSucc then
            finite (-(Float.ofNat ((← natural normalized.getAppArgs.back!)+1)))
          else do
            let some n ← getIntValue? normalized
              | throwError "reference-audit unsupported integer literal: {a.back!}"
            finite (match n with
              | .ofNat v => Float.ofNat v
              | .negSucc v => -(Float.ofNat (v+1)))
        values := values.push value
      else if name == some ``HAdd.hAdd || name == some ``HSub.hSub || name == some ``HMul.hMul ||
          name == some ``HDiv.hDiv || name == some ``max then
        let operation := if name == some ``HAdd.hAdd then BinaryPrimitive.add
          else if name == some ``HSub.hSub then .subtract
          else if name == some ``HMul.hMul then .multiply
          else if name == some ``HDiv.hDiv then .divide else .maximum
        tasks := tasks.push (.binary operation)
        tasks := tasks.push (.evaluate a.back!)
        tasks := tasks.push (.evaluate a[a.size-2]!)
      else if name == some ``Neg.neg || name == some ``Inv.inv || name == some ``Real.exp ||
          name == some ``Real.tanh || name == some ``Real.sqrt then
        let operation := if name == some ``Neg.neg then UnaryPrimitive.negate
          else if name == some ``Inv.inv then .inverse
          else if name == some ``Real.exp then .exponential
          else if name == some ``Real.tanh then .hyperbolicTangent else .squareRoot
        tasks := tasks.push (.unary operation)
        tasks := tasks.push (.evaluate a.back!)
      else if name == some ``HPow.hPow then
        tasks := tasks.push (.power (← natural a.back!))
        tasks := tasks.push (.evaluate a[a.size-2]!)
      else if name == some ``ite then
        if (a[2]!.find? numericMarker).isSome then
          throwError "reference-audit unsupported data-dependent condition"
        let decision ← withTransparency .all (whnf a[2]!)
        if decision.isAppOf ``Decidable.isTrue then
          tasks := tasks.push (.evaluate a[a.size-2]!)
        else if decision.isAppOf ``Decidable.isFalse then
          tasks := tasks.push (.evaluate a.back!)
        else throwError "reference-audit unsupported condition: {a[1]!}"
      else if name == some ``List.sum then
        let list := a.back!
        let count ← listLength list
        modify fun s => {s with sumTerms := s.sumTerms+count}
        values := values.push 0
        tasks := tasks.push (.sum list count)
      else if name == some ``List.foldl then
        let list := a.back!
        let count ← listLength list
        modify fun s => {s with sumTerms := s.sumTerms+count}
        tasks := tasks.push (.fold a[a.size-3]! list 0 count)
        tasks := tasks.push (.evaluate a[a.size-2]!)
      else if name.any referenceDefinition then
        tasks := tasks.push (.arguments e.getAppFn a (← argumentPlan e) 0)
      else
        tasks := tasks.push (.evaluate (← expand e))
  return (tasks,values)

structure MachineState where
  tasks : Array ScalarTask
  values : Array Float
  statistics : Statistics
  coreState : Core.State
  metaState : Meta.State

def scalar (expression : Expr) : AuditM Float := do
  let inputs ← read
  let coreContext ← readThe Core.Context
  let metaContext ← readThe Meta.Context
  let initial : MachineState := {
    tasks := #[.evaluate expression], values := #[], statistics := ← get,
    coreState := ← getThe Core.State, metaState := ← getThe Meta.State }
  -- IO.iterate is the compiled outer trampoline. Each interpreted chunk
  -- returns before the next begins. Carry the original Core.Context through
  -- CoreM.run: CoreM.toIO would reset initHeartbeats at every chunk.
  let iteration : IO (Except Lean.Exception MachineState) :=
    IO.iterate initial fun state => do
      let computation : MetaM ((Array ScalarTask × Array Float) × Statistics) := do
        let observed ← readThe Core.Context
        unless observed.initHeartbeats == coreContext.initHeartbeats &&
            observed.maxHeartbeats == coreContext.maxHeartbeats &&
            observed.maxRecDepth == coreContext.maxRecDepth do
          throwError "reference-audit changed resource context"
        Core.checkMaxHeartbeats "reference-audit"
        ((scalarChunk state.tasks state.values).run inputs).run state.statistics
      let outcome ← ((computation.run metaContext state.metaState).run
        coreContext state.coreState).toIO'
      match outcome with
      | .error exception => return .inr (.error exception)
      | .ok ((((tasks,values),statistics),metaState),coreState) =>
        let next : MachineState := {tasks,values,statistics,coreState,metaState}
        if tasks.isEmpty then return .inr (.ok next)
        return .inl next
  let outcome ← iteration
  let state ← match outcome with
    | .ok state => pure state
    | .error exception => throw exception
  set state.coreState
  set state.metaState
  set state.statistics
  if state.values.size != 1 then
    throwError "reference-audit scalar machine surplus values"
  return state.values.back!



def readInputs (path : String) : IO Inputs := do
  let raw ← IO.FS.readFile path
  let data ← match Lean.Json.parse raw with
    | .ok x => pure x
    | .error message => throw (IO.userError message)
  let schema ← match data.getObjValAs? Nat "schema" with
    | .ok x => pure x
    | .error message => throw (IO.userError message)
  if schema != 1 then throw (IO.userError "reference-audit unknown input schema")
  let buffers ← match data.getObjValAs? (Array (Array String)) "buffers" with
    | .ok x => pure x
    | .error message => throw (IO.userError message)
  return ← buffers.mapM fun buffer => do
   return ← buffer.mapM fun bits => do
    let some n := bits.toNat? | throw (IO.userError "reference-audit malformed float64 bits")
    if n >= 2^64 then throw (IO.userError "reference-audit float64 bits out of range")
    let value := Float.ofBits (UInt64.ofNat n)
    if value.isNaN || value.isInf then throw (IO.userError "reference-audit non-finite input")
    return value

elab "benchmark_audit_real " term:term " from " file:str " at " index:num : command => do
  traceStage "LARK_SPEC_STAGE reading-inputs"
  let inputs ← readInputs file.getString
  traceStage "LARK_SPEC_STAGE inputs-loaded"
  Lean.Elab.Command.liftTermElabM do
    let expectedType ← mkAppM ``List #[mkConst ``Real]
    let unresolved ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing
    let expression ← instantiateMVars unresolved
    if expression.hasMVar then throwError "reference-audit unresolved elaboration metavariables"
    let actualType ← inferType expression
    unless ← isDefEq actualType expectedType do
      throwError "reference-audit expected List Real, got {actualType}"
    traceStage "LARK_SPEC_STAGE expression-elaborated"
    let outputIndex := index.getNat
    let evaluation : AuditM Float := do
      traceStage "LARK_SPEC_STAGE measuring-list"
      let count ← listLength expression
      traceStage s!"LARK_SPEC_STAGE list-length={count}"
      if outputIndex >= count then throwError "reference-audit output index out of bounds"
      scalar (← listAt expression outputIndex)
    let (value, stats) ← evaluation.run inputs |>.run {}
    let record := Json.mkObj [
      ("index",toJson outputIndex), ("float64_bits",toJson (toString value.toBits.toNat)),
      ("nodes",toJson stats.nodes), ("sum_terms",toJson stats.sumTerms), ("fold_unfolds",toJson stats.foldUnfolds),
      ("unfolded_reference_definitions",toJson stats.definitions),
      ("elaborated_type",toJson (← ppExpr actualType).pretty),
      ("elaborated_expression",toJson (← ppExpr expression).pretty)]
    logInfo m!"LARK_SPEC_AUDIT {record.compress}"

elab "benchmark_audit_real_many " term:term " from " file:str " at " "[" indices:num,* "]" : command => do
  let inputs ← readInputs file.getString
  let outputIndices := indices.getElems.map (fun item => item.getNat)
  if outputIndices.isEmpty then throwError "reference-audit empty output selection"
  let mut seen : Array Nat := #[]
  for index in outputIndices do
    if seen.contains index then throwError "reference-audit duplicate output index"
    seen := seen.push index
  Command.liftTermElabM do
    let expectedType ← mkAppM ``List #[mkConst ``Real]
    let unresolved ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing
    let expression ← instantiateMVars unresolved
    if expression.hasMVar then throwError "reference-audit unresolved elaboration metavariables"
    let actualType ← inferType expression
    unless ← isDefEq actualType expectedType do
      throwError "reference-audit expected List Real, got {actualType}"
    let typeText := (← ppExpr actualType).pretty
    let expressionText := (← ppExpr expression).pretty
    let evaluation : AuditM (Array Json) := do
      let count ← listLength expression
      let mut records : Array Json := #[]
      for index in outputIndices do
        if index >= count then throwError "reference-audit output index out of bounds"
        let value ← scalar (← listAt expression index)
        let stats ← get
        records := records.push (Json.mkObj [
          ("index",toJson index), ("float64_bits",toJson (toString value.toBits.toNat)),
          ("nodes",toJson stats.nodes), ("sum_terms",toJson stats.sumTerms),
          ("fold_unfolds",toJson stats.foldUnfolds),
          ("unfolded_reference_definitions",toJson stats.definitions),
          ("elaborated_type",toJson typeText),
          ("elaborated_expression",toJson expressionText)])
      return records
    let (records,_) ← evaluation.run inputs |>.run {}
    for record in records do logInfo m!"LARK_SPEC_AUDIT {record.compress}"


end LarkBenchmarkRealAudit
