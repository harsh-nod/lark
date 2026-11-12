import Lean
import LarkReal.Ops

/-! Numerical evidence for elaborated reference expressions. This module does
not produce certificates or establish floating-point equivalence. Only named
reference definitions and explicitly supported mathematical constructs unfold.
-/
namespace LarkSpecAudit
open Lean Meta Elab
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

-- An expression marker interpreted by the numerical evaluator, never by a proof.
noncomputable def input (_buffer _offset : Nat) : ℝ := 0

abbrev Inputs := Array (Array Float)

structure Statistics where
  nodes : Nat := 0
  sumTerms : Nat := 0
  definitions : Array String := #[]
  checkedPrimitives : Array Expr := #[]
  deriving Inhabited

abbrev AuditM := ReaderT Inputs (StateT Statistics MetaM)

def tick : AuditM Unit := modify fun s => { s with nodes := s.nodes+1 }

def natural (e : Expr) : AuditM Nat := do
  if (e.find? fun node => node.isConstOf ``input).isSome then
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

def referenceDefinition (name : Name) : Bool :=
  [`LarkReal, `LarkNativeRope, `LarkSilu, `LarkNonlinear.Ops].any (·.isPrefixOf name)

def expand (e : Expr) : AuditM Expr := do
  let e := e.consumeMData.headBeta
  if let .letE _ _ value body _ := e then return body.instantiate1 value
  if let .proj struct index value := e.getAppFn then
    if !([``LarkNonlinear.Ops, `LarkReal.OnlineSoftmax.Entry].contains struct) then
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
  let .const name _ := e.getAppFn | throwError "reference-audit unsupported expression: {e}"
  if !referenceDefinition name then throwError "reference-audit unsupported declaration: {name}"
  let some unfolded ← withTransparency .all (unfoldDefinition? e true)
    | throwError "reference-audit cannot unfold declaration: {name}"
  if unfolded == e then throwError "reference-audit unchanged declaration: {name}"
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
      return mkNatLit index
    if name == some ``List.range' then
      if index >= (← natural a[1]!) then throwError "reference-audit list index out of bounds"
      return mkNatLit ((← natural a[0]!) + index * (← natural a[2]!))
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

  partial def scalar (expression : Expr) : AuditM Float := do
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
    if name == some ``id then return ← scalar a.back!
    if name == some ``input then
      let b ← natural a[0]!
      let i ← natural a[1]!
      let buffers ← read
      if b >= buffers.size || i >= buffers[b]!.size then
        throwError "reference-audit input index out of bounds: buffer={b}, offset={i}"
      return (buffers[b]!)[i]!
    if name == some ``OfNat.ofNat then
      let n ← natural a[1]!
      return ← finite (Float.ofNat n)
    if name == some ``Nat.cast then
      let n ← natural a.back!
      return ← finite (Float.ofNat n)
    if name == some ``Int.cast then
      let normalized ← withTransparency .all (reduce a.back!)
      let some n ← getIntValue? normalized
        | throwError "reference-audit unsupported integer literal: {a.back!}"
      return ← finite (match n with
        | .ofNat v => Float.ofNat v
        | .negSucc v => -(Float.ofNat (v+1)))
    if name == some ``HAdd.hAdd then
      return ← finite ((← scalar a[a.size-2]!) + (← scalar a.back!))
    if name == some ``HSub.hSub then
      return ← finite ((← scalar a[a.size-2]!) - (← scalar a.back!))
    if name == some ``HMul.hMul then
      return ← finite ((← scalar a[a.size-2]!) * (← scalar a.back!))
    if name == some ``HDiv.hDiv then
      let numerator ← scalar a[a.size-2]!
      let denominator ← scalar a.back!
      if denominator == 0 then throwError "reference-audit zero denominator"
      return ← finite (numerator / denominator)
    if name == some ``Neg.neg then return ← finite (-(← scalar a.back!))
    if name == some ``Inv.inv then
      let denominator ← scalar a.back!
      if denominator == 0 then throwError "reference-audit zero denominator"
      return ← finite (1 / denominator)
    if name == some ``HPow.hPow then
      let base ← scalar a[a.size-2]!
      let exponent ← natural a.back!
      let mut value : Float := 1
      for _ in [:exponent] do value ← finite (value * base)
      return value
    if name == some ``ite then
      if (a[2]!.find? fun node => node.isConstOf ``input).isSome then
        throwError "reference-audit unsupported data-dependent condition"
      let decision ← withTransparency .all (whnf a[2]!)
      if decision.isAppOf ``Decidable.isTrue then return ← scalar a[a.size-2]!
      if decision.isAppOf ``Decidable.isFalse then return ← scalar a.back!
      throwError "reference-audit unsupported condition: {a[1]!}"
    if name == some ``max then return max (← scalar a[a.size-2]!) (← scalar a.back!)
    if name == some ``Real.exp then return ← finite (← scalar a.back!).exp
    if name == some ``Real.tanh then return ← finite (← scalar a.back!).tanh
    if name == some ``Real.sqrt then
      let x ← scalar a.back!
      if x < 0 then throwError "reference-audit negative square-root input"
      return ← finite x.sqrt
    if name == some ``List.sum then
      let values := a.back!
      let count ← listLength values
      modify fun s => {s with sumTerms := s.sumTerms+count}
      -- Mathlib's List.sum is a right fold; preserve that fold in float64.
      let mut total : Float := 0
      for j in [:count] do
        total ← finite ((← scalar (← listAt values (count-1-j))) + total)
      return total
    scalar (← expand e)
end

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

elab "audit_spec " term:term " from " file:str " at " index:num : command => do
  let inputs ← readInputs file.getString
  Lean.Elab.Command.liftTermElabM do
    let expectedType ← mkAppM ``List #[mkConst ``Real]
    let unresolved ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing
    let expression ← instantiateMVars unresolved
    if expression.hasMVar then throwError "reference-audit unresolved elaboration metavariables"
    let actualType ← inferType expression
    unless ← isDefEq actualType expectedType do
      throwError "reference-audit expected List Real, got {actualType}"
    let outputIndex := index.getNat
    let (value, stats) ← (do
      let count ← listLength expression
      if outputIndex >= count then throwError "reference-audit output index out of bounds"
      scalar (← listAt expression outputIndex)).run inputs |>.run {}
    let record := Json.mkObj [
      ("index",toJson outputIndex), ("float64_bits",toJson (toString value.toBits.toNat)),
      ("nodes",toJson stats.nodes), ("sum_terms",toJson stats.sumTerms),
      ("unfolded_reference_definitions",toJson stats.definitions),
      ("elaborated_type",toJson (← ppExpr actualType).pretty),
      ("elaborated_expression",toJson (← ppExpr expression).pretty)]
    logInfo m!"LARK_SPEC_AUDIT {record.compress}"

end LarkSpecAudit
