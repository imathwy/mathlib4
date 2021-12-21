/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/
import Lean
import Mathlib.Tactic.Cache
import Mathlib.Tactic.Rcases

open Tactic

namespace Mathlib.Tactic.Ext
open Lean Meta

def withExtHyps (struct : Name) (k : Array Expr → (x y : Expr) → Array (Name × Expr) → MetaM α) : MetaM α := do
  unless isStructure (← getEnv) struct do throwError "not a structure: {struct}"
  let structC ← mkConstWithLevelParams struct
  forallTelescope (← inferType structC) fun params _ => do
  withNewBinderInfos (params.map (·.fvarId!, BinderInfo.implicit)) do
  withLocalDeclD `x (mkAppN structC params) fun x => do
  withLocalDeclD `y (mkAppN structC params) fun y => do
    let mut hyps := #[]
    for field in getStructureFieldsFlattened (← getEnv) struct (includeSubobjectFields := false) do
      let x_f ← mkProjection x field
      let y_f ← mkProjection y field
      if ← isProof x_f then
        ()
      else if ← isDefEq (← inferType x_f) (← inferType y_f) then
        hyps := hyps.push (field, ← mkEq x_f y_f)
      else
        hyps := hyps.push (field, ← mkHEq x_f y_f)
    k params x y hyps

scoped elab "ext_type%" struct:ident : term => do
  withExtHyps (← resolveGlobalConstNoOverload struct) fun params x y hyps => do
    let mut ty ← mkEq x y
    for (f, h) in hyps.reverse do
      ty := mkForall f BinderInfo.default h ty
    mkForallFVars (params |>.push x |>.push y) ty

def mkIff (p q : Expr) : Expr := mkApp2 (mkConst ``Iff) p q

def mkAndN : List Expr → Expr
  | [] => mkConst ``True
  | [p] => p
  | [p, q] => mkAnd p q
  | p :: ps => mkAnd p (mkAndN ps)

scoped elab "ext_iff_type%" struct:ident : term => do
  withExtHyps (← resolveGlobalConstNoOverload struct) fun params x y hyps => do
    mkForallFVars (params |>.push x |>.push y) <|
      mkIff (← mkEq x y) <| mkAndN (hyps.map (·.2)).toList

elab "subst_eqs" : tactic =>
  open Elab.Tactic in
  liftMetaTactic1 fun mvarId => substEqs mvarId

scoped macro "ext_proof%" : term =>
  `(fun {..} {..} => by intros; subst_eqs; rfl)

syntax "split_ands" : tactic
macro_rules | `(tactic| split_ands) => `(tactic| skip)
macro_rules | `(tactic| split_ands) => `(tactic| refine And.intro ?_ ?_ <;> split_ands)

macro_rules | `(tactic| rfl) => `(tactic| exact HEq.rfl)

scoped macro "ext_iff_proof%" : term => `(fun {..} {..} =>
  ⟨fun _ => by subst_eqs; split_ands <;> rfl,
   fun _ => by (repeat cases ‹_ ∧ _›); subst_eqs; rfl⟩)

scoped macro "declareExtTheoremsFor" struct:ident : command => do
  let extName ← mkIdent <| struct.getId.eraseMacroScopes.mkStr "ext"
  let extIffName ← mkIdent <| struct.getId.eraseMacroScopes.mkStr "ext_iff"
  `(@[ext] protected theorem $extName:ident : ext_type% $struct:ident := ext_proof%
    protected theorem $extIffName:ident : ext_iff_type% $struct:ident := ext_iff_proof%)

-- Attributes on structures are not supported yet,
-- so simulate it via macro expansion.
open Parser Term in
macro_rules
  | `($[$doc:docComment]? @[$attrs,*]
    structure $n:ident $binders* $[extends $parents,*]? $[: $ty]? :=
      $[$mk:ident ::]? $fields) => do
    for attr in attrs.getElems do
      if let `(attrInstance| ext) := attr then
        let attrs := attrs.getElems.filter (· != attr)
        return ← `($[$doc:docComment]? @[$attrs,*]
          structure $n:ident $binders* $[extends $parents,*]? $[: $ty]? := $[$mk:ident ::]? $fields
          declareExtTheoremsFor $n)
    Macro.throwUnsupported

initialize extAttribute : ParametricAttribute (Array DiscrTree.Key) ←
  registerParametricAttribute {
    name := `ext
    descr := "Marks a lemma as extensionality lemma"
    getParam := fun decl attr => MetaM.run' do
      let declTy := (← getConstInfo decl).type
      let (xs, bis, declTy) ← withReducible <| forallMetaTelescopeReducing declTy
      unless declTy.isAppOfArity ``Eq 3 && (declTy.getArg! 1).isMVar && (declTy.getArg! 2).isMVar do
        throwError "@[ext] attribute only applies to lemmas proving x = y, got {declTy}"
      let ty := declTy.getArg! 0
      if (← withReducible <| whnf ty).isForall then
        #[DiscrTree.Key.star] -- FIXME: workaround
      else
        withReducible <| DiscrTree.mkPath (declTy.getArg! 0)
  }

-- TODO: iterate over extension instead of all declarations
initialize extLemmasCache : DeclCache (DiscrTree Name) ←
  DeclCache.mk "ext: initialize cache" {} fun decl ci lemmas => do
    if let some keys := extAttribute.getParam (← getEnv) decl then
      lemmas.insertCore keys decl
    else
      lemmas

open Lean.Elab.Tactic in
elab "apply_ext_lemma" : tactic => do
  let tgt ← getMainTarget
  unless tgt.isAppOfArity ``Eq 3 do
    throwError "applyExtLemma only applies to equations"
  let s ← saveState
  for lem in ← (← extLemmasCache.get).getMatch (tgt.getArg! 0) do
    try
      liftMetaTactic (apply · (← mkConstWithFreshMVarLevels lem))
      return
    catch e =>
      s.restore
  throwError "no applicable extensionality lemma found"

scoped syntax "ext_or_skip" (colGt term:max)* : tactic
macro_rules | `(tactic| ext_or_skip) => `(tactic| skip)
macro_rules | `(tactic| ext_or_skip $xs*) => `(tactic| apply_ext_lemma; ext_or_skip $xs*)
macro_rules | `(tactic| ext_or_skip $x $xs*) => `(tactic| intro $x; ext_or_skip $xs*)

-- TODO: We need to use the following, to support existing uses of `ext` in mathlib3.
-- syntax (name := ext) "ext" (ppSpace rcasesPat)* (" : " num)? : tactic

syntax "ext" (colGt term:max)* : tactic
macro_rules | `(tactic| ext $xs*) => `(tactic| apply_ext_lemma; ext_or_skip $xs*)
