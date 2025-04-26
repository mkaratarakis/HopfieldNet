/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import Lean
import HopfieldNet.SampCert.Extractor.Translate
import HopfieldNet.SampCert.Extractor.IRToDafny

namespace Lean.ToDafny

syntax (name := export_dafny) "export_dafny" : attr

open Meta

def saveMethod (m : Method) : CoreM Unit :=
  modifyEnv fun env => extension.addEntry env (.toExport s!"{m.print}")

def toDafnyMethod(declName: Name) : MetaM Unit := do
  saveMethod (← CodeGen (← toDafnySLangDefIn declName))

initialize
  registerBuiltinAttribute {
    ref   := by exact decl_name%
    name  := `export_dafny
    descr := "instruct Lean to convert the given definition to a Dafny method"
    applicationTime := AttributeApplicationTime.afterTypeChecking
    add   := fun declName _ _attrKind =>
      let go : MetaM Unit :=
        do
          toDafnyMethod declName
      discard <| go.run {} {}
    erase := fun _ => do
      throwError "this attribute cannot be removed"
  }

end Lean.ToDafny
