/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Sebastian Ullrich
-/
import Lean.CoreM
import Lean.Replay

/-!
Batch adaptation of Lean 4.33.0's LeanChecker.replayFromImports.
The module-data loading logic and Environment.replay kernel checker are retained.
All custom declarations are collected before checking, and the initial environment
contains Mathlib only, so no custom theorem is trusted as an imported assumption.
Each source module's exported, server and private data parts are included.
This utility is not imported by the mathematical proof.
-/

open Lean

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  if args.isEmpty then
    throw <| IO.userError "Supply exact custom module names."
  let imports : Array Import := #[{ module := `Mathlib }]
  let (_, state) ← importModulesCore imports |>.run
  let env ← finalizeImport state imports {} 0 false false (isModule := true)
  let mut newConstants := {}
  let mut count : Nat := 0
  for arg in args do
    let modName := arg.toName
    let mFile ← findOLean modName
    unless (← mFile.pathExists) do
      throw <| IO.userError s!"Missing object file for {modName}"
    let mut fnames := #[mFile]
    let sFile := OLeanLevel.server.adjustFileName mFile
    if (← sFile.pathExists) then
      fnames := fnames.push sFile
      let pFile := OLeanLevel.private.adjustFileName mFile
      if (← pFile.pathExists) then
        fnames := fnames.push pFile
    let parts ← readModuleDataParts fnames
    if h : parts.size = 0 then
      throw <| IO.userError s!"No module data for {modName}"
    else
      for name in parts[parts.size - 1].1.constNames,
          ci in parts[parts.size - 1].1.constants do
        if ci.isUnsafe || ci.isPartial then
          throw <| IO.userError s!"Refusing unchecked unsafe/partial declaration: {name}"
        match ci with
        | .axiomInfo _ => throw <| IO.userError s!"Refusing custom axiom: {name}"
        | _ => pure ()
        if newConstants.contains name || (env.find? name).isSome then
          throw <| IO.userError s!"Declaration overlap: {name}"
        newConstants := newConstants.insert name ci
        count := count + 1
    IO.println s!"Collected {modName}"
    (← IO.getStdout).flush
  IO.println s!"Replaying {count} declarations from {args.length} modules against Mathlib only."
  (← IO.getStdout).flush
  let checked ← env.replay newConstants
  checked.freeRegions
  IO.println s!"Successfully replayed {count} declarations from {args.length} modules."
  return 0
