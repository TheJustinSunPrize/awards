/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Sebastian Ullrich
-/
import Lean.CoreM
import Lean.Replay

/-!
The replayFromImports routine below is copied unchanged from Lean 4.33.0
LeanChecker.lean, commit d8b18978322de05a8f3dba51ef03cf5461676c17.
The new CLI driver runs exactly the named modules, sequentially, avoiding the
official CLI's prefix expansion and concurrent replay of large dependencies.
This is a verification utility and is not imported by any theorem module.
-/

open Lean

unsafe def replayFromImports (module : Name) : IO Unit := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  -- Load all module data parts (exported, server, private)
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  if h : parts.size = 0 then throw <| IO.userError "failed to read module data" else
  let (mod, _) := parts[0]
  let (_, s) ← importModulesCore mod.imports |>.run
  let env ← finalizeImport s mod.imports {} 0 false false (isModule := true)
  let mut newConstants := {}
  -- Collect constants from last ("most private") part, which subsumes all prior ones
  for name in parts[parts.size-1].1.constNames, ci in parts[parts.size-1].1.constants do
    newConstants := newConstants.insert name ci
  let env' ← env.replay newConstants
  env'.freeRegions

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  if args.isEmpty then
    throw <| IO.userError "Supply exact module names to replay."
  for arg in args do
    IO.println s!"Replaying {arg}"
    (← IO.getStdout).flush
    replayFromImports arg.toName
  IO.println s!"Successfully replayed {args.length} module(s)."
  return 0
