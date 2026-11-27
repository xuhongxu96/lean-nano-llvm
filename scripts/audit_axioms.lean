import Lean
import LeanNanoLlvm
import Tests
import Main

/-!
# Transitive Axiom Audit

Verifies that every constant across every project module (`LeanNanoLlvm.*`, `Tests.*` and `Main`)
depends ONLY on the three standard Lean 4 axioms:
  `{propext, Classical.choice, Quot.sound}`
(no `sorryAx`, no `Lean.ofReduceBool` / `native_decide`, no custom axioms).
-/

open Lean

def allowedAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

#eval show MetaM Unit from do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut modCount : Nat := 0
  let mut state : CollectAxioms.State := {}
  for modIdx in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[modIdx]!
    if modName == `Main || modName.getRoot == `LeanNanoLlvm || modName.getRoot == `Tests then
      modCount := modCount + 1
      let modData := env.header.moduleData[modIdx]!
      for cName in modData.constNames do
        let (_, s') := (CollectAxioms.collect cName).run env state
        state := s'
        checked := checked + 1
  IO.println s!"Checked {checked} constants across {modCount} project modules (LeanNanoLlvm + Tests + Main)."
  IO.println s!"All axioms transitively referenced: {state.axioms.toList}"
  let unexpected := state.axioms.filter fun ax => !allowedAxioms.contains ax
  if unexpected.isEmpty then
    IO.println "AUDIT PASSED: Every constant uses ONLY standard Lean axioms {propext, Classical.choice, Quot.sound}!"
  else
    IO.println s!"AUDIT FAILED: unexpected axioms: {unexpected.toList}"
    let mut shown := 0
    for modIdx in [:env.header.moduleNames.size] do
      let modName := env.header.moduleNames[modIdx]!
      if modName == `Main || modName.getRoot == `LeanNanoLlvm || modName.getRoot == `Tests then
        let modData := env.header.moduleData[modIdx]!
        for cName in modData.constNames do
          if shown < 20 then
            let (_, s1) := (CollectAxioms.collect cName).run env {}
            let bad1 := s1.axioms.filter fun ax => !allowedAxioms.contains ax
            if !bad1.isEmpty then
              IO.println s!"  {cName}: {bad1.toList}"
              shown := shown + 1
    throwError "Non-standard axioms detected!"
