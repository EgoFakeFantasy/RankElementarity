import RankReflection.Unbounded
import Lean

/-! The default build fails if any theorem in this project uses an axiom
outside Lean/Mathlib's standard logical foundations. -/

#check RankReflection.rankElementaryInclusion_unbounded
#print axioms RankReflection.rankElementaryInclusion_unbounded
#print axioms RankReflection.exists_rankElementaryInclusion_between

open Lean Elab Command in
run_elab do
  let env ← getEnv
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count := 0
  let mut used : Array Name := #[]
  for (name, info) in env.constants.toList do
    if (`RankReflection).isPrefixOf name && info.isTheorem then
      count := count + 1
      let axioms ← collectAxioms name
      for ax in axioms do
        unless permitted.contains ax do
          throwError "Unexpected axiom {ax} in {name}"
        unless used.contains ax do
          used := used.push ax
  logInfo m!"RankReflection kernel audit passed: {count} theorem constants; axioms: {used}"
