import Lean
import Lean.Meta.Tactic.AuxLemma

namespace ArtinPrimitiveRoots.Proofs.a2_euler_sol

/-- Reuse imported auxiliary proof names after frozen definitions move across modules. -/
def seedImportedClosedProofs (names : Array Lean.Name) : Lean.CoreM Unit := do
  for n in names do
    let ci ← Lean.getConstInfo n
    let env ← Lean.getEnv
    let key : Lean.Meta.AuxLemmaKey := { type := ci.type, isPrivate := !env.isExporting, defeq := false }
    Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env fun state => { state with lemmas := state.lemmas.insert key (n, ci.levelParams) }

end ArtinPrimitiveRoots.Proofs.a2_euler_sol
