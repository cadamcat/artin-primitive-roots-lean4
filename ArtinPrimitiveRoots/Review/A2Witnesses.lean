import ArtinPrimitiveRoots.A2
import ArtinPrimitiveRoots.A2.Coherence

/-!
# A2 interface witnesses

The examples below witness the elementary shape predicates and the three kernel gates. The
analytic/arithmetic packages listed after them need their named source theories; the comments
identify the missing witness content rather than using any A2 result whose proof is still `sorry`.
-/

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical

namespace ArtinPrimitiveRoots.Review.A2Witnesses

theorem zeroSheetHypCInfinity :
    ArtinPrimitiveRoots.A2.SheetHypCInfinity 0 (fun _ : ℂ => (0 : ℂ)) := by
  refine ⟨contDiff_const.contDiffOn, ?_⟩
  intro j A hA
  refine ⟨0, ?_⟩
  intro y hy
  simp [ArtinPrimitiveRoots.A1.normDeriv]

theorem initialRegion_witness :
    ArtinPrimitiveRoots.A2.initialRegion (2 : ℂ) 3 1 := by
  norm_num [ArtinPrimitiveRoots.A2.initialRegion]

theorem eulerNeighborhood_witness :
    ArtinPrimitiveRoots.A2.eulerNeighborhood (fun _ : Fin 3 => (1 : ℂ)) := by
  unfold ArtinPrimitiveRoots.A2.eulerNeighborhood
  left
  norm_num

example : (0 - 1 + 1 : ℕ) = 1 ∧ (0 + 1 - 1 : ℕ) = 0 :=
  ArtinPrimitiveRoots.A2.localC_natural_subtraction_gate

example : (0 : ℂ) ^ (0 : ℕ) ≠ 0 :=
  ArtinPrimitiveRoots.A2.zeroth_power_mask_gate

/-!
Theory-dependent witnesses not constructed in this lane:

- `ExteriorArithmetic`, admissible `ReflectionCharacters`, and the S-integer frequency data
  require A1's ideal-generator, residue-ring, and Kummer-character constructions
  (`A1/Field.lean`, `A1/Characters.lean`; TeX 02:229-387 and 04:99-132). The corrected
  `FrequencyData.nonempty` needs finite order of `η`; its new masked prime field also needs the
  local Kummer ramification formula at positive valuations (`sol-thin-a2rp/PROOFS.md:632-640`).
- `ClassPairing` requires quotient descent of `HilbertData` to sixth-power classes
  (`A1/Hilbert.lean`; TeX 02:114-132).
- `SheetGeometry`, `RotatedPresentation`, and `ReflectionSetup` require the normalized Haar
  disintegration, fundamental domain, T6 profile producers, and the combined A1/theta data.
  The setup's `GaussSplit` needs the finite-order and angular Gauss characters as well
  (`A1/SLattice.lean`, `Theta/Shared.lean`, `Theta/AnalysisS.lean`; TeX 03:474-659, 04:19-35).
- `PoissonWeights`, `WeightSpec`, and `WeightDecay` require a nonzero Bruhat-Schwartz weight
  with the prescribed Mellin value and strip decay (TeX 05:24-75).
- The finite and complex local Tate functional-equation predicates require Fourier-transform
  calculations with the fixed local measures (TeX 05:37-75).
- `HeckeAnalysis` and `ConductorHeightBound` require Hecke continuation, principal zeta
  regularization, residue positivity, and uniform convexity (Hecke/Continuation.lean;
  TeX 06:37-73, 139-163, 413-477).
- `IncompleteDictionary`, `DensityOutput`, and `RayDeletion` require canonical complete and
  incomplete continuations, finite Euler deletion, zero coverage, and the ray-class modulus
  dictionary. The adapter proofs are available once these records are supplied; this witness file
  does not manufacture the analytic or arithmetic data (TeX 06:165-185, 691-764).
- `EulerHypotheses`, `EulerCorrection`, `HasPoHLocalBounds`, `HasPoHProduct`, the local-factor
  bounds, and `ZeroDensityData` require Gauss correction identities, convergent Euler products,
  and the zero-density/reciprocal estimates (TeX 02:389-625 and 05:596-765, 06:165-366).
- `IsFundamentalAt`, `activeFactor`, `activeNumerator`, and the reflection profile hypotheses
  require the chosen arithmetic rows, compact representatives, and theta estimates
  (TeX 04:19-35, 433-548).
- `DyadEnumeration` requires the finite dyadic shell theorem carried by `FrequencyData`.
- `reflection_row_element_injective` requires the arithmetic uniqueness of rows with the same
  represented element; finite-sum to subtype-`tsum` conversion is proved once that witness is
  supplied (TeX 04:1198-1228).

The result theorems in the three A2 missing-node files are the requested analytic obligations;
their `sorry` proofs are not used as witnesses here.
-/

#print axioms zeroSheetHypCInfinity
#print axioms initialRegion_witness
#print axioms eulerNeighborhood_witness
#print axioms ArtinPrimitiveRoots.A2.cross_prime_exponent_cancel
#print axioms ArtinPrimitiveRoots.A2.localC_natural_subtraction_gate
#print axioms ArtinPrimitiveRoots.A2.zeroth_power_mask_gate
#print axioms ArtinPrimitiveRoots.A2.cgen_valid
#print axioms ArtinPrimitiveRoots.A2.gaussSplit_of_data
#print axioms ArtinPrimitiveRoots.A2.finite_to_tsum
#print axioms ArtinPrimitiveRoots.A2.assembly_to_total
#print axioms ArtinPrimitiveRoots.A2.prop_reflection_total_from_assembly_exact
#print axioms ArtinPrimitiveRoots.A2.density_to_consumer
#print axioms ArtinPrimitiveRoots.A2.rowFamily_from_data
#print axioms ArtinPrimitiveRoots.A2.dyadEnumeration_nonempty
#print axioms ArtinPrimitiveRoots.A2.mellinInputs_of_nodes
#print axioms ArtinPrimitiveRoots.A2.boundary_from_mellin

end ArtinPrimitiveRoots.Review.A2Witnesses
