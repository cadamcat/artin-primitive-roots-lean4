import ArtinPrimitiveRoots.A2

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
  simp [normDeriv]

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

- `ExteriorArithmetic`, `ReflectionCharacters`, and the S-integer frequency data require the
  A1 ideal-generator, residue-ring, and Kummer-character constructions (`A1/Field.lean`,
  `A1/Characters.lean`; TeX 02:229-387 and 04:99-132).
- `ClassPairing` requires quotient descent of `HilbertData` to sixth-power classes
  (`A1/Hilbert.lean`; TeX 02:114-132).
- `SheetGeometry` and `RotatedPresentation` require the normalized Haar disintegration,
  fundamental domain, and T6 profile producers (`A1/SLattice.lean`, `Theta/Shared.lean`,
  `Theta/AnalysisS.lean`; TeX 03:474-659).
- `PoissonWeights`, `WeightSpec`, and `WeightDecay` require a nonzero Bruhat-Schwartz weight
  with the prescribed Mellin value and strip decay (TeX 05:24-75).
- The finite and complex local Tate functional-equation predicates require Fourier-transform
  calculations with the fixed local measures (TeX 05:37-75).
- `HeckeAnalysis` and `ConductorHeightBound` require Hecke continuation, principal zeta
  regularization, residue positivity, and uniform convexity (Hecke/Continuation.lean;
  TeX 06:37-73, 139-163, 413-477).
- `EulerHypotheses`, `EulerCorrection`, the local-factor bounds, and `ZeroDensityData` require
  Gauss correction identities, convergent Euler products, and the zero-density/reciprocal
  estimates (TeX 02:389-625 and 05:596-765, 06:165-366).
- `IsFundamentalAt`, `activeFactor`, `activeNumerator`, and the reflection profile hypotheses
  require the chosen arithmetic rows, compact representatives, and theta estimates
  (TeX 04:19-35, 433-548).
- `DyadEnumeration` requires the finite dyadic shell theorem carried by `FrequencyData`.

The result theorems in the three A2 missing-node files are the requested analytic obligations;
their `sorry` proofs are not used as witnesses here.
-/

#print axioms zeroSheetHypCInfinity
#print axioms initialRegion_witness
#print axioms eulerNeighborhood_witness
#print axioms ArtinPrimitiveRoots.A2.cross_prime_exponent_cancel
#print axioms ArtinPrimitiveRoots.A2.localC_natural_subtraction_gate
#print axioms ArtinPrimitiveRoots.A2.zeroth_power_mask_gate

end ArtinPrimitiveRoots.Review.A2Witnesses
