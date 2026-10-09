import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.RationalData
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianNorm
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.RationalOddGauss
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.RationalDyadicGauss
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.CharacterUniqueness
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.TraceCharacter
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.LatticeGaussian
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.TraceTransfer.PadicGaussian
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.TraceTransfer.Coordinates
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.TraceTransfer.FiberGaussian
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.TraceTransfer.Assembly

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Transfer actual normalized local Gaussians to the rational diagonal trace form.
Guide: PROOFS.md:480–485. Uses: completion tensor/trace decomposition; additive-character trace identification; rational_odd_gauss_sum; rational_dyadic_gauss_sums. -/
theorem quadratic_trace_transfer (D : FieldData F) (A : AddCharData F)
    (W : LocalGaussianData A) (a : Fˣ) (T : QuadraticTraceDiagonal a)
    (T1 : QuadraticTraceDiagonal (1 : Fˣ)) (p : Nat.Primes) :
    primeFiberIndex W p a = tracePrimePhase T p / tracePrimePhase T1 p := by
  exact ArtinPrimitiveRoots.Proofs.weil_trace_opus.quadratic_trace_transfer_proof D A W a T T1 p

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
