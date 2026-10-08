import ArtinPrimitiveRoots.Splitting.Defs
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! Shared finite products for the S7-EULER package. -/

set_option autoImplicit false
open scoped NumberField BigOperators
open NumberField IsDedekindDomain

noncomputable section
namespace ArtinPrimitiveRoots.Splitting
open ClassFieldTheory ArtinPrimitiveRoots.Hecke

/-- The complex dual of a finite group is finite; complex roots contain its exponent. -/
noncomputable instance s7CharacterFintype (G : Type*) [Group G] [Finite G] :
    Fintype (G →* ℂˣ) := by
  haveI : NeZero ((Monoid.exponent G : ℕ) : ℂ) :=
    ⟨by exact_mod_cast (Monoid.exponent_ne_zero_of_finite (G := G))⟩
  exact Fintype.ofFinite _

/-- Complex roots of a fixed nonzero order form a finite type. -/
noncomputable instance s7RootsOfUnityFintype (n : ℕ) [NeZero n] :
    Fintype (rootsOfUnity n ℂ) := by
  haveI : NeZero (n : ℂ) := ⟨by exact_mod_cast (NeZero.ne n)⟩
  exact Fintype.ofFinite _

variable (B T : Type*) [Field B] [NumberField B] [Field T] [NumberField T]
  [Algebra B T]

/-- The finite fiber of upstairs height-one primes over a base prime. -/
def s7PrimesAbove (v : HeightOneSpectrum (𝓞 B)) : Finset (HeightOneSpectrum (𝓞 T)) := by
  classical
  haveI := v.isPrime
  haveI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  exact ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 T)).preimage
    (f := fun w : HeightOneSpectrum (𝓞 T) => w.asIdeal)
    (fun _ _ _ _ h => HeightOneSpectrum.ext h)).toFinset

/-- Upstairs primes deleted by a ray modulus, counted once. -/
def s7BadTopPrimes (m : RayClassModulus B) : Finset (HeightOneSpectrum (𝓞 T)) := by
  classical
  exact m.finitePart.support.biUnion (s7PrimesAbove B T)

/-- The finite correction restoring the deleted upstairs Euler factors. -/
def s7UpstairsCorrection (m : RayClassModulus B) (s : ℂ) : ℂ :=
  ∏ w ∈ s7BadTopPrimes B T m, (1 - (Ideal.absNorm w.asIdeal : ℂ) ^ (-s))⁻¹

/-- The finite deletion factor for the trivial base character. -/
def s7BaseDeletion (m : RayClassModulus B) (s : ℂ) : ℂ :=
  ∏ v ∈ m.finitePart.support, (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))

end ArtinPrimitiveRoots.Splitting
end
