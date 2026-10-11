import ArtinPrimitiveRoots.Hecke.RayClassCopy

/-!
# Hecke L-function package: definitions

Partial Hecke L-series of ray class characters.
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.Hecke

open ClassFieldTheory

variable {K : Type*} [Field K] [NumberField K]

/-- A nonzero integral ideal as a unit of the fractional-ideal monoid. -/
def idealUnit (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) : NumberFieldFractionalIdealGroup K :=
  Units.mk0 (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (FractionalIdeal.coeIdeal_ne_zero.mpr hI)

/-- An integral ideal is coprime to the modulus `𝔪` (finite part) and nonzero. -/
def IsCoprimeTo (m : RayClassModulus K) (I : Ideal (𝓞 K)) : Prop :=
  ∃ hI : I ≠ ⊥, idealUnit I hI ∈ rayClassPrimeToIdeals m

/-- The ray class `[𝔞] ∈ Cl_𝔪(K)` of an integral ideal coprime to `𝔪`. -/
def rayClass (m : RayClassModulus K) (I : Ideal (𝓞 K)) (h : IsCoprimeTo m I) :
    RayClassGroup m :=
  QuotientGroup.mk (⟨idealUnit I h.1, h.2⟩ : rayClassPrimeToIdeals m)

open Classical in
/-- The character value `η([𝔞])`, extended by `0` to ideals that are zero or not coprime to `𝔪`. -/
def charValue {m : RayClassModulus K} (η : RayClassGroup m →* ℂˣ) (I : Ideal (𝓞 K)) : ℂ :=
  if h : IsCoprimeTo m I then (η (rayClass m I h) : ℂ) else 0

/-- Dirichlet coefficient: `a_η(n) = Σ_{N𝔞 = n} η([𝔞])`. -/
def coeff {m : RayClassModulus K} (η : RayClassGroup m →* ℂˣ) (n : ℕ) : ℂ :=
  ∑ I ∈ (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n).toFinset, charValue η I

/-- **The partial Hecke L-series** `L_K^{(𝔪)}(s, η) = Σ_{(𝔞,𝔪)=1} η([𝔞]) N𝔞^{-s}`
(B's notation N9).  Meaningful (absolutely convergent) for `Re s > 1`. -/
def LSeriesRay {m : RayClassModulus K} (η : RayClassGroup m →* ℂˣ) (s : ℂ) : ℂ :=
  LSeries (coeff η) s

/-- The norm `N𝔪 = ∏_v N(𝔭_v)^{e_v}` of the finite part of a modulus. -/
def modulusNorm (m : RayClassModulus K) : ℕ :=
  m.finitePart.prod (fun v e => (Ideal.absNorm v.asIdeal) ^ e)

/-- `η` factors through the smaller modulus `𝔫`: it is trivial on the classes of principal
ideals `(x)` coprime to `𝔪` with `x ≡ 1 mod^× 𝔫` (positivity at the real places of `𝔫`). -/
def FactorsThrough {m : RayClassModulus K} (η : RayClassGroup m →* ℂˣ)
    (n : RayClassModulus K) : Prop :=
  n ≤ m ∧ ∀ x : Kˣ, IsRayCongruent n x →
    ∀ h : toPrincipalIdeal (𝓞 K) K x ∈ rayClassPrimeToIdeals m,
      η (QuotientGroup.mk (⟨toPrincipalIdeal (𝓞 K) K x, h⟩ : rayClassPrimeToIdeals m)) = 1

/-- The norm of the conductor of `η`: the least `N𝔫` over moduli `𝔫 ≤ 𝔪` through which `η`
factors (the set contains `N𝔪`, so this is `≤ N𝔪`).  Only this number enters the interface;
the package proves internally that the minimum is attained by a unique primitive modulus. -/
def conductorNorm {m : RayClassModulus K} (η : RayClassGroup m →* ℂˣ) : ℕ :=
  sInf {N : ℕ | ∃ n : RayClassModulus K, FactorsThrough η n ∧ modulusNorm n = N}

end ArtinPrimitiveRoots.Hecke
