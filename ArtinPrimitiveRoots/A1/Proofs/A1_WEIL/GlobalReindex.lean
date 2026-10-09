import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.RationalData
import ArtinPrimitiveRoots.Hecke.Elementary.EulerProduct.PrimeFibers

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private theorem wi_mem_primeIndex_iff (v : FinPlace F) (p : Nat.Primes) :
    (p.1 : 𝓞 F) ∈ v.asIdeal ↔
      ArtinPrimitiveRoots.Hecke.EulerProduct.primeIndex (K := F) v = p := by
  constructor
  · intro hp
    have hpInt : ((p.1 : ℤ) : 𝓞 F) ∈ v.asIdeal := by simpa using hp
    have hdivInt : (Ideal.absNorm (v.asIdeal.under ℤ) : ℤ) ∣ (p.1 : ℤ) :=
      Int.cast_mem_ideal_iff.mp hpInt
    have hdiv :
        Ideal.absNorm (v.asIdeal.under ℤ) ∣ p.1 := Int.natCast_dvd_natCast.mp hdivInt
    have hqval : Ideal.absNorm (v.asIdeal.under ℤ) = p.1 :=
      (Nat.prime_dvd_prime_iff_eq
        (Nat.absNorm_under_prime v.asIdeal) p.2).mp hdiv
    apply Subtype.ext
    exact hqval
  · intro hqp
    have hnorm : Ideal.absNorm (v.asIdeal.under ℤ) = p.1 := by
      simpa [ArtinPrimitiveRoots.Hecke.EulerProduct.primeIndex] using
        congrArg Subtype.val hqp
    have hdivInt : (Ideal.absNorm (v.asIdeal.under ℤ) : ℤ) ∣ (p.1 : ℤ) := by
      rw [hnorm]
    have hpInt : ((p.1 : ℤ) : 𝓞 F) ∈ v.asIdeal :=
      Int.cast_mem_ideal_iff.mpr hdivInt
    simpa using hpInt

/-- Regroup a finite-support global product by its unique rational residue prime.
Guide: PROOFS.md:480–481. Uses: finite residue fields; rational-prime fibers; finprod partition identities. -/
theorem global_index_prime_fibers (A : AddCharData F) (W : LocalGaussianData A) (a : Fˣ)
    (ha : (Function.mulSupport fun v => W.index v (toLoc v a)).Finite) :
    (∏ᶠ v : FinPlace F, ((W.index v (toLoc v a) : ℂˣ) : ℂ)) =
      ∏ᶠ p : Nat.Primes, primeFiberIndex W p a := by
  classical
  let f : FinPlace F → ℂ := fun v => ((W.index v (toLoc v a) : ℂˣ) : ℂ)
  let primeBelow : FinPlace F → Nat.Primes :=
    ArtinPrimitiveRoots.Hecke.EulerProduct.primeIndex (K := F)
  have hcomplexSupport : (Function.mulSupport f).Finite := by
    apply ha.subset
    intro v hv
    change f v ≠ 1 at hv
    change W.index v (toLoc v a) ≠ 1
    intro hindex
    exact hv (by simp [f, hindex])
  let s := hcomplexSupport.toFinset
  have hs : Function.mulSupport f ⊆ s := by
    intro v hv
    exact hcomplexSupport.mem_toFinset.mpr hv
  have hfiber (p : Nat.Primes) :
      primeFiberIndex W p a = ∏ v ∈ s with primeBelow v = p, f v := by
    unfold primeFiberIndex
    let hpq : (fun v : FinPlace F => (p.1 : 𝓞 F) ∈ v.asIdeal) =
        fun v => primeBelow v = p := by
      funext v
      exact propext (wi_mem_primeIndex_iff v p)
    let e := Equiv.subtypeEquivProp hpq
    change (∏ᶠ v : {v : FinPlace F // (p.1 : 𝓞 F) ∈ v.asIdeal}, f v.1) =
      ∏ v ∈ s with primeBelow v = p, f v
    calc
      (∏ᶠ v : {v : FinPlace F // (p.1 : 𝓞 F) ∈ v.asIdeal}, f v.1) =
          ∏ᶠ v : {v : FinPlace F // primeBelow v = p}, f v.1 := by
        exact finprod_eq_of_bijective e e.bijective (fun _ => rfl)
      _ = ∏ v ∈ s with primeBelow v = p, f v := by
        rw [finprod_subtype_eq_finprod_cond]
        refine finprod_cond_eq_prod_of_cond_iff f ?_
        intro v hv
        have hvs : v ∈ s := hs (Function.mem_mulSupport.mpr hv)
        constructor
        · intro hprime
          exact Finset.mem_filter.mpr ⟨hvs, hprime⟩
        · intro hfilter
          exact (Finset.mem_filter.mp hfilter).2
  calc
    (∏ᶠ v : FinPlace F, f v) = ∏ v ∈ s, f v :=
      finprod_eq_prod_of_mulSupport_subset f hs
    _ = ∏ᶠ p : Nat.Primes, ∏ v ∈ s with primeBelow v = p, f v := by
      symm
      exact finprod_prod_filter primeBelow s f
    _ = ∏ᶠ p : Nat.Primes, primeFiberIndex W p a := by
      apply finprod_congr
      intro p
      exact (hfiber p).symm

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
