import ArtinPrimitiveRoots.A1.AddChar
import Mathlib.MeasureTheory.Group.Measure

/-!
# A1 arithmetic base: the S-integer lattice

This file records the Lean statements corresponding to `lem:s-lattice` and
`ar:balanced-compact` in the A1 blueprint.  The analytic objects are stated using the product
space `S.FS`, its diagonal S-integer subgroup, finite sums of standard archimedean Schwartz and
finite-place test functions, and a self-dual Haar measure for the character `S.e`.
The lattice outcomes take `D : FieldData F`, which supplies the paper's `μ₁₂ ⊂ F` hypothesis and
the required total-complexity property.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical SchwartzMap

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

local instance instMeasurableFS (S : SData F CE condη) : MeasurableSpace S.FS :=
  borel S.FS
local instance instBorelFS (S : SData F CE condη) : BorelSpace S.FS := ⟨rfl⟩

/-! ## Test functions and the self-dual measure -/

/-- Locally constant compactly supported test functions at a finite place in `S`. -/
def SData.FiniteTest (S : SData F CE condη) (v : S.Sf) :=
  {f : v.1.adicCompletion F → ℂ // Continuous f ∧ HasCompactSupport f ∧ IsLocallyConstant f}

/-- Archimedean Schwartz functions on the product of complex places. -/
abbrev SData.ArchSchwartz (F : Type) [Field F] [NumberField F] :=
  SchwartzMap (InfinitePlace F → ℂ) ℂ

/-- A pure tensor in the standard Bruhat--Schwartz space on `F_S`. -/
def SData.tensorFunction (S : SData F CE condη) (arch : SData.ArchSchwartz F)
    (finite : ∀ v : S.Sf, S.FiniteTest v) : S.FS → ℂ :=
  fun x => arch x.2 * ∏ v : S.Sf, (finite v).1 (x.1 v)

/-- The Bruhat--Schwartz space: finite linear combinations of archimedean Schwartz functions
tensored with locally constant compactly supported functions at the places in `S_f`. -/
def SData.BruhatSchwartz (S : SData F CE condη) : Submodule ℂ (S.FS → ℂ) :=
  Submodule.span ℂ (Set.range fun p : SData.ArchSchwartz F ×
      (∀ v : S.Sf, S.FiniteTest v) => S.tensorFunction p.1 p.2)

/-- The Fourier transform associated to `e` and a Haar measure on `F_S`. -/
def SData.fourier (S : SData F CE condη) (A : AddCharData F)
    (μ : Measure S.FS) (f : S.FS → ℂ) : S.FS → ℂ :=
  fun y => ∫ x, f x * S.e A (-(x * y)) ∂μ

/-- A self-dual Haar measure for the additive character `e`, characterized by Fourier inversion
on the Bruhat--Schwartz space. -/
structure SData.SelfDualMeasure (S : SData F CE condη) (A : AddCharData F) where
  measure : Measure S.FS
  isHaar : Measure.IsAddHaarMeasure measure
  fourier_inversion : ∀ f : S.BruhatSchwartz, ∀ x : S.FS,
    S.fourier A measure (S.fourier A measure (f : S.FS → ℂ)) x = (f : S.FS → ℂ) (-x)

/-! ## The lattice and its annihilator -/

/-- The diagonal image of the S-integers in `F_S`. -/
def SData.diagR (S : SData F CE condη) : Set S.FS :=
  Set.range fun x : S.R => S.diag (x : F)

/-- The annihilator of a subset of `F_S` under the pairing `e(xy)`. -/
def SData.annihilator (S : SData F CE condη) (A : AddCharData F) (Γ : Set S.FS) : Set S.FS :=
  {y | ∀ x ∈ Γ, S.e A (x * y) = 1}

/-- A measurable fundamental domain for the diagonal S-integer lattice. -/
def SData.IsLatticeFundamentalDomain (S : SData F CE condη) (K : Set S.FS) : Prop :=
  ∀ x : S.FS, ∃! p : S.R × S.FS, p.2 ∈ K ∧ x = S.diag (p.1 : F) + p.2

/-- The diagonal S-integer lattice is discrete and has compact quotient.  The compact set in the
second clause is a compact set of representatives modulo the diagonal image. -/
theorem SData.diagR_discrete_cocompact (S : SData F CE condη) (D : FieldData F) :
    IsDiscrete (S.diagR : Set S.FS) ∧
      ∃ K : Set S.FS, IsCompact K ∧
        ∀ x : S.FS, ∃ r : S.R, ∃ k ∈ K, x = S.diag (r : F) + k := by
  sorry

/-- The S-integer lattice is its own annihilator for the pairing `e(xy)`. -/
theorem SData.diagR_eq_annihilator (S : SData F CE condη) (D : FieldData F)
    (A : AddCharData F) :
    S.diagR = S.annihilator A S.diagR := by
  sorry

/-- The diagonal copy of `R` has covolume one for the self-dual Haar measure. -/
theorem SData.diagR_covolume_one (S : SData F CE condη) (D : FieldData F)
    (A : AddCharData F)
    (μ : S.SelfDualMeasure A) :
    ∃ K : Set S.FS, MeasurableSet K ∧ S.IsLatticeFundamentalDomain K ∧ μ.measure K = 1 := by
  sorry

/-- Poisson summation on `R` for Bruhat--Schwartz functions on `F_S`, including absolute
convergence of both lattice sums. -/
theorem SData.poisson (S : SData F CE condη) (D : FieldData F) (A : AddCharData F)
    (μ : S.SelfDualMeasure A) (f : S.BruhatSchwartz) :
    Summable (fun m : S.R => ‖(f : S.FS → ℂ) (S.diag (m : F))‖) ∧
      Summable (fun ν : S.R => ‖S.fourier A μ.measure (f : S.FS → ℂ) (S.diag (ν : F))‖) ∧
      ∑' m : S.R, (f : S.FS → ℂ) (S.diag (m : F)) =
        ∑' ν : S.R, S.fourier A μ.measure (f : S.FS → ℂ) (S.diag (ν : F)) := by
  sorry

/-! ## Scaling and the norm identity -/

/-- The annihilator of `aR` is `a⁻¹R`. -/
theorem SData.annihilator_diag_mul (S : SData F CE condη) (D : FieldData F)
    (A : AddCharData F)
    (a : Fˣ) :
    S.annihilator A (Set.range fun x : S.R => S.diag ((a : F) * (x : F))) =
      Set.range fun x : S.R => S.diag ((a : F)⁻¹ * (x : F)) := by
  sorry

/-- The norm identity in `lem:s-lattice` with the total-complexity hypothesis made explicit.
This is the corrected version of the frozen `SData.absS_diag_eq_norm`, whose interface omits
`FieldData F`. -/
theorem SData.absS_diag_eq_norm_ofFieldData (S : SData F CE condη) (D : FieldData F)
    (x : F) (I : Ideal (𝓞 F)) (hI : S.IsExterior I) (hx : S.IsGen x I) :
    S.absS (S.diag x) = Ideal.absNorm I := by
  have : IsTotallyComplex F := D.isTotallyComplex
  exact S.absS_diag_eq_norm x I hI hx

/-- Scaling Poisson summation from `R` to the exterior fractional ideal `aR`. -/
theorem SData.poisson_scaled (S : SData F CE condη) (D : FieldData F) (A : AddCharData F)
    (μ : S.SelfDualMeasure A) (f : S.BruhatSchwartz) (a : Fˣ) (I : Ideal (𝓞 F))
    (hI : S.IsExterior I) (ha : S.IsGen (a : F) I) :
    ∑' m : S.R, (f : S.FS → ℂ) (S.diag ((a : F) * (m : F))) =
      ((Ideal.absNorm I : ℝ) : ℂ)⁻¹ *
        ∑' ν : S.R, S.fourier A μ.measure (f : S.FS → ℂ)
          (S.diag ((a : F)⁻¹ * (ν : F))) := by
  sorry

/-- Every nonzero S-integer has S-norm at least one. -/
theorem SData.absS_diag_ge_one (S : SData F CE condη) (D : FieldData F)
    (x : S.R) (hx : (x : F) ≠ 0) :
    1 ≤ S.absS (S.diag (x : F)) := by
  have : IsTotallyComplex F := D.isTotallyComplex
  have hprod := prod_abs_eq_one hx
  have hf_supp : (Function.mulSupport fun v => ‖FinitePlace.embedding v (x : F)‖).Finite :=
    finitePlace_mk_hasFiniteMulSupport hx
  have h_split : (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖FinitePlace.embedding v (x : F)‖) =
      (∏ v ∈ S.Sf, ‖FinitePlace.embedding v (x : F)‖) * ∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖ := by
    have h_union := finprod_mem_union' (hst := disjoint_compl_right)
      (hs := S.Sf.finite_toSet.inter_of_left _)
      (ht := Set.Finite.subset hf_supp Set.inter_subset_right)
      (f := fun v => ‖FinitePlace.embedding v (x : F)‖)
    rw [Set.union_compl_self, finprod_mem_univ] at h_union
    rw [finprod_mem_coe_finset] at h_union
    exact h_union
  have h_prod_decomp : (∏ᶠ w : FinitePlace F, w (x : F)) =
      (∏ v ∈ S.Sf, ‖FinitePlace.embedding v (x : F)‖) * ∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖ := by
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    change (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖FinitePlace.embedding v (x : F)‖) = _
    exact h_split
  rw [h_prod_decomp] at hprod
  have h_absS : S.absS (S.diag (x : F)) =
      (∏ v ∈ S.Sf, ‖FinitePlace.embedding v (x : F)‖) * ∏ w : InfinitePlace F, w (x : F) ^ w.mult :=
    absS_diag_eq S (x : F)
  have h_prod_absS : S.absS (S.diag (x : F)) * (∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖) = 1 := by
    rw [h_absS]
    calc ((∏ v ∈ S.Sf, ‖FinitePlace.embedding v (x : F)‖) * ∏ w : InfinitePlace F, w (x : F) ^ w.mult) *
          (∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖)
      _ = (∏ w : InfinitePlace F, w (x : F) ^ w.mult) *
          ((∏ v ∈ S.Sf, ‖FinitePlace.embedding v (x : F)‖) * ∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖) := by ring
      _ = 1 := hprod
  have h_eq : (∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖) =
      ∏ v ∈ hf_supp.toFinset with v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖ :=
    finprod_mem_eq_prod_filter (fun v => ‖FinitePlace.embedding v (x : F)‖) ((S.Sf : Set _)ᶜ) hf_supp
  have hP_le_one : (∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖) ≤ 1 := by
    rw [h_eq]
    refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun v hv =>
      norm_embedding_le_one_of_valuation_le_one v (x : F) (x.property v (Finset.mem_filter.mp hv).2)
  have h_absS_nonneg : 0 ≤ S.absS (S.diag (x : F)) := by
    rw [h_absS]
    refine mul_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      (Finset.prod_nonneg fun w _ => ?_)
    exact pow_nonneg (w.1.nonneg _) _
  calc 1
    _ = S.absS (S.diag (x : F)) * (∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖) := h_prod_absS.symm
    _ ≤ S.absS (S.diag (x : F)) * 1 := mul_le_mul_of_nonneg_left hP_le_one h_absS_nonneg
    _ = S.absS (S.diag (x : F)) := mul_one _

/-! ## Compactness modulo sixth powers of S-units -/

/-- The norm-one subgroup of `F_Sˣ`. -/
def SData.FSOne (S : SData F CE condη) :=
  {x : S.FSˣ // S.absS (x : S.FS) = 1}

/-- Two norm-one elements differ by the sixth power of a diagonal S-unit. -/
def SData.fsOneRel (S : SData F CE condη) (x y : S.FSOne) : Prop :=
  ∃ u : S.US, x.1 = (S.diagU (u : Fˣ)) ^ 6 * y.1

/-- The equivalence relation defining `F_S^1 / U_S^6`. -/
def SData.fsOneSetoid (S : SData F CE condη) : Setoid S.FSOne where
  r := S.fsOneRel
  iseqv := {
    refl := by
      intro x
      change ∃ u : S.US, x.1 = (S.diagU (u : Fˣ)) ^ 6 * x.1
      refine ⟨1, ?_⟩
      simp
    symm := by
      intro x y h
      rcases h with ⟨u, hu⟩
      refine ⟨u⁻¹, ?_⟩
      have hmap : S.diagU ((u⁻¹ : S.US) : Fˣ) = (S.diagU (u : Fˣ))⁻¹ := by
        rw [show ((u⁻¹ : S.US) : Fˣ) = (u : Fˣ)⁻¹ by rfl, map_inv]
      rw [hmap, hu]
      group
    trans := by
      intro x y z hxy hyz
      rcases hxy with ⟨u, hu⟩
      rcases hyz with ⟨v, hv⟩
      refine ⟨u * v, ?_⟩
      have hmap : S.diagU ((u * v : S.US) : Fˣ) =
          S.diagU (u : Fˣ) * S.diagU (v : Fˣ) := by
        rw [show ((u * v : S.US) : Fˣ) = (u : Fˣ) * (v : Fˣ) by rfl, map_mul]
      rw [hmap]
      calc
        x.1 = (S.diagU (u : Fˣ)) ^ 6 * y.1 := hu
        _ = (S.diagU (u : Fˣ) * S.diagU (v : Fˣ)) ^ 6 * z.1 := by
          rw [hv, mul_pow]
          group
  }

/-- Compactness of `F_S^1/U_S^6`, stated as a compact set of representatives for its quotient. -/
theorem SData.FSOne_quotient_compact (S : SData F CE condη) (D : FieldData F) :
    ∃ K : Set S.FS, IsCompact K ∧
      ∀ x : S.FSOne, ∃ y : S.FSOne, (y.1 : S.FS) ∈ K ∧ S.fsOneRel x y := by
  sorry

end ArtinPrimitiveRoots.A1
