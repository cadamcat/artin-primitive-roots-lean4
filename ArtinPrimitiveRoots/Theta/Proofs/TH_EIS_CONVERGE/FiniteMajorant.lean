import ArtinPrimitiveRoots.Theta.TorusInd
import ArtinPrimitiveRoots.Theta.LocalInt
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_CONVERGE.LocalIwasawa
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Finite

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-- A finite-place section has bounded norm on every compact set: its open
right stabilizer makes it locally constant. -/
theorem section_norm_bound_on_compact
    {D : FieldData F} {H : HilbertData F} {v : FinPlace F}
    (L : FinLocalCover D H v) (T : TorusRep D H v) {s : ℂ}
    (f : L.L → T.V) (hf : IsSection L T s f)
    (K : Set L.L) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ K, ‖f g‖ ≤ C := by
  obtain ⟨m, hm, hright⟩ := hf.2.2
  have hloc : IsLocallyConstant f := by
    apply (IsLocallyConstant.iff_exists_open f).2
    intro g
    refine ⟨(fun h : L.L => g⁻¹ * h) ⁻¹' (L.Kc m : Set L.L),
      (L.Kc_open m hm).preimage (continuous_const.mul continuous_id), ?_, ?_⟩
    · simp
    · intro h hh
      simpa only [mul_inv_cancel_left] using hright g (g⁻¹ * h) hh
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hloc.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  exact fun g hg => (hC g hg).trans (le_max_left _ _)

/-- On unipotent, central and torus translates of a compact set, the norm of
a section is bounded by its real character weight. -/
theorem section_norm_majorant_on_compact
    {D : FieldData F} {H : HilbertData F} {v : FinPlace F}
    (L : FinLocalCover D H v) (T : TorusRep D H v) {s : ℂ}
    (f : L.L → T.V) (hf : IsSection L T s f)
    (K : Set L.L) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x : v.adicCompletion F) (ζ : rootsOfUnity 3 ℂ)
        (y : (v.adicCompletion F)ˣ) (k : L.L), k ∈ K →
        ‖f (L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * k)‖ ≤
          C * (absFin v (y : v.adicCompletion F)) ^ ((1 : ℝ) / 2 + s.re) := by
  let op : (v.adicCompletion F)ˣ → (T.V →L[ℂ] T.V) :=
    fun y => LinearMap.toContinuousLinearMap (T.σa y)
  have hop : (Set.range op).Finite := by
    change (Set.range fun y => LinearMap.toContinuousLinearMap (T.σa y)).Finite
    rw [Set.range_comp']
    exact T.σa_finite.image (fun A : T.V →ₗ[ℂ] T.V => LinearMap.toContinuousLinearMap A)
  obtain ⟨B, hB⟩ := hop.isCompact.exists_bound_of_continuousOn
    (f := fun A : T.V →L[ℂ] T.V => A) continuous_id.continuousOn
  let M : ℝ := max B 0
  have hM : 0 ≤ M := le_max_right B 0
  have hop_norm (y : (v.adicCompletion F)ˣ) : ‖op y‖ ≤ M :=
    (hB (op y) ⟨y, rfl⟩).trans (le_max_left B 0)
  have hop_bound (y : (v.adicCompletion F)ˣ) (u : T.V) :
      ‖(T.σa y) u‖ ≤ M * ‖u‖ :=
    ((op y).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right (hop_norm y) (norm_nonneg u))
  obtain ⟨A, hA, hfbound⟩ := section_norm_bound_on_compact L T f hf K hK
  refine ⟨M * A, mul_nonneg hM hA, ?_⟩
  intro x ζ y k hk
  have hζpow : (((ζ : ℂˣ) : ℂ)) ^ 3 = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg (fun u : ℂˣ => (u : ℂ)) ((mem_rootsOfUnity 3 (ζ : ℂˣ)).mp ζ.property)
  have hζ : ‖((ζ : ℂˣ) : ℂ)‖ = 1 :=
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hζpow⟩).norm_eq_one
  have hpos : 0 < absFin v (y : v.adicCompletion F) := absFin_pos y.ne_zero
  have hweight : ‖(absFin v (y : v.adicCompletion F) : ℂ) ^ ((1 : ℂ) / 2 + s)‖ =
      (absFin v (y : v.adicCompletion F)) ^ ((1 : ℝ) / 2 + s.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    congr 1
    norm_num
  have hcentral : L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * k =
      L.z ζ * (L.n (Multiplicative.ofAdd x) * L.a y * k) := by
    rw [← L.z_central ζ (L.n (Multiplicative.ofAdd x))]
    simp only [mul_assoc]
  rw [hcentral, hf.2.1 ζ _, hf.1 x y k, norm_smul, norm_smul, hζ, one_mul, hweight]
  rw [mul_comm (M * A) ((absFin v (y : v.adicCompletion F)) ^ ((1 : ℝ) / 2 + s.re))]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hpos.le _)
  exact (hop_bound y (f k)).trans (mul_le_mul_of_nonneg_left (hfbound k hk) hM)

end ArtinPrimitiveRoots.A1.Theta
