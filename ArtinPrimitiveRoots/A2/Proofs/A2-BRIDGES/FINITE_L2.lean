import /- Local package with a hyphenated directory name. -/ ArtinPrimitiveRoots.A2.Proofs.«A2-BRIDGES».Defs

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
open ArtinPrimitiveRoots A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private def bridgeL2Vec {α : Type*} (T : Finset α)
    [Fintype {i : α // i ∈ T}] (f : α → ℂ) :
    EuclideanSpace ℂ {i : α // i ∈ T} :=
  WithLp.toLp 2 (fun i : {i : α // i ∈ T} => f i.1)

private lemma bridgeL2_eq_norm {α : Type*} (T : Finset α)
    [Fintype {i : α // i ∈ T}] (f : α → ℂ) :
    bridgeL2 T f = ‖bridgeL2Vec T f‖ := by
  rw [bridgeL2, EuclideanSpace.norm_eq]
  congr 1
  simpa [bridgeL2Vec] using
    (Finset.sum_subtype T (fun _ => Iff.rfl) (fun i => ‖f i‖ ^ 2))

/-- Finite Euclidean triangle inequality; it applies before squaring the norm.
Guide: sol-thin-a2rp/PROOFS.md:67–68. Uses PiLp norm_sum_le. -/
theorem a2_bridge_FINITE_L2 {α β : Type*} (T : Finset α) (U : Finset β)
    (f : β → α → ℂ) :
    bridgeL2 T (fun i => ∑ j ∈ U, f j i) ≤ ∑ j ∈ U, bridgeL2 T (f j) := by
  classical
  letI : Fintype {i : α // i ∈ T} := Fintype.ofFinset T (by intro i; rfl)
  have hvec : bridgeL2Vec T (fun i => ∑ j ∈ U, f j i) =
      ∑ j ∈ U, bridgeL2Vec T (f j) := by
    ext i
    simp [bridgeL2Vec]
  calc
    bridgeL2 T (fun i => ∑ j ∈ U, f j i) =
        ‖bridgeL2Vec T (fun i => ∑ j ∈ U, f j i)‖ :=
      bridgeL2_eq_norm T _
    _ = ‖∑ j ∈ U, bridgeL2Vec T (f j)‖ := by rw [hvec]
    _ ≤ ∑ j ∈ U, ‖bridgeL2Vec T (f j)‖ := norm_sum_le _ _
    _ = ∑ j ∈ U, bridgeL2 T (f j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (bridgeL2_eq_norm T (f j)).symm

/-- Finite-coordinate Bochner Minkowski bound, with actual integrability hypotheses.
Guide: sol-thin-a2rp/PROOFS.md:67–68. Uses norm_integral_le_integral_norm in PiLp. -/
theorem a2_bridge_FINITE_L2_integral {α Ω : Type*} [MeasurableSpace Ω]
    (T : Finset α) (ν : Measure Ω) (f : Ω → α → ℂ)
    (hf : ∀ i ∈ T, Integrable (fun x => f x i) ν) :
    Integrable (fun x => bridgeL2 T (f x)) ν ∧
    bridgeL2 T (fun i => ∫ x, f x i ∂ν) ≤ ∫ x, bridgeL2 T (f x) ∂ν := by
  classical
  letI : Fintype {i : α // i ∈ T} := Fintype.ofFinset T (by intro i; rfl)
  let g : Ω → EuclideanSpace ℂ {i : α // i ∈ T} := fun x => bridgeL2Vec T (f x)
  have hcoord : ∀ i : {i : α // i ∈ T}, Integrable (fun x => f x i.1) ν :=
    fun i => hf i.1 i.2
  have hg : Integrable g ν := Integrable.of_eval_piLp (fun i => by
    simpa [g, bridgeL2Vec] using hcoord i)
  have hbridge : (fun x => bridgeL2 T (f x)) = fun x => ‖g x‖ := by
    funext x
    exact bridgeL2_eq_norm T (f x)
  have hcoord_int (i : {i : α // i ∈ T}) :
      (∫ x, g x ∂ν) i = ∫ x, f x i.1 ∂ν :=
    by
      simpa [g, bridgeL2Vec] using
        (eval_integral_piLp (f := g) (μ := ν)
          (fun k => by simpa [g, bridgeL2Vec] using hcoord k) i)
  have hvec_int :
      bridgeL2Vec T (fun i => ∫ x, f x i ∂ν) = ∫ x, g x ∂ν := by
    ext i
    exact (hcoord_int i).symm
  refine ⟨?_, ?_⟩
  · rw [hbridge]
    exact hg.norm
  · calc
      bridgeL2 T (fun i => ∫ x, f x i ∂ν) =
          ‖bridgeL2Vec T (fun i => ∫ x, f x i ∂ν)‖ := bridgeL2_eq_norm T _
      _ = ‖∫ x, g x ∂ν‖ := by rw [hvec_int]
      _ ≤ ∫ x, ‖g x‖ ∂ν := norm_integral_le_integral_norm _
      _ = ∫ x, bridgeL2 T (f x) ∂ν := by rw [← hbridge]

/-- Infinite outer sum in a complete finite-dimensional target.
Guide: sol-thin-a2rp/PROOFS.md:67–68. Uses summable_norm_iff and norm_tsum_le. -/
theorem a2_bridge_FINITE_L2_tsum {α β : Type*} (T : Finset α) (f : β → α → ℂ)
    (hf : Summable (fun j => bridgeL2 T (f j))) :
    (∀ i ∈ T, Summable (fun j => f j i)) ∧
    bridgeL2 T (fun i => ∑' j, f j i) ≤ ∑' j, bridgeL2 T (f j) := by
  classical
  letI : Fintype {i : α // i ∈ T} := Fintype.ofFinset T (by intro i; rfl)
  let g : β → EuclideanSpace ℂ {i : α // i ∈ T} := fun j => bridgeL2Vec T (f j)
  have hnorm : Summable (fun j => ‖g j‖) :=
    hf.congr fun j => bridgeL2_eq_norm T (f j)
  have hvec : Summable g := summable_norm_iff.mp hnorm
  have hcoord (i : {i : α // i ∈ T}) : Summable (fun j => f j i.1) := by
    apply Summable.of_norm_bounded hnorm
    intro j
    exact (PiLp.norm_apply_le (g j) i).trans_eq (by simp [g, bridgeL2Vec])
  have hvec_tsum :
      bridgeL2Vec T (fun i => ∑' j, f j i) = ∑' j, g j := by
    ext i
    have hproj :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : {i : α // i ∈ T} => ℂ) i).map_tsum hvec
    simpa [g, bridgeL2Vec] using hproj.symm
  refine ⟨?_, ?_⟩
  · intro i hi
    exact hcoord ⟨i, hi⟩
  · calc
      bridgeL2 T (fun i => ∑' j, f j i) =
          ‖bridgeL2Vec T (fun i => ∑' j, f j i)‖ := bridgeL2_eq_norm T _
      _ = ‖∑' j, g j‖ := by rw [hvec_tsum]
      _ ≤ ∑' j, ‖g j‖ := norm_tsum_le_tsum_norm hnorm
      _ = ∑' j, bridgeL2 T (f j) := tsum_congr fun j =>
        (bridgeL2_eq_norm T (f j)).symm

end ArtinPrimitiveRoots.A2
