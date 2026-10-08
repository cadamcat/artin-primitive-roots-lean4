import ArtinPrimitiveRoots.Spec.Proofs.SPEC_RELLICH.Defs
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option autoImplicit false
open MeasureTheory NumberField Module
open scoped ArtinPrimitiveRoots.A1.Spec.RellichChart
noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec.RellichChartMeasure

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

theorem coordsX_continuous : Continuous (coordsX F) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hchart⟩ := G1_h3_basics (F := F)
  obtain ⟨e, _, heinv⟩ := hchart
  have h := continuous_subtype_val.comp e.symm.continuous
  exact h.congr (fun z => heinv z)

theorem ptX_coordsX (z : X F) : ptX F (coordsX F z) = z := by
  obtain ⟨_, _, _, _, _, _, _, h, _, _, _, _⟩ := G1_h3_basics (F := F)
  exact h z

theorem coordsX_ptX (p : Coord F) (hp : p ∈ posSet F) :
    coordsX F (ptX F p) = p := by
  obtain ⟨_, _, _, _, _, _, h, _, _, _, _, _⟩ := G1_h3_basics (F := F)
  exact h p hp

theorem coordsX_mem_pos (z : X F) : coordsX F z ∈ posSet F := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hchart⟩ := G1_h3_basics (F := F)
  obtain ⟨e, _, heinv⟩ := hchart
  rw [← heinv z]
  exact (e.symm z).property

theorem continuous_of_isSmoothX {f : X F → ℂ} (hf : IsSmoothX F f) : Continuous f := by
  obtain ⟨_, _, _, _, _, _, _, hptx, _, _, _, hchart⟩ := G1_h3_basics (F := F)
  obtain ⟨e, _, heinv⟩ := hchart
  have hcoordsCont : Continuous (coordsX F) := by
    have h := continuous_subtype_val.comp e.symm.continuous
    exact h.congr (fun z => heinv z)
  have hcoordsPos : ∀ z, coordsX F z ∈ posSet F := by
    intro z
    rw [← heinv z]
    exact (e.symm z).property
  have hpull : Continuous (fun z => f (ptX F (coordsX F z))) := by
    exact hf.continuousOn.comp_continuous hcoordsCont hcoordsPos
  have heq : (fun z => f (ptX F (coordsX F z))) = f := by
    funext z
    rw [hptx]
  exact heq ▸ hpull

theorem continuous_of_isSmoothRealX {f : X F → ℝ} (hf : IsSmoothRealX F f) : Continuous f := by
  obtain ⟨_, _, _, _, _, _, _, hptx, _, _, _, hchart⟩ := G1_h3_basics (F := F)
  obtain ⟨e, _, heinv⟩ := hchart
  have hcoordsCont : Continuous (coordsX F) := by
    have h := continuous_subtype_val.comp e.symm.continuous
    exact h.congr (fun z => heinv z)
  have hcoordsPos : ∀ z, coordsX F z ∈ posSet F := by
    intro z
    rw [← heinv z]
    exact (e.symm z).property
  have hpull : Continuous (fun z => f (ptX F (coordsX F z))) := by
    exact hf.continuousOn.comp_continuous hcoordsCont hcoordsPos
  have heq : (fun z => f (ptX F (coordsX F z))) = f := by
    funext z
    rw [hptx]
  exact heq ▸ hpull

/-- The squared L² norm is the integral of the pointwise squared norm. -/
theorem lp_two_norm_sq_eq_integral_norm_sq {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (u : Lp ℂ 2 μ) :
    ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  calc
    ‖u‖ ^ 2 = RCLike.re (inner ℂ u u) := (inner_self_eq_norm_sq (𝕜 := ℂ) u).symm
    _ = RCLike.re (∫ x, inner ℂ (u x) (u x) ∂μ) := by rw [← MeasureTheory.L2.inner_def]
    _ = ∫ x, RCLike.re (inner ℂ (u x) (u x)) ∂μ :=
      (integral_re (MeasureTheory.L2.integrable_inner u u)).symm
    _ = ∫ x, ‖u x‖ ^ 2 ∂μ := by
      congr 1
      funext x
      exact inner_self_eq_norm_sq (u x)


/-- Split the three real coordinates at one complex place into a complex horizontal
coordinate and a real height. -/
def factorCoordEquiv : (Fin 3 → ℝ) ≃ᵐ (ℂ × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).trans <|
    (MeasurableEquiv.prodComm).trans <|
      MeasurableEquiv.prodCongr Complex.measurableEquivPi.symm
        (MeasurableEquiv.refl ℝ)

theorem factorCoordEquiv_measurePreserving :
    MeasurePreserving factorCoordEquiv volume volume := by
  have h₁ : MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2)
      volume (volume.prod (Measure.pi fun _ : Fin 2 => (volume : Measure ℝ))) := by
    exact MeasureTheory.volume_preserving_piFinSuccAbove _ _
  have hid : MeasurePreserving (fun x : ℝ => x) (volume : Measure ℝ) volume := by
    constructor
    · exact measurable_id
    · simp
  have h₂ : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        Complex.measurableEquivPi.symm)
      ((volume : Measure ℝ).prod volume)
      ((volume : Measure ℝ).prod (volume : Measure ℂ)) := by
    exact MeasureTheory.MeasurePreserving.prod hid Complex.volume_preserving_equiv_pi.symm
  have h₃ : MeasurePreserving MeasurableEquiv.prodComm
      ((volume : Measure ℝ).prod (volume : Measure ℂ))
      ((volume : Measure ℂ).prod (volume : Measure ℝ)) := by
    exact MeasureTheory.Measure.measurePreserving_swap
  convert h₃.comp (h₂.comp h₁) using 1 <;> rfl

/-- Volume on a finite Hilbert product is the product of the component volumes. -/
theorem piLp_ofLp_measurePreserving {ι : Type*} [Fintype ι]
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)]
    [∀ i, BorelSpace (E i)] [∀ i, FiniteDimensional ℝ (E i)]
    [MeasurableSpace (PiLp 2 E)] [BorelSpace (PiLp 2 E)] :
    MeasurePreserving (WithLp.ofLp : PiLp 2 E → (∀ i, E i))
      volume (Measure.pi fun i => (volume : Measure (E i))) := by
  classical
  let B : ∀ i, OrthonormalBasis (Fin (Module.finrank ℝ (E i))) ℝ (E i) :=
    fun i => stdOrthonormalBasis ℝ (E i)
  let bLP : OrthonormalBasis (Σ i, Fin (Module.finrank ℝ (E i))) ℝ (PiLp 2 E) :=
    Pi.orthonormalBasis B
  let bPi : Module.Basis (Σ i, Fin (Module.finrank ℝ (E i))) ℝ (∀ i, E i) :=
    Pi.basis fun i => (B i).toBasis
  have hpar : (bPi.parallelepiped : Set (∀ i, E i)) =
      Set.pi Set.univ (fun i => ((B i).toBasis.parallelepiped : Set (E i))) := by
    ext x
    change x ∈ _root_.parallelepiped bPi ↔ x ∈ Set.pi Set.univ _
    rw [parallelepiped_basis_eq]
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro hx i
      change x i ∈ _root_.parallelepiped (B i).toBasis
      rw [parallelepiped_basis_eq]
      intro j
      simpa [bPi, Pi.basis_repr] using hx ⟨i, j⟩
    · intro hx ij
      rcases ij with ⟨i, j⟩
      have hi := hx i
      change x i ∈ _root_.parallelepiped (B i).toBasis at hi
      rw [parallelepiped_basis_eq] at hi
      simpa [bPi, Pi.basis_repr] using hi j
  have hμ : Measure.pi (fun i => (volume : Measure (E i))) bPi.parallelepiped = 1 := by
    rw [hpar, MeasureTheory.Measure.pi_pi]
    simp [bPi, B, OrthonormalBasis.volume_parallelepiped]
  have hbPi : bPi.addHaar = Measure.pi (fun i => (volume : Measure (E i))) :=
    (Module.Basis.addHaar_eq_iff bPi _).2 hμ
  have hLP : bLP.toBasis.addHaar = (volume : Measure (PiLp 2 E)) :=
    OrthonormalBasis.addHaar_eq_volume bLP
  let f : WithLp 2 (∀ i, E i) ≃L[ℝ] (∀ i, E i) :=
    (WithLp.linearEquiv 2 ℝ (∀ i, E i)).toContinuousLinearEquiv
  have hmap : (bLP.toBasis.map f.toLinearEquiv) = bPi := by
    change ((Pi.orthonormalBasis B).toBasis.map
      (WithLp.linearEquiv 2 ℝ (∀ i, E i))) = Pi.basis (fun i => (B i).toBasis)
    rw [Pi.orthonormalBasis.toBasis]
    ext i
    simp [Module.Basis.map_apply]
  have hf : (WithLp.ofLp : WithLp 2 (∀ i, E i) → (∀ i, E i)) = f := by
    funext x
    rfl
  refine ⟨f.continuous.measurable, ?_⟩
  calc
    Measure.map WithLp.ofLp volume = Measure.map WithLp.ofLp bLP.toBasis.addHaar := by rw [hLP]
    _ = (bLP.toBasis.map f.toLinearEquiv).addHaar := by
      rw [hf]
      exact Module.Basis.map_addHaar bLP.toBasis f
    _ = Measure.pi (fun i => (volume : Measure (E i))) := by rw [hmap, hbPi]

@[simp] theorem factorCoordEquiv_apply (v : Fin 3 → ℝ) :
    factorCoordEquiv v = (Complex.ofReal (v 0) + Complex.I * Complex.ofReal (v 1), v 2) := by
  have h0 : (2 : Fin 3).succAbove (0 : Fin 2) = 0 := by decide
  have h1 : (2 : Fin 3).succAbove (1 : Fin 2) = 1 := by decide
  change (Complex.measurableEquivPi.symm (Fin.removeNth 2 v), v 2) = _
  apply Prod.ext
  · apply Complex.ext
    · simp [Complex.measurableEquivPi_symm_apply, Fin.removeNth_apply, h0]
    · simp [Complex.measurableEquivPi_symm_apply, Fin.removeNth_apply, h1]
  · rfl

/-- The Euclidean three-coordinate chart at one complex place. -/
def euclideanToFin3Pi : EuclideanSpace ℝ (Fin 3) ≃ᵐ (Fin 3 → ℝ) where
  toEquiv := (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toEquiv
  measurable_toFun :=
    ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toContinuousLinearEquiv).continuous.measurable
  measurable_invFun :=
    ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toContinuousLinearEquiv.symm).continuous.measurable

@[simp] theorem euclideanToFin3Pi_apply (p : EuclideanSpace ℝ (Fin 3)) :
    euclideanToFin3Pi p = WithLp.ofLp p := rfl

def factorCoordEquivEuclidean : EuclideanSpace ℝ (Fin 3) ≃ᵐ (ℂ × ℝ) :=
  euclideanToFin3Pi.trans factorCoordEquiv

theorem factorCoordEquivEuclidean_apply (p : EuclideanSpace ℝ (Fin 3)) :
    factorCoordEquivEuclidean p =
      (Complex.ofReal (p 0) + Complex.I * Complex.ofReal (p 1), p 2) := by
  change factorCoordEquiv (euclideanToFin3Pi p) = _
  rw [euclideanToFin3Pi_apply]
  exact factorCoordEquiv_apply _

theorem factorCoordEquivEuclidean_measurePreserving :
    MeasurePreserving factorCoordEquivEuclidean volume volume := by
  have hOf : MeasurePreserving (WithLp.ofLp :
      EuclideanSpace ℝ (Fin 3) → (Fin 3 → ℝ)) volume
      (Measure.pi fun _ : Fin 3 => (volume : Measure ℝ)) :=
    piLp_ofLp_measurePreserving (fun _ : Fin 3 => ℝ)
  exact factorCoordEquiv_measurePreserving.comp hOf

/-- The global real Euclidean chart and the product complex-height chart carry the same volume. -/
theorem rellichToCoord_measurePreserving (F : Type) [Field F] [NumberField F] :
    MeasurePreserving (rellichToCoord F)
      (volume : Measure (RellichCoord F)) (volume : Measure (Coord F)) := by
  classical
  let W := InfinitePlace F
  let e₁ : (W × Fin 3) ≃ Σ w : W, Fin 3 := (Equiv.sigmaEquivProd W (Fin 3)).symm
  let T₁ := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e₁
  let T₂ := LinearIsometryEquiv.piLpCurry ℝ 2 (fun _ : W => fun _ : Fin 3 => ℝ)
  let T := T₁.trans T₂
  have hT : MeasurePreserving T := LinearIsometryEquiv.measurePreserving T
  have hOf : MeasurePreserving (WithLp.ofLp :
      PiLp 2 (fun w : W => EuclideanSpace ℝ (Fin 3)) → (w : W) → EuclideanSpace ℝ (Fin 3))
      volume (Measure.pi fun w => (volume : Measure (EuclideanSpace ℝ (Fin 3)))) :=
    piLp_ofLp_measurePreserving (fun _ : W => EuclideanSpace ℝ (Fin 3))
  have hPi : MeasurePreserving (fun (a : W → EuclideanSpace ℝ (Fin 3)) (w : W) =>
      factorCoordEquivEuclidean (a w))
      (Measure.pi fun _ : W => (volume : Measure (EuclideanSpace ℝ (Fin 3))))
      (Measure.pi fun _ : W => (volume : Measure (ℂ × ℝ))) :=
    MeasureTheory.measurePreserving_pi _ _ (f := fun _ : W => factorCoordEquivEuclidean)
      (fun _ => factorCoordEquivEuclidean_measurePreserving)
  have hComp := hPi.comp (hOf.comp hT)
  have hfun : (fun p : RellichCoord F =>
      fun w : W => factorCoordEquivEuclidean (WithLp.toLp 2 (fun j : Fin 3 => p (w, j)))) =
      rellichToCoord F := by
    funext p w
    rw [factorCoordEquivEuclidean_apply]
    simp [rellichToCoord]
  have hT_apply (p : RellichCoord F) (w : W) :
      (WithLp.ofLp (T p)) w = WithLp.toLp 2 (fun j : Fin 3 => p (w, j)) := by
    ext j
    simp [T, T₁, T₂, LinearIsometryEquiv.piLpCurry_apply, Equiv.piCongrLeft',
      e₁, Sigma.curry]
  have hComp' : MeasurePreserving
      (fun p : RellichCoord F => fun w : W =>
        factorCoordEquivEuclidean (WithLp.toLp 2 (fun j : Fin 3 => p (w, j))))
      (volume : Measure (RellichCoord F))
      (Measure.pi fun _ : W => (volume : Measure (ℂ × ℝ))) := by
    convert hComp using 1
    funext p w
    simp only [Function.comp_apply]
    rw [← hT_apply p w]
  rw [hfun] at hComp'
  simpa [RellichCoord, Coord, W, MeasureTheory.volume_pi] using hComp'

/-- The inverse coordinate map from the complex-height chart to real triples. -/
def coordToRellich (F : Type) [Field F] [NumberField F] (q : Coord F) : RellichCoord F :=
  WithLp.toLp 2 (fun i : InfinitePlace F × Fin 3 =>
    match i.2 with
    | 0 => (q i.1).1.re
    | 1 => (q i.1).1.im
    | 2 => (q i.1).2)

theorem rellichToCoord_coordToRellich (F : Type) [Field F] [NumberField F] (q : Coord F) :
    rellichToCoord F (coordToRellich F q) = q := by
  funext w
  apply Prod.ext
  · apply Complex.ext <;> simp [coordToRellich, rellichToCoord]
  · simp [coordToRellich, rellichToCoord]

theorem coordToRellich_rellichToCoord (F : Type) [Field F] [NumberField F]
    (p : RellichCoord F) : coordToRellich F (rellichToCoord F p) = p := by
  ext i
  rcases i with ⟨w, j⟩
  fin_cases j <;> simp [coordToRellich, rellichToCoord]

noncomputable def rellichCoordMeasurableEquiv (F : Type) [Field F] [NumberField F] :
    RellichCoord F ≃ᵐ Coord F where
  toEquiv :=
    { toFun := rellichToCoord F
      invFun := coordToRellich F
      left_inv := coordToRellich_rellichToCoord F
      right_inv := rellichToCoord_coordToRellich F }
  measurable_toFun := (rellichToCoord_measurePreserving F).measurable
  measurable_invFun := by
    classical
    have hcoords : Continuous (fun q : Coord F =>
        fun i : InfinitePlace F × Fin 3 =>
          match i.2 with
          | 0 => (q i.1).1.re
          | 1 => (q i.1).1.im
          | 2 => (q i.1).2) := by
      apply continuous_pi
      intro i
      rcases i with ⟨w, j⟩
      fin_cases j <;> fun_prop
    have htoLp : Continuous (WithLp.toLp 2 :
        (InfinitePlace F × Fin 3 → ℝ) → RellichCoord F) :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : InfinitePlace F × Fin 3 => ℝ)).symm.continuous
    change Measurable (fun q : Coord F => WithLp.toLp 2 (fun i : InfinitePlace F × Fin 3 =>
      match i.2 with
      | 0 => (q i.1).1.re
      | 1 => (q i.1).1.im
      | 2 => (q i.1).2))
    exact (htoLp.comp hcoords).measurable

theorem rellichCoordMeasurableEquiv_measurePreserving (F : Type) [Field F] [NumberField F] :
    MeasurePreserving (rellichCoordMeasurableEquiv F)
      (volume : Measure (RellichCoord F)) (volume : Measure (Coord F)) :=
  rellichToCoord_measurePreserving F

end ArtinPrimitiveRoots.A1.Spec.RellichChartMeasure
