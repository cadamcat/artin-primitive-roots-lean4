import Mathlib

/-!
Coordinate changes for the simplex integrals defining rough-number densities.
-/

namespace ArtinPrimitiveRoots.Proofs.b_density_sol

open MeasureTheory
open scoped ENNReal

/-- The linear part of swapping one independent simplex coordinate with the dependent last one. -/
def simplexSwapMatrix {n : ℕ} (i : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  (1 : Matrix (Fin n) (Fin n) ℝ).updateRow i (fun _ => -1)

/-- The affine coordinate change that replaces coordinate `i` by the dependent coordinate. -/
def simplexSwap {n : ℕ} (i : Fin n) (x : Fin n → ℝ) : Fin n → ℝ :=
  Function.update x i (1 - ∑ k, x k)

/-- The matrix of the linear part of `simplexSwap`. -/
def simplexSwapLinear {n : ℕ} (i : Fin n) : (Fin n → ℝ) →ₗ[ℝ] Fin n → ℝ :=
  Matrix.toLin' (simplexSwapMatrix i)

lemma simplexSwapMatrix_det {n : ℕ} (i : Fin n) :
    (simplexSwapMatrix i).det = -1 := by
  let A : Matrix (Fin n) (Fin n) ℝ := 1
  have hrow : (fun _ : Fin n => (-1 : ℝ)) = ∑ k : Fin n, (-1 : ℝ) • A k := by
    funext j
    simp [A, Matrix.one_apply, eq_comm]
  have hM : simplexSwapMatrix i = A.updateRow i (∑ k : Fin n, (-1 : ℝ) • A k) := by
    ext r c
    by_cases hr : r = i
    · subst r
      simp [simplexSwapMatrix, A, hrow]
    · simp [simplexSwapMatrix, A, hr]
  rw [hM, Matrix.det_updateRow_sum]
  simp [A]

lemma simplexSwap_eq_linear_add {n : ℕ} (i : Fin n) (x : Fin n → ℝ) :
    simplexSwap i x = simplexSwapLinear i x + Function.update (0 : Fin n → ℝ) i (1 : ℝ) := by
  funext k
  by_cases hk : k = i
  · subst k
    simp [simplexSwap, simplexSwapLinear, Matrix.toLin'_apply, Matrix.mulVec,
      dotProduct, simplexSwapMatrix, Matrix.updateRow_apply, Function.update_self]
    ring
  · simp [simplexSwap, simplexSwapLinear, Matrix.toLin'_apply, Matrix.mulVec,
      dotProduct, simplexSwapMatrix, Matrix.updateRow_apply,
      Matrix.one_apply, hk]

lemma simplexSwap_sum {n : ℕ} (i : Fin n) (x : Fin n → ℝ) :
    ∑ k, simplexSwap i x k = 1 - x i := by
  simp [simplexSwap, Finset.sum_update_of_mem (Finset.mem_univ i)]

lemma simplexSwap_involutive {n : ℕ} (i : Fin n) :
    Function.Involutive (simplexSwap i) := by
  intro x
  funext k
  by_cases hk : k = i
  · subst k
    change Function.update (simplexSwap i x) i
      (1 - ∑ k, simplexSwap i x k) i = x i
    simp only [Function.update_self]
    rw [simplexSwap_sum]
    ring
  · simp [simplexSwap, hk]

lemma simplexSwap_measurePreserving_fun {n : ℕ} (i : Fin n) :
    MeasurePreserving (simplexSwap i) volume volume := by
  let L := simplexSwapLinear i
  let c : Fin n → ℝ := Function.update 0 i 1
  have hdet : LinearMap.det L = -1 := by
    simp [L, simplexSwapLinear, simplexSwapMatrix_det]
  have hdet0 : LinearMap.det L ≠ 0 := by rw [hdet]; norm_num
  have hL : MeasurePreserving L volume volume := by
    refine ⟨L.continuous_of_finiteDimensional.measurable, ?_⟩
    rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet0]
    simp [hdet]
  have ht : MeasurePreserving (fun y : Fin n → ℝ => y + c) volume volume :=
    MeasureTheory.measurePreserving_add_right volume c
  have hcomp := ht.comp hL
  convert hcomp using 1
  · funext x
    exact simplexSwap_eq_linear_add i x

lemma simplexSwap_measurable {n : ℕ} (i : Fin n) : Measurable (simplexSwap i) := by
  let L := simplexSwapLinear i
  let c : Fin n → ℝ := Function.update 0 i 1
  have h : simplexSwap i = fun x => L x + c := by
    funext x
    exact simplexSwap_eq_linear_add i x
  rw [h]
  fun_prop

/-- A measurable equivalence implementing the affine simplex coordinate swap. -/
def simplexSwapMeasurableEquiv {n : ℕ} (i : Fin n) :
    (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
  MeasurableEquiv.ofInvolutive (simplexSwap i) (simplexSwap_involutive i)
    (simplexSwap_measurable i)

lemma simplexSwap_measurePreserving {n : ℕ} (i : Fin n) :
    MeasurePreserving (simplexSwapMeasurableEquiv i) volume volume := by
  have hfun : (⇑(simplexSwapMeasurableEquiv i) : (Fin n → ℝ) → Fin n → ℝ) = simplexSwap i := by
    funext x
    simp [simplexSwapMeasurableEquiv]
  rw [hfun]
  exact simplexSwap_measurePreserving_fun i

/-- The full list of simplex coordinates, including the dependent coordinate. -/
def simplexCoordinate {n : ℕ} (x : Fin n → ℝ) : Option (Fin n) → ℝ
  | none => 1 - ∑ k, x k
  | some i => x i

private def simplexCoordinateSumLinear {n : ℕ} : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, x i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' r x := by simp [Finset.mul_sum]

private def simplexCoordinateEvalLinear {n : ℕ} (i : Fin n) :
    (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun x := x i
  map_add' x y := rfl
  map_smul' r x := rfl

/-- The affine map underlying a full simplex coordinate. -/
def simplexCoordinateAffine {n : ℕ} (c : Option (Fin n)) :
    (Fin n → ℝ) →ᵃ[ℝ] ℝ := by
  cases c with
  | none =>
    exact AffineMap.mk (fun x => 1 - ∑ i, x i) (-simplexCoordinateSumLinear)
      (by
        intro p v
        simp [simplexCoordinateSumLinear, Finset.sum_add_distrib]
        ring)
  | some i =>
    exact AffineMap.mk (fun x => x i) (simplexCoordinateEvalLinear i)
      (by intro p v; rfl)

lemma simplexCoordinateAffine_apply {n : ℕ} (c : Option (Fin n)) (x : Fin n → ℝ) :
    simplexCoordinateAffine c x = simplexCoordinate x c := by
  cases c <;> rfl

/-- The affine subspace where two distinct full simplex coordinates tie. -/
noncomputable def simplexTieSubspace {n : ℕ} (c d : Option (Fin n)) :
    AffineSubspace ℝ (Fin n → ℝ) :=
  ({(0 : ℝ)} : AffineSubspace ℝ ℝ).comap
    (simplexCoordinateAffine c - simplexCoordinateAffine d)

lemma simplexTieSubspace_coe {n : ℕ} (c d : Option (Fin n)) :
    (simplexTieSubspace c d : Set (Fin n → ℝ)) =
      {x | simplexCoordinate x c = simplexCoordinate x d} := by
  ext x
  simp [simplexTieSubspace, AffineSubspace.mem_comap, simplexCoordinateAffine_apply,
    sub_eq_zero]

lemma exists_simplexCoordinate_ne {n : ℕ} {c d : Option (Fin n)} (hcd : c ≠ d) :
    ∃ x : Fin n → ℝ, simplexCoordinate x c ≠ simplexCoordinate x d := by
  cases c with
  | none =>
    cases d with
    | none => exact (hcd rfl).elim
    | some j =>
      refine ⟨0, ?_⟩
      simp [simplexCoordinate]
  | some i =>
    cases d with
    | none =>
      refine ⟨0, ?_⟩
      simp [simplexCoordinate]
    | some j =>
      by_cases hij : i = j
      · subst j
        exact (hcd rfl).elim
      · refine ⟨Function.update 0 i 1, ?_⟩
        simp [simplexCoordinate, Function.update_of_ne (Ne.symm hij)]

lemma simplexTieSubspace_ne_top {n : ℕ} {c d : Option (Fin n)} (hcd : c ≠ d) :
    simplexTieSubspace c d ≠ ⊤ := by
  obtain ⟨x, hx⟩ := exists_simplexCoordinate_ne hcd
  intro htop
  have hxmem : x ∈ simplexTieSubspace c d := by simpa [htop]
  have hcoe : x ∈ (simplexTieSubspace c d : Set (Fin n → ℝ)) := hxmem
  rw [simplexTieSubspace_coe] at hcoe
  exact hx hcoe

lemma volume_simplexCoordinate_tie {n : ℕ} {c d : Option (Fin n)} (hcd : c ≠ d) :
    volume {x : Fin n → ℝ | simplexCoordinate x c = simplexCoordinate x d} = 0 := by
  rw [← simplexTieSubspace_coe]
  exact MeasureTheory.Measure.addHaar_affineSubspace volume (simplexTieSubspace c d)
    (simplexTieSubspace_ne_top hcd)

lemma ae_simplexCoordinate_ne {n : ℕ} {c d : Option (Fin n)} (hcd : c ≠ d) :
    ∀ᵐ x : Fin n → ℝ ∂volume, simplexCoordinate x c ≠ simplexCoordinate x d := by
  rw [ae_iff]
  simpa [ne_eq, not_not] using volume_simplexCoordinate_tie hcd

/-- The simplex domain with every full coordinate at least `b`. -/
def simplexGoodSet {n : ℕ} (b : ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ c, b ≤ simplexCoordinate x c}

/-- The symmetric reciprocal-coordinate kernel on the simplex. -/
noncomputable def simplexWeight {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∏ c : Option (Fin n), 1 / simplexCoordinate x c

/-- The reciprocal-coordinate kernel restricted to the rough simplex. -/
noncomputable def simplexIntegrand {n : ℕ} (b : ℝ) (x : Fin n → ℝ) : ℝ :=
  Set.indicator (simplexGoodSet b) simplexWeight x

lemma simplexIntegrand_integrable {n : ℕ} {b : ℝ} (hb : 0 < b) :
    Integrable (simplexIntegrand b : (Fin n → ℝ) → ℝ) volume := by
  classical
  let cube : Set (Fin n → ℝ) := Set.Icc 0 1
  let C : ℝ := (1 / b) ^ Fintype.card (Option (Fin n))
  have hC : 0 ≤ C := by positivity
  have hcubeMeas : MeasurableSet cube := measurableSet_Icc
  have hcubeFinite : volume cube < ∞ := by
    rw [show cube = Set.Icc (0 : Fin n → ℝ) 1 by rfl, Real.volume_Icc_pi]
    simp
  have hmajor : Integrable (fun x : Fin n → ℝ => Set.indicator cube (fun _ => C) x) volume := by
    apply (integrable_indicator_iff hcubeMeas).2
    exact integrableOn_const hcubeFinite.ne
  have hcoordMeas : ∀ c : Option (Fin n),
      Measurable (fun x : Fin n → ℝ => simplexCoordinate x c) := by
    intro c
    cases c <;> dsimp [simplexCoordinate] <;> fun_prop
  have hweightMeas : Measurable (simplexWeight : (Fin n → ℝ) → ℝ) := by
    unfold simplexWeight
    fun_prop [simplexCoordinate]
  have hgoodMeas : MeasurableSet (simplexGoodSet (n := n) b) := by
    unfold simplexGoodSet
    measurability
  have hsm : AEStronglyMeasurable (simplexIntegrand (n := n) b) volume := by
    unfold simplexIntegrand
    exact hweightMeas.aestronglyMeasurable.indicator hgoodMeas
  have hbound : ∀ᵐ x ∂volume,
      ‖simplexIntegrand b x‖ ≤ Set.indicator cube (fun _ => C) x := by
    filter_upwards [] with x
    by_cases hx : x ∈ simplexGoodSet b
    · have hcube : x ∈ cube := by
        change (0 : Fin n → ℝ) ≤ x ∧ x ≤ 1
        constructor
        · intro i
          exact (le_of_lt hb).trans (hx (some i))
        · intro i
          have hdep : b ≤ 1 - ∑ j, x j := by
            simpa [simplexCoordinate] using hx none
          have hsum : ∑ j, x j ≤ 1 - b := by linarith
          have hterms : ∀ j, 0 ≤ x j := fun j => (le_of_lt hb).trans (hx (some j))
          have hsingle : x i ≤ ∑ j, x j :=
            Finset.single_le_sum (fun j _ => hterms j) (Finset.mem_univ i)
          have hupper : 1 - b ≤ 1 := by linarith
          exact le_trans (le_trans hsingle hsum) hupper
      have hrec : ∀ c, 0 < 1 / simplexCoordinate x c ∧
          1 / simplexCoordinate x c ≤ 1 / b := by
        intro c
        have hc : 0 < simplexCoordinate x c := lt_of_lt_of_le hb (hx c)
        constructor
        · positivity
        · rw [div_le_div_iff₀ hc hb]
          nlinarith [hx c]
      have hw_nonneg : 0 ≤ simplexWeight x := by
        unfold simplexWeight
        exact Finset.prod_nonneg fun c _ => (hrec c).1.le
      have hw_bound : simplexWeight x ≤ C := by
        unfold simplexWeight C
        calc
          _ ≤ ∏ _c : Option (Fin n), (1 / b : ℝ) :=
            Finset.prod_le_prod₀ (fun c _ => (hrec c).1.le) (fun c _ => (hrec c).2)
          _ = (1 / b) ^ Fintype.card (Option (Fin n)) := by simp
      rw [simplexIntegrand, Set.indicator_of_mem hx, Set.indicator_of_mem hcube,
        Real.norm_eq_abs, abs_of_nonneg hw_nonneg]
      exact hw_bound
    · by_cases hcube : x ∈ cube <;> simp [simplexIntegrand, hx, hcube, hC]
  exact hmajor.mono' hsm hbound

lemma simplexCoordinate_swap {n : ℕ} (i : Fin n) (x : Fin n → ℝ) (c : Option (Fin n)) :
    simplexCoordinate (simplexSwap i x) c =
      simplexCoordinate x (Equiv.swap none (some i) c) := by
  cases c with
  | none =>
    simp [simplexCoordinate, simplexSwap_sum]
  | some k =>
    by_cases hk : k = i
    · subst k
      simp [simplexCoordinate, simplexSwap]
    · simp [simplexCoordinate, simplexSwap, hk]
      rw [Equiv.swap_apply_of_ne_of_ne (by simp) (by simpa using hk)]

lemma simplexGoodSet_swap {n : ℕ} (b : ℝ) (i : Fin n) (x : Fin n → ℝ) :
    simplexGoodSet b (simplexSwap i x) ↔ simplexGoodSet b x := by
  constructor <;> intro h c
  · have := h (Equiv.swap none (some i) c)
    simpa [simplexCoordinate_swap] using this
  · have := h (Equiv.swap none (some i) c)
    simpa [simplexCoordinate_swap] using this

lemma simplexWeight_swap {n : ℕ} (i : Fin n) (x : Fin n → ℝ) :
    simplexWeight (simplexSwap i x) = simplexWeight x := by
  unfold simplexWeight
  rw [show (fun c : Option (Fin n) => 1 / simplexCoordinate (simplexSwap i x) c) =
      (fun c => (fun d => 1 / simplexCoordinate x d) (Equiv.swap none (some i) c)) by
        funext c
        simp [simplexCoordinate_swap]]
  exact Equiv.prod_comp (Equiv.swap none (some i))
    (fun c : Option (Fin n) => 1 / simplexCoordinate x c)

lemma simplexIntegrand_swap {n : ℕ} (b : ℝ) (i : Fin n) (x : Fin n → ℝ) :
    simplexIntegrand b (simplexSwap i x) = simplexIntegrand b x := by
  by_cases hx : x ∈ simplexGoodSet b
  · have ht : simplexSwap i x ∈ simplexGoodSet b := (simplexGoodSet_swap b i x).mpr hx
    simp only [simplexIntegrand]
    rw [Set.indicator_of_mem ht, Set.indicator_of_mem hx, simplexWeight_swap]
  · have ht : simplexSwap i x ∉ simplexGoodSet b := fun h => hx ((simplexGoodSet_swap b i x).mp h)
    simp [simplexIntegrand, hx, ht]

/-- A specified full coordinate is a minimum among all simplex coordinates. -/
def simplexIsMinimum {n : ℕ} (x : Fin n → ℝ) (c : Option (Fin n)) : Prop :=
  ∀ d, simplexCoordinate x c ≤ simplexCoordinate x d

/-- The simplex integrand restricted to points where one full coordinate is minimal. -/
noncomputable def simplexMinIntegrand {n : ℕ} (b : ℝ) (c : Option (Fin n))
    (x : Fin n → ℝ) : ℝ :=
  Set.indicator {x | simplexIsMinimum x c} (simplexIntegrand b) x

lemma simplexIsMinimum_swap {n : ℕ} (i : Fin n) (x : Fin n → ℝ) :
    simplexIsMinimum (simplexSwap i x) (some i) ↔ simplexIsMinimum x none := by
  constructor
  · intro h c
    calc
      simplexCoordinate x none = simplexCoordinate (simplexSwap i x) (some i) := by
        simpa using (simplexCoordinate_swap i x (some i)).symm
      _ ≤ simplexCoordinate (simplexSwap i x) (Equiv.swap none (some i) c) :=
        h (Equiv.swap none (some i) c)
      _ = simplexCoordinate x c := by
        rw [simplexCoordinate_swap]
        simp
  · intro h c
    calc
      simplexCoordinate (simplexSwap i x) (some i) = simplexCoordinate x none := by
        simpa using simplexCoordinate_swap i x (some i)
      _ ≤ simplexCoordinate x (Equiv.swap none (some i) c) :=
        h (Equiv.swap none (some i) c)
      _ = simplexCoordinate (simplexSwap i x) c :=
        (simplexCoordinate_swap i x c).symm

lemma simplexIsMinimum_measurableSet {n : ℕ} (c : Option (Fin n)) :
    MeasurableSet {x : Fin n → ℝ | simplexIsMinimum x c} := by
  classical
  simp only [simplexIsMinimum, Set.setOf_forall]
  apply MeasurableSet.iInter
  intro d
  have hc : Measurable (fun x : Fin n → ℝ => simplexCoordinate x c) := by
    cases c <;> dsimp [simplexCoordinate] <;> fun_prop
  have hd : Measurable (fun x : Fin n → ℝ => simplexCoordinate x d) := by
    cases d <;> dsimp [simplexCoordinate] <;> fun_prop
  exact measurableSet_le hc hd

lemma simplexMinIntegrand_swap {n : ℕ} (b : ℝ) (i : Fin n) (x : Fin n → ℝ) :
    simplexMinIntegrand b (some i) (simplexSwap i x) = simplexMinIntegrand b none x := by
  classical
  by_cases hx : simplexIsMinimum x none
  · have ht : simplexIsMinimum (simplexSwap i x) (some i) :=
      (simplexIsMinimum_swap i x).2 hx
    simp only [simplexMinIntegrand]
    rw [Set.indicator_of_mem ht, Set.indicator_of_mem hx, simplexIntegrand_swap]
  · have ht : ¬ simplexIsMinimum (simplexSwap i x) (some i) :=
      fun h => hx ((simplexIsMinimum_swap i x).1 h)
    simp [simplexMinIntegrand, ht, hx]

lemma integral_simplexMinIntegrand_swap {n : ℕ} (b : ℝ) (i : Fin n) :
    ∫ x : Fin n → ℝ, simplexMinIntegrand b (some i) x =
      ∫ x : Fin n → ℝ, simplexMinIntegrand b none x := by
  have hfun : (⇑(simplexSwapMeasurableEquiv i) : (Fin n → ℝ) → Fin n → ℝ) = simplexSwap i := by
    funext x
    simp [simplexSwapMeasurableEquiv]
  have hchange :
      ∫ x : Fin n → ℝ, simplexMinIntegrand b (some i) (simplexSwap i x) =
        ∫ x : Fin n → ℝ, simplexMinIntegrand b (some i) x := by
    simpa only [hfun] using
      (simplexSwap_measurePreserving i).integral_comp' (simplexMinIntegrand b (some i))
  calc
    ∫ x : Fin n → ℝ, simplexMinIntegrand b (some i) x =
        ∫ x : Fin n → ℝ, simplexMinIntegrand b (some i) (simplexSwap i x) := hchange.symm
    _ = ∫ x : Fin n → ℝ, simplexMinIntegrand b none x := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact simplexMinIntegrand_swap b i x

lemma simplexMinIntegrand_integrable {n : ℕ} {b : ℝ} (hb : 0 < b)
    (c : Option (Fin n)) : Integrable (simplexMinIntegrand b c) volume := by
  unfold simplexMinIntegrand
  exact (simplexIntegrand_integrable hb).indicator (simplexIsMinimum_measurableSet c)

lemma ae_simplexUniqueMinimum {n : ℕ} :
    ∀ᵐ x : Fin n → ℝ ∂volume, ∃! c : Option (Fin n), simplexIsMinimum x c := by
  classical
  have hpair : ∀ᵐ x : Fin n → ℝ ∂volume,
      ∀ c d : Option (Fin n), c ≠ d → simplexCoordinate x c ≠ simplexCoordinate x d := by
    rw [ae_all_iff]
    intro c
    rw [ae_all_iff]
    intro d
    by_cases hdc : d = c
    · filter_upwards [] with x hneq
      exact (hneq hdc.symm).elim
    · have hcd : c ≠ d := fun h => hdc h.symm
      filter_upwards [ae_simplexCoordinate_ne hcd] with x hx
      intro _
      exact hx
  filter_upwards [hpair] with x hx
  obtain ⟨c, hc⟩ := Finite.exists_min (fun c : Option (Fin n) => simplexCoordinate x c)
  refine ⟨c, hc, ?_⟩
  intro d hd
  by_contra hnot
  have hcd : c ≠ d := by
    intro heq
    apply hnot
    exact heq.symm
  exact hx c d hcd (le_antisymm (hc d) (hd c))

lemma simplexIntegrand_eq_sum_min_of_unique {n : ℕ} (b : ℝ) (x : Fin n → ℝ)
    (huniq : ∃! c : Option (Fin n), simplexIsMinimum x c) :
    simplexIntegrand b x = ∑ c : Option (Fin n), simplexMinIntegrand b c x := by
  classical
  obtain ⟨c₀, hc₀, huniq⟩ := huniq
  have hmin : ∀ c, simplexIsMinimum x c ↔ c = c₀ := by
    intro c
    constructor
    · exact huniq c
    · rintro rfl
      exact hc₀
  calc
    simplexIntegrand b x =
        ∑ c : Option (Fin n), (if c = c₀ then simplexIntegrand b x else 0) := by simp
    _ = ∑ c : Option (Fin n), simplexMinIntegrand b c x := by
      apply Finset.sum_congr rfl
      intro c hc
      simp [simplexMinIntegrand, Set.indicator_apply, hmin]

lemma integral_simplexIntegrand_eq_sum_min {n : ℕ} {b : ℝ} (hb : 0 < b) :
    ∫ x : Fin n → ℝ, simplexIntegrand b x =
      ∑ c : Option (Fin n), ∫ x : Fin n → ℝ, simplexMinIntegrand b c x := by
  have hae : simplexIntegrand b =ᵐ[volume] fun x => ∑ c : Option (Fin n),
      simplexMinIntegrand b c x := by
    filter_upwards [ae_simplexUniqueMinimum] with x hx
    exact simplexIntegrand_eq_sum_min_of_unique b x hx
  calc
    ∫ x : Fin n → ℝ, simplexIntegrand b x =
        ∫ x : Fin n → ℝ, ∑ c : Option (Fin n), simplexMinIntegrand b c x := by
          apply integral_congr_ae
          exact hae
    _ = ∑ c : Option (Fin n), ∫ x : Fin n → ℝ, simplexMinIntegrand b c x := by
          simpa using integral_finsetSum Finset.univ
            (fun c hc => simplexMinIntegrand_integrable hb c)

/-- The region and kernel seen after making the least coordinate an explicit variable. -/
def simplexMinChartSet {k : ℕ} (b t : ℝ) (u : Fin k → ℝ) : Prop :=
  b ≤ t ∧ (∀ i, t ≤ u i) ∧ ∑ i, u i ≤ 1 - 2 * t

noncomputable def simplexMinChartKernel {k : ℕ} (t : ℝ) (u : Fin k → ℝ) : ℝ :=
  (1 / t) * (1 / (1 - t - ∑ i, u i)) * ∏ i, (1 / u i)

noncomputable def simplexMinChartIntegrand {k : ℕ} (b t : ℝ) (u : Fin k → ℝ) : ℝ :=
  Set.indicator {u | simplexMinChartSet b t u} (simplexMinChartKernel t) u

lemma simplexMinIntegrand_finCons {k : ℕ} (b t : ℝ) (u : Fin k → ℝ) :
    simplexMinIntegrand b (some 0) (Fin.cons t u) = simplexMinChartIntegrand b t u := by
  classical
  have hdom :
      simplexIsMinimum (Fin.cons t u) (some 0) ∧ simplexGoodSet b (Fin.cons t u) ↔
        simplexMinChartSet b t u := by
    constructor
    · rintro ⟨hmin, hgood⟩
      have ht : b ≤ t := by simpa [simplexCoordinate] using hgood (some 0)
      have hu : ∀ i, t ≤ u i := by
        intro i
        simpa [simplexCoordinate] using hmin (some (Fin.succ i))
      have hdep0 : t ≤ 1 - (t + ∑ i, u i) := by
        simpa [simplexCoordinate, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] using hmin none
      have hdep : t ≤ 1 - t - ∑ i, u i := by linarith
      refine ⟨ht, hu, ?_⟩
      linarith
    · rintro ⟨ht, hu, hsum⟩
      constructor
      · intro c
        cases c with
        | none =>
          have hdep : t ≤ 1 - t - ∑ i, u i := by linarith
          have hdep0 : t ≤ 1 - (t + ∑ i, u i) := by linarith
          simpa [simplexCoordinate, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] using hdep0
        | some i =>
          cases i using Fin.cases with
          | zero => simpa [simplexCoordinate, Fin.cons_zero] using ht
          | succ i =>
            simpa [simplexCoordinate, Fin.cons_succ] using hu i
      · intro c
        cases c with
        | none =>
          have hdep : b ≤ 1 - (t + ∑ i, u i) := by linarith [ht, hsum]
          simpa [simplexCoordinate, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] using hdep
        | some i =>
          cases i using Fin.cases with
          | zero => simpa [simplexCoordinate, Fin.cons_zero] using ht
          | succ i => simpa [simplexCoordinate, Fin.cons_succ] using (ht.trans (hu i))
  have hweight : simplexWeight (Fin.cons t u) = simplexMinChartKernel t u := by
    simp [simplexWeight, simplexMinChartKernel, simplexCoordinate, Fin.cons_zero,
      Fin.cons_succ, Fin.sum_univ_succ, Fin.prod_univ_succ, Fintype.prod_option]
    ring
  unfold simplexMinIntegrand simplexIntegrand simplexMinChartIntegrand
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  by_cases hmin : simplexIsMinimum (Fin.cons t u) (some 0)
  · by_cases hgood : simplexGoodSet b (Fin.cons t u)
    · have hchart : simplexMinChartSet b t u := hdom.mp ⟨hmin, hgood⟩
      simp only [if_pos hmin, if_pos hchart]
      change (if simplexGoodSet b (Fin.cons t u) then
          simplexWeight (Fin.cons t u) else 0) = simplexMinChartKernel t u
      rw [if_pos hgood, hweight]
    · have hchart : ¬ simplexMinChartSet b t u := fun hc => hgood (hdom.mpr hc).2
      simp only [if_pos hmin, if_neg hchart]
      change (if simplexGoodSet b (Fin.cons t u) then
          simplexWeight (Fin.cons t u) else 0) = 0
      rw [if_neg hgood]
  · have hchart : ¬ simplexMinChartSet b t u := fun hc => hmin (hdom.mpr hc).1
    simp only [if_neg hmin, if_neg hchart]

lemma integral_simplexMinIntegrand_finCons {k : ℕ} {b : ℝ} (hb : 0 < b) :
    ∫ x : Fin (k + 1) → ℝ, simplexMinIntegrand b (some 0) x =
      ∫ t : ℝ, ∫ u : Fin k → ℝ, simplexMinChartIntegrand b t u := by
  classical
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0
  have hvol : MeasurePreserving e (volume : Measure (Fin (k + 1) → ℝ))
      (volume : Measure (ℝ × (Fin k → ℝ))) := by
    simpa [e] using MeasureTheory.volume_preserving_piFinSuccAbove
      (fun _ : Fin (k + 1) => ℝ) 0
  have hfun (t : ℝ) (u : Fin k → ℝ) : e.symm (t, u) = Fin.cons t u := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, MeasurableEquiv.piFinSuccAbove,
        Fin.insertNthEquiv, Fin.insertNth_zero]
    · intro i
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, MeasurableEquiv.piFinSuccAbove,
        Fin.insertNthEquiv]
  have hG : Integrable (fun p : ℝ × (Fin k → ℝ) =>
      simplexMinIntegrand b (some 0) (e.symm p)) (volume.prod volume) := by
    exact (hvol.symm.integrable_comp_emb e.symm.measurableEmbedding).2
      (simplexMinIntegrand_integrable hb (some 0))
  calc
    ∫ x : Fin (k + 1) → ℝ, simplexMinIntegrand b (some 0) x =
        ∫ x, simplexMinIntegrand b (some 0) (e.symm (e x)) := by
          apply integral_congr_ae
          filter_upwards [] with x
          rw [e.symm_apply_apply]
    _ = ∫ p : ℝ × (Fin k → ℝ), simplexMinIntegrand b (some 0) (e.symm p) :=
      hvol.integral_comp' (fun p => simplexMinIntegrand b (some 0) (e.symm p))
    _ = ∫ t : ℝ, ∫ u : Fin k → ℝ,
        simplexMinIntegrand b (some 0) (e.symm (t, u)) := integral_prod _ hG
    _ = ∫ t : ℝ, ∫ u : Fin k → ℝ, simplexMinChartIntegrand b t u := by
      simp_rw [hfun, simplexMinIntegrand_finCons]

lemma integrable_simplexMinChartInner {k : ℕ} {b : ℝ} (hb : 0 < b) :
    Integrable (fun t : ℝ => ∫ u : Fin k → ℝ, simplexMinChartIntegrand b t u) volume := by
  classical
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0
  have hvol : MeasurePreserving e (volume : Measure (Fin (k + 1) → ℝ))
      (volume : Measure (ℝ × (Fin k → ℝ))) := by
    simpa [e] using MeasureTheory.volume_preserving_piFinSuccAbove
      (fun _ : Fin (k + 1) => ℝ) 0
  have hfun (t : ℝ) (u : Fin k → ℝ) : e.symm (t, u) = Fin.cons t u := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, MeasurableEquiv.piFinSuccAbove,
        Fin.insertNthEquiv, Fin.insertNth_zero]
    · intro i
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, MeasurableEquiv.piFinSuccAbove,
        Fin.insertNthEquiv]
  have hF : Integrable (simplexMinIntegrand b (some 0) :
      (Fin (k + 1) → ℝ) → ℝ) volume := simplexMinIntegrand_integrable hb (some 0)
  have hG : Integrable (fun p : ℝ × (Fin k → ℝ) =>
      simplexMinIntegrand b (some 0) (e.symm p)) (volume.prod volume) := by
    exact (hvol.symm.integrable_comp_emb e.symm.measurableEmbedding).2 hF
  have hbase := hG.integral_prod_left
  have hEq : (fun t : ℝ => ∫ u : Fin k → ℝ,
      simplexMinIntegrand b (some 0) (e.symm (t, u))) =ᵐ[volume]
      (fun t => ∫ u : Fin k → ℝ, simplexMinChartIntegrand b t u) := by
    filter_upwards [] with t
    apply integral_congr_ae
    filter_upwards [] with u
    rw [hfun]
    exact simplexMinIntegrand_finCons b t u
  exact hbase.congr hEq

end ArtinPrimitiveRoots.Proofs.b_density_sol
