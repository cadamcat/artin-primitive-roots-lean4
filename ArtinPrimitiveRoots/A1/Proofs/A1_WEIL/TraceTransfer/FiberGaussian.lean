import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.TraceTransfer.PadicGaussian
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ClassFieldTheory.AlgebraicNumberTheory.Idele.LocallyCompact
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Products of local Gaussians over a finite family of places

Given an additive homeomorphism `Φ : (Fin n → ℚ_[p]) ≃ₜ+ Π_w F_w` under which the product of
the local phases `ψ_w(α_w x_w²)` becomes a product of one-variable phases `g_i(y_i)`, the
product of the truncated local Gaussians is a positive multiple of the product of the
one-variable integrals over large balls. The comparison of the two exhaustions uses the lead's
`large_subgroup_phase_integrals_eq`; the change of variables uses uniqueness of Haar measure.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.weil_trace_opus

open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.Proofs.a1_weil_sol

attribute [local instance] padicMeasurableSpace padicBorelSpace

variable {F : Type} [Field F] [NumberField F]

local instance fiberMeasurable (v : FinPlace F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance fiberBorel (v : FinPlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

/-- The valuation ball `{x | v(x) ≤ exp k}` as an additive subgroup. -/
def valBall (v : FinPlace F) (k : ℤ) : AddSubgroup (v.adicCompletion F) where
  carrier := {x | Valued.v x ≤ WithZero.exp k}
  add_mem' := by
    intro x y hx hy
    exact (Valued.v.map_add x y).trans (max_le hx hy)
  zero_mem' := by
    change Valued.v (0 : v.adicCompletion F) ≤ WithZero.exp k
    rw [map_zero]
    exact zero_le'
  neg_mem' := by
    intro x hx
    change Valued.v (-x) ≤ WithZero.exp k
    rw [Valuation.map_neg]
    exact hx

theorem mem_valBall {v : FinPlace F} {k : ℤ} {x : v.adicCompletion F} :
    x ∈ valBall v k ↔ Valued.v x ≤ WithZero.exp k := Iff.rfl

theorem valBall_mono (v : FinPlace F) {k l : ℤ} (h : k ≤ l) : valBall v k ≤ valBall v l :=
  fun _ hx => hx.trans (WithZero.exp_le_exp.mpr h)

theorem valBall_eq_image (v : FinPlace F) (k : ℤ) :
    ∃ b : v.adicCompletion F, b ≠ 0 ∧
      (valBall v k : Set (v.adicCompletion F)) =
        (fun x => b * x) '' (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  obtain ⟨b, hb⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp k)
  have hb0 : b ≠ 0 := by
    intro h
    apply WithZero.exp_ne_zero (a := k)
    rw [← hb, h, map_zero]
  refine ⟨b, hb0, ?_⟩
  ext x
  simp only [SetLike.mem_coe, mem_valBall, Set.mem_image]
  constructor
  · intro hx
    refine ⟨b⁻¹ * x, ?_, by field_simp⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, hb]
    calc (WithZero.exp k)⁻¹ * Valued.v x ≤ (WithZero.exp k)⁻¹ * WithZero.exp k :=
          mul_le_mul' (le_refl _) hx
      _ = 1 := inv_mul_cancel₀ (WithZero.exp_ne_zero)
  · rintro ⟨y, hy, rfl⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hy
    rw [map_mul, hb]
    calc WithZero.exp k * Valued.v y ≤ WithZero.exp k * 1 := mul_le_mul' (le_refl _) hy
      _ = WithZero.exp k := mul_one _

theorem integers_isCompact (v : FinPlace F) :
    IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  have hset : (v.adicCompletionIntegers F : Set (v.adicCompletion F)) =
      Metric.closedBall (0 : v.adicCompletion F) 1 := by
    ext x
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, Metric.mem_closedBall,
      dist_zero_right]
    exact (Valued.toNormedField.norm_le_one_iff (L := v.adicCompletion F)
      (Γ₀ := WithZero (Multiplicative ℤ)) (x := x)).symm
  rw [hset]
  exact isCompact_closedBall 0 1

theorem valBall_isCompact (v : FinPlace F) (k : ℤ) :
    IsCompact (valBall v k : Set (v.adicCompletion F)) := by
  obtain ⟨b, -, hb⟩ := valBall_eq_image v k
  rw [hb]
  exact (integers_isCompact v).image (continuous_const.mul continuous_id)

theorem valBall_isOpen (v : FinPlace F) (k : ℤ) :
    IsOpen (valBall v k : Set (v.adicCompletion F)) := by
  obtain ⟨b, hb0, hb⟩ := valBall_eq_image v k
  rw [hb]
  exact (Homeomorph.mulLeft₀ b hb0).isOpenMap _ (Valued.isOpen_valuationSubring _)

/-- Every compact set lies in some valuation ball. -/
theorem exists_valBall_superset (v : FinPlace F) {S : Set (v.adicCompletion F)}
    (hS : IsCompact S) : ∃ k : ℕ, S ⊆ valBall v k := by
  have hcover : S ⊆ ⋃ k : ℕ, (valBall v k : Set (v.adicCompletion F)) := by
    intro x _
    rw [Set.mem_iUnion]
    by_cases hx : Valued.v x = 0
    · exact ⟨0, by rw [SetLike.mem_coe, mem_valBall, hx]; exact zero_le'⟩
    · refine ⟨(WithZero.log (Valued.v x)).toNat, ?_⟩
      rw [SetLike.mem_coe, mem_valBall]
      calc Valued.v x = WithZero.exp (WithZero.log (Valued.v x)) := (WithZero.exp_log hx).symm
        _ ≤ WithZero.exp ((WithZero.log (Valued.v x)).toNat : ℤ) :=
          WithZero.exp_le_exp.mpr (Int.self_le_toNat _)
  exact hS.elim_directed_cover _ (fun k => valBall_isOpen v k) hcover
    (fun k l => ⟨max k l, valBall_mono v (by exact_mod_cast le_max_left k l),
      valBall_mono v (by exact_mod_cast le_max_right k l)⟩)

/-- On a small ball the quadratic phase is trivial. -/
theorem exists_quadratic_trivial_ball (A : AddCharData F) (v : FinPlace F)
    (α : (v.adicCompletion F)ˣ) :
    ∃ k : ℤ, k ≤ 0 ∧ ∀ y ∈ valBall v k, A.ψ v ((α : v.adicCompletion F) * y ^ 2) = 1 := by
  have hα : Valued.v (α : v.adicCompletion F) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact α.ne_zero
  set m := WithZero.log (Valued.v (α : v.adicCompletion F))
  refine ⟨-|m|, by simp, fun y hy => A.integral v _ ?_⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_pow, ← WithZero.exp_log hα]
  calc WithZero.exp m * Valued.v y ^ 2 ≤ WithZero.exp m * WithZero.exp (-|m|) ^ 2 :=
        mul_le_mul' (le_refl _) (pow_le_pow_left₀ zero_le' hy 2)
    _ = WithZero.exp (m - 2 * |m|) := by
        rw [← WithZero.exp_nsmul, ← WithZero.exp_add]
        congr 1
        simp only [smul_neg, nsmul_eq_mul, Nat.cast_ofNat]
        ring
    _ ≤ 1 := by
        rw [← WithZero.exp_zero]
        exact WithZero.exp_le_exp.mpr (by linarith [le_abs_self m, neg_abs_le m])

/-- The annihilator of a ball under a nontrivial continuous character is bounded. -/
theorem exists_annihilator_ball (A : AddCharData F) (v : FinPlace F)
    (hreg : LocalCharacterRegular A v) (β : (v.adicCompletion F)ˣ) (k : ℤ) :
    ∃ l : ℕ, ∀ x : v.adicCompletion F,
      (∀ y ∈ valBall v k, A.ψ v ((β : v.adicCompletion F) * x * y) = 1) → x ∈ valBall v l := by
  obtain ⟨z, hz⟩ : ∃ z, A.ψ v z ≠ 1 := by
    by_contra h
    push_neg at h
    exact hreg.2.1 (DFunLike.ext _ _ h)
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, AddChar.map_zero_eq_one] at hz
    exact hz rfl
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp (valBall_isOpen v k) 0 (valBall v k).zero_mem
  have hβ : 0 < ‖(β : v.adicCompletion F)‖ := norm_pos_iff.mpr β.ne_zero
  let B : ℝ := ‖z‖ / (‖(β : v.adicCompletion F)‖ * ρ)
  obtain ⟨l, hl⟩ := exists_valBall_superset v (isCompact_closedBall (0 : v.adicCompletion F) B)
  refine ⟨l, fun x hx => hl ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hlarge
  push_neg at hlarge
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlarge
    exact (not_lt.mpr (by positivity : (0 : ℝ) ≤ B)) hlarge
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let y := z / ((β : v.adicCompletion F) * x)
  have hy : y ∈ valBall v k := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right]
    simp only [y, norm_div, norm_mul]
    rw [div_lt_iff₀ (mul_pos hβ hxpos)]
    have := (div_lt_iff₀ (mul_pos hβ hρ)).mp hlarge
    nlinarith
  apply hz
  have := hx y hy
  rwa [show (β : v.adicCompletion F) * x * y = z by
    simp only [y]
    field_simp [β.ne_zero, hx0]] at this

theorem mem_addSubgroup_pi_univ {ι : Type*} {G : ι → Type*} [∀ i, AddGroup (G i)]
    (H : ∀ i, AddSubgroup (G i)) (x : ∀ i, G i) :
    x ∈ AddSubgroup.pi Set.univ H ↔ ∀ i, x i ∈ H i := by
  rw [← SetLike.mem_coe, AddSubgroup.coe_pi]
  simp

/-- The product of the truncated local Gaussians over a finite family of places is a positive
multiple of the product of one-variable integrals in the coordinates `Φ`. -/
theorem fiber_gaussian_eq {ι : Type} [Fintype ι] (pl : ι → FinPlace F) (A : AddCharData F)
    (hreg : ∀ w, LocalCharacterRegular A (pl w))
    (μ : ∀ w, Measure ((pl w).adicCompletion F)) [hμ : ∀ w, (μ w).IsAddHaarMeasure]
    (α : ∀ w, ((pl w).adicCompletion F)ˣ)
    {n : ℕ} (p : ℕ) [Fact p.Prime] (lam : Measure ℚ_[p]) [lam.IsAddHaarMeasure]
    (g : Fin n → ℚ_[p] → ℂ)
    (Φ : (Fin n → ℚ_[p]) ≃ₜ+ ((w : ι) → (pl w).adicCompletion F))
    (hΦ : ∀ y, ∏ w, A.ψ (pl w) ((α w : (pl w).adicCompletion F) * Φ y w ^ 2) =
      ∏ i, g i (y i)) :
    ∃ r : ℝ, 0 < r ∧ ∃ N0 : ℕ, ∃ s0 : ℤ, ∀ N, N0 ≤ N → ∀ s, s0 ≤ s →
      ∏ w, quadraticIntegral A (pl w) (μ w) (α w) N =
        r * ∏ i, ∫ y in (padicBall p s : Set ℚ_[p]), g i y ∂lam := by
  classical
  let μV : Measure ((w : ι) → (pl w).adicCompletion F) := Measure.pi μ
  haveI : μV.IsAddHaarMeasure := Measure.pi.isAddHaarMeasure μ
  let lamN : Measure (Fin n → ℚ_[p]) := Measure.pi fun _ => lam
  haveI : lamN.IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let ν := Measure.map Φ lamN
  haveI : ν.IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map lamN Φ
  have hνeq : ν = Measure.addHaarScalarFactor ν μV • μV := Measure.isAddLeftInvariant_eq_smul ν μV
  set c := Measure.addHaarScalarFactor ν μV with hcdef
  have hc : (c : ℝ) ≠ 0 := by
    intro h0
    have hc0 : c = 0 := by exact_mod_cast h0
    have hpos := isOpen_univ.measure_pos ν (Set.univ_nonempty)
    rw [hνeq, hc0, zero_smul] at hpos
    exact lt_irrefl _ hpos
  have hcpos : (0 : ℝ) < c := lt_of_le_of_ne c.2 (Ne.symm hc)
  refine ⟨(c : ℝ)⁻¹, inv_pos.mpr hcpos, ?_⟩
  -- small balls on which the quadratic phases are trivial, and bounds for annihilators
  choose k hk0 hk using fun w => exists_quadratic_trivial_ball A (pl w) (α w)
  have h2α (w : ι) : (2 : (pl w).adicCompletion F) * (α w : (pl w).adicCompletion F) ≠ 0 :=
    mul_ne_zero two_ne_zero (α w).ne_zero
  choose l hl using fun w => exists_annihilator_ball A (pl w) (hreg w)
    (Units.mk0 _ (h2α w)) (k w)
  let N0 : ℕ := ∑ w, l w
  have hlN0 (w : ι) : l w ≤ N0 := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ w)
  let P : Set ((w : ι) → (pl w).adicCompletion F) :=
    Set.pi Set.univ (fun w => (valBall (pl w) N0 : Set ((pl w).adicCompletion F)))
  have hP : IsCompact P := isCompact_univ_pi fun w => valBall_isCompact (pl w) N0
  have hQ : IsCompact (Φ ⁻¹' P) := Φ.toHomeomorph.isCompact_preimage.mpr hP
  choose sI hsI using fun i : Fin n =>
    exists_padicBall_superset (p := p) (hQ.image (continuous_apply i))
  refine ⟨N0, ∑ i, |sI i|, ?_⟩
  intro N hN s hs
  have hsi (i : Fin n) : sI i ≤ s :=
    ((le_abs_self (sI i)).trans (Finset.single_le_sum (fun j _ => abs_nonneg (sI j))
      (Finset.mem_univ i))).trans hs
  let U : AddSubgroup ((w : ι) → (pl w).adicCompletion F) :=
    AddSubgroup.pi Set.univ (fun w => valBall (pl w) N)
  let Bx : AddSubgroup (Fin n → ℚ_[p]) := AddSubgroup.pi Set.univ (fun _ => padicBall p s)
  let V' : AddSubgroup ((w : ι) → (pl w).adicCompletion F) :=
    Bx.map Φ.toAddEquiv.toAddMonoidHom
  let K : AddSubgroup ((w : ι) → (pl w).adicCompletion F) :=
    AddSubgroup.pi Set.univ (fun w => valBall (pl w) (k w))
  have hBx : (Bx : Set (Fin n → ℚ_[p])) = Set.pi Set.univ (fun _ => (padicBall p s : Set ℚ_[p])) :=
    AddSubgroup.coe_pi _ _
  have hV'coe : (V' : Set ((w : ι) → (pl w).adicCompletion F)) = Φ '' (Bx : Set _) :=
    AddSubgroup.coe_map _ _
  have hPV : ∀ x ∈ P, x ∈ V' := by
    intro x hx
    have hq : Φ.symm x ∈ Φ ⁻¹' P := by
      simpa only [Set.mem_preimage, ContinuousAddEquiv.apply_symm_apply] using hx
    have hbox : Φ.symm x ∈ Bx := by
      rw [← SetLike.mem_coe, hBx]
      intro i _
      exact padicBall_mono (hsi i) (hsI i (sI i) le_rfl ⟨Φ.symm x, hq, rfl⟩)
    rw [← SetLike.mem_coe, hV'coe]
    exact ⟨Φ.symm x, hbox, ContinuousAddEquiv.apply_symm_apply Φ x⟩
  let f : ((w : ι) → (pl w).adicCompletion F) → ℂ :=
    fun x => ∏ w, A.ψ (pl w) ((α w : (pl w).adicCompletion F) * x w ^ 2)
  let χ : ((w : ι) → (pl w).adicCompletion F) → AddChar ((w : ι) → (pl w).adicCompletion F) ℂ :=
    fun x =>
      { toFun := fun y => ∏ w, A.ψ (pl w)
          (2 * (α w : (pl w).adicCompletion F) * x w * y w)
        map_zero_eq_one' := by simp
        map_add_eq_mul' := by
          intro y z
          rw [← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl
          intro w _
          rw [← AddChar.map_add_eq_mul, Pi.add_apply, mul_add] }
  have hχ (x y : (w : ι) → (pl w).adicCompletion F) :
      χ x y = ∏ w, A.ψ (pl w) (2 * (α w : (pl w).adicCompletion F) * x w * y w) := rfl
  have hfcont : Continuous f :=
    continuous_finset_prod _ fun w _ =>
      (hreg w).1.comp (continuous_const.mul ((continuous_apply w).pow 2))
  have hfbound : ∀ x, ‖f x‖ ≤ 1 := by
    intro x
    simp only [f, norm_prod, (hreg _).2.2, Finset.prod_const_one, le_refl]
  have hKcoe : (K : Set ((w : ι) → (pl w).adicCompletion F)) =
      Set.pi Set.univ (fun w => (valBall (pl w) (k w) : Set _)) := AddSubgroup.coe_pi _ _
  have hKopen : IsOpen (K : Set ((w : ι) → (pl w).adicCompletion F)) := by
    rw [hKcoe]
    exact isOpen_set_pi Set.finite_univ fun w _ => valBall_isOpen (pl w) (k w)
  have hKcompact : IsCompact (K : Set ((w : ι) → (pl w).adicCompletion F)) := by
    rw [hKcoe]
    exact isCompact_univ_pi fun w => valBall_isCompact (pl w) (k w)
  have hKmass : (μV (K : Set _)).toReal ≠ 0 :=
    (ENNReal.toReal_pos (hKopen.measure_pos μV ⟨0, K.zero_mem⟩).ne'
      hKcompact.measure_lt_top.ne).ne'
  have hUcompact : IsCompact (U : Set ((w : ι) → (pl w).adicCompletion F)) := by
    rw [AddSubgroup.coe_pi]
    exact isCompact_univ_pi fun w => valBall_isCompact (pl w) N
  have hBxcompact : IsCompact (Bx : Set (Fin n → ℚ_[p])) := by
    rw [hBx]
    exact isCompact_univ_pi fun _ => padicBall_isCompact s
  have hV'compact : IsCompact (V' : Set ((w : ι) → (pl w).adicCompletion F)) := by
    rw [hV'coe]
    exact hBxcompact.image Φ.continuous_toFun
  have hKP : ∀ x ∈ K, x ∈ P := by
    intro x hx w _
    have := (mem_addSubgroup_pi_univ _ _).mp hx w
    exact valBall_mono (pl w) (by have := hk0 w; omega) this
  have hCw : ∀ x : (w : ι) → (pl w).adicCompletion F, (∀ y ∈ K, χ x y = 1) →
      ∀ w, x w ∈ valBall (pl w) (l w) := by
    intro x hx w
    apply hl w
    intro t ht
    have hy : (Pi.single w t : (w : ι) → (pl w).adicCompletion F) ∈ K := by
      apply (mem_addSubgroup_pi_univ _ _).mpr
      intro w'
      by_cases hw : w' = w
      · subst hw
        simpa only [Pi.single_eq_same] using ht
      · simp only [Pi.single_eq_of_ne hw]
        exact (valBall (pl w') (k w')).zero_mem
    have h := hx _ hy
    rw [hχ, Finset.prod_eq_single w] at h
    · simpa only [Pi.single_eq_same, Units.val_mk0] using h
    · intro w' _ hw'
      rw [Pi.single_eq_of_ne hw', mul_zero, AddChar.map_zero_eq_one]
    · intro hw
      exact absurd (Finset.mem_univ w) hw
  have havg := large_subgroup_phase_integrals_eq μV U V' K hUcompact hV'compact hKcompact hKmass
    (fun x hx => (mem_addSubgroup_pi_univ _ _).mpr fun w =>
      valBall_mono (pl w) (by have := hk0 w; omega) ((mem_addSubgroup_pi_univ _ _).mp hx w))
    (fun x hx => hPV x (hKP x hx)) f hfcont hfbound χ
    (by
      intro x y hy
      simp only [f, hχ, Pi.add_apply]
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro w _
      have hyw := hk w (y w) ((mem_addSubgroup_pi_univ _ _).mp hy w)
      have : (α w : (pl w).adicCompletion F) * (y w + x w) ^ 2 =
          (α w : (pl w).adicCompletion F) * x w ^ 2 +
            2 * (α w : (pl w).adicCompletion F) * x w * y w +
              (α w : (pl w).adicCompletion F) * y w ^ 2 := by ring
      rw [this, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hyw, mul_one])
    (by
      have : {x : (w : ι) → (pl w).adicCompletion F | ∀ y ∈ K, χ x y = 1} =
          ⋂ y ∈ (K : Set ((w : ι) → (pl w).adicCompletion F)), {x | χ x y = 1} := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_iInter, SetLike.mem_coe]
      rw [this]
      apply IsClosed.measurableSet
      apply isClosed_biInter
      intro y _
      apply isClosed_eq _ continuous_const
      simp only [hχ]
      exact continuous_finset_prod _ fun w _ =>
        (hreg w).1.comp ((continuous_const.mul (continuous_apply w)).mul continuous_const))
    (fun x hx => (mem_addSubgroup_pi_univ _ _).mpr fun w =>
      valBall_mono (pl w) (by have := hlN0 w; omega) (hCw x hx w))
    (fun x hx => hPV x fun w _ => valBall_mono (pl w) (by exact_mod_cast hlN0 w) (hCw x hx w))
  -- the left side is the product of the local truncated Gaussians
  have hleft : (∫ x in (U : Set ((w : ι) → (pl w).adicCompletion F)), f x ∂μV) =
      ∏ w, quadraticIntegral A (pl w) (μ w) (α w) N := by
    rw [AddSubgroup.coe_pi]
    change (∫ x in Set.pi Set.univ (fun w => (valBall (pl w) N : Set _)), f x ∂Measure.pi μ) = _
    rw [Measure.restrict_pi_pi]
    exact integral_fintype_prod_eq_prod (𝕜 := ℂ)
      (fun w t => A.ψ (pl w) ((α w : (pl w).adicCompletion F) * t ^ 2))
  -- the right side, through the Haar comparison and the coordinates
  have hright : (∫ x in (V' : Set ((w : ι) → (pl w).adicCompletion F)), f x ∂ν) =
      ∏ i, ∫ y in (padicBall p s : Set ℚ_[p]), g i y ∂lam := by
    let e := Φ.toHomeomorph.toMeasurableEquiv
    have he : (e : (Fin n → ℚ_[p]) → (w : ι) → (pl w).adicCompletion F) = Φ := rfl
    change (∫ x in (V' : Set _), f x ∂Measure.map e lamN) = _
    rw [setIntegral_map_equiv, he, hV'coe,
      Set.preimage_image_eq _ (show Function.Injective (Φ : (Fin n → ℚ_[p]) → _) from
        fun a b h => Φ.toAddEquiv.injective h), hBx]
    simp only [f, hΦ]
    change (∫ y in Set.pi Set.univ (fun _ => (padicBall p s : Set ℚ_[p])),
      ∏ i, g i (y i) ∂Measure.pi fun _ => lam) = _
    rw [Measure.restrict_pi_pi]
    exact integral_fintype_prod_eq_prod (𝕜 := ℂ) (fun i t => g i t)
  have hscale : (∫ x in (V' : Set ((w : ι) → (pl w).adicCompletion F)), f x ∂ν) =
      (c : ℂ) * ∫ x in (V' : Set ((w : ι) → (pl w).adicCompletion F)), f x ∂μV := by
    rw [hνeq, Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def,
      Complex.real_smul]
  rw [← hleft, havg, ← hright, hscale, ← mul_assoc]
  push_cast
  rw [inv_mul_cancel₀ (by exact_mod_cast hc), one_mul]

end ArtinPrimitiveRoots.Proofs.weil_trace_opus
