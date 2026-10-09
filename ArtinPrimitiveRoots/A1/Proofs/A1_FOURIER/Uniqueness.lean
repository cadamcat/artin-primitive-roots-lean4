import ArtinPrimitiveRoots.A1.Proofs.A1_FOURIER.EBasic
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# A1-FOURIER part `a1_fourier_uniqueness` (LEAD)

Fourier uniqueness on the compact quotient `F_S / R`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

namespace A1FourierUniqueness

/-- The diagonal S-integer lattice as an additive subgroup of `F_S`. -/
def latticeSubgroup (S : SData F CE condη) : AddSubgroup S.FS :=
  S.R.toSubring.toAddSubgroup.map S.diag.toAddMonoidHom

theorem mem_latticeSubgroup (S : SData F CE condη) {y : S.FS} :
    y ∈ latticeSubgroup S ↔ ∃ r : S.R, S.diag (r : F) = y := by
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨r, rfl⟩
    exact AddSubgroup.mem_map.mpr ⟨(r : F), r.2, rfl⟩

theorem coe_latticeSubgroup (S : SData F CE condη) :
    (latticeSubgroup S : Set S.FS) = Set.range fun r : S.R => S.diag (r : F) := by
  ext y
  exact mem_latticeSubgroup S

end A1FourierUniqueness

open A1FourierUniqueness

/-- Fourier uniqueness on `F_S / R`: a continuous `R`-periodic function all of whose Fourier
coefficients `∫_K Q(x) e(-x ν) dμ` (`ν ∈ R`) vanish is identically zero.

Proof plan: `F_S ⧸ R` is compact (`A1_LATTICE.diagR_has_compact_cover`) and Hausdorff (`R` is
discrete, hence closed: `A1_LATTICE.diagR_isDiscrete`). The characters `x ↦ e(x ν)` descend to
it (`hself`), are closed under products and conjugation, and separate points: if
`e(x ν) = e(y ν)` for all `ν` then `x - y` lies in the annihilator of `R`, hence in `R`
(`hann`). Stone–Weierstrass (`ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints`)
gives uniform approximation of `Q` by character polynomials, so `∫_K |Q|² = 0`; then `Q = 0`
a.e. on `K`, hence a.e. on `F_S` by periodicity, hence everywhere by continuity (Haar measures
charge nonempty open sets).
Uses: `a1_fourier_e_basic`. Used by: `a1_fourier_poisson_abstract`. -/
theorem a1_fourier_uniqueness (S : SData F CE condη) (D : FieldData F) (A : AddCharData F)
    {mS : MeasurableSpace S.FS} [BorelSpace S.FS]
    (μ : Measure S.FS) [μ.IsAddHaarMeasure]
    (K : Set S.FS) (hKm : MeasurableSet K)
    (hK : ∀ x : S.FS, ∃! p : S.R × S.FS, p.2 ∈ K ∧ x = S.diag (p.1 : F) + p.2)
    (hKμ : μ K = 1)
    (hself : ∀ r s : S.R, S.e A (S.diag (r : F) * S.diag (s : F)) = 1)
    (hann : ∀ y : S.FS, (∀ r : S.R, S.e A (S.diag (r : F) * y) = 1) →
      ∃ r : S.R, y = S.diag (r : F))
    (Q : S.FS → ℂ) (hQ : Continuous Q)
    (hper : ∀ (m : S.R) (x : S.FS), Q (x + S.diag (m : F)) = Q x)
    (hcoef : ∀ ν : S.R, ∫ x in K, Q x * S.e A (-(x * S.diag (ν : F))) ∂μ = 0) :
    ∀ x : S.FS, Q x = 0 := by
  classical
  obtain ⟨he_cont, he_norm, he_add, -⟩ := a1_fourier_e_basic S A
  have he_ne (y : S.FS) : S.e A y ≠ 0 := by
    intro h
    have := he_norm y
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have he0 : S.e A 0 = 1 := by
    have h := he_add 0 0
    rw [add_zero] at h
    have h' : S.e A 0 * 1 = S.e A 0 * S.e A 0 := by rw [mul_one]; exact h
    exact (mul_left_cancel₀ (he_ne 0) h').symm
  have he_neg (y : S.FS) : S.e A (-y) = (starRingEnd ℂ) (S.e A y) := by
    have h1 : S.e A y * S.e A (-y) = 1 := by rw [← he_add, add_neg_cancel, he0]
    have h2 : S.e A y * (starRingEnd ℂ) (S.e A y) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, he_norm]
      norm_num
    exact mul_left_cancel₀ (he_ne y) (h1.trans h2.symm)
  -- periodicity of the characters
  have hchar_per (ν r : S.R) (x : S.FS) :
      S.e A ((x + S.diag (r : F)) * S.diag (ν : F)) = S.e A (x * S.diag (ν : F)) := by
    rw [add_mul, he_add, hself, mul_one]
  -- countability of `R`
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  -- the quotient `F_S / R`
  set Γ : AddSubgroup S.FS := latticeSubgroup S with hΓ
  have hΓclosed : IsClosed (Γ : Set S.FS) := by
    apply AddSubgroup.isClosed_of_isDiscrete
    rw [hΓ, coe_latticeSubgroup]
    exact ArtinPrimitiveRoots.Proofs.A1_LATTICE.diagR_isDiscrete S D
  haveI : IsClosed (Γ : Set S.FS) := hΓclosed
  let X := S.FS ⧸ Γ
  let π : S.FS → X := QuotientAddGroup.mk
  have hπcont : Continuous π := continuous_quotient_mk'
  have hπsurj : Function.Surjective π := QuotientAddGroup.mk_surjective
  have hπeq (x y : S.FS) : π x = π y ↔ ∃ r : S.R, y = x + S.diag (r : F) := by
    change ((x : X) = y) ↔ _
    rw [QuotientAddGroup.eq, mem_latticeSubgroup]
    constructor
    · rintro ⟨r, hr⟩
      exact ⟨r, by rw [hr]; abel⟩
    · rintro ⟨r, hr⟩
      exact ⟨r, by rw [hr]; abel⟩
  haveI : CompactSpace X := by
    obtain ⟨K0, hK0, hcover⟩ := ArtinPrimitiveRoots.Proofs.A1_LATTICE.diagR_has_compact_cover S D
    refine ⟨?_⟩
    have himg : π '' K0 = Set.univ := by
      apply Set.eq_univ_of_forall
      intro q
      obtain ⟨x, rfl⟩ := hπsurj q
      obtain ⟨r, k, hk, rfl⟩ := hcover x
      refine ⟨k, hk, ?_⟩
      exact (hπeq k _).mpr ⟨r, by abel⟩
    rw [← himg]
    exact hK0.image hπcont
  -- lifting periodic continuous functions
  have hlift : ∀ h : S.FS → ℂ, Continuous h → (∀ (r : S.R) (x : S.FS), h (x + S.diag (r : F)) = h x) →
      ∃ hb : C(X, ℂ), ∀ x, hb (π x) = h x := by
    intro h hh hhper
    have hrel : ∀ a b : S.FS, QuotientAddGroup.leftRel Γ a b → h a = h b := by
      intro a b hab
      rw [QuotientAddGroup.leftRel_apply, mem_latticeSubgroup] at hab
      obtain ⟨r, hr⟩ := hab
      have hb : b = a + S.diag (r : F) := by rw [hr]; abel
      rw [hb, hhper]
    exact ⟨⟨fun q => Quotient.liftOn' q h hrel, hh.quotient_liftOn' hrel⟩, fun x => rfl⟩
  -- the characters on the quotient
  have hχex : ∀ ν : S.R, ∃ χ : C(X, ℂ), ∀ x, χ (π x) = S.e A (x * S.diag (ν : F)) := by
    intro ν
    exact hlift _ (he_cont.comp (continuous_id.mul continuous_const))
      (fun r x => hchar_per ν r x)
  choose χ hχ using hχex
  have hext : ∀ a b : C(X, ℂ), (∀ x, a (π x) = b (π x)) → a = b := by
    intro a b hab
    ext q
    obtain ⟨x, rfl⟩ := hπsurj q
    exact hab x
  have hχmul (ν ν' : S.R) : χ ν * χ ν' = χ (ν + ν') := by
    apply hext
    intro x
    rw [ContinuousMap.mul_apply, hχ, hχ, hχ, ← he_add, ← mul_add]
    congr 2
    push_cast
    rw [map_add]
  have hχone : χ 0 = 1 := by
    apply hext
    intro x
    rw [hχ]
    simp [he0]
  have hχstar (ν : S.R) : star (χ ν) = χ (-ν) := by
    apply hext
    intro x
    rw [ContinuousMap.star_apply, hχ, hχ]
    change (starRingEnd ℂ) (S.e A (x * S.diag (ν : F))) = _
    rw [← he_neg]
    congr 1
    push_cast
    rw [map_neg, mul_neg]
  -- the star subalgebra spanned by the characters
  let V : Submodule ℂ C(X, ℂ) := Submodule.span ℂ (Set.range χ)
  have hVmul : ∀ a b : C(X, ℂ), a ∈ V → b ∈ V → a * b ∈ V := by
    intro a b ha hb
    have hab := Submodule.mul_mem_mul ha hb
    rw [Submodule.span_mul_span] at hab
    refine Submodule.span_mono ?_ hab
    intro z hz
    obtain ⟨_, ⟨ν, rfl⟩, _, ⟨ν', rfl⟩, rfl⟩ := Set.mem_mul.mp hz
    exact ⟨ν + ν', (hχmul ν ν').symm⟩
  have hVone : (1 : C(X, ℂ)) ∈ V := Submodule.subset_span ⟨0, hχone⟩
  have hVstar : ∀ a : C(X, ℂ), a ∈ V → star a ∈ V := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ν, rfl⟩ := hx
      rw [hχstar]
      exact Submodule.subset_span ⟨-ν, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [star_add]
      exact V.add_mem hx hy
    | smul c x _ hx =>
      rw [star_smul]
      exact V.smul_mem _ hx
  let Alg : StarSubalgebra ℂ C(X, ℂ) :=
    { carrier := V
      mul_mem' := fun {a b} ha hb => hVmul a b ha hb
      one_mem' := hVone
      add_mem' := fun {a b} ha hb => V.add_mem ha hb
      zero_mem' := V.zero_mem
      algebraMap_mem' := fun c => by
        rw [Algebra.algebraMap_eq_smul_one]
        exact V.smul_mem c hVone
      star_mem' := fun {a} ha => hVstar a ha }
  have hsep : Alg.SeparatesPoints := by
    intro q1 q2 hq
    obtain ⟨x1, rfl⟩ := hπsurj q1
    obtain ⟨x2, rfl⟩ := hπsurj q2
    by_contra hcon
    push Not at hcon
    have hall : ∀ ν : S.R, S.e A (S.diag (ν : F) * (x2 - x1)) = 1 := by
      intro ν
      have h := hcon (χ ν) ⟨χ ν, Submodule.subset_span ⟨ν, rfl⟩, rfl⟩
      simp only [hχ] at h
      have hx2 : x2 * S.diag (ν : F) = (x2 - x1) * S.diag (ν : F) + x1 * S.diag (ν : F) := by
        ring
      rw [hx2, he_add] at h
      have h' : 1 * S.e A (x1 * S.diag (ν : F)) =
          S.e A ((x2 - x1) * S.diag (ν : F)) * S.e A (x1 * S.diag (ν : F)) := by
        rw [one_mul]; exact h
      rw [mul_comm (S.diag (ν : F))]
      exact (mul_right_cancel₀ (he_ne _) h').symm
    obtain ⟨r, hr⟩ := hann _ hall
    exact hq ((hπeq x1 x2).mpr ⟨r, by rw [← hr]; abel⟩)
  have hdense : Alg.topologicalClosure = ⊤ :=
    ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints Alg hsep
  -- the lifted function `Q`
  obtain ⟨Qb, hQb⟩ := hlift Q hQ hper
  have hQbound (x : S.FS) : ‖Q x‖ ≤ ‖Qb‖ := by
    rw [← hQb]
    exact Qb.norm_coe_le_norm (π x)
  -- the measure on `K`
  haveI : IsFiniteMeasure (μ.restrict K) := by
    rw [isFiniteMeasure_restrict, hKμ]
    exact ENNReal.one_ne_top
  have hKreal : μ.real K = 1 := by
    simp [Measure.real, hKμ]
  have hint : ∀ h : C(X, ℂ),
      Integrable (fun x => (starRingEnd ℂ) (Q x) * h (π x)) (μ.restrict K) := by
    intro h
    refine Integrable.of_bound
      ((Complex.continuous_conj.comp hQ).mul (h.continuous.comp hπcont)).aestronglyMeasurable
      (‖Qb‖ * ‖h‖) (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hQbound x) (h.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)
  let Λ : C(X, ℂ) → ℂ := fun h => ∫ x in K, (starRingEnd ℂ) (Q x) * h (π x) ∂μ
  have hΛsub (a b : C(X, ℂ)) : Λ a - Λ b =
      ∫ x in K, (starRingEnd ℂ) (Q x) * (a - b) (π x) ∂μ := by
    simp only [Λ]
    rw [← integral_sub (hint a) (hint b)]
    congr 1
    funext x
    rw [ContinuousMap.sub_apply, mul_sub]
  have hΛcont : Continuous Λ := by
    apply LipschitzWith.continuous (K := ⟨‖Qb‖, norm_nonneg _⟩)
    apply LipschitzWith.of_dist_le_mul
    intro a b
    rw [dist_eq_norm, dist_eq_norm, hΛsub]
    change _ ≤ ‖Qb‖ * ‖a - b‖
    have hb : ∀ x ∈ K, ‖(starRingEnd ℂ) (Q x) * (a - b) (π x)‖ ≤ ‖Qb‖ * ‖a - b‖ := by
      intro x _
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (hQbound x) ((a - b).norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)
    have := norm_setIntegral_le_of_norm_le_const (by rw [hKμ]; exact ENNReal.one_lt_top) hb
    rw [hKreal, mul_one] at this
    simpa using this
  have hΛadd (a b : C(X, ℂ)) : Λ (a + b) = Λ a + Λ b := by
    simp only [Λ]
    rw [← integral_add (hint a) (hint b)]
    congr 1
    funext x
    rw [ContinuousMap.add_apply, mul_add]
  have hΛsmul (c : ℂ) (a : C(X, ℂ)) : Λ (c • a) = c * Λ a := by
    simp only [Λ]
    rw [← integral_const_mul]
    congr 1
    funext x
    rw [ContinuousMap.smul_apply, smul_eq_mul]
    ring
  have hΛχ (ν : S.R) : Λ (χ ν) = 0 := by
    have h := congrArg (starRingEnd ℂ) (hcoef ν)
    rw [map_zero, ← integral_conj] at h
    rw [← h]
    simp only [Λ]
    congr 1
    funext x
    rw [hχ, map_mul, he_neg, Complex.conj_conj]
  have hΛV : ∀ a ∈ V, Λ a = 0 := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ν, rfl⟩ := hx
      exact hΛχ ν
    | zero =>
      simp [Λ]
    | add x y _ _ hx hy => rw [hΛadd, hx, hy, add_zero]
    | smul c x _ hx => rw [hΛsmul, hx, mul_zero]
  have hΛQ : Λ Qb = 0 := by
    have hmem : Qb ∈ Alg.topologicalClosure := by rw [hdense]; trivial
    have hclosed : IsClosed {h : C(X, ℂ) | Λ h = 0} := isClosed_eq hΛcont continuous_const
    have hsub : (Alg : Set C(X, ℂ)) ⊆ {h : C(X, ℂ) | Λ h = 0} := fun a ha => hΛV a ha
    exact closure_minimal hsub hclosed hmem
  -- `∫_K |Q|² = 0`
  have hsq : ∫ x in K, ‖Q x‖ ^ 2 ∂μ = 0 := by
    have h1 : Λ Qb = ((∫ x in K, ‖Q x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
      simp only [Λ]
      rw [← integral_complex_ofReal]
      congr 1
      funext x
      rw [hQb, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hΛQ] at h1
    exact_mod_cast h1.symm
  have hsq_int : Integrable (fun x => ‖Q x‖ ^ 2) (μ.restrict K) := by
    refine Integrable.of_bound (hQ.norm.pow 2).aestronglyMeasurable (‖Qb‖ ^ 2)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hQbound x) 2
  have hae : (fun x => ‖Q x‖ ^ 2) =ᵐ[μ.restrict K] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => by positivity) hsq_int).mp hsq
  -- the null set `K ∩ {Q ≠ 0}`
  set Z : Set S.FS := {x | Q x ≠ 0} with hZ
  have hZK : μ (Z ∩ K) = 0 := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hKm] at hae
    rw [ae_iff] at hae
    refine measure_mono_null ?_ hae
    rintro x ⟨hxZ, hxK⟩ hcon
    apply hxZ
    have := hcon hxK
    simpa using this
  have hZsub : Z ⊆ ⋃ r : S.R, (fun x => x + S.diag (r : F)) ⁻¹' (Z ∩ K) := by
    intro x hx
    obtain ⟨⟨r, k⟩, ⟨hk, hxk⟩, -⟩ := hK x
    refine Set.mem_iUnion.mpr ⟨-r, ?_⟩
    have hk' : x + S.diag ((-r : S.R) : F) = k := by
      rw [hxk]
      push_cast
      rw [map_neg]
      abel
    change x + S.diag ((-r : S.R) : F) ∈ Z ∩ K
    rw [hk']
    refine ⟨?_, hk⟩
    change Q k ≠ 0
    rw [← hk', hper]
    exact hx
  have hZnull : μ Z = 0 := by
    refine measure_mono_null hZsub (measure_iUnion_null fun r => ?_)
    rw [measure_preimage_add_right]
    exact hZK
  have hZopen : IsOpen Z := isOpen_ne_fun hQ continuous_const
  have hZempty : Z = ∅ := (hZopen.measure_eq_zero_iff μ).mp hZnull
  intro x
  by_contra hx
  have : x ∈ Z := hx
  rw [hZempty] at this
  exact this

end ArtinPrimitiveRoots.A1
