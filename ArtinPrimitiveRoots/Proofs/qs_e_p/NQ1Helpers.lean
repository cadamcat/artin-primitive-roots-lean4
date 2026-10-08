import ArtinPrimitiveRoots.A1.Residue
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-BOOT».Boot
import ArtinPrimitiveRoots.Proofs.qs_nq0_sol.ResidueUnits
import ClassFieldTheory.AlgebraicNumberTheory.SUnit.Rank
import Mathlib.GroupTheory.FiniteAbelian.Basic

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped NumberField Classical
open scoped nonZeroDivisors
open ArtinPrimitiveRoots.A1

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- The square-class quotient of the group of `S`-units. -/
abbrev qsSUnitSquareClasses (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  SUnitGroup (K := K) S ⧸
    (powMonoidHom (α := SUnitGroup (K := K) S) 2).range

theorem qsSUnitSquareClasses_finite (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Finite (qsSUnitSquareClasses (K := K) S) := by
  classical
  let G := SUnitGroup (K := K) S
  have hmodule : Module.Finite ℤ (Additive G) := SUnitGroup.moduleFinite (K := K) S
  letI : Module.Finite ℤ (Additive G) := hmodule
  letI : AddGroup.FG (Additive G) := Module.Finite.iff_addGroup_fg.mp hmodule
  letI : Group.FG G := GroupFG.iff_add_fg.mpr (Module.Finite.iff_addGroup_fg.mp hmodule)
  have hindex : (powMonoidHom (α := G) 2).range.FiniteIndex :=
    Subgroup.finiteIndex_range_powMonoidHom_of_fg G (by norm_num)
  exact Subgroup.finiteIndex_iff_finite_quotient.mp hindex

theorem qsNormT_mono_NQ1 {T U : Finset (HeightOneSpectrum (𝓞 K))}
    (hTU : T ⊆ U) : qsNormT T ≤ qsNormT U := by
  classical
  unfold qsNormT
  apply Finset.prod_le_prod_of_subset_of_one_le hTU
  intro v hv hvT
  have hn : 0 < Ideal.absNorm v.asIdeal :=
    Ideal.absNorm_pos_of_nonZeroDivisors ⟨v.asIdeal,
      mem_nonZeroDivisors_of_ne_zero (by simpa [Ideal.zero_eq_bot] using v.ne_bot)⟩
  omega

theorem qs_decompose_at_S_NQ1
    (S S' T : Finset (HeightOneSpectrum (𝓞 K))) (hSS' : S ⊆ S')
    (hTS : Disjoint T S) : T = (T \ S') ∪ (T ∩ (S' \ S)) := by
  classical
  ext v
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
  constructor
  · intro hvT
    by_cases hvS' : v ∈ S'
    · right
      refine ⟨hvT, hvS', ?_⟩
      intro hvS
      exact (Finset.disjoint_left.mp hTS hvT) hvS
    · left
      exact ⟨hvT, hvS'⟩
  · intro hv
    rcases hv with ⟨hvT, _⟩ | ⟨hvT, _, _⟩
    · exact hvT
    · exact hvT

private theorem qs_residue_repr_NQ1 (v : HeightOneSpectrum (𝓞 K)) (x : K)
    (a b : 𝓞 K) (hb : b ∉ v.asIdeal)
    (hab : x * algebraMap (𝓞 K) K b = algebraMap (𝓞 K) K a) :
    residue v x * Ideal.Quotient.mk v.asIdeal b = Ideal.Quotient.mk v.asIdeal a := by
  classical
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hex : ∃ ab : 𝓞 K × 𝓞 K, ab.2 ∉ v.asIdeal ∧
      x * algebraMap (𝓞 K) K ab.2 = algebraMap (𝓞 K) K ab.1 := ⟨(a, b), hb, hab⟩
  have hcross : hex.choose.1 * b = a * hex.choose.2 := by
    apply IsFractionRing.injective (𝓞 K) K
    simp only [map_mul]
    rw [← hex.choose_spec.2, ← hab]
    ring
  have hqcross := congrArg (Ideal.Quotient.mk v.asIdeal) hcross
  have hbq : Ideal.Quotient.mk v.asIdeal b ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hb
  have hdq : Ideal.Quotient.mk v.asIdeal hex.choose.2 ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hex.choose_spec.1
  unfold residue
  have hqcross' : Ideal.Quotient.mk v.asIdeal a * Ideal.Quotient.mk v.asIdeal hex.choose.2 =
      Ideal.Quotient.mk v.asIdeal hex.choose.1 * Ideal.Quotient.mk v.asIdeal b := by
    simpa only [map_mul] using hqcross.symm
  rw [dif_pos hex]
  calc
    (Ideal.Quotient.mk v.asIdeal hex.choose.1 *
        (Ideal.Quotient.mk v.asIdeal hex.choose.2)⁻¹) *
        Ideal.Quotient.mk v.asIdeal b =
      (Ideal.Quotient.mk v.asIdeal hex.choose.1 * Ideal.Quotient.mk v.asIdeal b) *
        (Ideal.Quotient.mk v.asIdeal hex.choose.2)⁻¹ := by ring
    _ = (Ideal.Quotient.mk v.asIdeal a * Ideal.Quotient.mk v.asIdeal hex.choose.2) *
        (Ideal.Quotient.mk v.asIdeal hex.choose.2)⁻¹ := by rw [← hqcross']
    _ = Ideal.Quotient.mk v.asIdeal a := by
      rw [mul_assoc, mul_inv_cancel₀ hdq, mul_one]

private theorem qs_residue_mul_NQ1 (v : HeightOneSpectrum (𝓞 K)) (x y : K)
    (hx : v.valuation K x ≤ 1) (hy : v.valuation K y ≤ 1) :
    residue v (x * y) = residue v x * residue v y := by
  classical
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  obtain ⟨a, b, hab⟩ := v.exists_primeCompl_mul_eq_of_integer x hx
  obtain ⟨c, d, hcd⟩ := v.exists_primeCompl_mul_eq_of_integer y hy
  have hbd : b.val * d.val ∉ v.asIdeal := fun h =>
    (v.isPrime.mem_or_mem h).elim b.property d.property
  have hrep : (x * y) * algebraMap (𝓞 K) K (b.val * d.val) =
      algebraMap (𝓞 K) K (a * c) := by
    rw [map_mul, map_mul, ← hab, ← hcd]
    ring
  have hxy := qs_residue_repr_NQ1 v _ _ _ hbd hrep
  have hx' := qs_residue_repr_NQ1 v _ _ _ b.property hab
  have hy' := qs_residue_repr_NQ1 v _ _ _ d.property hcd
  have hbdq : Ideal.Quotient.mk v.asIdeal (b.val * d.val) ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hbd
  apply (mul_right_cancel₀ hbdq)
  calc
    residue v (x * y) * Ideal.Quotient.mk v.asIdeal (b.val * d.val) =
        Ideal.Quotient.mk v.asIdeal (a * c) := hxy
    _ = (residue v x * residue v y) *
        Ideal.Quotient.mk v.asIdeal (b.val * d.val) := by
      calc
        _ = Ideal.Quotient.mk v.asIdeal a * Ideal.Quotient.mk v.asIdeal c := by
          rw [map_mul]
        _ = (residue v x * Ideal.Quotient.mk v.asIdeal b.val) *
            (residue v y * Ideal.Quotient.mk v.asIdeal d.val) := by
          rw [hx', hy']
        _ = (residue v x * residue v y) *
            (Ideal.Quotient.mk v.asIdeal b.val * Ideal.Quotient.mk v.asIdeal d.val) := by ring
        _ = (residue v x * residue v y) *
            Ideal.Quotient.mk v.asIdeal (b.val * d.val) := by rw [map_mul]

theorem qs_exterior_count_NQ1
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (c : 𝓞 K)
    (hc : qsIsExteriorGenerator S T c) (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    FractionalIdeal.count K v (Ideal.span {c} : FractionalIdeal (𝓞 K)⁰ K) =
      if v ∈ T then 1 else 0 := by
  classical
  have hc0 : c ≠ 0 := by
    intro h
    exact hc.1 (by simp [h])
  have hI0 : Ideal.span {c} ≠ ⊥ := by
    intro h
    exact hc0 (Ideal.span_singleton_eq_bot.mp h)
  have hfac :
      (Associates.mk v.asIdeal).count
          (Associates.mk (Ideal.span {c} : Ideal (𝓞 K))).factors =
        (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {c} : Ideal (𝓞 K))).count
          v.asIdeal :=
    Ideal.count_associates_factors_eq hI0 v.isPrime v.ne_bot
  rw [FractionalIdeal.count_coe K v hI0, hfac]
  by_cases hT : v ∈ T
  · have hcv := (hc.2 v hv).1.mpr hT
    have hle : Ideal.span {c} ≤ v.asIdeal := by
      apply Ideal.span_le.mpr
      intro x hx
      have hx' : x = c := by simpa using hx
      simpa [hx'] using hcv
    have hlt : ¬Ideal.span {c} ≤ v.asIdeal ^ (2 : ℕ) := by
      intro h
      exact (hc.2 v hv).2 (h (Ideal.subset_span (by simp)))
    have hcount := Ideal.count_normalizedFactors_eq (p := v.asIdeal)
      (x := Ideal.span {c}) (n := 1) (by simpa [pow_one] using hle) (by simpa using hlt)
    simp [hT, hcount]
  · have hcnv : c ∉ v.asIdeal := fun h => hT ((hc.2 v hv).1.mp h)
    have hlt : ¬Ideal.span {c} ≤ v.asIdeal := by
      intro h
      exact hcnv (h (Ideal.subset_span (by simp)))
    have hle : Ideal.span {c} ≤ v.asIdeal ^ (0 : ℕ) := by simp
    have hcount := Ideal.count_normalizedFactors_eq (p := v.asIdeal)
      (x := Ideal.span {c}) (n := 0) hle (by simpa using hlt)
    simp [hT, hcount]

theorem qsQuadSymbolAt_mul_NQ1 (v : HeightOneSpectrum (𝓞 K)) (a b : 𝓞 K) :
    qsQuadSymbolAt v (a * b) = qsQuadSymbolAt v a * qsQuadSymbolAt v b := by
  classical
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  letI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  letI : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  simp [qsQuadSymbolAt, map_mul]

theorem qsQuadSymbol_mul_NQ1 (T : Finset (HeightOneSpectrum (𝓞 K))) (a b : 𝓞 K) :
    qsQuadSymbol T (a * b) = qsQuadSymbol T a * qsQuadSymbol T b := by
  classical
  unfold qsQuadSymbol
  simp only [qsQuadSymbolAt_mul_NQ1, Finset.prod_mul_distrib]

theorem qsQuadSymbol_union_NQ1 {A B : Finset (HeightOneSpectrum (𝓞 K))}
    (hAB : Disjoint A B) (c : 𝓞 K) :
    qsQuadSymbol (A ∪ B) c = qsQuadSymbol A c * qsQuadSymbol B c := by
  classical
  unfold qsQuadSymbol
  rw [Finset.prod_union hAB]

theorem qsQuadSymbol_norm_le_one_NQ1
    (T : Finset (HeightOneSpectrum (𝓞 K))) (c : 𝓞 K) :
    ‖(qsQuadSymbol T c : ℂ)‖ ≤ 1 := by
  classical
  have hfactor (v : HeightOneSpectrum (𝓞 K)) :
      qsQuadSymbolAt v c ^ 2 = 0 ∨ qsQuadSymbolAt v c ^ 2 = 1 := by
    letI : v.asIdeal.IsMaximal := v.isMaximal
    letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
    letI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    letI : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
    by_cases hzero : Ideal.Quotient.mk v.asIdeal c = 0
    · left
      simp [qsQuadSymbolAt, hzero]
    · right
      change (quadraticChar (𝓞 K ⧸ v.asIdeal) (Ideal.Quotient.mk v.asIdeal c)) ^ 2 = 1
      exact quadraticChar_sq_one hzero
  have hprod : (∏ v ∈ T, qsQuadSymbolAt v c ^ 2) = 0 ∨
      (∏ v ∈ T, qsQuadSymbolAt v c ^ 2) = 1 := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert v T hv ih =>
        rw [Finset.prod_insert hv]
        rcases hfactor v with h0 | h1
        · simp [h0]
        · simp [h1, ih]
  have hsq : (qsQuadSymbol T c) ^ 2 ≤ 1 := by
    unfold qsQuadSymbol
    rw [← Finset.prod_pow]
    rcases hprod with h0 | h1
    · simp [h0]
    · simp [h1]
  have habs : (|qsQuadSymbol T c| : ℝ) ≤ 1 := by
    exact_mod_cast (sq_le_one_iff_abs_le_one _).mp hsq
  simpa only [Complex.norm_intCast, Int.cast_abs] using habs

noncomputable def qsUnitSymbolAt (S : Finset (HeightOneSpectrum (𝓞 K)))
    (v : HeightOneSpectrum (𝓞 K)) (u : SUnitGroup (K := K) S) : ℤ :=
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  letI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  letI : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  quadraticChar (𝓞 K ⧸ v.asIdeal) (residue v ((u : Kˣ) : K))

theorem qsUnitSymbolAt_mul (S : Finset (HeightOneSpectrum (𝓞 K)))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S)
    (u w : SUnitGroup (K := K) S) :
    qsUnitSymbolAt S v (u * w) = qsUnitSymbolAt S v u * qsUnitSymbolAt S v w := by
  classical
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  letI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  letI : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  have hu : v.valuation K ((u : Kˣ) : K) = 1 :=
    (mem_SUnitGroup_iff (K := K) S (u : Kˣ)).mp u.property v hv
  have hw : v.valuation K ((w : Kˣ) : K) = 1 :=
    (mem_SUnitGroup_iff (K := K) S (w : Kˣ)).mp w.property v hv
  change quadraticChar (𝓞 K ⧸ v.asIdeal)
      (residue v (((u : Kˣ) : K) * ((w : Kˣ) : K))) = _
  rw [qs_residue_mul_NQ1 v _ _ hu.le hw.le, map_mul]
  simpa only [qsUnitSymbolAt]

theorem qsUnitSymbolAt_sq (S : Finset (HeightOneSpectrum (𝓞 K)))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S)
    (u : SUnitGroup (K := K) S) : qsUnitSymbolAt S v (u ^ 2) = 1 := by
  classical
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  letI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  letI : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  have hu : v.valuation K ((u : Kˣ) : K) = 1 :=
    (mem_SUnitGroup_iff (K := K) S (u : Kˣ)).mp u.property v hv
  have hres : residue v ((u : Kˣ) : K) ≠ 0 :=
    (qs_nq0_residue_ne_zero_iff_valuation_one v _).2 hu
  dsimp [qsUnitSymbolAt]
  have hsq : residue v (((u : Kˣ) ^ 2 : Kˣ) : K) =
      residue v ((u : Kˣ) : K) ^ 2 := by
    calc
      residue v (((u : Kˣ) ^ 2 : Kˣ) : K) =
          residue v (((u : Kˣ) * (u : Kˣ) : Kˣ) : K) := by
            congr 1
            simp [pow_two]
      _ = residue v ((u : Kˣ) : K) * residue v ((u : Kˣ) : K) :=
        qs_residue_mul_NQ1 v _ _ hu.le hu.le
      _ = residue v ((u : Kˣ) : K) ^ 2 := by rw [pow_two]
  have hpowMap : (((u : Kˣ) : K) ^ 2) = (((u : Kˣ) ^ 2 : Kˣ) : K) := by simp
  rw [hpowMap, hsq, map_pow]
  exact quadraticChar_sq_one hres

theorem qsUnitSymbolAt_value_sq (S : Finset (HeightOneSpectrum (𝓞 K)))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S)
    (u : SUnitGroup (K := K) S) : (qsUnitSymbolAt S v u) ^ 2 = 1 := by
  classical
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  letI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  letI : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  have hu : v.valuation K ((u : Kˣ) : K) = 1 :=
    (mem_SUnitGroup_iff (K := K) S (u : Kˣ)).mp u.property v hv
  have hres : residue v ((u : Kˣ) : K) ≠ 0 :=
    (qs_nq0_residue_ne_zero_iff_valuation_one v _).2 hu
  change (quadraticChar (𝓞 K ⧸ v.asIdeal) (residue v ((u : Kˣ) : K))) ^ 2 = 1
  exact quadraticChar_sq_one hres

def qsUnitSymbolOnRows (S D : Finset (HeightOneSpectrum (𝓞 K)))
    (u : SUnitGroup (K := K) S) : ℤ :=
  ∏ v ∈ D, qsUnitSymbolAt S v u

theorem qsUnitSymbolOnRows_eq_of_squareClass
    (S D : Finset (HeightOneSpectrum (𝓞 K))) (hDS : Disjoint D S)
    (u w : SUnitGroup (K := K) S)
    (hclass : (QuotientGroup.mk u : qsSUnitSquareClasses (K := K) S) =
      QuotientGroup.mk w) : qsUnitSymbolOnRows S D u = qsUnitSymbolOnRows S D w := by
  classical
  have hpow : u / w ∈
      (powMonoidHom (α := SUnitGroup (K := K) S) 2).range :=
    (QuotientGroup.eq_iff_div_mem).mp hclass
  obtain ⟨z, hz⟩ := hpow
  have hz' : z ^ 2 = u / w := by simpa only [powMonoidHom_apply] using hz
  have hu : u = w * z ^ 2 := by
    calc
      u = (u / w) * w := (div_mul_cancel u w).symm
      _ = z ^ 2 * w := by rw [hz']
      _ = w * z ^ 2 := by ac_rfl
  unfold qsUnitSymbolOnRows
  apply Finset.prod_congr rfl
  intro v hv
  have hvS : v ∉ S := Finset.disjoint_left.mp hDS hv
  calc
    qsUnitSymbolAt S v u = qsUnitSymbolAt S v (w * z ^ 2) := by rw [hu]
    _ = qsUnitSymbolAt S v w := by
      calc
        qsUnitSymbolAt S v (w * z ^ 2) =
            qsUnitSymbolAt S v w * qsUnitSymbolAt S v (z ^ 2) :=
          qsUnitSymbolAt_mul S v hvS w (z ^ 2)
        _ = qsUnitSymbolAt S v w := by rw [qsUnitSymbolAt_sq S v hvS]; simp

theorem qsUnitSymbolOnRows_sq
    (S D : Finset (HeightOneSpectrum (𝓞 K))) (hDS : Disjoint D S)
    (u : SUnitGroup (K := K) S) : (qsUnitSymbolOnRows S D u) ^ 2 = 1 := by
  classical
  unfold qsUnitSymbolOnRows
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro v hv
  have hvS : v ∉ S := Finset.disjoint_left.mp hDS hv
  exact qsUnitSymbolAt_value_sq S v hvS u

theorem qsUnitSymbolOnRows_norm_eq_one
    (S D : Finset (HeightOneSpectrum (𝓞 K))) (hDS : Disjoint D S)
    (u : SUnitGroup (K := K) S) :
    ‖(qsUnitSymbolOnRows S D u : ℂ)‖ = 1 := by
  rcases (sq_eq_one_iff).mp (qsUnitSymbolOnRows_sq S D hDS u) with h | h
  · simp [h]
  · simp [h]

theorem qs_norm_sum_sq_le_card_NQ1 {ι : Type} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  classical
  have htriangle : ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le _ _
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖f i‖)
  simp only [one_mul, one_pow] at hcs
  simp at hcs
  calc
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 htriangle
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
      simpa using hcs

theorem qsSUnit_of_exterior_ratio_NQ1
    (S S' T T' : Finset (HeightOneSpectrum (𝓞 K))) (hSS' : S ⊆ S')
    (g g' : 𝓞 K) (hg : qsIsExteriorGenerator S T g)
    (hg' : qsIsExteriorGenerator S' T' g')
    (hTT' : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S' → (v ∈ T ↔ v ∈ T')) :
    ∃ u : SUnitGroup (K := K) S',
      (u : Kˣ) = Units.mk0 ((g : K) / (g' : K)) (by
        apply div_ne_zero
        · exact (IsFractionRing.injective (𝓞 K) K).ne hg.1
        · exact (IsFractionRing.injective (𝓞 K) K).ne hg'.1) := by
  classical
  have hgK : (g : K) ≠ 0 := (IsFractionRing.injective (𝓞 K) K).ne hg.1
  have hg'K : (g' : K) ≠ 0 := (IsFractionRing.injective (𝓞 K) K).ne hg'.1
  let r : K := (g : K) / (g' : K)
  have hr : r ≠ 0 := div_ne_zero hgK hg'K
  let ru : Kˣ := Units.mk0 r hr
  have hdivCount (v : HeightOneSpectrum (𝓞 K)) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
      FractionalIdeal.count K v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (a / b)) =
        FractionalIdeal.count K v
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a) -
          FractionalIdeal.count K v
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) b) := by
    rw [← FractionalIdeal.spanSingleton_div_spanSingleton, div_eq_mul_inv,
      FractionalIdeal.count_mul K v
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr ha)
        (inv_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hb)),
      FractionalIdeal.count_inv]
    ring
  have hcountR (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S') :
      FractionalIdeal.count K v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) r) = 0 := by
    have hcountg := qs_exterior_count_NQ1 S T g hg v (fun h => hv (hSS' h))
    have hcountg' := qs_exterior_count_NQ1 S' T' g' hg' v hv
    have hcountg'' : FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (g : K)) =
        if v ∈ T then 1 else 0 := by
      simpa only [← FractionalIdeal.coeIdeal_span_singleton] using hcountg
    have hcountg''' : FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (g' : K)) =
        if v ∈ T' then 1 else 0 := by
      simpa only [← FractionalIdeal.coeIdeal_span_singleton] using hcountg'
    have hratio := hdivCount v (g : K) (g' : K) hgK hg'K
    change FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((g : K) / (g' : K))) = 0
    rw [hratio, hcountg'', hcountg''']
    simp [hTT' v hv]
  have hvalR (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S') :
      v.valuation K r = 1 := by
    have hlog := qs_nq0_count_spanSingleton_eq_neg_log_valuation v r hr
    rw [hcountR v hv] at hlog
    have hlog0 : WithZero.log (v.valuation K r) = 0 := neg_eq_zero.mp hlog.symm
    calc
      v.valuation K r = WithZero.exp (WithZero.log (v.valuation K r)) :=
        (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hr)).symm
      _ = 1 := by rw [hlog0, WithZero.exp_zero]
  refine ⟨⟨ru, ?_⟩, rfl⟩
  apply (mem_SUnitGroup_iff (K := K) S' ru).2
  intro v hv
  simpa [ru, r] using hvalR v hv

theorem qsQuadSymbol_mul_sunit_NQ1
    (S' D : Finset (HeightOneSpectrum (𝓞 K))) (hDS : Disjoint D S')
    (g g' : 𝓞 K) (u : SUnitGroup (K := K) S')
    (hgu : (g : K) = (g' : K) * ((u : Kˣ) : K)) :
    qsQuadSymbol D g = qsQuadSymbol D g' * qsUnitSymbolOnRows S' D u := by
  classical
  unfold qsQuadSymbol qsUnitSymbolOnRows
  have hloc (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ D) :
      qsQuadSymbolAt v g = qsQuadSymbolAt v g' * qsUnitSymbolAt S' v u := by
    have hvS' : v ∉ S' := Finset.disjoint_left.mp hDS hv
    letI : v.asIdeal.IsMaximal := v.isMaximal
    letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
    letI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    letI : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
    have hu : v.valuation K ((u : Kˣ) : K) = 1 :=
      (mem_SUnitGroup_iff (K := K) S' (u : Kˣ)).mp u.property v hvS'
    have hresmul : residue v (g : K) = residue v (g' : K) * residue v ((u : Kˣ) : K) := by
      rw [hgu, qs_residue_mul_NQ1 v _ _ (HeightOneSpectrum.valuation_le_one v _) hu.le]
    have hresg : residue v (g : K) = Ideal.Quotient.mk v.asIdeal g :=
      qs_nq0_residue_algebraMap v g
    have hresg' : residue v (g' : K) = Ideal.Quotient.mk v.asIdeal g' :=
      qs_nq0_residue_algebraMap v g'
    change quadraticChar (𝓞 K ⧸ v.asIdeal) (Ideal.Quotient.mk v.asIdeal g) =
      quadraticChar (𝓞 K ⧸ v.asIdeal) (Ideal.Quotient.mk v.asIdeal g') *
        quadraticChar (𝓞 K ⧸ v.asIdeal) (residue v ((u : Kˣ) : K))
    rw [← hresg, hresmul, hresg', map_mul]
  calc
    (∏ v ∈ D, qsQuadSymbolAt v g) =
        ∏ v ∈ D, qsQuadSymbolAt v g' * qsUnitSymbolAt S' v u := by
      refine Finset.prod_congr rfl ?_
      intro v hv
      exact hloc v hv
    _ = (∏ v ∈ D, qsQuadSymbolAt v g') * ∏ v ∈ D, qsUnitSymbolAt S' v u := by
      rw [Finset.prod_mul_distrib]

end ArtinPrimitiveRoots.A2
