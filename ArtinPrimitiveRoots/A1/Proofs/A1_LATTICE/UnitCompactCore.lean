import ArtinPrimitiveRoots.A1.Field
import ArtinPrimitiveRoots.A1.Proofs.A1_LATTICE.Core
import ArtinPrimitiveRoots.Arith.SUnit
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
Low-level S-unit compactness and norm identities shared by A1 lattice consumers.
This module deliberately does not import Hilbert, AddChar, or SLattice.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical nonZeroDivisors

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.A1_LATTICE

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private theorem absFin_algebraMap_core (v : FinPlace F) (x : F) :
    absFin v (algebraMap F (v.adicCompletion F) x) = ‖FinitePlace.embedding v x‖ := by
  dsimp [absFin]
  have hpos : (Ideal.absNorm v.asIdeal : NNReal) ≠ 0 :=
    HeightOneSpectrum.absNorm_ne_zero v
  rw [dif_pos hpos]
  rw [← FinitePlace.norm_def]
  congr 1

private lemma count_spanSingleton_div_addchar (v : FinPlace F) (x y : F)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x / y)) =
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) x) -
        FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) y) := by
  rw [← FractionalIdeal.spanSingleton_div_spanSingleton, div_eq_mul_inv,
    FractionalIdeal.count_mul F v
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
      (inv_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy)),
    FractionalIdeal.count_inv]
  ring

private lemma count_spanSingleton_eq_neg_log_intValuation_addchar (v : FinPlace F)
    (r : 𝓞 F) (hr : r ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          (algebraMap (𝓞 F) F r)) =
      -WithZero.log (v.intValuation r) := by
  have hspan : (Ideal.span {r} : Ideal (𝓞 F)) ≠ 0 := by
    simpa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hr
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe F v hspan,
    v.intValuation_if_neg hr, WithZero.log_exp]
  ring

set_option linter.unnecessarySimpa false in
private lemma count_spanSingleton_eq_neg_log_valuation_addchar (v : FinPlace F)
    (z : F) (hz : z ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) z) =
      -WithZero.log (HeightOneSpectrum.valuation F v z) := by
  obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors (𝓞 F)) z
  have hn : n ≠ 0 := by
    intro hn
    apply hz
    rw [← hnd, IsFractionRing.mk'_eq_div, hn, map_zero, zero_div]
  have hd : (d : 𝓞 F) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hmapn : (algebraMap (𝓞 F) F n) ≠ 0 := by
    intro h
    exact hn ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
  have hmapd : (algebraMap (𝓞 F) F (d : 𝓞 F)) ≠ 0 := by
    intro h
    exact hd ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
  have hval : HeightOneSpectrum.valuation F v z = v.intValuation n / v.intValuation (d : 𝓞 F) := by
    rw [← hnd]
    exact v.valuation_of_mk'
  rw [hval, ← hnd, IsFractionRing.mk'_eq_div,
    count_spanSingleton_div_addchar v (algebraMap (𝓞 F) F n) (algebraMap (𝓞 F) F (d : 𝓞 F))
      hmapn hmapd,
    count_spanSingleton_eq_neg_log_intValuation_addchar v n hn,
    count_spanSingleton_eq_neg_log_intValuation_addchar v (d : 𝓞 F) hd,
    WithZero.log_div (v.intValuation_ne_zero n hn) (v.intValuation_ne_zero (d : 𝓞 F) hd)]
  ring

lemma norm_embedding_eq_absNorm_zpow (v : FinPlace F) (z : F) (hz : z ≠ 0) :
    ‖FinitePlace.embedding v z‖ =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (- FractionalIdeal.count F v (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) z)) := by
  rw [FinitePlace.norm_embedding']
  have hm : (v.valuation F) z ≠ 0 := (v.valuation F).ne_zero_iff.mpr hz
  rw [WithZeroMulInt.toNNReal_neg_apply (HeightOneSpectrum.absNorm_ne_zero v) hm]
  rw [WithZero.toAdd_unzero_eq_log hm]
  have hlog : WithZero.log (v.valuation F z) =
      - FractionalIdeal.count F v (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) z) := by
    rw [count_spanSingleton_eq_neg_log_valuation_addchar v z hz, neg_neg]
  rw [hlog]
  push_cast
  rfl

lemma norm_embedding_mul_maxPowDividing_eq_one {S : SData F CE condη} {x : F} {I : Ideal (𝓞 F)}
    (hx : S.IsGen x I) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S.Sf) :
    ‖FinitePlace.embedding v x‖ * (Ideal.absNorm (v.maxPowDividing I) : ℝ) = 1 := by
  rw [norm_embedding_eq_absNorm_zpow v x hx.2.1]
  rw [hx.2.2 v hv]
  rw [FractionalIdeal.count_coe F v hx.1.1]
  dsimp [HeightOneSpectrum.maxPowDividing]
  rw [map_pow]
  push_cast
  rw [← zpow_natCast]
  rw [zpow_neg]
  exact inv_mul_cancel₀ (zpow_ne_zero _ (Nat.cast_ne_zero.mpr (ne_of_gt (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)))))

lemma finitePlace_mk_hasFiniteMulSupport {x : F} (hx : x ≠ 0) :
    (fun v : HeightOneSpectrum (𝓞 F) => (FinitePlace.mk v) x).HasFiniteMulSupport := by
  have h := FinitePlace.hasFiniteMulSupport (K := F) hx
  have hsub : Function.mulSupport ((fun w : FinitePlace F => w x) ∘ FinitePlace.equivHeightOneSpectrum.symm) ⊆
      FinitePlace.equivHeightOneSpectrum '' (Function.mulSupport (fun w : FinitePlace F => w x)) := by
    intro v hv
    simp only [Function.mem_mulSupport, Function.comp_apply] at hv
    exact ⟨FinitePlace.equivHeightOneSpectrum.symm v, hv, by simp⟩
  exact (h.image _).subset hsub

lemma absFin_algebraMap (v : FinPlace F) (x : F) :
    absFin v (algebraMap F (v.adicCompletion F) x) = ‖FinitePlace.embedding v x‖ := by
  dsimp [absFin]
  have hpos : (Ideal.absNorm v.asIdeal : NNReal) ≠ 0 :=
    HeightOneSpectrum.absNorm_ne_zero v
  rw [dif_pos hpos]
  rw [← FinitePlace.norm_def]
  congr 1

lemma maxPowDividing_eq_one_of_not_le {I : Ideal (𝓞 F)} (hI : I ≠ 0)
    (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ I ≤ v.asIdeal) :
    v.maxPowDividing I = 1 := by
  have hcount : (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0 := by
    by_contra hc
    have hdvd := (Associates.count_ne_zero_iff_dvd hI v.irreducible).mp hc
    rw [Ideal.dvd_iff_le] at hdvd
    exact hv hdvd
  dsimp [HeightOneSpectrum.maxPowDividing]
  rw [hcount, pow_zero]

lemma maxPowDividing_eq_one_of_mem_Sf {S : SData F CE condη} {I : Ideal (𝓞 F)}
    (hI : S.IsExterior I) {v : FinPlace F} (hv : v ∈ S.Sf) :
    v.maxPowDividing I = 1 :=
  maxPowDividing_eq_one_of_not_le hI.1 v (hI.2 v hv)

lemma absNorm_maxPowDividing_eq_one_of_mem_Sf {S : SData F CE condη} {I : Ideal (𝓞 F)}
    (hI : S.IsExterior I) {v : FinPlace F} (hv : v ∈ S.Sf) :
    (Ideal.absNorm (v.maxPowDividing I) : ℝ) = 1 := by
  rw [maxPowDividing_eq_one_of_mem_Sf hI hv, Ideal.one_eq_top, Ideal.absNorm_top, Nat.cast_one]

lemma absNorm_eq_finprod_absNorm_maxPowDividing {I : Ideal (𝓞 F)} (hI : I ≠ 0) :
    (Ideal.absNorm I : ℝ) = ∏ᶠ v : HeightOneSpectrum (𝓞 F), (Ideal.absNorm (v.maxPowDividing I) : ℝ) := by
  have h_factor : ∏ᶠ v : HeightOneSpectrum (𝓞 F), v.maxPowDividing I = I :=
    Ideal.finprod_heightOneSpectrum_factorization hI
  have h_prod : (Ideal.absNorm (∏ᶠ v : HeightOneSpectrum (𝓞 F), v.maxPowDividing I) : ℝ) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), (Ideal.absNorm (v.maxPowDividing I) : ℝ) :=
    ((Nat.castRingHom ℝ).toMonoidHom.comp Ideal.absNorm.toMonoidHom).map_finprod_of_preimage_one
      (by simp) _
  nth_rw 1 [← h_factor]
  exact h_prod

lemma hasFiniteMulSupport_absNorm_maxPowDividing {I : Ideal (𝓞 F)} (hI : I ≠ 0) :
    (fun v : HeightOneSpectrum (𝓞 F) => (Ideal.absNorm (v.maxPowDividing I) : ℝ)).HasFiniteMulSupport := by
  have h_supp : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 F) => (Ideal.absNorm (v.maxPowDividing I) : ℝ)) ⊆
      Function.mulSupport (fun v : HeightOneSpectrum (𝓞 F) => v.maxPowDividing I) := by
    intro v hv
    simp only [Function.mem_mulSupport, ne_eq] at hv ⊢
    intro h1
    apply hv
    rw [h1, Ideal.one_eq_top, Ideal.absNorm_top, Nat.cast_one]
  exact (Ideal.hasFiniteMulSupport hI).subset h_supp

lemma absNorm_eq_finprod_exterior {S : SData F CE condη} {I : Ideal (𝓞 F)}
    (hI : S.IsExterior I) :
    (Ideal.absNorm I : ℝ) = ∏ᶠ v ∉ S.Sf, (Ideal.absNorm (v.maxPowDividing I) : ℝ) := by
  rw [absNorm_eq_finprod_absNorm_maxPowDividing hI.1]
  let f := fun v : HeightOneSpectrum (𝓞 F) => (Ideal.absNorm (v.maxPowDividing I) : ℝ)
  have hf : f.HasFiniteMulSupport := hasFiniteMulSupport_absNorm_maxPowDividing hI.1
  have h_split : ∏ᶠ v, f v = (∏ᶠ v ∈ (S.Sf : Set (HeightOneSpectrum (𝓞 F))), f v) *
      ∏ᶠ v ∉ S.Sf, f v := by
    have h_union := finprod_mem_union' (hst := disjoint_compl_right)
      (hs := S.Sf.finite_toSet.inter_of_left _)
      (ht := Set.Finite.subset hf Set.inter_subset_right) (f := f)
    rw [Set.union_compl_self, finprod_mem_univ] at h_union
    exact h_union
  rw [h_split]
  have h_sf_one : (∏ᶠ v ∈ (S.Sf : Set (HeightOneSpectrum (𝓞 F))), f v) = 1 := by
    rw [finprod_mem_coe_finset]
    have : ∀ v ∈ S.Sf, f v = 1 := fun v hv => absNorm_maxPowDividing_eq_one_of_mem_Sf hI hv
    rw [Finset.prod_congr rfl this, Finset.prod_const_one]
  rw [h_sf_one, one_mul]

lemma finprod_exterior_norm_embedding_mul_absNorm {S : SData F CE condη} {x : F} {I : Ideal (𝓞 F)}
    (hI : S.IsExterior I) (hx : S.IsGen x I) :
    (∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v x‖) * (Ideal.absNorm I : ℝ) = 1 := by
  rw [absNorm_eq_finprod_exterior hI]
  have hf_supp : (((S.Sf : Set (HeightOneSpectrum (𝓞 F)))ᶜ) ∩
      Function.mulSupport (fun v => ‖FinitePlace.embedding v x‖)).Finite := by
    have h_all : (Function.mulSupport (fun v => ‖FinitePlace.embedding v x‖)).Finite :=
      finitePlace_mk_hasFiniteMulSupport hx.2.1
    exact Set.Finite.subset h_all Set.inter_subset_right
  have hg_supp : (((S.Sf : Set (HeightOneSpectrum (𝓞 F)))ᶜ) ∩
      Function.mulSupport (fun v => (Ideal.absNorm (v.maxPowDividing I) : ℝ))).Finite := by
    have h := hasFiniteMulSupport_absNorm_maxPowDividing hI.1
    exact Set.Finite.subset h Set.inter_subset_right
  have h_one : ∀ v ∈ ((S.Sf : Set (HeightOneSpectrum (𝓞 F)))ᶜ),
      ‖FinitePlace.embedding v x‖ * (Ideal.absNorm (v.maxPowDividing I) : ℝ) = (1 : ℝ) := by
    intro v hv
    exact norm_embedding_mul_maxPowDividing_eq_one hx hv
  exact ((finprod_mem_mul_distrib' (s := ((S.Sf : Set (HeightOneSpectrum (𝓞 F)))ᶜ)) hf_supp hg_supp).symm).trans
    ((finprod_mem_congr rfl h_one).trans (finprod_mem_one _))


private lemma normSq_embedding_eq_core [IsTotallyComplex F] (w : InfinitePlace F) (x : F) :
    Complex.normSq (w.embedding x) = w x ^ w.mult := by
  rw [IsTotallyComplex.mult_eq w, Complex.normSq_eq_norm_sq, InfinitePlace.norm_embedding_eq]

private lemma absS_diag_eq_core [IsTotallyComplex F] (S : SData F CE condη) (x : F) :
    S.absS (S.diag x) =
      (∏ v ∈ S.Sf, ‖FinitePlace.embedding v x‖) * ∏ w : InfinitePlace F, w x ^ w.mult := by
  dsimp [SData.absS, SData.diag]
  congr 1
  · change (∏ v ∈ S.Sf.attach,
      absFin v.1 (algebraMap F (v.1.adicCompletion F) x)) = _
    rw [Finset.prod_attach S.Sf
      (fun v => absFin v (algebraMap F (v.adicCompletion F) x))]
    refine Finset.prod_congr rfl ?_
    intro v hv
    exact absFin_algebraMap_core v x
  · change (∏ w : InfinitePlace F, Complex.normSq (w.embedding x)) = _
    refine Fintype.prod_congr _ _ ?_
    intro w
    exact normSq_embedding_eq_core w x

private lemma finitePlace_mk_hasFiniteMulSupport_core {x : F} (hx : x ≠ 0) :
    (fun v : HeightOneSpectrum (𝓞 F) => (FinitePlace.mk v) x).HasFiniteMulSupport := by
  have h := FinitePlace.hasFiniteMulSupport (K := F) hx
  have hsub : Function.mulSupport
        ((fun w : FinitePlace F => w x) ∘ FinitePlace.equivHeightOneSpectrum.symm) ⊆
      FinitePlace.equivHeightOneSpectrum '' (Function.mulSupport (fun w : FinitePlace F => w x)) := by
    intro v hv
    simp only [Function.mem_mulSupport, Function.comp_apply] at hv
    exact ⟨FinitePlace.equivHeightOneSpectrum.symm v, hv, by simp⟩
  exact (h.image _).subset hsub

/-- The quotient of the `S`-unit group by sixth powers is finite. -/
theorem s_units_finite_mod_six_core (S : SData F CE condη) :
    Finite (S.US ⧸ (powMonoidHom 6 : S.US →* S.US).range) := by
  have hfg : Monoid.FG S.US := by
    change Monoid.FG ((S.Sf : Set (HeightOneSpectrum (𝓞 F))).unit F)
    exact ArtinPrimitiveRoots.Arith.sUnit_fg F S.Sf
  letI : Group.FG S.US := Group.fg_iff_monoid_fg.mpr hfg
  have hindex : (powMonoidHom (α := S.US) 6).range.FiniteIndex :=
    Subgroup.finiteIndex_range_powMonoidHom_of_fg S.US (by norm_num)
  exact Subgroup.finiteIndex_iff_finite_quotient.mp hindex

/-- The low-level S-norm identity used by `BData.exists_balanced`. -/
theorem absS_diag_eq_norm_core (D : FieldData F) (S : SData F CE condη)
    (x : F) (I : Ideal (𝓞 F)) (hI : S.IsExterior I) (hx : S.IsGen x I) :
    S.absS (S.diag x) = Ideal.absNorm I := by
  classical
  letI : IsTotallyComplex F := D.isTotallyComplex
  have hx0 : x ≠ 0 := hx.2.1
  have hprod := prod_abs_eq_one hx0
  have hf_supp : (Function.mulSupport fun v => ‖FinitePlace.embedding v x‖).Finite :=
    finitePlace_mk_hasFiniteMulSupport_core hx0
  have h_split : (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖FinitePlace.embedding v x‖) =
      (∏ v ∈ S.Sf, ‖FinitePlace.embedding v x‖) *
        ∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v x‖ := by
    have h_union := finprod_mem_union' (hst := disjoint_compl_right)
      (hs := S.Sf.finite_toSet.inter_of_left _)
      (ht := Set.Finite.subset hf_supp Set.inter_subset_right)
      (f := fun v => ‖FinitePlace.embedding v x‖)
    rw [Set.union_compl_self, finprod_mem_univ] at h_union
    rw [finprod_mem_coe_finset] at h_union
    exact h_union
  have h_prod_decomp : (∏ᶠ w : FinitePlace F, w x) =
      (∏ v ∈ S.Sf, ‖FinitePlace.embedding v x‖) *
        ∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v x‖ := by
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    change (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖FinitePlace.embedding v x‖) = _
    exact h_split
  rw [h_prod_decomp] at hprod
  have h_absS : S.absS (S.diag x) =
      (∏ v ∈ S.Sf, ‖FinitePlace.embedding v x‖) *
        ∏ w : InfinitePlace F, w x ^ w.mult := absS_diag_eq_core S x
  let sfNorm : ℝ := ∏ v ∈ S.Sf, ‖FinitePlace.embedding v x‖
  let archNorm : ℝ := ∏ w : InfinitePlace F, w x ^ w.mult
  let outsideNorm : ℝ := ∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v x‖
  have hprod' : archNorm * (sfNorm * outsideNorm) = 1 := by
    simpa [archNorm, sfNorm, outsideNorm] using hprod
  have h_prod_absS : S.absS (S.diag x) * outsideNorm = 1 := by
    rw [h_absS]
    calc
      _ = archNorm * (sfNorm * outsideNorm) := by
        simp only [archNorm, sfNorm, outsideNorm]
        ring
      _ = 1 := hprod'
  have h_ext := finprod_exterior_norm_embedding_mul_absNorm hI hx
  calc
    S.absS (S.diag x) = S.absS (S.diag x) * 1 := by rw [mul_one]
    _ = S.absS (S.diag x) *
        ((∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v x‖) * (Ideal.absNorm I : ℝ)) := by
          rw [← h_ext]
    _ = (S.absS (S.diag x) *
        (∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v x‖)) * (Ideal.absNorm I : ℝ) := by
          rw [mul_assoc]
    _ = 1 * (Ideal.absNorm I : ℝ) := by
      simpa only [outsideNorm, h_prod_absS]
    _ = Ideal.absNorm I := by rw [one_mul]

private theorem covol_absS_diag_sunit_eq_one_core (D : FieldData F)
    (S : SData F CE condη) (u : S.US) :
    S.absS (S.diag ((u : Fˣ) : F)) = 1 := by
  have hI : S.IsExterior (⊤ : Ideal (𝓞 F)) := by
    refine ⟨by simp, ?_⟩
    intro v hv htop
    have heq : v.asIdeal = ⊤ := top_le_iff.mp htop
    exact v.isPrime.ne_top heq
  have hx : S.IsGen ((u : Fˣ) : F) (⊤ : Ideal (𝓞 F)) := by
    refine ⟨hI, Units.ne_zero (u : Fˣ), ?_⟩
    intro v hv
    have hcount := count_spanSingleton_eq_neg_log_valuation_addchar v
      ((u : Fˣ) : F) (Units.ne_zero (u : Fˣ))
    have hval : v.valuation F ((u : Fˣ) : F) = 1 := u.property v hv
    rw [hval] at hcount
    rw [FractionalIdeal.coeIdeal_top, FractionalIdeal.count_one]
    simpa using hcount
  have hnorm := absS_diag_eq_norm_core D S ((u : Fˣ) : F) ⊤ hI hx
  simpa using hnorm

theorem covol_sunit_prime_power_core (S : SData F CE condη) (v : S.Sf) :
    ∃ t : S.US, ∀ w : S.Sf,
      Valued.v (algebraMap F (w.1.adicCompletion F) ((t : Fˣ) : F)) =
        if w.1 = v.1 then
          WithZero.exp (Fintype.card (ClassGroup (𝓞 F)) : ℤ) else 1 := by
  classical
  let N := Fintype.card (ClassGroup (𝓞 F))
  obtain ⟨a, ha⟩ := exists_principal_power_generator v.1
  have hNpow : v.1.asIdeal ^ N ≠ ⊥ := pow_ne_zero _ v.1.ne_bot
  have ha0 : a ≠ 0 := by
    intro ha0
    apply hNpow
    rw [← ha, ha0]
    simp
  have haF0 : (algebraMap (𝓞 F) F a) ≠ 0 := by
    intro h
    apply ha0
    exact FaithfulSMul.algebraMap_injective (𝓞 F) F (by simpa using h)
  let aUnit : Fˣ := Units.mk0 (algebraMap (𝓞 F) F a) haF0
  let t0 : Fˣ := aUnit⁻¹
  have hcount (w : FinPlace F) :
      FractionalIdeal.count F w (Ideal.span {a} : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        if w = v.1 then (N : ℤ) else 0 := by
    rw [ha, FractionalIdeal.coeIdeal_pow]
    by_cases hwv : w = v.1
    · subst w
      simpa using (FractionalIdeal.count_pow_self (K := F) v.1 N)
    · have hvw : v.1 ≠ w := Ne.symm hwv
      rw [FractionalIdeal.count_pow, FractionalIdeal.count_maximal_coprime F w hvw]
      simp [hwv]
  have hcountA (w : FinPlace F) :
      FractionalIdeal.count F w
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          (algebraMap (𝓞 F) F a)) = if w = v.1 then (N : ℤ) else 0 := by
    rw [← FractionalIdeal.coeIdeal_span_singleton]
    exact hcount w
  have hlogA (w : FinPlace F) :
      WithZero.log (w.valuation F (algebraMap (𝓞 F) F a)) =
        -(if w = v.1 then (N : ℤ) else 0) := by
    have h := count_spanSingleton_eq_neg_log_valuation_addchar w
      (algebraMap (𝓞 F) F a) haF0
    rw [hcountA w] at h
    omega
  have hvalA (w : FinPlace F) :
      w.valuation F (algebraMap (𝓞 F) F a) =
        WithZero.exp (-(if w = v.1 then (N : ℤ) else 0)) := by
    have hne : w.valuation F (algebraMap (𝓞 F) F a) ≠ 0 :=
      (w.valuation F).ne_zero_iff.mpr haF0
    calc
      w.valuation F (algebraMap (𝓞 F) F a) =
          WithZero.exp (WithZero.log (w.valuation F (algebraMap (𝓞 F) F a))) :=
            (WithZero.exp_log hne).symm
      _ = _ := by rw [hlogA]
  have hvalT (w : FinPlace F) :
      w.valuation F ((t0 : Fˣ) : F) =
        WithZero.exp (if w = v.1 then (N : ℤ) else 0) := by
    have hvalUnit : w.valuation F ((aUnit : Fˣ) : F) =
        WithZero.exp (-(if w = v.1 then (N : ℤ) else 0)) := by
      simpa [aUnit] using hvalA w
    calc
      w.valuation F ((t0 : Fˣ) : F) =
          (w.valuation F ((aUnit : Fˣ) : F))⁻¹ := by simp [t0]
      _ = (WithZero.exp (-(if w = v.1 then (N : ℤ) else 0)))⁻¹ := by rw [hvalUnit]
      _ = WithZero.exp (if w = v.1 then (N : ℤ) else 0) := by
        rw [WithZero.exp_neg]
        simp
  have htMem : ∀ w : FinPlace F, w ∉ S.Sf →
      w.valuation F ((t0 : Fˣ) : F) = 1 := by
    intro w hw
    have hwv : w ≠ v.1 := by
      intro h
      apply hw
      simpa [h] using v.2
    rw [hvalT w, if_neg hwv]
    simp
  let t : S.US := ⟨t0, htMem⟩
  refine ⟨t, ?_⟩
  intro w
  change Valued.v (algebraMap F (w.1.adicCompletion F) ((t0 : Fˣ) : F)) = _
  change Valued.v (((t0 : Fˣ) : F) : w.1.adicCompletion F) = _
  rw [w.1.valuedAdicCompletion_eq_valuation']
  by_cases h : w.1 = v.1
  · simpa [h, N] using hvalT w.1
  · simpa [h, N] using hvalT w.1

open Module NumberField.Units NumberField.Units.dirichletUnitTheorem

theorem covol_unit_balance_core (D : FieldData F)
    (E : Subgroup (𝓞 F)ˣ) [E.FiniteIndex] :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : InfinitePlace F → ℝ, (∀ w, 0 < t w) →
      ∃ ε : (𝓞 F)ˣ, ε ∈ E ∧ ∀ w,
        |Real.log (‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ * t w) -
          (Fintype.card (InfinitePlace F) : ℝ)⁻¹ *
            ∑ w' : InfinitePlace F, Real.log (t w')| ≤ B := by
  classical
  letI : IsTotallyComplex F := D.isTotallyComplex
  let w₀ : InfinitePlace F := dirichletUnitTheorem.w₀
  let b : Basis (Fin (Units.rank F)) ℝ (dirichletUnitTheorem.logSpace F) :=
    (Units.basisUnitLattice F).ofZLatticeBasis ℝ (Units.unitLattice F)
  let C : ℝ := ∑ i, ‖b i‖
  let n : ℕ := E.index
  let r : ℝ := Fintype.card (InfinitePlace F)
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (InfinitePlace F))
  have hn0 : n ≠ 0 := by
    dsimp [n]
    exact Subgroup.FiniteIndex.index_ne_zero
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨r * n * C, mul_nonneg (mul_nonneg hr.le (Nat.cast_nonneg _)) hC, ?_⟩
  intro t ht
  let m : ℝ := r⁻¹ * ∑ w : InfinitePlace F, Real.log (t w)
  let x : dirichletUnitTheorem.logSpace F := fun w => -2 * (Real.log (t w.val) - m)
  let q : dirichletUnitTheorem.logSpace F := (n : ℝ)⁻¹ • x
  let l : dirichletUnitTheorem.logSpace F := (ZSpan.floor b q : dirichletUnitTheorem.logSpace F)
  let p : dirichletUnitTheorem.logSpace F := ZSpan.fract b q
  have hp : ‖p‖ ≤ C := by
    dsimp [p, C]
    exact ZSpan.norm_fract_le b q
  have hcoord (w : {w : InfinitePlace F // w ≠ w₀}) : |p w| ≤ C := by
    have hc : ‖p w‖ ≤ ‖p‖ := by
      rw [Pi.norm_def]
      have hs : ‖p w‖₊ ≤ Finset.univ.sup
          (fun b : {w : InfinitePlace F // w ≠ w₀} => ‖p b‖₊) :=
        Finset.le_sup (f := fun b : {w : InfinitePlace F // w ≠ w₀} => ‖p b‖₊)
          (Finset.mem_univ w)
      exact NNReal.coe_le_coe.mpr hs
    rw [← Real.norm_eq_abs]
    exact hc.trans hp
  have hlattice : (l : dirichletUnitTheorem.logSpace F) ∈ Units.unitLattice F := by
    have hspan : l ∈ Submodule.span ℤ (Set.range b) := by
      dsimp [l]
      exact (ZSpan.floor b q).property
    have heq : Submodule.span ℤ (Set.range b) = Units.unitLattice F :=
      Module.Basis.ofZLatticeBasis_span ℝ (Units.unitLattice F)
        (Units.basisUnitLattice F)
    exact heq ▸ hspan
  change l ∈ Submodule.map (logEmbedding F).toIntLinearMap ⊤ at hlattice
  obtain ⟨z, hz, hzl⟩ := Submodule.mem_map.mp hlattice
  let η : (𝓞 F)ˣ := z.toMul
  have hη : logEmbedding F (Additive.ofMul η) = l := by
    simpa [η] using hzl
  let ε : (𝓞 F)ˣ := η ^ n
  have hεE : ε ∈ E := by
    dsimp [ε, η]
    exact E.pow_index_mem z.toMul
  have hεlog : logEmbedding F (Additive.ofMul ε) = n • l := by
    rw [show ε = η ^ n by rfl, ofMul_pow, map_nsmul, hη]
  have hcenter : ∑ w : InfinitePlace F, (Real.log (t w) - m) = 0 := by
    dsimp [m, r]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [Nat.cast_ne_zero.mpr (Fintype.card_pos.ne' :
      Fintype.card (InfinitePlace F) ≠ 0)]
    ring
  have hunit : ∑ w : InfinitePlace F,
      Real.log ‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ = 0 := by
    have hu := Units.sum_mult_mul_log ε
    have hu' : ∑ w : InfinitePlace F,
        2 * Real.log ‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ = 0 := by
      simpa [IsTotallyComplex.mult_eq, ← InfinitePlace.norm_embedding_eq] using hu
    have hsum := hu'
    rw [← Finset.mul_sum] at hsum
    nlinarith
  let d : InfinitePlace F → ℝ := fun w =>
      Real.log ‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ + Real.log (t w) - m
  have hdsum : ∑ w : InfinitePlace F, d w = 0 := by
    dsimp [d]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hunit]
    have hc : (∑ w : InfinitePlace F, Real.log (t w)) -
        (∑ w : InfinitePlace F, m) = 0 := by
      simpa only [Finset.sum_sub_distrib] using hcenter
    linarith [hc]
  have hretained (w : {w : InfinitePlace F // w ≠ w₀}) : |d w.val| ≤ (n : ℝ) * C := by
    have hlog : 2 * Real.log
        ‖w.val.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ =
          (n : ℝ) * (ZSpan.floor b q : dirichletUnitTheorem.logSpace F) w := by
      simpa [logEmbedding_component, IsTotallyComplex.mult_eq,
        InfinitePlace.norm_embedding_eq, Pi.smul_apply, smul_eq_mul, l]
        using congrFun hεlog w
    have hqcoord : q w = (n : ℝ)⁻¹ * x w := by simp [q, Pi.smul_apply]
    have hfract : p w = q w - (ZSpan.floor b q : dirichletUnitTheorem.logSpace F) w := by
      simp [p, ZSpan.fract_apply]
    have hxmul : (n : ℝ) * q w = x w := by
      rw [hqcoord]
      field_simp [hn.ne']
    have hldiff :
        (n : ℝ) * (ZSpan.floor b q : dirichletUnitTheorem.logSpace F) w - x w =
          -(n : ℝ) * p w := by
      rw [← hxmul, hfract]
      ring
    have hvalue : d w.val =
        ((n : ℝ) * (ZSpan.floor b q : dirichletUnitTheorem.logSpace F) w - x w) / 2 := by
      dsimp [d, x]
      rw [← hlog]
      ring
    calc
      |d w.val| = |-(n : ℝ) * p w / 2| := by rw [hvalue, hldiff]
      _ = (n : ℝ) * |p w| / 2 := by
        rw [abs_div, abs_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg n)]
        norm_num
      _ ≤ (n : ℝ) * C / 2 := by gcongr; exact hcoord w
      _ ≤ (n : ℝ) * C := by nlinarith [mul_nonneg (Nat.cast_nonneg n) hC]
  have hsplit := Fintype.sum_eq_add_sum_subtype_ne d w₀
  have hw₀ : d w₀ = -∑ w : {w : InfinitePlace F // w ≠ w₀}, d w.val := by
    have h := hdsum
    rw [hsplit] at h
    linarith
  have hdrop : |d w₀| ≤ r * (n : ℝ) * C := by
    rw [hw₀, abs_neg]
    calc
      |∑ w : {w : InfinitePlace F // w ≠ w₀}, d w.val| ≤
          ∑ w : {w : InfinitePlace F // w ≠ w₀}, |d w.val| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ w : {w : InfinitePlace F // w ≠ w₀}, (n : ℝ) * C :=
          Finset.sum_le_sum fun w hw => hretained w
      _ = (Fintype.card {w : InfinitePlace F // w ≠ w₀} : ℝ) * ((n : ℝ) * C) := by simp
      _ ≤ r * (n : ℝ) * C := by
          have hcard : Fintype.card {w : InfinitePlace F // w ≠ w₀} ≤
              Fintype.card (InfinitePlace F) := Fintype.card_subtype_le _
          have hreal : (Fintype.card {w : InfinitePlace F // w ≠ w₀} : ℝ) ≤ r := by
            dsimp [r]
            exact_mod_cast hcard
          calc
            (Fintype.card {w : InfinitePlace F // w ≠ w₀} : ℝ) * ((n : ℝ) * C) ≤
                r * ((n : ℝ) * C) := mul_le_mul_of_nonneg_right hreal
                  (mul_nonneg (Nat.cast_nonneg n) hC)
            _ = r * (n : ℝ) * C := by ring
  have hr1 : 1 ≤ r := by
    dsimp [r]
    have hc : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
    exact_mod_cast (show 1 ≤ Fintype.card (InfinitePlace F) by omega)
  have hnormpos (w : InfinitePlace F) :
      0 < ‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ := by
    apply norm_pos_iff.mpr
    have hO : (ε : 𝓞 F) ≠ 0 := Units.ne_zero ε
    have hF : algebraMap (𝓞 F) F (ε : 𝓞 F) ≠ 0 :=
      (map_ne_zero_iff (algebraMap (𝓞 F) F)
        (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr hO
    exact (map_ne_zero_iff w.embedding w.embedding.injective).mpr hF
  have htarget (w : InfinitePlace F) :
      Real.log (‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ * t w) -
        r⁻¹ * ∑ w' : InfinitePlace F, Real.log (t w') = d w := by
    rw [Real.log_mul (hnormpos w).ne' (ht w).ne']
  refine ⟨ε, hεE, ?_⟩
  intro w
  by_cases hw : w = w₀
  · subst w
    rw [htarget]
    exact hdrop
  · have hd := hretained ⟨w, hw⟩
    have hbound : (n : ℝ) * C ≤ r * (n : ℝ) * C := by
      have hnc : 0 ≤ (n : ℝ) * C := mul_nonneg (Nat.cast_nonneg n) hC
      nlinarith [mul_nonneg (sub_nonneg.mpr hr1) hnc]
    rw [htarget]
    exact hd.trans hbound

private def covol_localLog (S : SData F CE condη) (v : S.Sf)
    (z : (v.1.adicCompletion F)ˣ) : ℤ :=
  WithZero.log (Valued.v (z : v.1.adicCompletion F))

private lemma covol_localLog_mul (S : SData F CE condη) (v : S.Sf)
    (z z' : (v.1.adicCompletion F)ˣ) :
    covol_localLog S v (z * z') = covol_localLog S v z + covol_localLog S v z' := by
  change WithZero.log (Valued.v ((z * z' : (v.1.adicCompletion F)ˣ) : v.1.adicCompletion F)) = _
  rw [Units.val_mul, Valuation.map_mul]
  exact WithZero.log_mul ((Valued.v).ne_zero_iff.mpr z.ne_zero)
    ((Valued.v).ne_zero_iff.mpr z'.ne_zero)

private lemma covol_localLog_zpow (S : SData F CE condη) (v : S.Sf)
    (z : (v.1.adicCompletion F)ˣ) (n : ℤ) :
    covol_localLog S v (z ^ n) = n * covol_localLog S v z := by
  change WithZero.log (Valued.v ((z ^ n : (v.1.adicCompletion F)ˣ) : v.1.adicCompletion F)) = _
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, WithZero.log_zpow]
  simp [covol_localLog]

private lemma covol_localLog_prod (S : SData F CE condη) (v : S.Sf) (s : Finset S.Sf)
    (f : S.Sf → (v.1.adicCompletion F)ˣ) :
    covol_localLog S v (s.prod f) = s.sum (fun w => covol_localLog S v (f w)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [covol_localLog]
  | @insert w s hw ih =>
      rw [Finset.prod_insert hw, Finset.sum_insert hw, covol_localLog_mul, ih]

private lemma covol_localLog_diagU_of_valued (S : SData F CE condη) (v : S.Sf)
    (t : S.US) (n : ℤ)
    (h : Valued.v (algebraMap F (v.1.adicCompletion F) ((t : Fˣ) : F)) =
      WithZero.exp n) :
    covol_localLog S v (S.compU v (S.diagU (t : Fˣ))) = n := by
  change WithZero.log (Valued.v
    (algebraMap F (v.1.adicCompletion F) ((t : Fˣ) : F))) = n
  rw [h, WithZero.log_exp]

private lemma covol_localLog_pow (S : SData F CE condη) (v : S.Sf)
    (z : (v.1.adicCompletion F)ˣ) (n : ℕ) :
    covol_localLog S v (z ^ n) = (n : ℤ) * covol_localLog S v z := by
  change WithZero.log (Valued.v ((z ^ n : (v.1.adicCompletion F)ˣ) : v.1.adicCompletion F)) = _
  rw [Units.val_pow_eq_pow_val, Valuation.map_pow, WithZero.log_pow]
  simp [covol_localLog, zsmul_eq_mul]

private theorem covol_sunit_finite_reduction_core (S : SData F CE condη)
    (x : {x : S.FSˣ // S.absS (x : S.FS) = 1}) :
    ∃ a : S.US, ∀ v : S.Sf,
      0 ≤ WithZero.log (Valued.v
        ((S.compU v ((S.diagU (a : Fˣ)) ^ 6 * x.1) : (v.1.adicCompletion F)ˣ) :
          v.1.adicCompletion F)) ∧
      WithZero.log (Valued.v
        ((S.compU v ((S.diagU (a : Fˣ)) ^ 6 * x.1) : (v.1.adicCompletion F)ˣ) :
          v.1.adicCompletion F)) <
        (6 * Fintype.card (ClassGroup (𝓞 F)) : ℤ) := by
  classical
  let N : ℤ := Fintype.card (ClassGroup (𝓞 F))
  let c : ℤ := 6 * N
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (ClassGroup (𝓞 F)))
  have hc : 0 < c := by dsimp [c]; positivity
  let t : ∀ w : S.Sf, S.US := fun w => Classical.choose (covol_sunit_prime_power_core S w)
  have ht (w : S.Sf) (v : S.Sf) :
      Valued.v (algebraMap F (v.1.adicCompletion F) ((t w : Fˣ) : F)) =
        if v.1 = w.1 then WithZero.exp N else 1 := by
    exact Classical.choose_spec (covol_sunit_prime_power_core S w) v
  let m : S.Sf → ℤ := fun v => covol_localLog S v (S.compU v x.1)
  let q : S.Sf → ℤ := fun v => -(m v / c)
  let a : S.US := ∏ w : S.Sf, (t w) ^ q w
  have hdiag (v : S.Sf) :
      covol_localLog S v (S.compU v (S.diagU (a : Fˣ))) = q v * N := by
    have hprod : S.compU v (S.diagU (a : Fˣ)) =
        ∏ w : S.Sf, (S.compU v (S.diagU ((t w : S.US) : Fˣ))) ^ q w := by
      simp [a, map_prod, map_zpow]
    have hterm (w : S.Sf) :
        covol_localLog S v (S.compU v (S.diagU ((t w : S.US) : Fˣ))) =
          if v.1 = w.1 then N else 0 := by
      by_cases hvw : v.1 = w.1
      · have hval := ht w v
        rw [if_pos hvw] at hval
        simpa [hvw] using covol_localLog_diagU_of_valued S v (t w) N hval
      · have hval := ht w v
        rw [if_neg hvw] at hval
        have hlog := covol_localLog_diagU_of_valued S v (t w) 0 (by simpa using hval)
        simpa [hvw] using hlog
    calc
      covol_localLog S v (S.compU v (S.diagU (a : Fˣ))) =
          ∑ w : S.Sf, covol_localLog S v
            (S.compU v (S.diagU ((t w : S.US) : Fˣ)) ^ q w) := by
              rw [hprod, covol_localLog_prod]
      _ = ∑ w : S.Sf, q w * (if v.1 = w.1 then N else 0) := by
            apply Finset.sum_congr rfl
            intro w hw
            rw [covol_localLog_zpow, hterm]
      _ = q v * N := by
            rw [Finset.sum_eq_single v]
            · simp
            · intro w hw hwv
              have hne : v.1 ≠ w.1 := by
                intro h
                exact hwv (Subtype.ext h.symm)
              simp [hne]
            · simp
  refine ⟨a, ?_⟩
  intro v
  have htotal :
      covol_localLog S v (S.compU v ((S.diagU (a : Fˣ)) ^ 6 * x.1)) =
        m v + c * q v := by
    calc
      _ = covol_localLog S v
          (S.compU v (S.diagU (a : Fˣ)) ^ 6 * S.compU v x.1) := by
            rw [map_mul, map_pow]
      _ = covol_localLog S v (S.compU v (S.diagU (a : Fˣ)) ^ 6) + m v := by
            rw [covol_localLog_mul]
      _ = 6 * (q v * N) + m v := by
            rw [covol_localLog_pow, hdiag]
            push_cast
            ring
      _ = m v + c * q v := by dsimp [c]; ring
  have hmod (v : S.Sf) : m v + c * q v = m v % c := by
    dsimp [q]
    have hdiv := Int.emod_add_mul_ediv (m v) c
    have hsub : m v - c * (m v / c) = m v % c := by omega
    calc
      m v + c * -(m v / c) = m v - c * (m v / c) := by ring
      _ = m v % c := hsub
  rw [show WithZero.log (Valued.v
      ((S.compU v ((S.diagU (a : Fˣ)) ^ 6 * x.1) : (v.1.adicCompletion F)ˣ) :
        v.1.adicCompletion F)) =
      covol_localLog S v (S.compU v ((S.diagU (a : Fˣ)) ^ 6 * x.1)) by rfl]
  rw [htotal, hmod]
  constructor
  · exact Int.emod_nonneg _ hc.ne'
  · simpa [c, N] using Int.emod_lt_of_pos (m v) hc

private theorem covol_local_log_compact_cover_core (v : FinPlace F) (M : ℕ) :
    ∃ K : Set (v.adicCompletion F), IsCompact K ∧
      (∀ z : (v.adicCompletion F)ˣ,
        0 ≤ WithZero.log (Valued.v (z : v.adicCompletion F)) →
        WithZero.log (Valued.v (z : v.adicCompletion F)) < (M : ℤ) →
        (z : v.adicCompletion F) ∈ K) ∧
      (∀ e : v.adicCompletion F, e ∈ v.adicCompletionIntegers F →
        ∀ z ∈ K, e * z ∈ K) := by
  classical
  obtain ⟨πF, hπF⟩ := v.valuation_exists_uniformizer F
  have hπFne : πF ≠ 0 := by
    apply (v.valuation F).ne_zero_iff.mp
    rw [hπF]
    simp
  have hπval : Valued.v (algebraMap F (v.adicCompletion F) πF) =
      WithZero.exp (-1 : ℤ) := by
    change Valued.v (πF : v.adicCompletion F) = _
    rw [v.valuedAdicCompletion_eq_valuation']
    exact hπF
  have hπcompne : algebraMap F (v.adicCompletion F) πF ≠ 0 := by
    intro hzero
    have hzeroVal : Valued.v (algebraMap F (v.adicCompletion F) πF) = 0 := by
      rw [hzero]
      exact map_zero _
    rw [hπval] at hzeroVal
    simp at hzeroVal
  let π : (v.adicCompletion F)ˣ :=
    Units.mk0 (algebraMap F (v.adicCompletion F) πF) hπcompne
  have hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := hπval
  let f : v.adicCompletion F → v.adicCompletion F := fun y =>
    (((π⁻¹) ^ M : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y
  let K : Set (v.adicCompletion F) :=
    f '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hf : Continuous f := by
    dsimp [f]
    exact continuous_const.mul continuous_id
  have hK : IsCompact K := by
    dsimp [K]
    exact adicCompletionIntegers_compact v |>.image hf
  refine ⟨K, hK, ?_, ?_⟩
  · intro z hz0 hzM
    let y : v.adicCompletion F := ((π : v.adicCompletion F) ^ M) * (z : v.adicCompletion F)
    have hπnz : Valued.v (π : v.adicCompletion F) ≠ 0 := by
      rw [hπ]
      simp
    have hznz : Valued.v (z : v.adicCompletion F) ≠ 0 :=
      (Valued.v).ne_zero_iff.mpr z.ne_zero
    have hπpowlog : WithZero.log ((Valued.v (π : v.adicCompletion F)) ^ M) =
        -(M : ℤ) := by
      rw [hπ, ← WithZero.exp_nsmul, WithZero.log_exp]
      simp
    have hylog : WithZero.log (Valued.v y) = -(M : ℤ) +
        WithZero.log (Valued.v (z : v.adicCompletion F)) := by
      dsimp [y]
      calc
        WithZero.log (Valued.v
            (((π : v.adicCompletion F) ^ M) * (z : v.adicCompletion F))) =
            WithZero.log ((Valued.v (π : v.adicCompletion F)) ^ M *
              Valued.v (z : v.adicCompletion F)) := by
                rw [Valuation.map_mul, Valuation.map_pow]
        _ = WithZero.log ((Valued.v (π : v.adicCompletion F)) ^ M) +
            WithZero.log (Valued.v (z : v.adicCompletion F)) :=
              WithZero.log_mul (pow_ne_zero _ hπnz) hznz
        _ = -(M : ℤ) + WithZero.log (Valued.v (z : v.adicCompletion F)) := by
              rw [hπpowlog]
    have hylt : WithZero.log (Valued.v y) < 0 := by
      rw [hylog]
      omega
    have hynz : Valued.v y ≠ 0 :=
      (Valued.v).ne_zero_iff.mpr (mul_ne_zero (pow_ne_zero _ π.ne_zero) z.ne_zero)
    have hyltVal : Valued.v y < 1 := by
      rw [← WithZero.log_lt_log hynz one_ne_zero, WithZero.log_one]
      exact hylt
    have hyO : y ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      exact hyltVal.le
    have hcancel : (((π⁻¹) ^ M : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
        (((π : v.adicCompletion F) ^ M)) = 1 := by
      have hunit : (π⁻¹) ^ M * π ^ M = (1 : (v.adicCompletion F)ˣ) := by
        rw [← mul_pow]
        simp
      exact congrArg (fun u : (v.adicCompletion F)ˣ => (u : v.adicCompletion F)) hunit
    have hzK : (z : v.adicCompletion F) ∈ K := by
      refine ⟨y, hyO, ?_⟩
      dsimp [f, y]
      calc
        (((π⁻¹) ^ M : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
            (((π : v.adicCompletion F) ^ M) * (z : v.adicCompletion F)) =
          ((((π⁻¹) ^ M : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
            ((π : v.adicCompletion F) ^ M)) * (z : v.adicCompletion F) := by ac_rfl
        _ = 1 * (z : v.adicCompletion F) := by rw [hcancel]
        _ = z := by simp
    exact hzK
  · intro e he z hz
    change e * z ∈ f '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))
    change z ∈ f '' (v.adicCompletionIntegers F : Set (v.adicCompletion F)) at hz
    obtain ⟨y, hyO, hy⟩ :=
      (Set.mem_image f (v.adicCompletionIntegers F : Set (v.adicCompletion F)) z).mp hz
    refine ⟨e * y, mul_mem he hyO, ?_⟩
    change (((π⁻¹) ^ M : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y = z at hy
    dsimp [f]
    calc
      (((π⁻¹) ^ M : (v.adicCompletion F)ˣ) : v.adicCompletion F) * (e * y) =
          e * ((((π⁻¹) ^ M : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y) := by ac_rfl
      _ = e * z := by rw [hy]

private theorem covol_sunit_finite_compact_reduction_core (S : SData F CE condη) :
    ∃ K : Set (∀ v : S.Sf, v.1.adicCompletion F), IsCompact K ∧
      (∀ x : {x : S.FSˣ // S.absS (x : S.FS) = 1},
        ∃ a : S.US,
          (fun v : S.Sf =>
            ((S.compU v ((S.diagU (a : Fˣ)) ^ 6 * x.1) :
              (v.1.adicCompletion F)ˣ) : v.1.adicCompletion F)) ∈ K ∧
          (∀ v : S.Sf,
            0 ≤ WithZero.log (Valued.v
              ((S.compU v ((S.diagU (a : Fˣ)) ^ 6 * x.1) :
                (v.1.adicCompletion F)ˣ) : v.1.adicCompletion F)) ∧
            WithZero.log (Valued.v
              ((S.compU v ((S.diagU (a : Fˣ)) ^ 6 * x.1) :
                (v.1.adicCompletion F)ˣ) : v.1.adicCompletion F)) <
              (6 * Fintype.card (ClassGroup (𝓞 F)) : ℤ))) ∧
      (∀ e : 𝓞 F, ∀ z, z ∈ K →
        (fun v : S.Sf =>
          algebraMap F (v.1.adicCompletion F) ((e : 𝓞 F) : F) * z v) ∈ K) := by
  classical
  let M : ℕ := 6 * Fintype.card (ClassGroup (𝓞 F))
  let Kloc : ∀ v : S.Sf, Set (v.1.adicCompletion F) := fun v =>
    Classical.choose (covol_local_log_compact_cover_core v.1 M)
  have hKloc (v : S.Sf) : IsCompact (Kloc v) := by
    exact (Classical.choose_spec (covol_local_log_compact_cover_core v.1 M)).1
  let K : Set (∀ v : S.Sf, v.1.adicCompletion F) := Set.pi Set.univ Kloc
  have hK : IsCompact K := by
    dsimp [K]
    exact isCompact_univ_pi hKloc
  refine ⟨K, hK, ?_, ?_⟩
  · intro x
    obtain ⟨a, ha⟩ := covol_sunit_finite_reduction_core S x
    refine ⟨a, ?_, ?_⟩
    · change ∀ v : S.Sf, v ∈ Set.univ →
        ((S.compU v ((S.diagU (a : Fˣ)) ^ 6 * x.1) :
          (v.1.adicCompletion F)ˣ) : v.1.adicCompletion F) ∈ Kloc v
      intro v hv
      have hcover := (Classical.choose_spec (covol_local_log_compact_cover_core v.1 M)).2.1
      apply hcover
      · exact (ha v).1
      · simpa [M] using (ha v).2
    · intro v
      simpa [M] using ha v
  · intro e z hz
    change ∀ v : S.Sf, v ∈ Set.univ →
      algebraMap F (v.1.adicCompletion F) ((e : 𝓞 F) : F) * z v ∈ Kloc v
    intro v hv
    have hzv : z v ∈ Kloc v := by
      change ∀ v : S.Sf, v ∈ Set.univ → z v ∈ Kloc v at hz
      exact hz v hv
    have he : algebraMap F (v.1.adicCompletion F) ((e : 𝓞 F) : F) ∈
        v.1.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v (((e : 𝓞 F) : F) : v.1.adicCompletion F) ≤ 1
      rw [v.1.valuedAdicCompletion_eq_valuation']
      exact v.1.valuation_le_one e
    exact (Classical.choose_spec (covol_local_log_compact_cover_core v.1 M)).2.2
      _ he (z v) hzv

private theorem covol_absFin_log_formula_core (v : FinPlace F)
    (z : v.adicCompletion F) (hz : Valued.v z ≠ 0) :
    absFin v z = (Ideal.absNorm v.asIdeal : ℝ) ^ WithZero.log (Valued.v z) := by
  dsimp [absFin]
  have hq : (Ideal.absNorm v.asIdeal : NNReal) ≠ 0 := HeightOneSpectrum.absNorm_ne_zero v
  rw [dif_pos hq, WithZeroMulInt.toNNReal_neg_apply hq hz,
    WithZero.toAdd_unzero_eq_log hz]
  norm_cast

private theorem covol_arch_log_mean_bound_core (S : SData F CE condη)
    (x : {x : S.FSˣ // S.absS (x : S.FS) = 1}) (M : ℕ)
    (hfinite : ∀ v : S.Sf,
      0 ≤ WithZero.log (Valued.v
        ((S.compU v x.1 : (v.1.adicCompletion F)ˣ) : v.1.adicCompletion F)) ∧
      WithZero.log (Valued.v
        ((S.compU v x.1 : (v.1.adicCompletion F)ˣ) : v.1.adicCompletion F)) < (M : ℤ)) :
    |(Fintype.card (InfinitePlace F) : ℝ)⁻¹ *
        ∑ w : InfinitePlace F, Real.log ‖(S.compC w x.1 : ℂ)‖| ≤
      (M : ℝ) * (∑ v : S.Sf, Real.log (Ideal.absNorm v.1.asIdeal : ℝ)) /
        (2 * (Fintype.card (InfinitePlace F) : ℝ)) := by
  classical
  let y : S.FS := x.1
  let m : S.Sf → ℤ := fun v => WithZero.log (Valued.v (y.1 v))
  let q : S.Sf → ℝ := fun v => (Ideal.absNorm v.1.asIdeal : ℝ)
  have hcoordFin (v : S.Sf) :
      ((S.compU v x.1 : (v.1.adicCompletion F)ˣ) : v.1.adicCompletion F) = y.1 v := by
    simp [SData.compU, y]
  have hcoordArch (w : InfinitePlace F) :
      (S.compC w x.1 : ℂ) = y.2 w := by
    simp [SData.compC, y]
  have hm (v : S.Sf) : 0 ≤ m v ∧ m v < (M : ℤ) := by
    simpa [m, hcoordFin] using hfinite v
  have hvalnz (v : S.Sf) : Valued.v (y.1 v) ≠ 0 := by
    rw [← hcoordFin]
    exact (Valued.v).ne_zero_iff.mpr (Units.ne_zero (S.compU v x.1))
  have hqone (v : S.Sf) : 1 < q v := by
    dsimp [q]
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.1
  have hqlog (v : S.Sf) : 0 < Real.log (q v) := Real.log_pos (hqone v)
  have habsFin (v : S.Sf) : absFin v.1 (y.1 v) = q v ^ m v := by
    simpa [m, q] using covol_absFin_log_formula_core v.1 (y.1 v) (hvalnz v)
  have hfinPos (v : S.Sf) : 0 < absFin v.1 (y.1 v) := by
    rw [habsFin]
    exact zpow_pos (by linarith [hqone v]) (m v)
  have hfinLog (v : S.Sf) :
      Real.log (absFin v.1 (y.1 v)) = (m v : ℝ) * Real.log (q v) := by
    rw [habsFin, Real.log_zpow]
  let P : ℝ := ∏ v : S.Sf, absFin v.1 (y.1 v)
  let A : ℝ := ∏ w : InfinitePlace F, Complex.normSq (y.2 w)
  have hPpos : 0 < P := by
    dsimp [P]
    exact Finset.prod_pos (fun v hv => hfinPos v)
  have hnormPos (w : InfinitePlace F) : 0 < ‖y.2 w‖ := by
    rw [← hcoordArch]
    exact norm_pos_iff.mpr (Units.ne_zero (S.compC w x.1))
  have hApos : 0 < A := by
    dsimp [A]
    exact Finset.prod_pos (fun w hw => by
      rw [Complex.normSq_eq_norm_sq]
      exact sq_pos_of_pos (hnormPos w))
  have hnormone : P * A = 1 := by
    simpa [P, A, y, SData.absS] using x.2
  have hPlog : Real.log P =
      ∑ v : S.Sf, Real.log (absFin v.1 (y.1 v)) := by
    dsimp [P]
    exact Real.log_prod (fun v hv => (hfinPos v).ne')
  have hAlog : Real.log A =
      2 * ∑ w : InfinitePlace F, Real.log ‖y.2 w‖ := by
    calc
      Real.log A = ∑ w : InfinitePlace F, Real.log (Complex.normSq (y.2 w)) := by
        dsimp [A]
        exact Real.log_prod (fun w hw => by
          rw [Complex.normSq_eq_norm_sq]
          exact (sq_pos_of_pos (hnormPos w)).ne')
      _ = ∑ w : InfinitePlace F, 2 * Real.log ‖y.2 w‖ := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [Complex.normSq_eq_norm_sq, Real.log_pow]
        norm_num
      _ = 2 * ∑ w : InfinitePlace F, Real.log ‖y.2 w‖ := by rw [Finset.mul_sum]
  have hlogprod : Real.log P + Real.log A = 0 := by
    have h := congrArg Real.log hnormone
    rw [Real.log_mul hPpos.ne' hApos.ne', Real.log_one] at h
    exact h
  have htotal :
      (∑ v : S.Sf, Real.log (absFin v.1 (y.1 v))) +
        2 * ∑ w : InfinitePlace F, Real.log ‖y.2 w‖ = 0 := by
    rw [← hPlog, ← hAlog]
    exact hlogprod
  have hfinNonneg :
      0 ≤ ∑ v : S.Sf, Real.log (absFin v.1 (y.1 v)) := by
    apply Finset.sum_nonneg
    intro v hv
    rw [hfinLog]
    exact mul_nonneg (by exact_mod_cast (hm v).1) (le_of_lt (hqlog v))
  have hfinUpper :
      (∑ v : S.Sf, Real.log (absFin v.1 (y.1 v))) ≤
        (M : ℝ) * ∑ v : S.Sf, Real.log (q v) := by
    calc
      _ = ∑ v : S.Sf, (m v : ℝ) * Real.log (q v) := by
        apply Finset.sum_congr rfl
        intro v hv
        exact hfinLog v
      _ ≤ ∑ v : S.Sf, (M : ℝ) * Real.log (q v) := by
        apply Finset.sum_le_sum
        intro v hv
        apply mul_le_mul_of_nonneg_right _ (le_of_lt (hqlog v))
        exact_mod_cast (le_of_lt (hm v).2)
      _ = (M : ℝ) * ∑ v : S.Sf, Real.log (q v) := by rw [Finset.mul_sum]
  let r : ℝ := Fintype.card (InfinitePlace F)
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (InfinitePlace F))
  let finLog : ℝ := ∑ v : S.Sf, Real.log (absFin v.1 (y.1 v))
  let archLog : ℝ := ∑ w : InfinitePlace F, Real.log ‖y.2 w‖
  have harchEq : archLog = -finLog / 2 := by
    have htotal' := htotal
    dsimp [archLog, finLog] at htotal'
    dsimp [archLog, finLog]
    linarith [htotal']
  have hmeanEq : r⁻¹ * archLog = -finLog / (2 * r) := by
    rw [harchEq]
    field_simp
    <;> ring
  have hmeanNonpos : r⁻¹ * archLog ≤ 0 := by
    rw [hmeanEq]
    have : 0 ≤ finLog := by simpa [finLog] using hfinNonneg
    apply div_nonpos_of_nonpos_of_nonneg
    · exact neg_nonpos.mpr this
    · positivity
  have hmeanAbs : |r⁻¹ * archLog| = finLog / (2 * r) := by
    rw [abs_of_nonpos hmeanNonpos, hmeanEq]
    ring
  have hfinUpper' : finLog ≤ (M : ℝ) * ∑ v : S.Sf, Real.log (q v) := by
    simpa [finLog] using hfinUpper
  have hdenpos : 0 < 2 * r := by positivity
  calc
    |r⁻¹ * archLog| = finLog / (2 * r) := hmeanAbs
    _ ≤ ((M : ℝ) * ∑ v : S.Sf, Real.log (q v)) / (2 * r) :=
      div_le_div_of_nonneg_right hfinUpper' hdenpos.le
    _ = (M : ℝ) * (∑ v : S.Sf, Real.log (Ideal.absNorm v.1.asIdeal : ℝ)) /
          (2 * (Fintype.card (InfinitePlace F) : ℝ)) := by
        simp [q, r, div_eq_mul_inv, mul_assoc, mul_comm]

private theorem covol_arch_balanced_log_core (D : FieldData F) (S : SData F CE condη)
    (x : {x : S.FSˣ // S.absS (x : S.FS) = 1}) (M : ℕ)
    (hfinite : ∀ v : S.Sf,
      0 ≤ WithZero.log (Valued.v
        ((S.compU v x.1 : (v.1.adicCompletion F)ˣ) : v.1.adicCompletion F)) ∧
      WithZero.log (Valued.v
        ((S.compU v x.1 : (v.1.adicCompletion F)ˣ) : v.1.adicCompletion F)) < (M : ℤ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ ε : (𝓞 F)ˣ, ∀ w : InfinitePlace F,
      |Real.log (‖w.embedding (algebraMap (𝓞 F) F ((ε : 𝓞 F) ^ 6))‖ *
          ‖(S.compC w x.1 : ℂ)‖)| ≤ C := by
  classical
  let E : Subgroup (𝓞 F)ˣ := (powMonoidHom (α := (𝓞 F)ˣ) 6).range
  have hfg : Monoid.FG (𝓞 F)ˣ := inferInstance
  letI : Group.FG (𝓞 F)ˣ := Group.fg_iff_monoid_fg.mpr hfg
  letI : E.FiniteIndex := by
    dsimp [E]
    exact Subgroup.finiteIndex_range_powMonoidHom_of_fg (𝓞 F)ˣ (by norm_num)
  obtain ⟨B, hBnonneg, hbalance⟩ := covol_unit_balance_core D E
  let t : InfinitePlace F → ℝ := fun w => ‖(S.compC w x.1 : ℂ)‖
  have ht (w : InfinitePlace F) : 0 < t w := by
    dsimp [t]
    exact norm_pos_iff.mpr (Units.ne_zero (S.compC w x.1))
  obtain ⟨εbal, hεE, hdev⟩ := hbalance t ht
  have hεrange : εbal ∈ (powMonoidHom (α := (𝓞 F)ˣ) 6).range := by
    simpa [E] using hεE
  obtain ⟨ε, hε⟩ := MonoidHom.mem_range.mp hεrange
  have hεpow : ε ^ 6 = εbal := by
    simpa using hε
  have hεcoe : (ε : 𝓞 F) ^ 6 = (εbal : 𝓞 F) := by
    simpa only [Units.val_pow_eq_pow_val] using
      congrArg (fun u : (𝓞 F)ˣ => (u : 𝓞 F)) hεpow
  let Cmean : ℝ :=
    (M : ℝ) * (∑ v : S.Sf, Real.log (Ideal.absNorm v.1.asIdeal : ℝ)) /
      (2 * (Fintype.card (InfinitePlace F) : ℝ))
  have hmean :
      |(Fintype.card (InfinitePlace F) : ℝ)⁻¹ *
        ∑ w : InfinitePlace F, Real.log (t w)| ≤ Cmean := by
    simpa [Cmean, t] using covol_arch_log_mean_bound_core S x M hfinite
  have hsumlog : 0 ≤ ∑ v : S.Sf,
      Real.log (Ideal.absNorm v.1.asIdeal : ℝ) := by
    apply Finset.sum_nonneg
    intro v hv
    apply le_of_lt
    apply Real.log_pos
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.1
  have hCmean : 0 ≤ Cmean := by
    dsimp [Cmean]
    apply div_nonneg
    · exact mul_nonneg (Nat.cast_nonneg _) hsumlog
    · positivity
  refine ⟨B + Cmean, add_nonneg hBnonneg hCmean, ε, ?_⟩
  intro w
  have hdev' := hdev w
  have hbound :
      |Real.log (‖w.embedding (algebraMap (𝓞 F) F (εbal : 𝓞 F))‖ * t w)| ≤
        B + Cmean := by
    let mean : ℝ := (Fintype.card (InfinitePlace F) : ℝ)⁻¹ *
      ∑ w' : InfinitePlace F, Real.log (t w')
    calc
      |Real.log (‖w.embedding (algebraMap (𝓞 F) F (εbal : 𝓞 F))‖ * t w)| =
          |(Real.log (‖w.embedding (algebraMap (𝓞 F) F (εbal : 𝓞 F))‖ * t w) - mean) +
            mean| := by congr 1 <;> ring
      _ ≤ |Real.log (‖w.embedding (algebraMap (𝓞 F) F (εbal : 𝓞 F))‖ * t w) - mean| +
            |mean| := abs_add_le _ _
      _ ≤ B + Cmean := add_le_add hdev' (by
        simpa [mean] using hmean)
  simpa [t, hεcoe] using hbound


private theorem covol_arch_uniform_balanced_log_core (D : FieldData F)
    (S : SData F CE condη) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : {x : S.FSˣ // S.absS (x : S.FS) = 1},
      (∀ v : S.Sf,
        0 ≤ WithZero.log (Valued.v
          ((S.compU v x.1 : (v.1.adicCompletion F)ˣ) : v.1.adicCompletion F)) ∧
        WithZero.log (Valued.v
          ((S.compU v x.1 : (v.1.adicCompletion F)ˣ) : v.1.adicCompletion F)) < (M : ℤ)) →
      ∃ ε : (𝓞 F)ˣ, ∀ w : InfinitePlace F,
        |Real.log (‖w.embedding (algebraMap (𝓞 F) F ((ε : 𝓞 F) ^ 6))‖ *
            ‖(S.compC w x.1 : ℂ)‖)| ≤ C := by
  classical
  let E : Subgroup (𝓞 F)ˣ := (powMonoidHom (α := (𝓞 F)ˣ) 6).range
  have hfg : Monoid.FG (𝓞 F)ˣ := inferInstance
  letI : Group.FG (𝓞 F)ˣ := Group.fg_iff_monoid_fg.mpr hfg
  letI : E.FiniteIndex := by
    dsimp [E]
    exact Subgroup.finiteIndex_range_powMonoidHom_of_fg (𝓞 F)ˣ (by norm_num)
  obtain ⟨B, hBnonneg, hbalance⟩ := covol_unit_balance_core D E
  let r : ℝ := Fintype.card (InfinitePlace F)
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (InfinitePlace F))
  let Cmean : ℝ :=
    (M : ℝ) * (∑ v : S.Sf, Real.log (Ideal.absNorm v.1.asIdeal : ℝ)) / (2 * r)
  have hsumlog : 0 ≤ ∑ v : S.Sf,
      Real.log (Ideal.absNorm v.1.asIdeal : ℝ) := by
    apply Finset.sum_nonneg
    intro v hv
    apply le_of_lt
    apply Real.log_pos
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.1
  have hCmean : 0 ≤ Cmean := by
    dsimp [Cmean]
    apply div_nonneg
    · exact mul_nonneg (Nat.cast_nonneg _) hsumlog
    · positivity
  refine ⟨B + Cmean, add_nonneg hBnonneg hCmean, ?_⟩
  intro x hfinite
  let t : InfinitePlace F → ℝ := fun w => ‖(S.compC w x.1 : ℂ)‖
  have ht (w : InfinitePlace F) : 0 < t w := by
    dsimp [t]
    exact norm_pos_iff.mpr (Units.ne_zero (S.compC w x.1))
  obtain ⟨εbal, hεE, hdev⟩ := hbalance t ht
  have hεrange : εbal ∈ (powMonoidHom (α := (𝓞 F)ˣ) 6).range := by
    simpa [E] using hεE
  obtain ⟨ε, hε⟩ := MonoidHom.mem_range.mp hεrange
  have hεpow : ε ^ 6 = εbal := by simpa using hε
  have hεcoe : (ε : 𝓞 F) ^ 6 = (εbal : 𝓞 F) := by
    simpa only [Units.val_pow_eq_pow_val] using
      congrArg (fun u : (𝓞 F)ˣ => (u : 𝓞 F)) hεpow
  have hmean :
      |r⁻¹ * ∑ w : InfinitePlace F, Real.log (t w)| ≤ Cmean := by
    simpa [Cmean, r, t] using covol_arch_log_mean_bound_core S x M hfinite
  refine ⟨ε, ?_⟩
  intro w
  have hdev' := hdev w
  have hbound :
      |Real.log (‖w.embedding (algebraMap (𝓞 F) F (εbal : 𝓞 F))‖ * t w)| ≤
        B + Cmean := by
    let mean : ℝ := r⁻¹ * ∑ w' : InfinitePlace F, Real.log (t w')
    calc
      |Real.log (‖w.embedding (algebraMap (𝓞 F) F (εbal : 𝓞 F))‖ * t w)| =
          |(Real.log (‖w.embedding (algebraMap (𝓞 F) F (εbal : 𝓞 F))‖ * t w) - mean) +
            mean| := by congr 1 <;> ring
      _ ≤ |Real.log (‖w.embedding (algebraMap (𝓞 F) F (εbal : 𝓞 F))‖ * t w) - mean| +
            |mean| := abs_add_le _ _
      _ ≤ B + Cmean := add_le_add hdev' (by simpa [mean] using hmean)
  simpa [t, hεcoe] using hbound


/-- Compact norm-one representatives modulo sixth powers of S-units, stated using only `Field`.
The norm-one condition on every point of `K` is needed by the balanced-generator target. -/
theorem fsOne_compact_representatives_core (S : SData F CE condη) (D : FieldData F) :
    ∃ K : Set S.FS, IsCompact K ∧ (∀ y ∈ K, S.absS y = 1) ∧
      ∀ x : {x : S.FSˣ // S.absS (x : S.FS) = 1},
        ∃ y : {y : S.FSˣ // S.absS (y : S.FS) = 1},
          (y.1 : S.FS) ∈ K ∧
            ∃ u : S.US, x.1 = (S.diagU (u : Fˣ)) ^ 6 * y.1 := by
  classical
  have hAbsFinNorm (v : FinPlace F) (z : v.adicCompletion F) :
      absFin v z = ‖z‖ := by
    unfold absFin
    rw [dif_pos (HeightOneSpectrum.absNorm_ne_zero v)]
    exact (FinitePlace.norm_def v z).symm
  have hAbsSMul (a b : S.FSˣ) :
      S.absS (((a * b : S.FSˣ) : S.FS)) =
        S.absS (a : S.FS) * S.absS (b : S.FS) := by
    simp only [SData.absS]
    have hfin (v : S.Sf) :
        absFin v.1 (((a * b : S.FSˣ) : S.FS).1 v) =
          absFin v.1 ((a : S.FS).1 v) * absFin v.1 ((b : S.FS).1 v) := by
      change absFin v.1 ((a : S.FS).1 v * (b : S.FS).1 v) = _
      rw [hAbsFinNorm, hAbsFinNorm, hAbsFinNorm, norm_mul]
    have harch (w : InfinitePlace F) :
        Complex.normSq (((a * b : S.FSˣ) : S.FS).2 w) =
          Complex.normSq ((a : S.FS).2 w) * Complex.normSq ((b : S.FS).2 w) := by
      simp [Complex.normSq_eq_norm_sq, norm_mul, mul_pow]
    rw [show (∏ v : S.Sf,
        absFin v.1 (((a * b : S.FSˣ) : S.FS).1 v)) =
          ∏ v : S.Sf, (absFin v.1 ((a : S.FS).1 v) * absFin v.1 ((b : S.FS).1 v)) by
            apply Finset.prod_congr rfl
            intro v hv
            exact hfin v]
    rw [show (∏ w : InfinitePlace F,
        Complex.normSq (((a * b : S.FSˣ) : S.FS).2 w)) =
          ∏ w : InfinitePlace F,
            (Complex.normSq ((a : S.FS).2 w) * Complex.normSq ((b : S.FS).2 w)) by
              apply Finset.prod_congr rfl
              intro w hw
              exact harch w]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    ring
  have hcontAbsS : Continuous S.absS := by
    change Continuous (fun y : S.FS =>
      (∏ v : S.Sf, absFin v.1 (y.1 v)) *
        ∏ w : InfinitePlace F, Complex.normSq (y.2 w))
    simp_rw [hAbsFinNorm]
    fun_prop
  let M : ℕ := 6 * Fintype.card (ClassGroup (𝓞 F))
  obtain ⟨Kfin, hKfin, hreduce, hstable⟩ :=
    covol_sunit_finite_compact_reduction_core S
  obtain ⟨C, hC, hbalance⟩ := covol_arch_uniform_balanced_log_core D S M
  let Karch : Set (InfinitePlace F → ℂ) :=
    Set.pi Set.univ (fun _ => Metric.closedBall (0 : ℂ) (Real.exp C))
  have hKarch : IsCompact Karch := by
    dsimp [Karch]
    exact isCompact_univ_pi (fun _ => isCompact_closedBall (0 : ℂ) (Real.exp C))
  let Kprod : Set S.FS := Kfin ×ˢ Karch
  have hKprod : IsCompact Kprod := hKfin.prod hKarch
  let K : Set S.FS := Kprod ∩ {y | S.absS y = 1}
  have hK : IsCompact K := by
    apply hKprod.inter_right
    exact isClosed_eq hcontAbsS continuous_const
  refine ⟨K, hK, ?_, ?_⟩
  · intro y hy
    exact hy.2
  · intro x
    obtain ⟨a, haFin, haLog⟩ := hreduce x
    let xAdj : S.FSˣ := (S.diagU (a : Fˣ)) ^ 6 * x.1
    have hdiagNorm (u : S.US) :
        S.absS ((S.diagU (u : Fˣ) : S.FSˣ) : S.FS) = 1 := by
      simpa [SData.diagU] using covol_absS_diag_sunit_eq_one_core D S u
    have hdiagPowNorm (u : S.US) :
        S.absS ((((S.diagU (u : Fˣ)) ^ 6 : S.FSˣ) : S.FS)) = 1 := by
      have h := covol_absS_diag_sunit_eq_one_core D S (u ^ 6)
      simpa [SData.diagU, map_pow] using h
    have hxAdjNorm : S.absS (xAdj : S.FS) = 1 := by
      calc
        S.absS (xAdj : S.FS) =
            S.absS (((S.diagU (a : Fˣ)) ^ 6 : S.FSˣ) : S.FS) *
              S.absS (x.1 : S.FS) := hAbsSMul _ _
        _ = 1 := by rw [hdiagPowNorm a, x.2]; norm_num
    obtain ⟨ε, hεlog⟩ := hbalance ⟨xAdj, hxAdjNorm⟩ haLog
    let εF : Fˣ := Units.map (algebraMap (𝓞 F) F).toMonoidHom ε
    have hεmem : εF ∈ S.US := by
      change ∀ v : FinPlace F, v ∉ S.Sf →
        v.valuation F ((εF : Fˣ) : F) = 1
      intro v hv
      change v.valuation F (algebraMap (𝓞 F) F (ε : 𝓞 F)) = 1
      rw [HeightOneSpectrum.valuation_eq_one_iff_notMem]
      exact Ideal.notMem_of_isUnit v.asIdeal ε.isUnit
    let εS : S.US := ⟨εF, hεmem⟩
    let u : S.US := εS * a
    let yUnit : S.FSˣ := (S.diagU (εS : Fˣ)) ^ 6 * xAdj
    have hyFactor : yUnit = (S.diagU (u : Fˣ)) ^ 6 * x.1 := by
      dsimp [yUnit, xAdj, u]
      rw [map_mul, mul_pow]
      group
    have hyNorm : S.absS (yUnit : S.FS) = 1 := by
      calc
        S.absS (yUnit : S.FS) =
            S.absS (((S.diagU (εS : Fˣ)) ^ 6 : S.FSˣ) : S.FS) *
              S.absS (xAdj : S.FS) := hAbsSMul _ _
        _ = 1 := by rw [hdiagPowNorm εS, hxAdjNorm]; norm_num
    have hyFin : (yUnit : S.FS).1 ∈ Kfin := by
      have h := hstable ((ε : 𝓞 F) ^ 6) (fun v : S.Sf => (xAdj : S.FS).1 v) haFin
      convert h using 1
      funext v
      simp [yUnit, xAdj, SData.diagU, SData.diag, εS, εF]
    have hyArchBound (w : InfinitePlace F) :
        ‖(yUnit : S.FS).2 w‖ ≤ Real.exp C := by
      have hlog := (abs_le.mp (hεlog w)).2
      have hpos : 0 <
          ‖w.embedding (algebraMap (𝓞 F) F ((ε : 𝓞 F) ^ 6))‖ *
            ‖(S.compC w xAdj : ℂ)‖ := by
        apply mul_pos
        · apply norm_pos_iff.mpr
          intro hzero
          apply Units.ne_zero (ε ^ 6)
          exact FaithfulSMul.algebraMap_injective (𝓞 F) F
            (w.embedding.injective (by simpa using hzero))
        · exact norm_pos_iff.mpr (Units.ne_zero (S.compC w xAdj))
      have hnormProd :
          ‖(yUnit : S.FS).2 w‖ =
            ‖w.embedding (algebraMap (𝓞 F) F ((ε : 𝓞 F) ^ 6))‖ *
              ‖(S.compC w xAdj : ℂ)‖ := by
        simp [yUnit, xAdj, SData.diagU, SData.diag, SData.compC, εS, εF,
          Complex.norm_mul]
      rw [hnormProd]
      exact (Real.log_le_iff_le_exp hpos).mp hlog
    have hyArch : (yUnit : S.FS).2 ∈ Karch := by
      change ∀ w : InfinitePlace F, w ∈ Set.univ →
        (yUnit : S.FS).2 w ∈ Metric.closedBall (0 : ℂ) (Real.exp C)
      intro w hw
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hyArchBound w
    have hyMem : (yUnit : S.FS) ∈ K := by
      refine ⟨⟨hyFin, hyArch⟩, hyNorm⟩
    refine ⟨⟨yUnit, hyNorm⟩, hyMem, u⁻¹, ?_⟩
    change x.1 = S.diagU ((u⁻¹ : S.US) : Fˣ) ^ 6 * yUnit
    rw [hyFactor]
    have hmapinv : S.diagU ((u⁻¹ : S.US) : Fˣ) =
        (S.diagU (u : Fˣ))⁻¹ := by
      rw [show ((u⁻¹ : S.US) : Fˣ) = ((u : Fˣ)⁻¹) by rfl, map_inv]
    rw [hmapinv]
    group

end ArtinPrimitiveRoots.Proofs.A1_LATTICE
