import ArtinPrimitiveRoots.A1.Hilbert
import ArtinPrimitiveRoots.A1.Proofs.A1_DUAL.PairingCore
import ArtinPrimitiveRoots.A1.Proofs.«A1-CRT».Localization
import OAI.NumberTheory.DirichletL.GaussSum.ChineseRemainder

/-!
# A1 interface, §4: additive character and Gauss sums

Frozen interface of part A1 (paper §§2, 2a, 3, App. 10). Each `sorry` is owned by a package of
`research/design/A1-DESIGN.md` §3, named in its docstring. Design: `research/design/A1-Interface.lean`
(Opus A1 sub-agent, 2026-10-07).
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-! ## 4. Additive character (def:ar-psi; resolves D2) and Gauss sums (eq:normalized-gauss) -/

/-- Tate's standard additive character: `ψ_v = ψ_{ℚ_p} ∘ Tr_{F_v/ℚ_p}` with
`ψ_{ℚ_p}(x) = exp(2πi{x}_p)` at finite `v`, and `ψ_w(z) = exp(-2πi·Tr_{ℂ/ℝ} z) = exp(-4πi Re z)`
at complex `w` (independent of which of the two embeddings represents `w`).
Supplied by package P-PSI (local traces); its global consequences are the fields below. -/
structure AddCharData (F : Type) [Field F] [NumberField F] where
  ψ : (v : FinPlace F) → AddChar (v.adicCompletion F) ℂ
  /-- `ψ` is trivial on `F`: the archimedean factor is `exp(-2πi Tr_{F/ℚ} z)`. -/
  trivial_on_F : ∀ z : F, (Function.mulSupport fun v => ψ v (algebraMap F _ z)).Finite ∧
    (∏ᶠ v, ψ v (algebraMap F _ z)) *
      Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ))) = 1
  /-- `ψ_v` is trivial on `O_v` at every finite place (Tate's `ψ_v` has conductor `𝔇_v⁻¹ ⊇ O_v`).
  Added 2026-10-07 after lane `a1-psi` showed `SData.e_diag_eq` false without it. -/
  integral : ∀ (v : FinPlace F) (x : v.adicCompletion F), x ∈ v.adicCompletionIntegers F →
    ψ v x = 1
  /-- at `v ∤ 𝔇`, `ψ_v` has conductor `O_v`. -/
  unramified : ∀ v : FinPlace F, ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal →
    (∀ x : v.adicCompletion F, x ∈ v.adicCompletionIntegers F → ψ v x = 1) ∧
    ∀ π : F, HeightOneSpectrum.valuation F v π = WithZero.exp (-1) →
      ∃ x : 𝓞 F, ψ v (algebraMap F _ ((x : F) / π)) ≠ 1

/-- Complex component: `ψ_w(z) = exp(-4πi Re z)`. -/
def psiC (z : ℂ) : ℂ := Complex.exp (-(4 * Real.pi * Complex.I * (z.re : ℂ)))

/-- `e(x) = Π_{v∈S} ψ_v(x_v)` on `F_S` (02:50). -/
def SData.e (S : SData F CE condη) (A : AddCharData F) (x : S.FS) : ℂ :=
  (∏ v : S.Sf, A.ψ v.1 (x.1 v)) * ∏ w : InfinitePlace F, psiC (x.2 w)

private theorem trace_eq_pair_sum_re {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (z : F) :
    (Algebra.trace ℚ F z : ℂ) =
      ∑ w : InfinitePlace F, (w.embedding z + ComplexEmbedding.conjugate w.embedding z) := by
  classical
  have htrace := trace_eq_sum_embeddings (K := ℚ) (L := F) (E := ℂ) (x := z)
  have hring :
      (∑ φ : F →+* ℂ, φ z) =
        ∑ σ : F →ₐ[ℚ] ℂ, σ z := by
    exact Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) _ _ (fun _ => rfl)
  have hall : (Algebra.trace ℚ F z : ℂ) = ∑ φ : F →+* ℂ, φ z := by
    rw [hring.symm] at htrace
    exact htrace
  rw [hall]
  rw [← Finset.sum_fiberwise (s := Finset.univ)
    (g := fun φ : F →+* ℂ => InfinitePlace.mk φ) (f := fun φ => φ z)]
  apply Finset.sum_congr rfl
  intro w hw
  have hmk (φ : F →+* ℂ) : InfinitePlace.mk φ = w ↔
      φ = w.embedding ∨ φ = ComplexEmbedding.conjugate w.embedding := by
    constructor
    · intro h
      rw [← InfinitePlace.mk_embedding w] at h
      have h' := InfinitePlace.mk_eq_iff.mp h
      rcases h' with h' | h'
      · exact Or.inl (by simpa using h')
      · right
        have hc := congrArg ComplexEmbedding.conjugate h'
        simpa using hc
    · intro h
      rw [← InfinitePlace.mk_embedding w]
      apply InfinitePlace.mk_eq_iff.mpr
      rcases h with h | h
      · exact Or.inl (by simpa using h)
      · right
        have hc := congrArg ComplexEmbedding.conjugate h
        simpa using hc
  have hneq : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
    intro h
    apply (IsTotallyComplex.complexEmbedding_not_isReal w.embedding)
    rw [ComplexEmbedding.isReal_iff]
    exact h.symm
  have hset : Finset.univ.filter (fun φ : F →+* ℂ => InfinitePlace.mk φ = w) =
      ({w.embedding, ComplexEmbedding.conjugate w.embedding} : Finset (F →+* ℂ)) := by
    ext φ
    simp [hmk]
  change (∑ φ ∈ Finset.univ.filter
    (fun φ : F →+* ℂ => InfinitePlace.mk φ = w), φ z) = _
  rw [hset, Finset.sum_pair hneq]

private theorem trace_eq_two_real_sum {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (z : F) :
    (Algebra.trace ℚ F z : ℂ) =
      (2 : ℂ) * ∑ w : InfinitePlace F, ((w.embedding z).re : ℂ) := by
  rw [trace_eq_pair_sum_re]
  simp only [ComplexEmbedding.conjugate_coe_eq, Complex.add_conj]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [Finset.mul_sum]

private theorem arch_exp_eq_trace {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (z : F) :
    (∏ w : InfinitePlace F,
        Complex.exp (-(4 * Real.pi * Complex.I * ((w.embedding z).re : ℂ)))) =
      Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ))) := by
  rw [← Complex.exp_sum]
  apply congrArg Complex.exp
  calc
    ∑ w : InfinitePlace F,
        -(4 * Real.pi * Complex.I * ((w.embedding z).re : ℂ)) =
        -(4 * Real.pi * Complex.I *
          ∑ w : InfinitePlace F, ((w.embedding z).re : ℂ)) := by
            rw [Finset.sum_neg_distrib, Finset.mul_sum]
    _ = -(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ)) := by
      rw [trace_eq_two_real_sum]
      ring

/-- Global formula for `e` on `F` (derived in A1-DESIGN §2.2): if `z' - z ∈ O_v` at every finite
`v ∉ S` and `z' ∈ O_v` at `v ∈ S_f`, then `e(z) = exp(-2πi Tr_{F/ℚ} z')`. Package P-PSI. -/
theorem SData.e_diag_eq [IsTotallyComplex F] (S : SData F CE condη) (A : AddCharData F) (z z' : F)
    (h1 : ∀ v : FinPlace F, v ∉ S.Sf →
      HeightOneSpectrum.valuation F v (z' - z) ≤ 1)
    (h2 : ∀ v ∈ S.Sf, HeightOneSpectrum.valuation F v z' ≤ 1) :
    S.e A (S.diag z) = Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z' : ℂ))) := by
  classical
  let f : FinPlace F → ℂ := fun v =>
    A.ψ v (algebraMap F (v.adicCompletion F) (z - z'))
  have houtside (v : FinPlace F) (hv : v ∉ S.Sf) : f v = 1 := by
    have hval : v.valuation F (z - z') ≤ 1 := by
      rw [show z - z' = -(z' - z) by ring, Valuation.map_neg]
      exact h1 v hv
    have hmem : (algebraMap F (v.adicCompletion F) (z - z')) ∈
        v.adicCompletionIntegers F := by
      change ((z - z' : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F
      rw [HeightOneSpectrum.mem_adicCompletionIntegers,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact hval
    exact A.integral v _ hmem
  let e : {v : FinPlace F // v ∈ S.Sf} ↪ PLift (FinPlace F) :=
    ⟨fun v => PLift.up v.1, fun a b h => Subtype.ext (congrArg PLift.down h)⟩
  let s : Finset (PLift (FinPlace F)) := S.Sf.attach.map e
  have hsupp : Function.mulSupport (f ∘ PLift.down) ⊆ s := by
    intro x hx
    change f x.down ≠ 1 at hx
    have hxS : x.down ∈ S.Sf := by
      by_contra hnot
      exact hx (houtside x.down hnot)
    apply Finset.mem_map.mpr
    exact ⟨⟨x.down, hxS⟩, Finset.mem_attach _ _, by cases x; rfl⟩
  have hfinprod : (∏ᶠ v, f v) = ∏ v : S.Sf, f v := by
    rw [finprod_eq_prod_plift_of_mulSupport_subset hsupp]
    simp [s, e]
    apply Finset.prod_congr rfl
    intro v hv
    rfl
  have hinside (v : S.Sf) :
      A.ψ v.1 (algebraMap F (v.1.adicCompletion F) z') = 1 := by
    apply A.integral
    change ((z' : F) : v.1.adicCompletion F) ∈ v.1.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact h2 v.1 v.2
  have hlocal (v : S.Sf) :
      f v.1 = A.ψ v.1 (algebraMap F (v.1.adicCompletion F) z) := by
    have hsum :
        algebraMap F (v.1.adicCompletion F) (z - z') +
            algebraMap F (v.1.adicCompletion F) z' =
          algebraMap F (v.1.adicCompletion F) z := by
      rw [← map_add]
      congr 1
      ring
    have hchar := (A.ψ v.1).map_add_eq_mul
      (algebraMap F (v.1.adicCompletion F) (z - z'))
      (algebraMap F (v.1.adicCompletion F) z')
    rw [hsum, hinside v, mul_one] at hchar
    exact hchar.symm
  have hSprod :
      (∏ v : S.Sf, A.ψ v.1 (algebraMap F (v.1.adicCompletion F) z)) =
        ∏ v : S.Sf, f v := by
    apply Finset.prod_congr rfl
    intro v hv
    exact (hlocal v).symm
  have hglobal := (A.trivial_on_F (z - z')).2
  rw [hfinprod, ← hSprod] at hglobal
  change
    (∏ v : S.Sf, A.ψ v.1 (algebraMap F (v.1.adicCompletion F) z)) *
        Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F (z - z') : ℂ))) = 1 at hglobal
  have hprod :
      (∏ v : S.Sf, A.ψ v.1 (algebraMap F (v.1.adicCompletion F) z)) =
        Complex.exp (2 * Real.pi * Complex.I * (Algebra.trace ℚ F (z - z') : ℂ)) := by
    have hexp := eq_inv_of_mul_eq_one_right hglobal
    rw [Complex.exp_neg] at hexp
    exact ((inv_inj).mp hexp).symm
  change
    (∏ v : S.Sf, A.ψ v.1 (algebraMap F (v.1.adicCompletion F) z)) *
        ∏ w : InfinitePlace F, psiC (w.embedding z) =
      Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z' : ℂ)))
  rw [hprod]
  change Complex.exp (2 * Real.pi * Complex.I *
      (Algebra.trace ℚ F (z - z') : ℂ)) *
      (∏ w : InfinitePlace F,
        Complex.exp (-(4 * Real.pi * Complex.I * ((w.embedding z).re : ℂ)))) = _
  rw [arch_exp_eq_trace]
  rw [← Complex.exp_add]
  congr 1
  simp only [map_sub]
  push_cast
  ring

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

set_option linter.unusedSectionVars false in
lemma normSq_embedding_eq [IsTotallyComplex F] (w : InfinitePlace F) (x : F) :
    Complex.normSq (w.embedding x) = w x ^ w.mult := by
  rw [IsTotallyComplex.mult_eq w, Complex.normSq_eq_norm_sq, InfinitePlace.norm_embedding_eq]

lemma absS_diag_eq [IsTotallyComplex F] (S : SData F CE condη) (x : F) :
    S.absS (S.diag x) = (∏ v ∈ S.Sf, ‖FinitePlace.embedding v x‖) * ∏ w : InfinitePlace F, w x ^ w.mult := by
  dsimp [SData.absS, SData.diag]
  congr 1
  · change (∏ v ∈ S.Sf.attach, absFin v.1 (algebraMap F (v.1.adicCompletion F) x)) = _
    rw [Finset.prod_attach S.Sf (fun v => absFin v (algebraMap F (v.adicCompletion F) x))]
    refine Finset.prod_congr rfl ?_
    intro v hv
    exact absFin_algebraMap v x
  · change (∏ w : InfinitePlace F, Complex.normSq (w.embedding x)) = _
    refine Fintype.prod_congr _ _ ?_
    intro w
    exact normSq_embedding_eq w x

lemma norm_embedding_le_one_of_valuation_le_one (v : HeightOneSpectrum (𝓞 F)) (z : F)
    (hz : v.valuation F z ≤ 1) :
    ‖FinitePlace.embedding v z‖ ≤ 1 := by
  rw [FinitePlace.norm_embedding']
  exact NNReal.coe_le_one.mpr
    ((WithZeroMulInt.toNNReal_le_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal v)).mpr hz)

/-- lem:s-lattice (e)/(f) (02:63–108; consumed at 05:152): `‖x‖_S = N(xR)` for `x ∈ F^×`
generating the exterior fractional ideal `I`; in particular `‖x‖_S ≥ 1` for `x ∈ R ∖ 0`.
Package P-ARITH-BASE. -/
theorem SData.absS_diag_eq_norm [IsTotallyComplex F] (S : SData F CE condη) (x : F) (I : Ideal (𝓞 F))
    (hI : S.IsExterior I) (hx : S.IsGen x I) :
    S.absS (S.diag x) = Ideal.absNorm I := by
  have hx0 : x ≠ 0 := hx.2.1
  have hprod := prod_abs_eq_one hx0
  have hf_supp : (Function.mulSupport fun v => ‖FinitePlace.embedding v x‖).Finite :=
    finitePlace_mk_hasFiniteMulSupport hx0
  have h_split : (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖FinitePlace.embedding v x‖) =
      (∏ v ∈ S.Sf, ‖FinitePlace.embedding v x‖) * ∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v x‖ := by
    have h_union := finprod_mem_union' (hst := disjoint_compl_right)
      (hs := S.Sf.finite_toSet.inter_of_left _)
      (ht := Set.Finite.subset hf_supp Set.inter_subset_right)
      (f := fun v => ‖FinitePlace.embedding v x‖)
    rw [Set.union_compl_self, finprod_mem_univ] at h_union
    rw [finprod_mem_coe_finset] at h_union
    exact h_union
  have h_prod_decomp : (∏ᶠ w : FinitePlace F, w x) =
      (∏ v ∈ S.Sf, ‖FinitePlace.embedding v x‖) * ∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v x‖ := by
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    change (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖FinitePlace.embedding v x‖) = _
    exact h_split
  rw [h_prod_decomp] at hprod
  have h_absS : S.absS (S.diag x) = (∏ v ∈ S.Sf, ‖FinitePlace.embedding v x‖) * ∏ w : InfinitePlace F, w x ^ w.mult :=
    absS_diag_eq S x
  have h_prod_absS : S.absS (S.diag x) * (∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v x‖) = 1 := by
    rw [h_absS]
    calc ((∏ v ∈ S.Sf, ‖FinitePlace.embedding v x‖) * ∏ w : InfinitePlace F, w x ^ w.mult) *
          (∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v x‖)
      _ = (∏ w : InfinitePlace F, w x ^ w.mult) *
          ((∏ v ∈ S.Sf, ‖FinitePlace.embedding v x‖) * ∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v x‖) := by ring
      _ = 1 := hprod
  have h_ext := finprod_exterior_norm_embedding_mul_absNorm hI hx
  calc S.absS (S.diag x)
    _ = S.absS (S.diag x) * 1 := by rw [mul_one]
    _ = S.absS (S.diag x) * ((∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v x‖) * (Ideal.absNorm I : ℝ)) := by rw [← h_ext]
    _ = (S.absS (S.diag x) * (∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v x‖)) * (Ideal.absNorm I : ℝ) := by rw [mul_assoc]
    _ = 1 * (Ideal.absNorm I : ℝ) := by rw [h_prod_absS]
    _ = (Ideal.absNorm I : ℝ) := by rw [one_mul]

private theorem e_diag_R_eq_one (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) (r : S.R) :
    S.e A (S.diag (r : F)) = 1 := by
  letI : IsTotallyComplex F := D.isTotallyComplex
  have hrmem : (r : F) ∈ (S.Sf : Set (FinPlace F)).integer F := r.property
  have hr : ∀ v : FinPlace F, v ∉ S.Sf → v.valuation F (r : F) ≤ 1 := by
    intro v hv
    change ∀ v ∉ S.Sf, v.valuation F (r : F) ≤ 1 at hrmem
    exact hrmem v hv
  have h1 : ∀ v : FinPlace F, v ∉ S.Sf →
      v.valuation F (0 - (r : F)) ≤ 1 := by
    intro v hv
    rw [zero_sub, Valuation.map_neg]
    exact hr v hv
  have h2 : ∀ v : FinPlace F, v ∈ S.Sf → v.valuation F (0 : F) ≤ 1 := by
    intro v hv
    simp
  rw [S.e_diag_eq A (r : F) 0 h1 h2]
  simp

private theorem integral_div_gen (S : SData F CE condη) (I : Ideal (𝓞 F))
    (c : F) (hc : S.IsGen c I) (n : 𝓞 F) (hn : n ∈ I) :
    algebraMap (𝓞 F) F n / c ∈ S.R := by
  classical
  by_cases hn0 : n = 0
  · subst n
    simp
  change ∀ v : FinPlace F, v ∉ S.Sf →
    v.valuation F (algebraMap (𝓞 F) F n / c) ≤ 1
  intro v hv
  have hnmap : algebraMap (𝓞 F) F n ≠ 0 := by
    intro h
    exact hn0 ((FaithfulSMul.algebraMap_injective (𝓞 F) F) h)
  have hspan : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
      (algebraMap (𝓞 F) F n) ≤ (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
    rw [FractionalIdeal.spanSingleton_le_iff_mem]
    simpa using hn
  have hspanNe : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
      (algebraMap (𝓞 F) F n) ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.mpr hnmap
  have hmono : FractionalIdeal.count F v
      (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≤
      FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          (algebraMap (𝓞 F) F n)) :=
    FractionalIdeal.count_mono F v hspanNe hspan
  have hcount : FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) c) ≤
      FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          (algebraMap (𝓞 F) F n)) := by
    calc
      _ = FractionalIdeal.count F v
          (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := hc.2.2 v hv
      _ ≤ FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
            (algebraMap (𝓞 F) F n)) := hmono
  have hcount' := hcount
  rw [count_spanSingleton_eq_neg_log_valuation_addchar v c hc.2.1,
    count_spanSingleton_eq_neg_log_valuation_addchar v
      (algebraMap (𝓞 F) F n) hnmap] at hcount'
  have hlog : WithZero.log (v.valuation F (algebraMap (𝓞 F) F n)) ≤
      WithZero.log (v.valuation F c) := by linarith
  have hnvalNe : v.valuation F (algebraMap (𝓞 F) F n) ≠ 0 :=
    (v.valuation F).ne_zero_iff.mpr hnmap
  have hcvalNe : v.valuation F c ≠ 0 := (v.valuation F).ne_zero_iff.mpr hc.2.1
  have hval : v.valuation F (algebraMap (𝓞 F) F n) ≤ v.valuation F c := by
    calc
      v.valuation F (algebraMap (𝓞 F) F n) =
          WithZero.exp (WithZero.log (v.valuation F (algebraMap (𝓞 F) F n))) :=
        (WithZero.exp_log hnvalNe).symm
      _ ≤ WithZero.exp (WithZero.log (v.valuation F c)) := WithZero.exp_le_exp.mpr hlog
      _ = v.valuation F c := WithZero.exp_log hcvalNe
  rw [map_div₀]
  exact (div_le_one₀ (by
    rw [← WithZero.exp_log hcvalNe]
    exact WithZero.exp_pos)).2 hval

private theorem mem_ideal_of_div_mem_R (S : SData F CE condη) (I : Ideal (𝓞 F))
    (hI : S.IsExterior I) (c : F) (hc : S.IsGen c I) (n : 𝓞 F)
    (hn : algebraMap (𝓞 F) F n / c ∈ S.R) : n ∈ I := by
  classical
  by_cases hn0 : n = 0
  · subst n
    exact I.zero_mem
  change ∀ q : FinPlace F, q ∉ S.Sf →
    q.valuation F (algebraMap (𝓞 F) F n / c) ≤ 1 at hn
  rw [← Ideal.iInf_maxPowDividing_eq hI.1]
  simp only [Submodule.mem_iInf]
  intro q
  change n ∈ q.maxPowDividing I
  let e : ℕ := (Associates.mk q.asIdeal).count (Associates.mk I).factors
  change n ∈ q.asIdeal ^ e
  by_cases hqS : q ∈ S.Sf
  · have hezero : e = 0 := by
      dsimp [e]
      by_contra he
      have hdvd := (Associates.count_ne_zero_iff_dvd hI.1 q.irreducible).mp he
      rw [Ideal.dvd_iff_le] at hdvd
      exact hI.2 q hqS hdvd
    rw [hezero]
    simp
  · have hcountI : FractionalIdeal.count F q
        (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = (e : ℤ) := by
      rw [FractionalIdeal.count_coe F q hI.1]
    have hcountC : FractionalIdeal.count F q
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) c) = (e : ℤ) := by
      rw [hc.2.2 q hqS, hcountI]
    have hcountCLog :=
      count_spanSingleton_eq_neg_log_valuation_addchar q c hc.2.1
    rw [hcountC] at hcountCLog
    have hlogC : WithZero.log (q.valuation F c) = -(e : ℤ) := by
      linarith
    have hcValNe : q.valuation F c ≠ 0 := (q.valuation F).ne_zero_iff.mpr hc.2.1
    have hvalC : q.valuation F c = WithZero.exp (-(e : ℤ)) := by
      calc
        q.valuation F c = WithZero.exp (WithZero.log (q.valuation F c)) :=
          (WithZero.exp_log hcValNe).symm
        _ = WithZero.exp (-(e : ℤ)) := by rw [hlogC]
    have hqR := hn q hqS
    rw [map_div₀] at hqR
    have hcValPos : 0 < q.valuation F c := by
      rw [hvalC]
      exact WithZero.exp_pos
    have hvalN : q.valuation F (algebraMap (𝓞 F) F n) ≤
        WithZero.exp (-(e : ℤ)) := by
      have h := (div_le_one₀ hcValPos).1 hqR
      rw [hvalC] at h
      exact h
    have hIntVal : q.intValuation n ≤ WithZero.exp (-(e : ℤ)) := by
      rw [← q.valuation_of_algebraMap (K := F)]
      exact hvalN
    exact (q.intValuation_le_pow_iff_mem n e).1 hIntVal

/-- lem:s-lattice, the self-duality consequence used at 02:397 and 06:76: for an exterior ideal `I`
with generator `c`, `(n, d) ↦ e(nd/c)` is a perfect pairing on `O_F/I`. Package P-ARITH-BASE.
Corrected per rev-theta to state both annihilator directions under fixed field data. -/
theorem SData.e_pairing_perfect (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) (I : Ideal (𝓞 F)) (hI : S.IsExterior I) (c : F)
    (hc : S.IsGen c I) :
    (∀ n : 𝓞 F, n ∈ I → ∀ d : 𝓞 F,
      S.e A (S.diag (algebraMap (𝓞 F) F (n * d) / c)) = 1) ∧
    (∀ n : 𝓞 F,
      (∀ d : 𝓞 F, S.e A (S.diag (algebraMap (𝓞 F) F (n * d) / c)) = 1) → n ∈ I) := by
  classical
  letI : IsTotallyComplex F := D.isTotallyComplex
  constructor
  · intro n hn d
    have hnd : n * d ∈ I := by
      simpa [mul_comm] using I.mul_mem_left d hn
    have hdiv := integral_div_gen S I c hc (n * d) hnd
    exact e_diag_R_eq_one D S A ⟨_, hdiv⟩
  · intro n htriv
    by_contra hnI
    let z : F := algebraMap (𝓞 F) F n / c
    have hzR : z ∉ S.R := by
      intro hz
      exact hnI (mem_ideal_of_div_mem_R S I hI c hc n (by simpa [z] using hz))
    obtain ⟨d, hdetect⟩ :=
      ArtinPrimitiveRoots.Proofs.a1_dual_p.external_character_detector S A.ψ
        A.trivial_on_F A.integral A.unramified z hzR
    have hdetect' : S.e A (S.diag (z * (d : F))) ≠ 1 := by
      simpa [SData.e, psiC, ArtinPrimitiveRoots.Proofs.a1_dual_p.eOnFS] using hdetect
    have hzmul : z * (d : F) = algebraMap (𝓞 F) F (n * d) / c := by
      simp [z, map_mul]
      ring
    exact hdetect' (by rw [hzmul]; exact htriv d)

/-- Normalized Gauss sum `γ_j(𝔠) = q_𝔠^{-1/2} Σ_{x mod 𝔠} χ_𝔠(x)^j e(x/c)` for a squarefree
exterior ideal `I = 𝔠` with allowed generator `c` (eq:normalized-gauss, 02:391). The finite sum is a
`finsum` over `O_F/I` (finite for `I ≠ ⊥`). -/
def gamma (D : FieldData F) (S : SData F CE condη) (A : AddCharData F) (j : ℤ)
    (I : Ideal (𝓞 F)) (c : F) : ℂ :=
  ((Ideal.absNorm I : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
    ∑ᶠ x : 𝓞 F ⧸ I, chiIdealPow D I (algebraMap (𝓞 F) F x.out) j *
      S.e A (S.diag (algebraMap (𝓞 F) F x.out / c))

open ArtinPrimitiveRoots.Proofs.A1Generators ArtinPrimitiveRoots.Proofs.A1CRT

local instance crt_residue_maximal (v : FinPlace F) : v.asIdeal.IsMaximal := v.isMaximal
noncomputable local instance crt_residue_field (v : FinPlace F) : Field (𝓞 F ⧸ v.asIdeal) :=
  Ideal.Quotient.field v.asIdeal

private theorem crt_count_coe_eq_factors (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (v : FinPlace F) :
    FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      (Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors I) : ℤ) := by
  have hI0 : I ≠ 0 := by simpa only [Ideal.zero_eq_bot] using hI
  rw [FractionalIdeal.count_coe F v hI0]
  exact_mod_cast (Ideal.count_associates_factors_eq hI0 v.isPrime v.ne_bot)

private theorem crt_count_principal_le (v : FinPlace F) {a c : F}
    (ha : a ≠ 0) (hc : c ≠ 0) (hval : v.valuation F a ≤ v.valuation F c) :
    FractionalIdeal.count F v (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) c) ≤
      FractionalIdeal.count F v (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) a) := by
  have hlog : WithZero.log (v.valuation F a) ≤ WithZero.log (v.valuation F c) :=
    (WithZero.log_le_log ((v.valuation F).ne_zero_iff.mpr ha)
      ((v.valuation F).ne_zero_iff.mpr hc)).2 hval
  rw [count_spanSingleton_eq_neg_log_valuation_addchar v c hc,
    count_spanSingleton_eq_neg_log_valuation_addchar v a ha]
  exact neg_le_neg hlog

private theorem crt_valuation_le_principal_count_le (v : FinPlace F) {a c : F}
    (ha : a ≠ 0) (hc : c ≠ 0)
    (hcount : FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) c) ≤
      FractionalIdeal.count F v (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) a)) :
    v.valuation F a ≤ v.valuation F c := by
  have hlog : WithZero.log (v.valuation F a) ≤ WithZero.log (v.valuation F c) := by
    rw [count_spanSingleton_eq_neg_log_valuation_addchar v c hc,
      count_spanSingleton_eq_neg_log_valuation_addchar v a ha] at hcount
    linarith
  exact (WithZero.log_le_log ((v.valuation F).ne_zero_iff.mpr ha)
    ((v.valuation F).ne_zero_iff.mpr hc)).mp hlog

private theorem crt_ideal_mem_of_valuation_le (S : SData F CE condη)
    {I : Ideal (𝓞 F)} (hI : S.IsExterior I) {c : F} (hc : S.IsGen c I)
    (a : 𝓞 F) (hval : ∀ v : FinPlace F, v ∉ S.Sf →
      v.valuation F (a : F) ≤ v.valuation F c) : a ∈ I := by
  by_cases ha0 : a = 0
  · simp [ha0]
  have haF : (a : F) ≠ 0 := by
    intro h
    exact ha0 ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
  have hspan : Ideal.span {a} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot, Ideal.zero_eq_bot] using ha0
  have hfactor : UniqueFactorizationMonoid.normalizedFactors I ≤
      UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a}) := by
    apply Multiset.le_iff_count.mpr
    intro Q
    by_cases hQ : Q.IsPrime ∧ Q ≠ ⊥
    · let v : FinPlace F := ⟨Q, hQ.1, hQ.2⟩
      by_cases hvS : v ∈ S.Sf
      · have hnot : Q ∉ UniqueFactorizationMonoid.normalizedFactors I := by
          intro hmem
          have hP := (Ideal.mem_normalizedFactors_iff hI.1).mp hmem
          have hle : I ≤ Q := hP.2
          exact hI.2 v hvS (by simpa [v] using hle)
        rw [Multiset.count_eq_zero.mpr hnot]
        exact Nat.zero_le _
      · have hcount : FractionalIdeal.count F v
            (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≤
          FractionalIdeal.count F v
            (Ideal.span {a} : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
          calc
            _ = FractionalIdeal.count F v
                (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) c) :=
                  (hc.2.2 v hvS).symm
            _ ≤ _ := crt_count_principal_le v haF hc.2.1 (hval v hvS)
            _ = FractionalIdeal.count F v
                (Ideal.span {a} : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
                  rw [← FractionalIdeal.coeIdeal_span_singleton]
        rw [crt_count_coe_eq_factors I hI.1 v,
          crt_count_coe_eq_factors (Ideal.span {a}) hspan v] at hcount
        exact_mod_cast hcount
    · have hnot : Q ∉ UniqueFactorizationMonoid.normalizedFactors I := by
        intro hmem
        have hP := (Ideal.mem_normalizedFactors_iff hI.1).mp hmem
        have hQ0 : Q ≠ ⊥ := by
          intro hbot
          apply hI.1
          exact bot_unique (by simpa [hbot] using hP.2)
        exact hQ ⟨hP.1, hQ0⟩
      rw [Multiset.count_eq_zero.mpr hnot]
      exact Nat.zero_le _
  have hdiv : I ∣ Ideal.span {a} :=
    (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hI.1 hspan).2 hfactor
  have hle : Ideal.span {a} ≤ I := Ideal.dvd_iff_le.mp hdiv
  exact hle (Ideal.subset_span (by simp))

private theorem crt_denominator_quotient_unit (S : SData F CE condη)
    (I : Ideal (𝓞 F)) (hI : S.IsExterior I) (d : generatorDenominators S) :
    IsUnit (Ideal.Quotient.mk I (d : 𝓞 F)) := by
  have htop : Ideal.span {(d : 𝓞 F)} ⊔ I = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hIM : I ≤ M := le_trans le_sup_right hle
    have hM0 : M ≠ ⊥ := by
      intro hMbot
      exact hI.1 (bot_unique (by simpa [hMbot] using hIM))
    let v : FinPlace F := ⟨M, hM.isPrime, hM0⟩
    by_cases hvS : v ∈ S.Sf
    · exact hI.2 v hvS (by simpa [v] using hIM)
    · have hdv := d.property.2 v hvS
      have hnotmem : (d : 𝓞 F) ∉ v.asIdeal := v.valuation_eq_one_iff_notMem.mp hdv
      have hspan : Ideal.span {(d : 𝓞 F)} ≤ v.asIdeal := le_trans le_sup_left hle
      exact hnotmem (hspan (Ideal.subset_span (by simp)))
  have hone : (1 : 𝓞 F) ∈ Ideal.span {(d : 𝓞 F)} ⊔ I := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hone
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hx
  apply isUnit_iff_exists_inv.mpr
  refine ⟨Ideal.Quotient.mk I c, ?_⟩
  have heq := congrArg (Ideal.Quotient.mk I) hxy
  rw [map_add, map_mul, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr hy, add_zero] at heq
  simpa [mul_comm] using heq

private noncomputable def crtResidueRed (S : SData F CE condη) (I : Ideal (𝓞 F))
    (hI : S.IsExterior I) : S.R →+* 𝓞 F ⧸ I := by
  letI : IsLocalization (generatorDenominators S) S.R := sInteger_isLocalization S
  exact IsLocalization.lift (M := generatorDenominators S) (S := S.R)
    (g := Ideal.Quotient.mk I) (crt_denominator_quotient_unit S I hI)

private theorem crtResidueRed_integral (S : SData F CE condη) (I : Ideal (𝓞 F))
    (hI : S.IsExterior I) (a : 𝓞 F) :
    crtResidueRed S I hI (algebraMap (𝓞 F) S.R a) = Ideal.Quotient.mk I a := by
  letI : IsLocalization (generatorDenominators S) S.R := sInteger_isLocalization S
  simp [crtResidueRed, IsLocalization.lift_eq]

private theorem crtResidueRed_ker (S : SData F CE condη) (I : Ideal (𝓞 F))
    (hI : S.IsExterior I) :
    RingHom.ker (crtResidueRed S I hI) = Ideal.map (algebraMap (𝓞 F) S.R) I := by
  classical
  letI : IsLocalization (generatorDenominators S) S.R := sInteger_isLocalization S
  ext x
  change crtResidueRed S I hI x = 0 ↔ x ∈ Ideal.map (algebraMap (𝓞 F) S.R) I
  constructor
  · intro hx
    obtain ⟨a, d, hxd⟩ := IsLocalization.exists_mk'_eq (generatorDenominators S) x
    have hmk : crtResidueRed S I hI (IsLocalization.mk' S.R a d) = 0 := by
      rw [hxd]
      exact hx
    have ha0 : Ideal.Quotient.mk I a = 0 := by
      have hspec := IsLocalization.lift_mk'_spec
        (M := generatorDenominators S) (S := S.R)
        (crt_denominator_quotient_unit S I hI) a 0 d
      simpa [crtResidueRed] using hspec.mp hmk
    have haI : a ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp ha0
    rw [← hxd]
    exact (IsLocalization.mk'_mem_map_algebraMap_iff
      (M := generatorDenominators S) (S := S.R) I a d).2
        ⟨1, (generatorDenominators S).one_mem, by simpa using haI⟩
  · intro hx
    obtain ⟨y, hxd⟩ :=
      (IsLocalization.mem_map_algebraMap_iff
        (M := generatorDenominators S) (S := S.R) (I := I) (z := x)).mp hx
    have hyI : (y.1 : 𝓞 F) ∈ I := y.1.property
    have hred := congrArg (crtResidueRed S I hI) hxd
    have hdunit := crt_denominator_quotient_unit S I hI y.2
    have hzero : Ideal.Quotient.mk I (y.1 : 𝓞 F) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hyI
    have hmul : crtResidueRed S I hI x * Ideal.Quotient.mk I (y.2 : 𝓞 F) = 0 := by
      rw [map_mul, crtResidueRed_integral S I hI (y.2 : 𝓞 F),
        crtResidueRed_integral S I hI (y.1 : 𝓞 F), hzero] at hred
      exact hred
    exact (IsUnit.mul_left_eq_zero hdunit).mp hmul

private def crtSInteger (S : SData F CE condη) {I : Ideal (𝓞 F)} {c : F}
    (hc : S.IsGen c I) : S.R := ⟨c, by
    change ∀ v : FinPlace F, v ∉ S.Sf → v.valuation F c ≤ 1
    intro v hv
    have hcount : 0 ≤ FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) c) := by
      rw [hc.2.2 v hv]
      exact FractionalIdeal.count_coe_nonneg F v I
    rw [count_spanSingleton_eq_neg_log_valuation_addchar v c hc.2.1] at hcount
    have hlog : WithZero.log (v.valuation F c) ≤ 0 := by linarith
    exact WithZero.le_exp_of_log_le hlog⟩

private theorem crt_ideal_map_eq_span (S : SData F CE condη) {I : Ideal (𝓞 F)}
    (hI : S.IsExterior I) {c : F} (hc : S.IsGen c I) :
    Ideal.map (algebraMap (𝓞 F) S.R) I = Ideal.span {crtSInteger S hc} := by
  let cR : S.R := crtSInteger S hc
  change Ideal.map (algebraMap (𝓞 F) S.R) I = Ideal.span {cR}
  have hunder : (Ideal.span {cR}).under (𝓞 F) = I := by
    ext a
    change algebraMap (𝓞 F) S.R a ∈ Ideal.span {cR} ↔ a ∈ I
    constructor
    · intro ha
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp ha
      have hfield : (a : F) = c * (r : F) := by
        have h := congrArg (fun z : S.R => (z : F)) hr
        change (r : F) * (cR : F) = (a : F) at h
        calc
          (a : F) = (r : F) * (cR : F) := h.symm
          _ = c * (r : F) := by
            rw [show (cR : F) = c from rfl]
            exact mul_comm _ _
      apply crt_ideal_mem_of_valuation_le S hI hc a
      intro v hv
      rw [hfield, map_mul]
      calc
        v.valuation F c * v.valuation F (r : F) ≤ v.valuation F c * 1 :=
          mul_le_mul_of_nonneg_left (r.property v hv) (zero_le)
        _ = v.valuation F c := by simp
    · intro ha
      by_cases ha0 : a = 0
      · subst a
        simp
      have haF : (a : F) ≠ 0 := by
        intro h
        exact ha0 ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
      have hspan : Ideal.span {a} ≠ ⊥ := by
        simpa [Ideal.span_singleton_eq_bot, Ideal.zero_eq_bot] using ha0
      have hspanle : Ideal.span {a} ≤ I := Ideal.span_le.mpr (by
        intro x hx
        rw [Set.mem_singleton_iff.mp hx]
        exact ha)
      have hspanleF :
          (Ideal.span {a} : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≤
            (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
        (FractionalIdeal.coeIdeal_le_coeIdeal F).2 hspanle
      have hspanF :
          (Ideal.span {a} : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 :=
        FractionalIdeal.coeIdeal_ne_zero.mpr (by simpa only [Ideal.zero_eq_bot] using hspan)
      let r : S.R := ⟨(a : F) / c, by
        change ∀ v : FinPlace F, v ∉ S.Sf → v.valuation F ((a : F) / c) ≤ 1
        intro v hv
        have hcount : FractionalIdeal.count F v
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) c) ≤
          FractionalIdeal.count F v
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) := by
          calc
            _ = FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
              hc.2.2 v hv
            _ ≤ FractionalIdeal.count F v
                (Ideal.span {a} : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
              FractionalIdeal.count_mono F v hspanF hspanleF
            _ = _ := by rw [FractionalIdeal.coeIdeal_span_singleton]
        have hval := crt_valuation_le_principal_count_le v haF hc.2.1 hcount
        rw [Valuation.map_div]
        exact (div_le_one₀
          (WithZero.pos_iff_ne_zero.mpr ((v.valuation F).ne_zero_iff.mpr hc.2.1))).2 hval⟩
      apply Ideal.mem_span_singleton'.mpr
      refine ⟨r, ?_⟩
      apply Subtype.ext
      change ((a : F) / c) * c = (a : F)
      field_simp [hc.2.1]
  letI : IsLocalization (generatorDenominators S) S.R := sInteger_isLocalization S
  calc
    Ideal.map (algebraMap (𝓞 F) S.R) I =
        Ideal.map (algebraMap (𝓞 F) S.R) ((Ideal.span {cR}).under (𝓞 F)) := by rw [hunder]
    _ = Ideal.span {cR} :=
      IsLocalization.map_under (generatorDenominators S) S.R (Ideal.span {cR})

private noncomputable def crtResidueEquiv (S : SData F CE condη) {I : Ideal (𝓞 F)}
    (hI : S.IsExterior I) {c : F} (hc : S.IsGen c I) :
    S.R ⧸ Ideal.span {crtSInteger S hc} ≃+* 𝓞 F ⧸ I := by
  let cR : S.R := crtSInteger S hc
  have hmap : Ideal.map (algebraMap (𝓞 F) S.R) I = Ideal.span {cR} :=
    crt_ideal_map_eq_span S hI hc
  have hker : RingHom.ker (crtResidueRed S I hI) = Ideal.span {cR} := by
    rw [crtResidueRed_ker S I hI, hmap]
  have hsurj : Function.Surjective (crtResidueRed S I hI) := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨algebraMap (𝓞 F) S.R a, crtResidueRed_integral S I hI a⟩
  exact (Ideal.quotEquivOfEq hker).symm.trans
    (RingHom.quotientKerEquivOfSurjective hsurj)

private theorem crtResidueEquiv_mk (S : SData F CE condη) {I : Ideal (𝓞 F)}
    (hI : S.IsExterior I) {c : F} (hc : S.IsGen c I) (x : S.R) :
    crtResidueEquiv S hI hc (Ideal.Quotient.mk (Ideal.span {crtSInteger S hc}) x) =
      crtResidueRed S I hI x := by
  let cR := crtSInteger S hc
  have hmap : Ideal.map (algebraMap (𝓞 F) S.R) I = Ideal.span {cR} :=
    crt_ideal_map_eq_span S hI hc
  have hker : RingHom.ker (crtResidueRed S I hI) = Ideal.span {cR} := by
    rw [crtResidueRed_ker S I hI, hmap]
  have hsurj : Function.Surjective (crtResidueRed S I hI) := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨algebraMap (𝓞 F) S.R a, crtResidueRed_integral S I hI a⟩
  change ((Ideal.quotEquivOfEq hker).symm.trans
      (RingHom.quotientKerEquivOfSurjective hsurj))
      (Ideal.Quotient.mk (Ideal.span {cR}) x) = crtResidueRed S I hI x
  simp [Ideal.quotEquivOfEq_symm, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

private theorem crt_residue_rep (v : FinPlace F) (x : F) (a b : 𝓞 F)
    (hb : b ∉ v.asIdeal)
    (hab : x * algebraMap (𝓞 F) F b = algebraMap (𝓞 F) F a) :
    residue v x = Ideal.Quotient.mk v.asIdeal a / Ideal.Quotient.mk v.asIdeal b := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hex : ∃ ab : 𝓞 F × 𝓞 F, ab.2 ∉ v.asIdeal ∧
      x * algebraMap (𝓞 F) F ab.2 = algebraMap (𝓞 F) F ab.1 := ⟨(a, b), hb, hab⟩
  have hcross : hex.choose.1 * b = a * hex.choose.2 := by
    apply IsFractionRing.injective (𝓞 F) F
    simp only [map_mul]
    rw [← hex.choose_spec.2, ← hab]
    ring
  have hqcross := congrArg (Ideal.Quotient.mk v.asIdeal) hcross
  have hbq : Ideal.Quotient.mk v.asIdeal b ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hb
  have hdq : Ideal.Quotient.mk v.asIdeal hex.choose.2 ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hex.choose_spec.1
  unfold residue
  rw [dif_pos hex]
  rw [← div_eq_mul_inv, div_eq_div_iff hdq hbq]
  simpa only [map_mul] using hqcross

set_option maxHeartbeats 1000000 in
private theorem crt_residue_compat (S : SData F CE condη) {I : Ideal (𝓞 F)}
    (hI : S.IsExterior I) (v : FinPlace F) (hvS : v ∉ S.Sf) (hIv : I ≤ v.asIdeal)
    (x : S.R) :
    residue v (x : F) =
      Ideal.Quotient.factor hIv (crtResidueRed S I hI x) := by
  classical
  letI : IsLocalization (generatorDenominators S) S.R := sInteger_isLocalization S
  obtain ⟨a, d, hxd⟩ := sInteger_fraction S x
  have hdv : v.valuation F ((d : 𝓞 F) : F) = 1 := d.property.2 v hvS
  have hdnot : (d : 𝓞 F) ∉ v.asIdeal := v.valuation_eq_one_iff_notMem.mp hdv
  have hdi : IsUnit (Ideal.Quotient.mk I (d : 𝓞 F)) :=
    crt_denominator_quotient_unit S I hI d
  let ud : (𝓞 F ⧸ I)ˣ := hdi.unit
  have hud : (ud : 𝓞 F ⧸ I) = Ideal.Quotient.mk I (d : 𝓞 F) := hdi.unit_spec
  have hmk : IsLocalization.mk' S.R a d = x := by
    apply IsLocalization.mk'_eq_iff_eq_mul.mpr
    apply Subtype.ext
    change (a : F) = (x : F) * ((d : 𝓞 F) : F)
    exact hxd.symm
  have hredFrac : crtResidueRed S I hI x =
      Ideal.Quotient.mk I a * ((ud⁻¹ : (𝓞 F ⧸ I)ˣ) : 𝓞 F ⧸ I) := by
    rw [← hmk]
    change IsLocalization.lift (M := generatorDenominators S) (S := S.R)
        (g := Ideal.Quotient.mk I) (crt_denominator_quotient_unit S I hI)
        (IsLocalization.mk' S.R a d) = _
    apply (IsLocalization.lift_mk'_spec
      (M := generatorDenominators S) (S := S.R)
      (crt_denominator_quotient_unit S I hI) a
      (Ideal.Quotient.mk I a * ((ud⁻¹ : (𝓞 F ⧸ I)ˣ) : 𝓞 F ⧸ I)) d).mpr
    calc
      Ideal.Quotient.mk I a = (ud : 𝓞 F ⧸ I) *
          (Ideal.Quotient.mk I a * ((ud⁻¹ : (𝓞 F ⧸ I)ˣ) : 𝓞 F ⧸ I)) := by
        have hu : (ud : 𝓞 F ⧸ I) * ((ud⁻¹ : (𝓞 F ⧸ I)ˣ) : 𝓞 F ⧸ I) = 1 :=
          congrArg Units.val (mul_inv_cancel ud)
        calc
          Ideal.Quotient.mk I a = 1 * Ideal.Quotient.mk I a := by simp
          _ = ((ud : 𝓞 F ⧸ I) * ((ud⁻¹ : (𝓞 F ⧸ I)ˣ) : 𝓞 F ⧸ I)) *
              Ideal.Quotient.mk I a := by rw [hu]
          _ = (ud : 𝓞 F ⧸ I) *
              (Ideal.Quotient.mk I a * ((ud⁻¹ : (𝓞 F ⧸ I)ˣ) : 𝓞 F ⧸ I)) := by ring
      _ = Ideal.Quotient.mk I (d : 𝓞 F) *
          (Ideal.Quotient.mk I a * ((ud⁻¹ : (𝓞 F ⧸ I)ˣ) : 𝓞 F ⧸ I)) := by
        rw [← hud]
  have hmapFrac :
      Ideal.Quotient.factor hIv
        (Ideal.Quotient.mk I a * ((ud⁻¹ : (𝓞 F ⧸ I)ˣ) : 𝓞 F ⧸ I)) =
        Ideal.Quotient.mk v.asIdeal a / Ideal.Quotient.mk v.asIdeal (d : 𝓞 F) := by
    let f := Ideal.Quotient.factor hIv
    let udv : (𝓞 F ⧸ v.asIdeal)ˣ := Units.map f.toMonoidHom ud
    have hval : (udv : 𝓞 F ⧸ v.asIdeal) = Ideal.Quotient.mk v.asIdeal (d : 𝓞 F) := by
      simp [udv, f, ud]
    have hinv : f ((ud⁻¹ : (𝓞 F ⧸ I)ˣ) : 𝓞 F ⧸ I) =
        (Ideal.Quotient.mk v.asIdeal (d : 𝓞 F))⁻¹ := by
      calc
        f ((ud⁻¹ : (𝓞 F ⧸ I)ˣ) : 𝓞 F ⧸ I) =
            ((Units.map f.toMonoidHom (ud⁻¹) : (𝓞 F ⧸ v.asIdeal)ˣ) : 𝓞 F ⧸ v.asIdeal) := rfl
        _ = ((Units.map f.toMonoidHom ud)⁻¹ : (𝓞 F ⧸ v.asIdeal)ˣ) := by rw [map_inv]
        _ = (Ideal.Quotient.mk v.asIdeal (d : 𝓞 F))⁻¹ := by
          have hvalInv := congrArg (fun z : 𝓞 F ⧸ v.asIdeal => z⁻¹) hval
          simpa only [udv, Units.val_inv_eq_inv_val] using hvalInv
    calc
      f (Ideal.Quotient.mk I a * ((ud⁻¹ : (𝓞 F ⧸ I)ˣ) : 𝓞 F ⧸ I)) =
          f (Ideal.Quotient.mk I a) * f ((ud⁻¹ : (𝓞 F ⧸ I)ˣ) : 𝓞 F ⧸ I) := map_mul _ _ _
      _ = Ideal.Quotient.mk v.asIdeal a * (Ideal.Quotient.mk v.asIdeal (d : 𝓞 F))⁻¹ := by
        rw [Ideal.Quotient.factor_mk, hinv]
      _ = _ := by rw [div_eq_mul_inv]
  calc
    residue v (x : F) =
        Ideal.Quotient.mk v.asIdeal a / Ideal.Quotient.mk v.asIdeal (d : 𝓞 F) :=
      crt_residue_rep v (x : F) a (d : 𝓞 F) hdnot hxd
    _ = Ideal.Quotient.factor hIv (crtResidueRed S I hI x) := by
      rw [hredFrac, hmapFrac]

private theorem crt_residue_algInt (v : FinPlace F) (a : 𝓞 F) :
    residue v (algebraMap (𝓞 F) F a) = Ideal.Quotient.mk v.asIdeal a := by
  have h := crt_residue_rep v (algebraMap (𝓞 F) F a) a 1
    (Ideal.IsPrime.one_notMem v.isPrime) (by simp)
  simpa using h

private theorem crt_roots6_reduce_injective (v : FinPlace F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) :
    Function.Injective (fun ζ : rootsOfUnity 6 (𝓞 F) =>
      Ideal.Quotient.mk v.asIdeal ((ζ : (𝓞 F)ˣ) : 𝓞 F)) := by
  intro ζ η h
  let ρ : rootsOfUnity 6 (𝓞 F) := ζ * η⁻¹
  let q : (𝓞 F)ˣ →* (𝓞 F ⧸ v.asIdeal)ˣ :=
    Units.map (Ideal.Quotient.mk v.asIdeal).toMonoidHom
  have hq : q ζ = q η := by
    apply Units.ext
    exact h
  have hqηinv : q (η⁻¹ : rootsOfUnity 6 (𝓞 F)) = (q η)⁻¹ := by
    apply Units.ext
    simp [q, Units.val_inv_eq_inv_val]
  have hqρ : q ρ = 1 := by
    change q (ζ * η⁻¹) = 1
    rw [map_mul, hqηinv, hq]
    exact mul_inv_cancel (q η)
  have hρ : Ideal.Quotient.mk v.asIdeal ((ρ : (𝓞 F)ˣ) : 𝓞 F) = 1 :=
    congrArg Units.val hqρ
  let r : 𝓞 F := ((ρ : (𝓞 F)ˣ) : 𝓞 F)
  have hrpow : r ^ 6 = 1 := by
    have hp := (mem_rootsOfUnity 6 (ρ : (𝓞 F)ˣ)).mp ρ.2
    exact congrArg (fun z : (𝓞 F)ˣ => (z : 𝓞 F)) hp
  let S : 𝓞 F := ∑ i ∈ Finset.range 6, r ^ i
  have hsexp : S = 1 + r + r ^ 2 + r ^ 3 + r ^ 4 + r ^ 5 := by
    simp [S, Finset.sum_range_succ]
  have hgeom : (r - 1) * S = 0 := by
    rw [hsexp]
    calc
      (r - 1) * (1 + r + r ^ 2 + r ^ 3 + r ^ 4 + r ^ 5) = r ^ 6 - 1 := by ring
      _ = 0 := by rw [hrpow]; ring
  by_contra hne
  have hr_ne : r ≠ 1 := by
    intro heq
    have hρval : (ρ : (𝓞 F)ˣ) = 1 := by
      apply Units.ext
      exact heq
    have hρroot : ρ = 1 := by
      apply Subtype.ext
      exact hρval
    have hz := congrArg (fun z : rootsOfUnity 6 (𝓞 F) => z * η) hρroot
    apply hne
    simpa [ρ] using hz
  have hSzero : S = 0 := (mul_eq_zero.mp hgeom).resolve_left (sub_ne_zero.mpr hr_ne)
  have hsum : Ideal.Quotient.mk v.asIdeal S = 6 := by
    have hρr : Ideal.Quotient.mk v.asIdeal r = 1 := by
      dsimp [r]
      exact hρ
    rw [hsexp]
    simp only [map_add, map_one, map_pow, hρr, one_pow]
    norm_num
  have hmk6 : Ideal.Quotient.mk v.asIdeal (6 : 𝓞 F) = 0 := by
    calc
      Ideal.Quotient.mk v.asIdeal (6 : 𝓞 F) = (6 : 𝓞 F ⧸ v.asIdeal) :=
        map_natCast (Ideal.Quotient.mk v.asIdeal) 6
      _ = Ideal.Quotient.mk v.asIdeal S := hsum.symm
      _ = 0 := by rw [hSzero]; exact map_zero (Ideal.Quotient.mk v.asIdeal)
  exact hv ((Ideal.Quotient.eq_zero_iff_mem).1 hmk6)

private theorem crt_chiAlg_spec (D : FieldData F) (v : FinPlace F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (x : F) (hx : residue v x ≠ 0) :
    Ideal.Quotient.mk v.asIdeal ((chiAlg v x : (𝓞 F)ˣ) : 𝓞 F) =
      residue v x ^ ((Ideal.absNorm v.asIdeal - 1) / 6) := by
  have ⟨hcop, hne1⟩ := coprime_six_of_not_mem_six v hv
  have hdvd6 := six_dvd_absNorm_sub_one D v hv
  have hζ6 : IsPrimitiveRoot (D.ζ12 ^ 2) 6 :=
    D.hζ12.pow_of_dvd (p := 2) (by decide) (by decide)
  have hprim := hζ6.toInteger_isPrimitiveRoot.idealQuotient_mk
    (I := v.asIdeal) hne1 hcop
  have hru : IsUnit (residue v x) := isUnit_iff_ne_zero.mpr hx
  let ru : (𝓞 F ⧸ v.asIdeal)ˣ := hru.unit
  have hrueq : (ru : 𝓞 F ⧸ v.asIdeal) = residue v x := rfl
  have hrpow : (residue v x ^ ((Ideal.absNorm v.asIdeal - 1) / 6)) ^ 6 = 1 := by
    rw [← pow_mul, mul_comm, Nat.mul_div_cancel' hdvd6]
    have hvalpow : ((ru : 𝓞 F ⧸ v.asIdeal) ^ (Ideal.absNorm v.asIdeal - 1)) =
        (((ru ^ (Ideal.absNorm v.asIdeal - 1) : (𝓞 F ⧸ v.asIdeal)ˣ) :
          𝓞 F ⧸ v.asIdeal)) := by
      exact (Units.val_pow_eq_pow_val ru _).symm
    have hrucard : ru ^ (Ideal.absNorm v.asIdeal - 1) = 1 := by
      have hcard : Nat.card (𝓞 F ⧸ v.asIdeal)ˣ = Ideal.absNorm v.asIdeal - 1 := by
        rw [Nat.card_units, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
      rw [← hcard]
      exact pow_card_eq_one'
    rw [← hrueq, hvalpow, hrucard, Units.val_one]
  obtain ⟨i, hi, heq⟩ := hprim.eq_pow_of_pow_eq_one hrpow
  have hζpow : (hζ6.toInteger ^ i) ^ 6 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ6.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
  let ζ₀ : rootsOfUnity 6 (𝓞 F) := rootsOfUnity.mkOfPowEq (hζ6.toInteger ^ i) hζpow
  have hex : ∃ ζ : rootsOfUnity 6 (𝓞 F),
      Ideal.Quotient.mk v.asIdeal ((ζ : (𝓞 F)ˣ) : 𝓞 F) =
        residue v x ^ ((Ideal.absNorm v.asIdeal - 1) / 6) := by
    refine ⟨ζ₀, ?_⟩
    have hcoe : ((ζ₀ : (𝓞 F)ˣ) : 𝓞 F) = hζ6.toInteger ^ i :=
      rootsOfUnity.coe_mkOfPowEq hζpow
    rw [hcoe, map_pow]
    exact heq
  rw [chiAlg, dif_pos hex]
  exact hex.choose_spec

private theorem crt_chiAlg_mul (D : FieldData F) (v : FinPlace F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (a b : 𝓞 F)
    (ha : a ∉ v.asIdeal) (hb : b ∉ v.asIdeal) :
    chiAlg v ((a : F) * (b : F)) = chiAlg v (a : F) * chiAlg v (b : F) := by
  have hres_a : residue v (a : F) ≠ 0 := by
    rw [crt_residue_algInt]
    exact fun h => ha (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hres_b : residue v (b : F) ≠ 0 := by
    rw [crt_residue_algInt]
    exact fun h => hb (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hres_mul : residue v ((a : F) * (b : F)) =
      residue v (a : F) * residue v (b : F) := by
    calc
      residue v ((a : F) * (b : F)) = residue v (algebraMap (𝓞 F) F (a * b)) := by
        congr 1
      _ = Ideal.Quotient.mk v.asIdeal (a * b) := crt_residue_algInt v (a * b)
      _ = Ideal.Quotient.mk v.asIdeal a * Ideal.Quotient.mk v.asIdeal b := map_mul _ _ _
      _ = residue v (a : F) * residue v (b : F) := by
        rw [crt_residue_algInt, crt_residue_algInt]
  have hres_mul_ne : residue v ((a : F) * (b : F)) ≠ 0 := by
    rw [hres_mul]
    exact mul_ne_zero hres_a hres_b
  apply crt_roots6_reduce_injective v hv
  change Ideal.Quotient.mk v.asIdeal
      ((chiAlg v ((a : F) * (b : F)) : (𝓞 F)ˣ) : 𝓞 F) =
    Ideal.Quotient.mk v.asIdeal
      (((chiAlg v (a : F) * chiAlg v (b : F) : rootsOfUnity 6 (𝓞 F)) :
        (𝓞 F)ˣ) : 𝓞 F)
  rw [crt_chiAlg_spec D v hv _ hres_mul_ne]
  have hcoe : (((chiAlg v (a : F) * chiAlg v (b : F) : rootsOfUnity 6 (𝓞 F)) :
      (𝓞 F)ˣ) : 𝓞 F) =
      ((chiAlg v (a : F) : (𝓞 F)ˣ) : 𝓞 F) *
        ((chiAlg v (b : F) : (𝓞 F)ˣ) : 𝓞 F) := by
    push_cast
    rfl
  rw [hcoe, map_mul, crt_chiAlg_spec D v hv _ hres_a,
    crt_chiAlg_spec D v hv _ hres_b, ← mul_pow, ← hres_mul]

private theorem crt_chi_congr (D : FieldData F) (v : FinPlace F) (x y : F)
    (h : residue v x = residue v y) : chi D v x = chi D v y := by
  simp only [chi, chiAlg, h]

private theorem crt_chi_mul_integral (D : FieldData F) (v : FinPlace F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (a b : 𝓞 F)
    (ha : a ∉ v.asIdeal) (hb : b ∉ v.asIdeal) :
    chi D v ((a : F) * (b : F)) = chi D v (a : F) * chi D v (b : F) := by
  have hres_a : residue v (a : F) ≠ 0 := by
    rw [crt_residue_algInt]
    exact fun h => ha (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hres_b : residue v (b : F) ≠ 0 := by
    rw [crt_residue_algInt]
    exact fun h => hb (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hres_ab : residue v ((a : F) * (b : F)) ≠ 0 := by
    rw [show ((a : F) * (b : F)) = algebraMap (𝓞 F) F (a * b) by simp,
      crt_residue_algInt, map_mul, ← crt_residue_algInt, ← crt_residue_algInt]
    exact mul_ne_zero hres_a hres_b
  unfold chi
  rw [if_neg hres_ab, if_neg hres_a, if_neg hres_b,
    crt_chiAlg_mul D v hv a b ha hb]
  have hcoe : (((chiAlg v (a : F) * chiAlg v (b : F) : rootsOfUnity 6 (𝓞 F)) :
      (𝓞 F)ˣ) : 𝓞 F) =
      ((chiAlg v (a : F) : (𝓞 F)ˣ) : 𝓞 F) *
        ((chiAlg v (b : F) : (𝓞 F)ˣ) : 𝓞 F) := by
    push_cast
    rfl
  rw [hcoe]
  exact map_mul (D.σ0.comp (algebraMap (𝓞 F) F)) _ _

private theorem crt_chi_ne_zero (D : FieldData F) (v : FinPlace F) (x : F)
    (hx : residue v x ≠ 0) : chi D v x ≠ 0 := by
  rw [chi, if_neg hx]
  apply (map_ne_zero D.σ0).2
  intro h
  exact (Units.ne_zero (chiAlg v x)) ((IsFractionRing.injective (𝓞 F) F) h)

private theorem crt_residue_mul_integral (v : FinPlace F) (a b : 𝓞 F) :
    residue v ((a : F) * (b : F)) = residue v (a : F) * residue v (b : F) := by
  rw [show ((a : F) * (b : F)) = algebraMap (𝓞 F) F (a * b) by simp,
    crt_residue_algInt, map_mul, ← crt_residue_algInt, ← crt_residue_algInt]

private theorem crt_chiPow_mul_integral (D : FieldData F) (v : FinPlace F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (a b : 𝓞 F) (j : ℤ) :
    chiPow D v ((a : F) * (b : F)) j = chiPow D v (a : F) j * chiPow D v (b : F) j := by
  by_cases ha : residue v (a : F) = 0
  · have hab : residue v ((a : F) * (b : F)) = 0 := by
      rw [crt_residue_mul_integral]
      simp [ha]
    simp [chiPow, ha, hab]
  by_cases hb : residue v (b : F) = 0
  · have hab : residue v ((a : F) * (b : F)) = 0 := by
      rw [crt_residue_mul_integral]
      simp [hb]
    simp [chiPow, hb, hab]
  have hab : residue v ((a : F) * (b : F)) ≠ 0 := by
    rw [crt_residue_mul_integral]
    exact mul_ne_zero ha hb
  have hnota : a ∉ v.asIdeal := by
    intro h
    apply ha
    rw [crt_residue_algInt]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr h
  have hnotb : b ∉ v.asIdeal := by
    intro h
    apply hb
    rw [crt_residue_algInt]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr h
  have hχmul := crt_chi_mul_integral D v hv a b
    hnota hnotb
  have hχA := crt_chi_ne_zero D v (a : F) ha
  have hχB := crt_chi_ne_zero D v (b : F) hb
  have hχAB := crt_chi_ne_zero D v ((a : F) * (b : F)) hab
  let uA : ℂˣ := Units.mk0 (chi D v (a : F)) hχA
  let uB : ℂˣ := Units.mk0 (chi D v (b : F)) hχB
  let uAB : ℂˣ := Units.mk0 (chi D v ((a : F) * (b : F))) hχAB
  have hmul : uAB = uA * uB := by
    apply Units.ext
    exact hχmul
  calc
    chiPow D v ((a : F) * (b : F)) j = ((uAB ^ j : ℂˣ) : ℂ) := by
      simp [chiPow, hab, uAB, Units.val_zpow_eq_zpow_val]
    _ = ((uA ^ j : ℂˣ) : ℂ) * ((uB ^ j : ℂˣ) : ℂ) := by
      rw [hmul, mul_zpow, Units.val_mul]
    _ = chiPow D v (a : F) j * chiPow D v (b : F) j := by
      simp [chiPow, ha, hb, uA, uB, Units.val_zpow_eq_zpow_val]

private theorem crt_residue_integral_congr (v : FinPlace F) (a b : 𝓞 F)
    (hab : a - b ∈ v.asIdeal) : residue v (a : F) = residue v (b : F) := by
  rw [crt_residue_algInt, crt_residue_algInt, ← sub_eq_zero, ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hab

private theorem crt_chiPow_congr (D : FieldData F) (v : FinPlace F) (j : ℤ)
    {a b : 𝓞 F} (hab : a - b ∈ v.asIdeal) :
    chiPow D v (a : F) j = chiPow D v (b : F) j := by
  have hres := crt_residue_integral_congr v a b hab
  have hχ := crt_chi_congr D v (a : F) (b : F) hres
  unfold chiPow
  rw [hres, hχ]

private theorem crt_chiPow_residue_congr (D : FieldData F) (v : FinPlace F) (j : ℤ)
    {x y : F} (hres : residue v x = residue v y) :
    chiPow D v x j = chiPow D v y j := by
  unfold chiPow
  rw [hres, crt_chi_congr D v x y hres]

private theorem crt_multiset_prod_mul {α M : Type*} [CommMonoidWithZero M]
    (s : Multiset α) (f g : α → M) :
    (s.map (fun x => f x * g x)).prod = (s.map f).prod * (s.map g).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih, mul_assoc, mul_left_comm, mul_comm]

private theorem crt_chiIdealPow_congr (D : FieldData F) (I : Ideal (𝓞 F))
    (hI : I ≠ ⊥) (a b : 𝓞 F) (hab : a - b ∈ I) (j : ℤ) :
    chiIdealPow D I (a : F) j = chiIdealPow D I (b : F) j := by
  unfold chiIdealPow
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro Q hQ
  by_cases hQ' : Q.IsPrime ∧ Q ≠ ⊥
  · have hfac := (Ideal.mem_normalizedFactors_iff hI).mp hQ
    have habQ : a - b ∈ Q := hfac.2 hab
    simp only [dif_pos hQ']
    exact crt_chiPow_congr D ⟨Q, hQ'.1, hQ'.2⟩ j habQ
  · simp [hQ']

private theorem crt_chiIdealPow_mul (D : FieldData F) (S : SData F CE condη)
    {I : Ideal (𝓞 F)} (hI : S.IsExterior I) (a b : 𝓞 F) (j : ℤ) :
    chiIdealPow D I ((a : F) * (b : F)) j =
      chiIdealPow D I (a : F) j * chiIdealPow D I (b : F) j := by
  let factors := UniqueFactorizationMonoid.normalizedFactors I
  let f : Ideal (𝓞 F) → ℂ := fun Q =>
    if hQ : Q.IsPrime ∧ Q ≠ ⊥ then chiPow D ⟨Q, hQ.1, hQ.2⟩ (a : F) j else 1
  let g : Ideal (𝓞 F) → ℂ := fun Q =>
    if hQ : Q.IsPrime ∧ Q ≠ ⊥ then chiPow D ⟨Q, hQ.1, hQ.2⟩ (b : F) j else 1
  have hmap : factors.map (fun Q =>
      if hQ : Q.IsPrime ∧ Q ≠ ⊥ then chiPow D ⟨Q, hQ.1, hQ.2⟩ ((a : F) * (b : F)) j else 1) =
      factors.map (fun Q => f Q * g Q) := by
    apply Multiset.map_congr rfl
    intro Q hQ
    by_cases hQ' : Q.IsPrime ∧ Q ≠ ⊥
    · have hfac := (Ideal.mem_normalizedFactors_iff hI.1).mp hQ
      let v : FinPlace F := ⟨Q, hQ'.1, hQ'.2⟩
      have hvS : v ∉ S.Sf := by
        intro hv
        exact hI.2 v hv (by simpa [v] using hfac.2)
      have h6 : (6 : 𝓞 F) ∉ Q := by
        intro hmem
        exact hvS (S.over6 v hmem)
      simp only [dif_pos hQ']
      simp only [f, g, dif_pos hQ']
      exact crt_chiPow_mul_integral D v h6 a b j
    · simp [f, g, hQ']
  unfold chiIdealPow
  calc
    (factors.map (fun Q =>
        if hQ : Q.IsPrime ∧ Q ≠ ⊥ then
          chiPow D ⟨Q, hQ.1, hQ.2⟩ ((a : F) * (b : F)) j else 1)).prod
      = (factors.map (fun Q => f Q * g Q)).prod := congrArg Multiset.prod hmap
    _ = (factors.map f).prod * (factors.map g).prod := crt_multiset_prod_mul factors f g
    _ = _ := by simp [f, g, factors]

private theorem crt_chi_one (D : FieldData F) (v : FinPlace F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) : chi D v (1 : F) = 1 := by
  have hmul := crt_chi_mul_integral D v hv 1 1
    (Ideal.IsPrime.one_notMem v.isPrime) (Ideal.IsPrime.one_notMem v.isPrime)
  have hres : residue v (1 : F) ≠ 0 := by
    rw [show (1 : F) = algebraMap (𝓞 F) F (1 : 𝓞 F) by simp,
      crt_residue_algInt]
    exact one_ne_zero
  have hne : chi D v (1 : F) ≠ 0 := by
    rw [chi, if_neg hres]
    apply (map_ne_zero D.σ0).2
    intro h
    exact (Units.ne_zero (chiAlg v (1 : F)))
      ((IsFractionRing.injective (𝓞 F) F) h)
  have hself : chi D v (1 : F) = chi D v (1 : F) * chi D v (1 : F) := by
    simpa using hmul
  have hzero : chi D v (1 : F) * (chi D v (1 : F) - 1) = 0 := by
    calc
      _ = chi D v (1 : F) * chi D v (1 : F) - chi D v (1 : F) := by ring
      _ = 0 := by rw [← hself]; ring
  rcases mul_eq_zero.mp hzero with hz | hz
  · exact (hne hz).elim
  · exact sub_eq_zero.mp hz

private theorem crt_chiIdealPow_one (D : FieldData F) (S : SData F CE condη)
    {I : Ideal (𝓞 F)} (hI : S.IsExterior I) (j : ℤ) :
    chiIdealPow D I (1 : F) j = 1 := by
  unfold chiIdealPow
  let factors := UniqueFactorizationMonoid.normalizedFactors I
  let f : Ideal (𝓞 F) → ℂ := fun Q =>
    if hQ : Q.IsPrime ∧ Q ≠ ⊥ then chiPow D ⟨Q, hQ.1, hQ.2⟩ (1 : F) j else 1
  have hmap : factors.map (fun Q =>
      if hQ : Q.IsPrime ∧ Q ≠ ⊥ then chiPow D ⟨Q, hQ.1, hQ.2⟩ (1 : F) j else 1) =
      factors.map (fun _ => (1 : ℂ)) := by
    apply Multiset.map_congr rfl
    intro Q hQ
    by_cases hQ' : Q.IsPrime ∧ Q ≠ ⊥
    · have hfac := (Ideal.mem_normalizedFactors_iff hI.1).mp hQ
      let v : FinPlace F := ⟨Q, hQ'.1, hQ'.2⟩
      have hvS : v ∉ S.Sf := by
        intro hv
        exact hI.2 v hv (by simpa [v] using hfac.2)
      have h6 : (6 : 𝓞 F) ∉ Q := by
        intro hmem
        exact hvS (S.over6 v hmem)
      have hres : residue v (1 : F) ≠ 0 := by
        rw [show (1 : F) = algebraMap (𝓞 F) F (1 : 𝓞 F) by simp,
          crt_residue_algInt]
        exact fun hz => Ideal.IsPrime.one_notMem v.isPrime
          (Ideal.Quotient.eq_zero_iff_mem.mp hz)
      simp only [dif_pos hQ']
      change chiPow D v (1 : F) j = 1
      simp [chiPow, hres, crt_chi_one D v h6]
    · simp [hQ']
  calc
    (factors.map (fun Q => if hQ : Q.IsPrime ∧ Q ≠ ⊥ then
        chiPow D ⟨Q, hQ.1, hQ.2⟩ (1 : F) j else 1)).prod
      = (factors.map fun _ => (1 : ℂ)).prod := congrArg Multiset.prod hmap
    _ = 1 := by simp

private theorem crt_chiIdealPow_mul_ideal (D : FieldData F) {I J : Ideal (𝓞 F)}
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (x : F) (j : ℤ) :
    chiIdealPow D (I * J) x j = chiIdealPow D I x j * chiIdealPow D J x j := by
  unfold chiIdealPow
  rw [UniqueFactorizationMonoid.normalizedFactors_mul
    (by simpa [Ideal.zero_eq_bot] using hI) (by simpa [Ideal.zero_eq_bot] using hJ)]
  simp [Multiset.map_add, Multiset.prod_add]

private theorem crt_exists_factor_le (s : Multiset (Ideal (𝓞 F)))
    {M : Ideal (𝓞 F)} (hM : M.IsPrime) (hMtop : M ≠ ⊤)
    (hs : s.prod ≤ M) : ∃ Q ∈ s, Q ≤ M := by
  induction s using Multiset.induction_on with
  | empty =>
      simp at hs
      exact False.elim (hMtop hs)
  | cons Q s ih =>
      rw [Multiset.prod_cons] at hs
      rcases hM.mul_le.mp hs with hQ | hs
      · exact ⟨Q, by simp, hQ⟩
      · obtain ⟨R, hR, hRM⟩ := ih hs
        exact ⟨R, by simp [hR], hRM⟩

private theorem crt_chiIdealPow_zero_of_not_unit (D : FieldData F) (S : SData F CE condη)
    {I : Ideal (𝓞 F)} (hI : S.IsExterior I) (j : ℤ) (q : 𝓞 F ⧸ I)
    (hq : ¬ IsUnit q) :
    chiIdealPow D I (algebraMap (𝓞 F) F q.out) j = 0 := by
  by_cases htop : I = ⊤
  · subst I
    have hunitq : IsUnit q := by
      apply isUnit_iff_exists_inv.mpr
      exact ⟨q, Subsingleton.elim _ _⟩
    exact (hq hunitq).elim
  let a : 𝓞 F := q.out
  have hsum : Ideal.span {a} ⊔ I ≠ ⊤ := by
    intro htop'
    have hone : (1 : 𝓞 F) ∈ Ideal.span {a} ⊔ I := by rw [htop']; exact Submodule.mem_top
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hone
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hx
    have hq' : IsUnit (Ideal.Quotient.mk I a) := by
      apply isUnit_iff_exists_inv.mpr
      refine ⟨Ideal.Quotient.mk I r, ?_⟩
      have heq := congrArg (Ideal.Quotient.mk I) hxy
      rw [map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hy, add_zero] at heq
      simpa [mul_comm] using heq
    exact hq (by simpa [a] using hq')
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hsum
  have hIM : I ≤ M := le_trans le_sup_right hle
  have haM : a ∈ M := by
    have hspan : Ideal.span {a} ≤ M := le_trans le_sup_left hle
    exact hspan (Ideal.subset_span (by simp))
  have hprodM : (UniqueFactorizationMonoid.normalizedFactors I).prod ≤ M := by
    rw [Ideal.prod_normalizedFactors_eq_self hI.1]
    exact hIM
  obtain ⟨Q, hQ, hQM⟩ := crt_exists_factor_le
    (UniqueFactorizationMonoid.normalizedFactors I) hM.isPrime hM.isPrime.ne_top hprodM
  have hfac := (Ideal.mem_normalizedFactors_iff hI.1).mp hQ
  have hQ0 : Q ≠ ⊥ := by
    intro hbot
    exact hI.1 (bot_unique (by simpa [hbot] using hfac.2))
  let v : FinPlace F := ⟨Q, hfac.1, hQ0⟩
  have hQM' : Q = M := v.isMaximal.eq_of_le hM.isPrime.ne_top hQM
  have haQ : a ∈ Q := by rw [hQM']; exact haM
  have hres : residue v (a : F) = 0 := by
    rw [show (a : F) = algebraMap (𝓞 F) F a by simp, crt_residue_algInt]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr haQ
  have hzero : chiPow D v (a : F) j = 0 := by simp [chiPow, hres]
  unfold chiIdealPow
  apply Multiset.prod_eq_zero
  rw [Multiset.mem_map]
  refine ⟨Q, hQ, ?_⟩
  have hQ' : Q.IsPrime ∧ Q ≠ ⊥ := ⟨hfac.1, hQ0⟩
  have hzero' : chiPow D ⟨Q, hQ'.1, hQ'.2⟩
      (algebraMap (𝓞 F) F q.out) j = 0 := by
    simpa [a, v] using hzero
  simp [hQ', hzero']

private theorem crt_isGen_mul (S : SData F CE condη) {I J : Ideal (𝓞 F)}
    (hI : S.IsExterior I) (hJ : S.IsExterior J) (c d : Fˣ)
    (hc : S.IsGen (c : F) I) (hd : S.IsGen (d : F) J) :
    S.IsGen ((c * d : Fˣ) : F) (I * J) := by
  have hIJ : S.IsExterior (I * J) := by
    constructor
    · intro hzero
      rcases Ideal.mul_eq_bot.mp hzero with hi | hj
      · exact hI.1 hi
      · exact hJ.1 hj
    · intro v hv hle
      rcases v.isPrime.mul_le.mp hle with hi | hj
      · exact hI.2 v hv hi
      · exact hJ.2 v hv hj
  refine ⟨hIJ, mul_ne_zero (Units.ne_zero c) (Units.ne_zero d), ?_⟩
  intro v hv
  have hcdcount :
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ((c * d : Fˣ) : F)) =
        FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (c : F)) +
          FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (d : F)) := by
    change FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ((c : F) * (d : F))) = _
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton]
    exact FractionalIdeal.count_mul F v
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero c))
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero d))
  have hIJcount :
      FractionalIdeal.count F v
          ((I * J : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) +
          FractionalIdeal.count F v (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
    rw [FractionalIdeal.coeIdeal_mul]
    exact FractionalIdeal.count_mul F v
      (FractionalIdeal.coeIdeal_ne_zero.mpr (by simpa [Ideal.zero_eq_bot] using hI.1))
      (FractionalIdeal.coeIdeal_ne_zero.mpr (by simpa [Ideal.zero_eq_bot] using hJ.1))
  calc
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ((c * d : Fˣ) : F))
      = FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (c : F)) +
          FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (d : F)) := hcdcount
    _ = FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) +
          FractionalIdeal.count F v (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
        rw [hc.2.2 v hv, hd.2.2 v hv]
    _ = FractionalIdeal.count F v
        ((I * J : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := hIJcount.symm

private theorem crt_principal_coprime (S : SData F CE condη) {I J : Ideal (𝓞 F)}
    (hI : S.IsExterior I) (hJ : S.IsExterior J) (hIJ : IsCoprime I J)
    {c d : F} (hc : S.IsGen c I) (hd : S.IsGen d J) :
    IsCoprime (Ideal.span {crtSInteger S hc}) (Ideal.span {crtSInteger S hd}) := by
  let f := algebraMap (𝓞 F) S.R
  have hmapI : Ideal.map f I = Ideal.span {crtSInteger S hc} :=
    crt_ideal_map_eq_span S hI hc
  have hmapJ : Ideal.map f J = Ideal.span {crtSInteger S hd} :=
    crt_ideal_map_eq_span S hJ hd
  have hsum : I ⊔ J = ⊤ := Ideal.isCoprime_iff_sup_eq.mp hIJ
  have htop : Ideal.span {crtSInteger S hc} ⊔ Ideal.span {crtSInteger S hd} = ⊤ := by
    calc
      _ = Ideal.map f I ⊔ Ideal.map f J := by rw [hmapI, hmapJ]
      _ = Ideal.map f (I ⊔ J) := (Ideal.map_sup f I J).symm
      _ = ⊤ := by rw [hsum, Ideal.map_top]
  exact Ideal.isCoprime_iff_sup_eq.mpr htop

private theorem crt_unit_mk_of_principal_coprime {R : Type*} [CommRing R]
    (K : Ideal R) (a : R) (hcop : IsCoprime K (Ideal.span {a})) :
    IsUnit (Ideal.Quotient.mk K a) := by
  have htop : K ⊔ Ideal.span {a} = ⊤ := Ideal.isCoprime_iff_sup_eq.mp hcop
  have hone : (1 : R) ∈ K ⊔ Ideal.span {a} := by rw [htop]; exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hone
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp (show y ∈ Ideal.span {a} from hy)
  apply isUnit_iff_exists_inv.mpr
  refine ⟨Ideal.Quotient.mk K r, ?_⟩
  have heq := congrArg (Ideal.Quotient.mk K) hxy
  rw [map_add, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr hx, zero_add] at heq
  rw [hr, map_mul] at heq
  simpa [mul_comm] using heq

private theorem crt_principal_bezout (S : SData F CE condη) {I J : Ideal (𝓞 F)}
    (hI : S.IsExterior I) (hJ : S.IsExterior J) (hIJ : IsCoprime I J)
    {c d : F} (hc : S.IsGen c I) (hd : S.IsGen d J) :
    ∃ u v : S.R, u * crtSInteger S hc + v * crtSInteger S hd = 1 := by
  have hcop := crt_principal_coprime S hI hJ hIJ hc hd
  have htop : Ideal.span {crtSInteger S hc} ⊔ Ideal.span {crtSInteger S hd} = ⊤ :=
    Ideal.isCoprime_iff_sup_eq.mp hcop
  have hone : (1 : S.R) ∈
      Ideal.span {crtSInteger S hc} ⊔ Ideal.span {crtSInteger S hd} := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hone
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp hx
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp hy
  rw [hu, hv] at hxy
  exact ⟨u, v, by simpa [mul_comm] using hxy⟩

private noncomputable def crtChiQuotient (D : FieldData F) (S : SData F CE condη)
    {I : Ideal (𝓞 F)} (hI : S.IsExterior I) (j : ℤ) :
    MulChar (𝓞 F ⧸ I) ℂ where
  toFun q := chiIdealPow D I (q.out : F) j
  map_one' := by
    let a : 𝓞 F := (1 : 𝓞 F ⧸ I).out
    have hmk : Ideal.Quotient.mk I a = 1 := by simp [a]
    have hmem : a - 1 ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      calc
        Ideal.Quotient.mk I (a - 1) = Ideal.Quotient.mk I a - Ideal.Quotient.mk I 1 := by
          rw [map_sub]
        _ = 0 := by rw [hmk]; simp
    calc
      chiIdealPow D I ((1 : 𝓞 F ⧸ I).out : F) j = chiIdealPow D I (1 : F) j := by
        exact crt_chiIdealPow_congr D I hI.1 a 1 hmem j
      _ = 1 := crt_chiIdealPow_one D S hI j
  map_mul' x y := by
    let a : 𝓞 F := x.out
    let b : 𝓞 F := y.out
    have hx : Ideal.Quotient.mk I a = x := by simp [a]
    have hy : Ideal.Quotient.mk I b = y := by simp [b]
    have hquot : Ideal.Quotient.mk I ((x * y).out) = Ideal.Quotient.mk I (a * b) := by
      calc
        Ideal.Quotient.mk I ((x * y).out) = x * y := by simp
        _ = Ideal.Quotient.mk I a * Ideal.Quotient.mk I b := by rw [← hx, ← hy]
        _ = Ideal.Quotient.mk I (a * b) := by rw [map_mul]
    have hmem : (x * y).out - a * b ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      calc
        Ideal.Quotient.mk I ((x * y).out - a * b) =
            Ideal.Quotient.mk I ((x * y).out) - Ideal.Quotient.mk I (a * b) := by rw [map_sub]
        _ = 0 := by rw [hquot]; simp
    calc
      chiIdealPow D I ((x * y).out : F) j = chiIdealPow D I ((a * b : 𝓞 F) : F) j :=
        crt_chiIdealPow_congr D I hI.1 (x * y).out (a * b) hmem j
      _ = chiIdealPow D I (a : F) j * chiIdealPow D I (b : F) j :=
        crt_chiIdealPow_mul D S hI a b j
      _ = chiIdealPow D I (x.out : F) j * chiIdealPow D I (y.out : F) j := rfl
  map_nonunit' := by
    intro q hq
    exact crt_chiIdealPow_zero_of_not_unit D S hI j q hq

private theorem crt_chi_residue_compat (D : FieldData F) (S : SData F CE condη)
    {I : Ideal (𝓞 F)} (hI : S.IsExterior I) (j : ℤ) (x : S.R) :
    crtChiQuotient D S hI j (crtResidueRed S I hI x) =
      chiIdealPow D I (x : F) j := by
  let q := crtResidueRed S I hI x
  have hmk : Ideal.Quotient.mk I q.out = q := by simp [q]
  unfold crtChiQuotient chiIdealPow
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro Q hQ
  by_cases hQ' : Q.IsPrime ∧ Q ≠ ⊥
  · have hfac := (Ideal.mem_normalizedFactors_iff hI.1).mp hQ
    let v : FinPlace F := ⟨Q, hQ'.1, hQ'.2⟩
    have hvS : v ∉ S.Sf := by
      intro hv
      exact hI.2 v hv (by simpa [v] using hfac.2)
    have hres : residue v (q.out : F) = residue v (x : F) := by
      have hcmp := crt_residue_compat S hI v hvS hfac.2 x
      have hfacq : Ideal.Quotient.factor hfac.2 q = Ideal.Quotient.mk v.asIdeal q.out := by
        calc
          Ideal.Quotient.factor hfac.2 q =
              Ideal.Quotient.factor hfac.2 (Ideal.Quotient.mk I q.out) :=
            (congrArg (Ideal.Quotient.factor hfac.2) hmk).symm
          _ = Ideal.Quotient.mk v.asIdeal q.out :=
            Ideal.Quotient.factor_mk hfac.2 q.out
      calc
        residue v (q.out : F) = Ideal.Quotient.mk v.asIdeal q.out := by
          rw [show (q.out : F) = algebraMap (𝓞 F) F q.out by simp, crt_residue_algInt]
        _ = Ideal.Quotient.factor hfac.2 q := hfacq.symm
        _ = residue v (x : F) := hcmp.symm
    simp only [dif_pos hQ']
    exact crt_chiPow_residue_congr D v j hres
  · simp [hQ']

private noncomputable def crtChiRQuotient (D : FieldData F) (S : SData F CE condη)
    {I : Ideal (𝓞 F)} (hI : S.IsExterior I) (j : ℤ) {c : F}
    (hc : S.IsGen c I) :
    MulChar (S.R ⧸ Ideal.span {crtSInteger S hc}) ℂ :=
  MulChar.ofUnitHom
    ((crtChiQuotient D S hI j).toUnitHom.comp
      (Units.map (crtResidueEquiv S hI hc).toMonoidHom))

private theorem crtChiRQuotient_apply (D : FieldData F) (S : SData F CE condη)
    {I : Ideal (𝓞 F)} (hI : S.IsExterior I) (j : ℤ) {c : F}
    (hc : S.IsGen c I) (q : S.R ⧸ Ideal.span {crtSInteger S hc}) :
    crtChiRQuotient D S hI j hc q =
      crtChiQuotient D S hI j (crtResidueEquiv S hI hc q) := by
  classical
  by_cases hq : IsUnit q
  · obtain ⟨u, rfl⟩ := hq
    simp [crtChiRQuotient, MulChar.ofUnitHom_coe]
  · have hqo : ¬ IsUnit (crtResidueEquiv S hI hc q) := by
      intro h
      apply hq
      have h := h.map (crtResidueEquiv S hI hc).symm.toRingHom
      simpa using h
    rw [MulChar.map_nonunit (crtChiRQuotient D S hI j hc) hq,
      MulChar.map_nonunit (crtChiQuotient D S hI j) hqo]

private theorem crtChiRQuotient_mk (D : FieldData F) (S : SData F CE condη)
    {I : Ideal (𝓞 F)} (hI : S.IsExterior I) (j : ℤ) {c : F}
    (hc : S.IsGen c I) (x : S.R) :
    crtChiRQuotient D S hI j hc
        (Ideal.Quotient.mk (Ideal.span {crtSInteger S hc}) x) =
      chiIdealPow D I (x : F) j := by
  calc
    crtChiRQuotient D S hI j hc (Ideal.Quotient.mk (Ideal.span {crtSInteger S hc}) x) =
        crtChiQuotient D S hI j
          (crtResidueEquiv S hI hc (Ideal.Quotient.mk (Ideal.span {crtSInteger S hc}) x)) :=
      crtChiRQuotient_apply D S hI j hc _
    _ = crtChiQuotient D S hI j (crtResidueRed S I hI x) := by
      rw [crtResidueEquiv_mk]
    _ = chiIdealPow D I (x : F) j := crt_chi_residue_compat D S hI j x

private theorem crtChiRQuotient_out (D : FieldData F) (S : SData F CE condη)
    {I : Ideal (𝓞 F)} (hI : S.IsExterior I) (j : ℤ) {c : F}
    (hc : S.IsGen c I) (q : S.R ⧸ Ideal.span {crtSInteger S hc}) :
    crtChiRQuotient D S hI j hc q = chiIdealPow D I (q.out : F) j := by
  calc
    crtChiRQuotient D S hI j hc q =
        crtChiRQuotient D S hI j hc
          (Ideal.Quotient.mk (Ideal.span {crtSInteger S hc}) q.out) :=
      congrArg (crtChiRQuotient D S hI j hc) (Ideal.Quotient.mk_out q).symm
    _ = chiIdealPow D I (q.out : F) j := crtChiRQuotient_mk D S hI j hc q.out

private noncomputable def crtMulCharPullback {R T : Type*} [CommRing R] [CommRing T]
    (e : R ≃+* T) (χ : MulChar T ℂ) : MulChar R ℂ :=
  MulChar.ofUnitHom (χ.toUnitHom.comp (Units.map e.toMonoidHom))

private theorem crtMulCharPullback_apply {R T : Type*} [CommRing R] [CommRing T]
    (e : R ≃+* T) (χ : MulChar T ℂ) (x : R) :
    crtMulCharPullback e χ x = χ (e x) := by
  classical
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    simp [crtMulCharPullback, MulChar.ofUnitHom_coe]
  · have he : ¬ IsUnit (e x) := by
      intro h
      apply hx
      have h' := h.map e.symm.toRingHom
      simpa using h'
    rw [MulChar.map_nonunit (crtMulCharPullback e χ) hx,
      MulChar.map_nonunit χ he]

private theorem crt_factor_left_mk {R : Type*} [CommRing R]
    (K L : Ideal R) (hcop : IsCoprime K L) (x : R ⧸ K * L) :
    Ideal.Quotient.factor (Ideal.mul_le_left : K * L ≤ K) x = Ideal.Quotient.mk K x.out := by
  calc
    Ideal.Quotient.factor (Ideal.mul_le_left : K * L ≤ K) x =
        Ideal.Quotient.factor (Ideal.mul_le_left : K * L ≤ K)
          (Ideal.Quotient.mk (K * L) x.out) :=
            congrArg (Ideal.Quotient.factor (Ideal.mul_le_left : K * L ≤ K))
              (Ideal.Quotient.mk_out x).symm
    _ = Ideal.Quotient.mk K x.out := Ideal.Quotient.factor_mk _ _

private theorem crt_factor_right_mk {R : Type*} [CommRing R]
    (K L : Ideal R) (hcop : IsCoprime K L) (x : R ⧸ K * L) :
    Ideal.Quotient.factor (Ideal.mul_le_right : K * L ≤ L) x = Ideal.Quotient.mk L x.out := by
  calc
    Ideal.Quotient.factor (Ideal.mul_le_right : K * L ≤ L) x =
        Ideal.Quotient.factor (Ideal.mul_le_right : K * L ≤ L)
          (Ideal.Quotient.mk (K * L) x.out) :=
            congrArg (Ideal.Quotient.factor (Ideal.mul_le_right : K * L ≤ L))
              (Ideal.Quotient.mk_out x).symm
    _ = Ideal.Quotient.mk L x.out := Ideal.Quotient.factor_mk _ _

private theorem crtChiRQuotient_factor_left (D : FieldData F) (S : SData F CE condη)
    {I J : Ideal (𝓞 F)} (hI : S.IsExterior I) (hJ : S.IsExterior J)
    (c d : Fˣ) (hc : S.IsGen (c : F) I) (hd : S.IsGen (d : F) J)
    (hcopR : IsCoprime (Ideal.span {crtSInteger S hc}) (Ideal.span {crtSInteger S hd}))
    (j : ℤ) (x : S.R ⧸ Ideal.span {crtSInteger S hc} * Ideal.span {crtSInteger S hd}) :
    crtChiRQuotient D S hI j hc
        (Ideal.Quotient.factor
          (Ideal.mul_le_left : Ideal.span {crtSInteger S hc} *
            Ideal.span {crtSInteger S hd} ≤ Ideal.span {crtSInteger S hc}) x) =
      chiIdealPow D I (x.out : F) j := by
  let K := Ideal.span {crtSInteger S hc}
  let L := Ideal.span {crtSInteger S hd}
  have hfact : Ideal.Quotient.factor (Ideal.mul_le_left : K * L ≤ K) x =
      Ideal.Quotient.mk K x.out := crt_factor_left_mk K L hcopR x
  have heq : crtResidueEquiv S hI hc
      (Ideal.Quotient.factor (Ideal.mul_le_left : K * L ≤ K) x) =
      crtResidueRed S I hI x.out := by
    rw [hfact]
    exact crtResidueEquiv_mk S hI hc x.out
  calc
    crtChiRQuotient D S hI j hc
        (Ideal.Quotient.factor (Ideal.mul_le_left : K * L ≤ K) x) =
        crtChiQuotient D S hI j
          (crtResidueEquiv S hI hc
            (Ideal.Quotient.factor (Ideal.mul_le_left : K * L ≤ K) x)) :=
      crtChiRQuotient_apply D S hI j hc _
    _ = crtChiQuotient D S hI j (crtResidueRed S I hI x.out) := by rw [heq]
    _ = chiIdealPow D I (x.out : F) j := crt_chi_residue_compat D S hI j x.out

private theorem crtChiRQuotient_factor_right (D : FieldData F) (S : SData F CE condη)
    {I J : Ideal (𝓞 F)} (hI : S.IsExterior I) (hJ : S.IsExterior J)
    (c d : Fˣ) (hc : S.IsGen (c : F) I) (hd : S.IsGen (d : F) J)
    (hcopR : IsCoprime (Ideal.span {crtSInteger S hc}) (Ideal.span {crtSInteger S hd}))
    (j : ℤ) (x : S.R ⧸ Ideal.span {crtSInteger S hc} * Ideal.span {crtSInteger S hd}) :
    crtChiRQuotient D S hJ j hd
        (Ideal.Quotient.factor
          (Ideal.mul_le_right : Ideal.span {crtSInteger S hc} *
            Ideal.span {crtSInteger S hd} ≤ Ideal.span {crtSInteger S hd}) x) =
      chiIdealPow D J (x.out : F) j := by
  let K := Ideal.span {crtSInteger S hc}
  let L := Ideal.span {crtSInteger S hd}
  have hfact : Ideal.Quotient.factor (Ideal.mul_le_right : K * L ≤ L) x =
      Ideal.Quotient.mk L x.out := crt_factor_right_mk K L hcopR x
  have heq : crtResidueEquiv S hJ hd
      (Ideal.Quotient.factor (Ideal.mul_le_right : K * L ≤ L) x) =
      crtResidueRed S J hJ x.out := by
    rw [hfact]
    exact crtResidueEquiv_mk S hJ hd x.out
  calc
    crtChiRQuotient D S hJ j hd
        (Ideal.Quotient.factor (Ideal.mul_le_right : K * L ≤ L) x) =
        crtChiQuotient D S hJ j
          (crtResidueEquiv S hJ hd
            (Ideal.Quotient.factor (Ideal.mul_le_right : K * L ≤ L) x)) :=
      crtChiRQuotient_apply D S hJ j hd _
    _ = crtChiQuotient D S hJ j (crtResidueRed S J hJ x.out) := by rw [heq]
    _ = chiIdealPow D J (x.out : F) j := crt_chi_residue_compat D S hJ j x.out

private theorem crt_psiC_add (z w : ℂ) : psiC (z + w) = psiC z * psiC w := by
  unfold psiC
  have harg :
      -(4 * Real.pi * Complex.I * ((z + w).re : ℂ)) =
        -(4 * Real.pi * Complex.I * (z.re : ℂ)) +
          -(4 * Real.pi * Complex.I * (w.re : ℂ)) := by
    rw [Complex.add_re, Complex.ofReal_add]
    ring
  rw [harg, Complex.exp_add]

private theorem crt_e_diag_add (S : SData F CE condη) (A : AddCharData F) (x y : F) :
    S.e A (S.diag (x + y)) = S.e A (S.diag x) * S.e A (S.diag y) := by
  classical
  have hdiag : S.diag (x + y) = S.diag x + S.diag y := map_add (S.diag) x y
  unfold SData.e
  rw [hdiag]
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, AddChar.map_add_eq_mul]
  simp_rw [crt_psiC_add]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

private theorem crt_e_diag_zero (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) : S.e A (S.diag (0 : F)) = 1 := by
  letI : IsTotallyComplex F := D.isTotallyComplex
  rw [SData.e_diag_eq S A 0 0 (by intro v hv; simp) (by intro v hv; simp)]
  simp

private noncomputable def crtRawAddChar (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) (c : Fˣ) : AddChar (𝓞 F) ℂ where
  toFun n := S.e A (S.diag (algebraMap (𝓞 F) F n / (c : F)))
  map_zero_eq_one' := by
    change S.e A (S.diag (algebraMap (𝓞 F) F 0 / (c : F))) = 1
    rw [map_zero, zero_div]
    exact crt_e_diag_zero D S A
  map_add_eq_mul' n m := by
    have harg :
        algebraMap (𝓞 F) F (n + m) / (c : F) =
          algebraMap (𝓞 F) F n / (c : F) + algebraMap (𝓞 F) F m / (c : F) := by
      rw [map_add]
      field_simp [Units.ne_zero c]
    change S.e A (S.diag (algebraMap (𝓞 F) F (n + m) / (c : F))) = _
    rw [harg, crt_e_diag_add]

private theorem crt_e_diag_one_of_mem_R (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) (x : S.R) : S.e A (S.diag (x : F)) = 1 := by
  letI : IsTotallyComplex F := D.isTotallyComplex
  have h := SData.e_diag_eq S A (x : F) 0
    (by
      intro v hv
      simpa using x.property v hv)
    (by intro v hv; simp)
  simpa using h

private noncomputable def crtRawRAddChar (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) (c : Fˣ) : AddChar S.R ℂ where
  toFun x := S.e A (S.diag ((x : F) / (c : F)))
  map_zero_eq_one' := by
    change S.e A (S.diag ((0 : F) / (c : F))) = 1
    rw [zero_div]
    exact crt_e_diag_zero D S A
  map_add_eq_mul' x y := by
    have harg : ((x + y : S.R) : F) / (c : F) =
        (x : F) / (c : F) + (y : F) / (c : F) := by
      push_cast
      field_simp [Units.ne_zero c]
    change S.e A (S.diag (((x + y : S.R) : F) / (c : F))) = _
    rw [harg, crt_e_diag_add]

private noncomputable def crtPsiRQuotient (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) {I : Ideal (𝓞 F)} (hI : S.IsExterior I) (c : Fˣ)
    (hc : S.IsGen (c : F) I) :
    AddChar (S.R ⧸ Ideal.span {crtSInteger S hc}) ℂ :=
  OAI.IdealGaussCRT.quotientAddChar (Ideal.span {crtSInteger S hc})
    (crtRawRAddChar D S A c)
    (by
      intro r hr
      obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hr
      have hfield : (r : F) / (c : F) = (t : F) := by
        have h := congrArg (fun z : S.R => (z : F)) ht
        change (r : F) = (crtSInteger S hc : F) * (t : F) at h
        rw [show (crtSInteger S hc : F) = (c : F) from rfl] at h
        rw [h]
        field_simp [Units.ne_zero c]
      change S.e A (S.diag ((r : F) / (c : F))) = 1
      rw [hfield]
      exact crt_e_diag_one_of_mem_R D S A t)

private noncomputable def crtPsiQuotient (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) {I : Ideal (𝓞 F)} (hI : S.IsExterior I) (c : Fˣ)
    (hc : S.IsGen (c : F) I) : AddChar (𝓞 F ⧸ I) ℂ :=
  OAI.IdealGaussCRT.quotientAddChar I (crtRawAddChar D S A c)
    (by
      intro n hn
      have hper := (SData.e_pairing_perfect D S A I hI c hc).1 n hn 1
      simpa [crtRawAddChar] using hper)

private theorem crtPsiQuotient_mk (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) {I : Ideal (𝓞 F)} (hI : S.IsExterior I) (c : Fˣ)
    (hc : S.IsGen (c : F) I) (a : 𝓞 F) :
    crtPsiQuotient D S A hI c hc (Ideal.Quotient.mk I a) =
      S.e A (S.diag (algebraMap (𝓞 F) F a / (c : F))) := by
  simp [crtPsiQuotient, crtRawAddChar, OAI.IdealGaussCRT.quotientAddChar_mk]

private theorem crtPsiRQuotient_mk (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) {I : Ideal (𝓞 F)} (hI : S.IsExterior I) (c : Fˣ)
    (hc : S.IsGen (c : F) I) (x : S.R) :
    crtPsiRQuotient D S A hI c hc
        (Ideal.Quotient.mk (Ideal.span {crtSInteger S hc}) x) =
      S.e A (S.diag ((x : F) / (c : F))) := by
  simp [crtPsiRQuotient, crtRawRAddChar, OAI.IdealGaussCRT.quotientAddChar_mk]

private theorem crtPsiRQuotient_out (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) {I : Ideal (𝓞 F)} (hI : S.IsExterior I) (c : Fˣ)
    (hc : S.IsGen (c : F) I) (q : S.R ⧸ Ideal.span {crtSInteger S hc}) :
    crtPsiRQuotient D S A hI c hc q = S.e A (S.diag ((q.out : F) / (c : F))) := by
  calc
    crtPsiRQuotient D S A hI c hc q =
        crtPsiRQuotient D S A hI c hc
          (Ideal.Quotient.mk (Ideal.span {crtSInteger S hc}) q.out) :=
      congrArg (crtPsiRQuotient D S A hI c hc) (Ideal.Quotient.mk_out q).symm
    _ = S.e A (S.diag ((q.out : F) / (c : F))) := crtPsiRQuotient_mk D S A hI c hc q.out

private theorem crtPsi_equiv_compat (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) {I : Ideal (𝓞 F)} (hI : S.IsExterior I) (c : Fˣ)
    (hc : S.IsGen (c : F) I) (q : S.R ⧸ Ideal.span {crtSInteger S hc}) :
    crtPsiQuotient D S A hI c hc (crtResidueEquiv S hI hc q) =
      crtPsiRQuotient D S A hI c hc q := by
  let cR := crtSInteger S hc
  let x : S.R := q.out
  have hq : Ideal.Quotient.mk (Ideal.span {cR}) x = q := by simp [x]
  have heq : crtResidueEquiv S hI hc q = crtResidueRed S I hI x := by
    calc
      crtResidueEquiv S hI hc q =
          crtResidueEquiv S hI hc (Ideal.Quotient.mk (Ideal.span {cR}) x) := by rw [hq]
      _ = crtResidueRed S I hI x := crtResidueEquiv_mk S hI hc x
  let a : 𝓞 F := (crtResidueEquiv S hI hc q).out
  have hmkA : Ideal.Quotient.mk I a = crtResidueEquiv S hI hc q := by simp [a]
  have hredEq : crtResidueRed S I hI (algebraMap (𝓞 F) S.R a) =
      crtResidueRed S I hI x := by
    rw [crtResidueRed_integral S I hI a, hmkA, heq]
  have hzero : crtResidueRed S I hI (algebraMap (𝓞 F) S.R a - x) = 0 := by
    rw [map_sub, hredEq, sub_self]
  have hker : algebraMap (𝓞 F) S.R a - x ∈
      RingHom.ker (crtResidueRed S I hI) := by
    change crtResidueRed S I hI (algebraMap (𝓞 F) S.R a - x) = 0
    exact hzero
  have hmemMap : algebraMap (𝓞 F) S.R a - x ∈
      Ideal.map (algebraMap (𝓞 F) S.R) I := by
    rw [crtResidueRed_ker S I hI] at hker
    exact hker
  have hmap : Ideal.map (algebraMap (𝓞 F) S.R) I = Ideal.span {cR} :=
    crt_ideal_map_eq_span S hI hc
  have hmemSpan : algebraMap (𝓞 F) S.R a - x ∈ Ideal.span {cR} := by
    rw [← hmap]
    exact hmemMap
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hmemSpan
  have hdelta : (a : F) - (x : F) = (c : F) * (t : F) := by
    have h := congrArg (fun z : S.R => (z : F)) ht
    have hs := h.symm
    change (algebraMap (𝓞 F) F a) - (x : F) =
      (t : F) * (crtSInteger S hc : F) at hs
    calc
      (a : F) - (x : F) = (t : F) * (crtSInteger S hc : F) := hs
      _ = (c : F) * (t : F) := by rw [show (crtSInteger S hc : F) = (c : F) from rfl]; ring
  have harg : (a : F) / (c : F) = (x : F) / (c : F) + (t : F) := by
    have hsum : (a : F) = (x : F) + (c : F) * (t : F) := by
      calc
        (a : F) = ((a : F) - (x : F)) + (x : F) := by ring
        _ = (c : F) * (t : F) + (x : F) := by rw [hdelta]
        _ = (x : F) + (c : F) * (t : F) := by ring
    rw [hsum]
    field_simp [Units.ne_zero c]
  calc
    crtPsiQuotient D S A hI c hc (crtResidueEquiv S hI hc q) =
        S.e A (S.diag ((a : F) / (c : F))) := by
          rw [show crtResidueEquiv S hI hc q = Ideal.Quotient.mk I a by
            simp [a]]
          exact crtPsiQuotient_mk D S A hI c hc a
    _ = S.e A (S.diag ((x : F) / (c : F))) := by
      rw [harg, crt_e_diag_add, crt_e_diag_one_of_mem_R D S A t, mul_one]
    _ = crtPsiRQuotient D S A hI c hc q := by
      rw [show q = Ideal.Quotient.mk (Ideal.span {cR}) x by rw [hq]]
      exact (crtPsiRQuotient_mk D S A hI c hc x).symm

private theorem crt_gamma_eq_gaussSum (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) (j : ℤ) {I : Ideal (𝓞 F)} (hI : S.IsExterior I)
    (c : Fˣ) (hc : S.IsGen (c : F) I) [Fintype (𝓞 F ⧸ I)] :
    gamma D S A j I (c : F) =
      ((Ideal.absNorm I : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
        gaussSum (crtChiQuotient D S hI j) (crtPsiQuotient D S A hI c hc) := by
  classical
  have hterm (x : 𝓞 F ⧸ I) :
      chiIdealPow D I (algebraMap (𝓞 F) F x.out) j *
        S.e A (S.diag (algebraMap (𝓞 F) F x.out / (c : F))) =
      crtChiQuotient D S hI j x * crtPsiQuotient D S A hI c hc x := by
    have hψ : crtPsiQuotient D S A hI c hc x =
        S.e A (S.diag (algebraMap (𝓞 F) F x.out / (c : F))) := by
      unfold crtPsiQuotient
      let ψ := crtRawAddChar D S A c
      let hper : ∀ n : 𝓞 F, n ∈ I → ψ n = 1 := by
        intro n hn
        have h := (SData.e_pairing_perfect D S A I hI c hc).1 n hn 1
        simpa [ψ, crtRawAddChar] using h
      have hq :
          OAI.IdealGaussCRT.quotientAddChar I ψ hper x =
            OAI.IdealGaussCRT.quotientAddChar I ψ hper
              (Ideal.Quotient.mk I x.out) := by
        exact congrArg (OAI.IdealGaussCRT.quotientAddChar I ψ hper)
          (Ideal.Quotient.mk_out x).symm
      change OAI.IdealGaussCRT.quotientAddChar I ψ hper x = _
      rw [hq, OAI.IdealGaussCRT.quotientAddChar_mk]
      rfl
    change chiIdealPow D I (x.out : F) j *
        S.e A (S.diag (algebraMap (𝓞 F) F x.out / (c : F))) =
      chiIdealPow D I (x.out : F) j * crtPsiQuotient D S A hI c hc x
    rw [hψ]
  calc
    gamma D S A j I (c : F) =
        ((Ideal.absNorm I : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
          ∑ᶠ x : 𝓞 F ⧸ I,
            chiIdealPow D I (algebraMap (𝓞 F) F x.out) j *
              S.e A (S.diag (algebraMap (𝓞 F) F x.out / (c : F))) := rfl
    _ = ((Ideal.absNorm I : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
          ∑ᶠ x : 𝓞 F ⧸ I,
            crtChiQuotient D S hI j x * crtPsiQuotient D S A hI c hc x := by
      congr 1
      apply finsum_congr
      intro x
      exact hterm x
    _ = ((Ideal.absNorm I : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
          ∑ x : 𝓞 F ⧸ I,
            crtChiQuotient D S hI j x * crtPsiQuotient D S A hI c hc x := by
      rw [← finsum_eq_finsetSum_of_support_subset
        (fun x : 𝓞 F ⧸ I => crtChiQuotient D S hI j x * crtPsiQuotient D S A hI c hc x)
        (s := Finset.univ) (by intro x hx; simp)]
    _ = _ := by simp [gaussSum]

private theorem crt_gamma_eq_gaussSumR (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) (j : ℤ) {I : Ideal (𝓞 F)} (hI : S.IsExterior I)
    (c : Fˣ) (hc : S.IsGen (c : F) I)
    [Fintype (S.R ⧸ Ideal.span {crtSInteger S hc})] :
    gamma D S A j I (c : F) =
      ((Ideal.absNorm I : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
        gaussSum (crtChiRQuotient D S hI j hc) (crtPsiRQuotient D S A hI c hc) := by
  classical
  let e := crtResidueEquiv S hI hc
  let χO := crtChiQuotient D S hI j
  let ψO := crtPsiQuotient D S A hI c hc
  let χR := crtChiRQuotient D S hI j hc
  let ψR := crtPsiRQuotient D S A hI c hc
  letI : Fintype (𝓞 F ⧸ I) :=
    Fintype.ofEquiv (S.R ⧸ Ideal.span {crtSInteger S hc}) e.toEquiv
  have hbase := crt_gamma_eq_gaussSum D S A j hI c hc
  have hterm (x : 𝓞 F ⧸ I) :
      χO x * ψO x = χR (e.symm x) * ψR (e.symm x) := by
    have hχ := crtChiRQuotient_apply D S hI j hc (e.symm x)
    have hψ := crtPsi_equiv_compat D S A hI c hc (e.symm x)
    simpa [e, χO, ψO, χR, ψR] using congrArg₂ (fun u v => u * v) hχ.symm hψ
  have hsum :
      (∑ x : 𝓞 F ⧸ I, χO x * ψO x) =
        ∑ y : S.R ⧸ Ideal.span {crtSInteger S hc}, χR y * ψR y := by
    calc
      (∑ x : 𝓞 F ⧸ I, χO x * ψO x) =
          ∑ x : 𝓞 F ⧸ I, χR (e.symm x) * ψR (e.symm x) := by
            apply Finset.sum_congr rfl
            intro x hx
            exact hterm x
      _ = ∑ y : S.R ⧸ Ideal.span {crtSInteger S hc}, χR y * ψR y :=
        Equiv.sum_comp e.symm.toEquiv (fun y => χR y * ψR y)
  calc
    gamma D S A j I (c : F) =
        ((Ideal.absNorm I : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) * gaussSum χO ψO := by
      simpa [χO, ψO] using hbase
    _ = ((Ideal.absNorm I : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
          ∑ x : 𝓞 F ⧸ I, χO x * ψO x := by simp [gaussSum]
    _ = ((Ideal.absNorm I : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
          ∑ y : S.R ⧸ Ideal.span {crtSInteger S hc}, χR y * ψR y := by rw [hsum]
    _ = ((Ideal.absNorm I : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) * gaussSum χR ψR := by
      simp [gaussSum]

private theorem crt_gaussSum_pullback {R T : Type*} [CommRing R] [CommRing T]
    [Fintype R] [Fintype T] (e : R ≃+* T) (χ : MulChar T ℂ) (ψ : AddChar T ℂ) :
    gaussSum χ ψ =
      gaussSum (crtMulCharPullback e χ) (ψ.compAddMonoidHom e.toAddMonoidHom) := by
  classical
  calc
    gaussSum χ ψ = ∑ t : T, χ t * ψ t := by simp [gaussSum]
    _ = ∑ r : R, χ (e r) * ψ (e r) := (Equiv.sum_comp e.toEquiv _).symm
    _ = ∑ r : R,
        crtMulCharPullback e χ r * (ψ.compAddMonoidHom e.toAddMonoidHom) r := by
      apply Finset.sum_congr rfl
      intro r hr
      have hχ := crtMulCharPullback_apply e χ r
      have hψ : (ψ.compAddMonoidHom e.toAddMonoidHom) r = ψ (e r) := by
        change ψ (e.toAddMonoidHom r) = ψ (e r)
        congr 1
      calc
        χ (e r) * ψ (e r) = crtMulCharPullback e χ r * ψ (e r) := by rw [hχ.symm]
        _ = crtMulCharPullback e χ r * (ψ.compAddMonoidHom e.toAddMonoidHom) r := by
          rw [hψ.symm]
    _ = _ := by simp [gaussSum]

/-! eq:gauss-crt (02:428–435). Package P-ARITH-GAUSS. -/
theorem gamma_crt (D : FieldData F) (S : SData F CE condη) (A : AddCharData F) (H : HilbertData F)
    (Bd : BData S H) (j : ℤ) (I J : Ideal (𝓞 F)) (hI : S.IsExterior I) (hJ : S.IsExterior J)
    (hIs : Squarefree I) (hJs : Squarefree J) (hIJ : IsCoprime I J) (c d : Fˣ)
    (hc : S.IsGen (c : F) I ∧ Bd.Allowed c) (hd : S.IsGen (d : F) J ∧ Bd.Allowed d) :
    gamma D S A j (I * J) ((c * d : Fˣ) : F) =
      chiIdealPow D I (d : F) j * chiIdealPow D J (c : F) j *
        gamma D S A j I c * gamma D S A j J d := by
  classical
  let hcd : S.IsGen ((c * d : Fˣ) : F) (I * J) :=
    crt_isGen_mul S hI hJ c d hc.1 hd.1
  let cR : S.R := crtSInteger S hc.1
  let dR : S.R := crtSInteger S hd.1
  let K : Ideal S.R := Ideal.span {cR}
  let L : Ideal S.R := Ideal.span {dR}
  have hIJext : S.IsExterior (I * J) := hcd.1
  have hcopR : IsCoprime K L := crt_principal_coprime S hI hJ hIJ hc.1 hd.1
  obtain ⟨u, v, hbez⟩ := crt_principal_bezout S hI hJ hIJ hc.1 hd.1
  change u * cR + v * dR = 1 at hbez
  have hKL : K * L = Ideal.span {crtSInteger S hcd} := by
    change Ideal.span {cR} * Ideal.span {dR} = Ideal.span {crtSInteger S hcd}
    rw [Ideal.span_singleton_mul_span_singleton]
    have hgen : cR * dR = crtSInteger S hcd := by
      apply Subtype.ext
      rfl
    rw [hgen]
  let eI := crtResidueEquiv S hI hc.1
  let eJ := crtResidueEquiv S hJ hd.1
  let eIJ := crtResidueEquiv S hIJext hcd
  let eKL : S.R ⧸ (K * L) ≃+* S.R ⧸ Ideal.span {crtSInteger S hcd} :=
    Ideal.quotEquivOfEq hKL
  let eProd : S.R ⧸ (K * L) ≃+* 𝓞 F ⧸ (I * J) := eKL.trans eIJ
  have hqposI : 0 < Ideal.absNorm I :=
    Ideal.absNorm_pos_of_nonZeroDivisors
      ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr (by simpa [Ideal.zero_eq_bot] using hI.1)⟩
  have hqposJ : 0 < Ideal.absNorm J :=
    Ideal.absNorm_pos_of_nonZeroDivisors
      ⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr (by simpa [Ideal.zero_eq_bot] using hJ.1)⟩
  have hqposIJ : 0 < Ideal.absNorm (I * J) :=
    Ideal.absNorm_pos_of_nonZeroDivisors
      ⟨I * J, mem_nonZeroDivisors_iff_ne_zero.mpr
        (by simpa [Ideal.zero_eq_bot] using hIJext.1)⟩
  letI : Finite (𝓞 F ⧸ I) := (Ideal.absNorm_ne_zero_iff I).mp hqposI.ne'
  letI : Fintype (𝓞 F ⧸ I) := Fintype.ofFinite _
  letI : Finite (𝓞 F ⧸ J) := (Ideal.absNorm_ne_zero_iff J).mp hqposJ.ne'
  letI : Fintype (𝓞 F ⧸ J) := Fintype.ofFinite _
  letI : Finite (𝓞 F ⧸ (I * J)) :=
    (Ideal.absNorm_ne_zero_iff (I * J)).mp hqposIJ.ne'
  letI : Fintype (𝓞 F ⧸ (I * J)) := Fintype.ofFinite _
  letI : Fintype (S.R ⧸ K) := Fintype.ofEquiv (𝓞 F ⧸ I) eI.symm.toEquiv
  letI : Fintype (S.R ⧸ L) := Fintype.ofEquiv (𝓞 F ⧸ J) eJ.symm.toEquiv
  letI : Fintype (S.R ⧸ Ideal.span {crtSInteger S hcd}) :=
    Fintype.ofEquiv (𝓞 F ⧸ (I * J)) eIJ.symm.toEquiv
  letI : Fintype (S.R ⧸ (K * L)) :=
    Fintype.ofEquiv (𝓞 F ⧸ (I * J)) eProd.symm.toEquiv
  have hbezK : Ideal.Quotient.mk K (v * dR) = 1 := by
    have hc0 : Ideal.Quotient.mk K cR = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self cR)
    have h := congrArg (Ideal.Quotient.mk K) hbez
    have h' : Ideal.Quotient.mk K u * Ideal.Quotient.mk K cR +
        Ideal.Quotient.mk K v * Ideal.Quotient.mk K dR = 1 := by
      simpa only [map_add, map_mul, map_one] using h
    rw [hc0, mul_zero, zero_add] at h'
    exact h'
  have hbezL : Ideal.Quotient.mk L (u * cR) = 1 := by
    have hd0 : Ideal.Quotient.mk L dR = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self dR)
    have h := congrArg (Ideal.Quotient.mk L) hbez
    have h' : Ideal.Quotient.mk L u * Ideal.Quotient.mk L cR +
        Ideal.Quotient.mk L v * Ideal.Quotient.mk L dR = 1 := by
      simpa only [map_add, map_mul, map_one] using h
    rw [hd0, mul_zero, add_zero] at h'
    exact h'
  have hdUnit : IsUnit (Ideal.Quotient.mk K dR) :=
    crt_unit_mk_of_principal_coprime K dR hcopR
  have hcUnit : IsUnit (Ideal.Quotient.mk L cR) :=
    crt_unit_mk_of_principal_coprime L cR hcopR.symm
  let dbar : (S.R ⧸ K)ˣ := hdUnit.unit
  let cbar : (S.R ⧸ L)ˣ := hcUnit.unit
  have hdbarVal : (dbar : S.R ⧸ K) = Ideal.Quotient.mk K dR := hdUnit.unit_spec
  have hcbarVal : (cbar : S.R ⧸ L) = Ideal.Quotient.mk L cR := hcUnit.unit_spec
  have hvUnit : IsUnit (Ideal.Quotient.mk K v) :=
    isUnit_iff_exists_inv.mpr ⟨Ideal.Quotient.mk K dR, hbezK⟩
  have huUnit : IsUnit (Ideal.Quotient.mk L u) :=
    isUnit_iff_exists_inv.mpr ⟨Ideal.Quotient.mk L cR, hbezL⟩
  let vbar : (S.R ⧸ K)ˣ := hvUnit.unit
  let ubar : (S.R ⧸ L)ˣ := huUnit.unit
  have hvbarVal : (vbar : S.R ⧸ K) = Ideal.Quotient.mk K v := hvUnit.unit_spec
  have hubarVal : (ubar : S.R ⧸ L) = Ideal.Quotient.mk L u := huUnit.unit_spec
  have hvdbar : vbar * dbar = 1 := by
    apply Units.ext
    change (vbar : S.R ⧸ K) * (dbar : S.R ⧸ K) = 1
    rw [hvbarVal, hdbarVal]
    exact hbezK
  have hucbar : ubar * cbar = 1 := by
    apply Units.ext
    change (ubar : S.R ⧸ L) * (cbar : S.R ⧸ L) = 1
    rw [hubarVal, hcbarVal]
    exact hbezL
  let χI := crtChiRQuotient D S hI j hc.1
  let χJ := crtChiRQuotient D S hJ j hd.1
  let χIJ := crtChiRQuotient D S hIJext j hcd
  let ψI := crtPsiRQuotient D S A hI c hc.1
  let ψJ := crtPsiRQuotient D S A hJ d hd.1
  let ψIJ := crtPsiRQuotient D S A hIJext (c * d) hcd
  let eCRT := Ideal.quotientMulEquivQuotientProd K L hcopR
  let ψProd := ψIJ.compAddMonoidHom eKL.toAddMonoidHom
  let χProd := crtMulCharPullback eKL χIJ
  have hpreLeft (n : S.R) :
      eCRT.symm (Ideal.Quotient.mk K n, 0) =
        Ideal.Quotient.mk (K * L) (v * dR * n) := by
    have hfirst : Ideal.Quotient.mk K (v * dR * n) = Ideal.Quotient.mk K n := by
      calc
        Ideal.Quotient.mk K (v * dR * n) =
            Ideal.Quotient.mk K (v * dR) * Ideal.Quotient.mk K n := by simp [map_mul]
        _ = 1 * Ideal.Quotient.mk K n := by rw [hbezK]
        _ = Ideal.Quotient.mk K n := by simp
    have hdmem : dR ∈ L := Ideal.mem_span_singleton_self dR
    have hzL : v * dR * n ∈ L := by
      have h := L.mul_mem_left (v * n) hdmem
      simpa [mul_assoc, mul_left_comm, mul_comm] using h
    have hsecond : Ideal.Quotient.mk L (v * dR * n) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hzL
    have hpair : eCRT (Ideal.Quotient.mk (K * L) (v * dR * n)) =
        (Ideal.Quotient.mk K n, 0) := by
      apply Prod.ext
      · simpa [eCRT] using hfirst
      · simpa [eCRT, hsecond]
    apply eCRT.injective
    calc
      eCRT (eCRT.symm (Ideal.Quotient.mk K n, 0)) =
          (Ideal.Quotient.mk K n, 0) := eCRT.apply_symm_apply _
      _ = eCRT (Ideal.Quotient.mk (K * L) (v * dR * n)) := hpair.symm
  have hpreRight (n : S.R) :
      eCRT.symm (0, Ideal.Quotient.mk L n) =
        Ideal.Quotient.mk (K * L) (u * cR * n) := by
    have hsecond : Ideal.Quotient.mk L (u * cR * n) = Ideal.Quotient.mk L n := by
      calc
        Ideal.Quotient.mk L (u * cR * n) =
            Ideal.Quotient.mk L (u * cR) * Ideal.Quotient.mk L n := by simp [map_mul]
        _ = 1 * Ideal.Quotient.mk L n := by rw [hbezL]
        _ = Ideal.Quotient.mk L n := by simp
    have hcmem : cR ∈ K := Ideal.mem_span_singleton_self cR
    have hzK : u * cR * n ∈ K := by
      have h := K.mul_mem_left (u * n) hcmem
      simpa [mul_assoc, mul_left_comm, mul_comm] using h
    have hfirst : Ideal.Quotient.mk K (u * cR * n) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hzK
    have hpair : eCRT (Ideal.Quotient.mk (K * L) (u * cR * n)) =
        (0, Ideal.Quotient.mk L n) := by
      apply Prod.ext
      · simpa [eCRT, hfirst]
      · simpa [eCRT] using hsecond
    apply eCRT.injective
    calc
      eCRT (eCRT.symm (0, Ideal.Quotient.mk L n)) =
          (0, Ideal.Quotient.mk L n) := eCRT.apply_symm_apply _
      _ = eCRT (Ideal.Quotient.mk (K * L) (u * cR * n)) := hpair.symm
  have hleftM (n : S.R) :
      OAI.IdealGaussCRT.leftAddChar eCRT ψProd (Ideal.Quotient.mk K n) =
        ψI.mulShift vbar (Ideal.Quotient.mk K n) := by
    change ψProd (eCRT.symm (Ideal.Quotient.mk K n, 0)) = _
    rw [hpreLeft n, AddChar.mulShift_apply]
    have harg : ((v * dR * n : S.R) : F) / ((c * d : Fˣ) : F) =
        ((v * n : S.R) : F) / (c : F) := by
      have hdRval : (dR : F) = (d : F) := rfl
      have hcdval : ((c * d : Fˣ) : F) = (c : F) * (d : F) := rfl
      change (v : F) * (dR : F) * (n : F) / ((c * d : Fˣ) : F) = _
      simp only [Subalgebra.coe_mul, Units.val_mul]
      rw [hdRval]
      field_simp [Units.ne_zero c, Units.ne_zero d]
    have hvMul : vbar * Ideal.Quotient.mk K n =
        Ideal.Quotient.mk K (v * n) := by
      change (vbar : S.R ⧸ K) * Ideal.Quotient.mk K n = _
      rw [hvbarVal, map_mul]
    calc
      ψProd (Ideal.Quotient.mk (K * L) (v * dR * n)) =
          S.e A (S.diag (((v * dR * n : S.R) : F) / ((c * d : Fˣ) : F))) := by
            change ψIJ (eKL (Ideal.Quotient.mk (K * L) (v * dR * n))) = _
            rw [show eKL (Ideal.Quotient.mk (K * L) (v * dR * n)) =
                Ideal.Quotient.mk (Ideal.span {crtSInteger S hcd}) (v * dR * n) by
              change Ideal.quotEquivOfEq hKL (Ideal.Quotient.mk (K * L) (v * dR * n)) = _
              exact Ideal.quotEquivOfEq_mk hKL (v * dR * n)]
            exact crtPsiRQuotient_mk D S A hIJext (c * d) hcd (v * dR * n)
      _ = S.e A (S.diag (((v * n : S.R) : F) / (c : F))) := by rw [harg]
      _ = ψI (Ideal.Quotient.mk K (v * n)) :=
        (crtPsiRQuotient_mk D S A hI c hc.1 (v * n)).symm
      _ = ψI (vbar * Ideal.Quotient.mk K n) := by rw [hvMul]
  have hrightM (n : S.R) :
      OAI.IdealGaussCRT.rightAddChar eCRT ψProd (Ideal.Quotient.mk L n) =
        ψJ.mulShift ubar (Ideal.Quotient.mk L n) := by
    change ψProd (eCRT.symm (0, Ideal.Quotient.mk L n)) = _
    rw [hpreRight n, AddChar.mulShift_apply]
    have harg : ((u * cR * n : S.R) : F) / ((c * d : Fˣ) : F) =
        ((u * n : S.R) : F) / (d : F) := by
      have hcRval : (cR : F) = (c : F) := rfl
      have hcdval : ((c * d : Fˣ) : F) = (c : F) * (d : F) := rfl
      change (u : F) * (cR : F) * (n : F) / ((c * d : Fˣ) : F) = _
      simp only [Subalgebra.coe_mul, Units.val_mul]
      rw [hcRval]
      field_simp [Units.ne_zero c, Units.ne_zero d]
    have huMul : ubar * Ideal.Quotient.mk L n =
        Ideal.Quotient.mk L (u * n) := by
      change (ubar : S.R ⧸ L) * Ideal.Quotient.mk L n = _
      rw [hubarVal, map_mul]
    calc
      ψProd (Ideal.Quotient.mk (K * L) (u * cR * n)) =
          S.e A (S.diag (((u * cR * n : S.R) : F) / ((c * d : Fˣ) : F))) := by
            change ψIJ (eKL (Ideal.Quotient.mk (K * L) (u * cR * n))) = _
            rw [show eKL (Ideal.Quotient.mk (K * L) (u * cR * n)) =
                Ideal.Quotient.mk (Ideal.span {crtSInteger S hcd}) (u * cR * n) by
              change Ideal.quotEquivOfEq hKL (Ideal.Quotient.mk (K * L) (u * cR * n)) = _
              exact Ideal.quotEquivOfEq_mk hKL (u * cR * n)]
            exact crtPsiRQuotient_mk D S A hIJext (c * d) hcd (u * cR * n)
      _ = S.e A (S.diag (((u * n : S.R) : F) / (d : F))) := by rw [harg]
      _ = ψJ (Ideal.Quotient.mk L (u * n)) :=
        (crtPsiRQuotient_mk D S A hJ d hd.1 (u * n)).symm
      _ = ψJ (ubar * Ideal.Quotient.mk L n) := by rw [huMul]
  have hleft : OAI.IdealGaussCRT.leftAddChar eCRT ψProd = ψI.mulShift vbar := by
    ext q
    obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact hleftM n
  have hright : OAI.IdealGaussCRT.rightAddChar eCRT ψProd = ψJ.mulShift ubar := by
    ext q
    obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact hrightM n
  have hχIprod : χI vbar * χI dbar = 1 := by
    calc
      χI vbar * χI dbar =
          (χI.toUnitHom vbar : ℂ) * (χI.toUnitHom dbar : ℂ) := rfl
      _ = (χI.toUnitHom (vbar * dbar) : ℂ) := by rw [map_mul, Units.val_mul]
      _ = 1 := by rw [hvdbar, map_one, Units.val_one]
  have hχJprod : χJ ubar * χJ cbar = 1 := by
    calc
      χJ ubar * χJ cbar =
          (χJ.toUnitHom ubar : ℂ) * (χJ.toUnitHom cbar : ℂ) := rfl
      _ = (χJ.toUnitHom (ubar * cbar) : ℂ) := by rw [map_mul, Units.val_mul]
      _ = 1 := by rw [hucbar, map_one, Units.val_one]
  have hcrossI : χI⁻¹ vbar = chiIdealPow D I (d : F) j := by
    calc
      χI⁻¹ vbar = (χI vbar)⁻¹ := MulChar.inv_apply_eq_inv' χI vbar
      _ = χI dbar := (eq_inv_of_mul_eq_one_right hχIprod).symm
      _ = chiIdealPow D I (d : F) j := by
        calc
          χI dbar = χI (Ideal.Quotient.mk K dR) := by rw [hdbarVal]
          _ = chiIdealPow D I (dR : F) j := crtChiRQuotient_mk D S hI j hc.1 dR
          _ = chiIdealPow D I (d : F) j := by rfl
  have hcrossJ : χJ⁻¹ ubar = chiIdealPow D J (c : F) j := by
    calc
      χJ⁻¹ ubar = (χJ ubar)⁻¹ := MulChar.inv_apply_eq_inv' χJ ubar
      _ = χJ cbar := (eq_inv_of_mul_eq_one_right hχJprod).symm
      _ = chiIdealPow D J (c : F) j := by
        calc
          χJ cbar = χJ (Ideal.Quotient.mk L cR) := by rw [hcbarVal]
          _ = chiIdealPow D J (cR : F) j := crtChiRQuotient_mk D S hJ j hd.1 cR
          _ = chiIdealPow D J (c : F) j := by rfl
  have hcrt := OAI.IdealGaussCRT.gauss_sum_ideal_crt K L hcopR χI χJ ψProd
  have hpoint (q : S.R ⧸ (K * L)) :
      χProd q =
        χI (Ideal.Quotient.factor (Ideal.mul_le_left : K * L ≤ K) q) *
          χJ (Ideal.Quotient.factor (Ideal.mul_le_right : K * L ≤ L) q) := by
    have hKLmk : eKL q = Ideal.Quotient.mk (Ideal.span {crtSInteger S hcd}) q.out := by
      calc
        eKL q = eKL (Ideal.Quotient.mk (K * L) q.out) :=
          congrArg eKL (Ideal.Quotient.mk_out q).symm
        _ = Ideal.Quotient.mk (Ideal.span {crtSInteger S hcd}) q.out := by
          change Ideal.quotEquivOfEq hKL (Ideal.Quotient.mk (K * L) q.out) = _
          exact Ideal.quotEquivOfEq_mk hKL q.out
    have hχprod : χProd q = chiIdealPow D (I * J) (q.out : F) j := by
      calc
        χProd q = χIJ (eKL q) := crtMulCharPullback_apply eKL χIJ q
        _ = χIJ (Ideal.Quotient.mk (Ideal.span {crtSInteger S hcd}) q.out) := by rw [hKLmk]
        _ = chiIdealPow D (I * J) (q.out : F) j :=
          crtChiRQuotient_mk D S hIJext j hcd q.out
    have hχleft := crtChiRQuotient_factor_left D S hI hJ c d hc.1 hd.1 hcopR j q
    have hχright := crtChiRQuotient_factor_right D S hI hJ c d hc.1 hd.1 hcopR j q
    calc
      χProd q = chiIdealPow D (I * J) (q.out : F) j := hχprod
      _ = chiIdealPow D I (q.out : F) j * chiIdealPow D J (q.out : F) j :=
        crt_chiIdealPow_mul_ideal D hI.1 hJ.1 (q.out : F) j
      _ = χI (Ideal.Quotient.factor (Ideal.mul_le_left : K * L ≤ K) q) *
          χJ (Ideal.Quotient.factor (Ideal.mul_le_right : K * L ≤ L) q) := by
        rw [← hχleft, ← hχright]
  have hsumCRT : gaussSum χProd ψProd =
      ∑ q : S.R ⧸ (K * L),
        χI (Ideal.Quotient.factor (Ideal.mul_le_left : K * L ≤ K) q) *
          χJ (Ideal.Quotient.factor (Ideal.mul_le_right : K * L ≤ L) q) * ψProd q := by
    simp only [gaussSum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [hpoint q]
  have hgaussFactor : gaussSum χProd ψProd =
      chiIdealPow D I (d : F) j * chiIdealPow D J (c : F) j *
        gaussSum χI ψI * gaussSum χJ ψJ := by
    calc
      gaussSum χProd ψProd = _ := hsumCRT.trans hcrt
      _ = chiIdealPow D I (d : F) j * chiIdealPow D J (c : F) j *
          gaussSum χI ψI * gaussSum χJ ψJ := by
        rw [hleft, hright, gaussSum_mulShift_eq, gaussSum_mulShift_eq,
          hcrossI, hcrossJ]
        ring
  have hgammaI := crt_gamma_eq_gaussSumR D S A j hI c hc.1
  have hgammaJ := crt_gamma_eq_gaussSumR D S A j hJ d hd.1
  have hgammaIJ := crt_gamma_eq_gaussSumR D S A j hIJext (c * d) hcd
  have hgammaI' : gamma D S A j I c =
      (((Ideal.absNorm I : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * gaussSum χI ψI := by
    simpa [χI, ψI] using hgammaI
  have hgammaJ' : gamma D S A j J d =
      (((Ideal.absNorm J : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * gaussSum χJ ψJ := by
    simpa [χJ, ψJ] using hgammaJ
  have hgauss : gaussSum χIJ ψIJ =
      chiIdealPow D I (d : F) j * chiIdealPow D J (c : F) j *
        gaussSum χI ψI * gaussSum χJ ψJ := by
    calc
      gaussSum χIJ ψIJ = gaussSum χProd ψProd := by
        simpa [χProd, ψProd] using crt_gaussSum_pullback eKL χIJ ψIJ
      _ = _ := hgaussFactor
  have hnorm :
      (Ideal.absNorm (I * J) : ℝ) ^ (-(1 / 2 : ℝ)) =
        (Ideal.absNorm I : ℝ) ^ (-(1 / 2 : ℝ)) *
          (Ideal.absNorm J : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [show Ideal.absNorm (I * J) = Ideal.absNorm I * Ideal.absNorm J by
      exact map_mul Ideal.absNorm I J, Nat.cast_mul]
    exact Real.mul_rpow (by positivity) (by positivity)
  have hnormC :
      (((Ideal.absNorm (I * J) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
        (((Ideal.absNorm I : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          (((Ideal.absNorm J : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) :=
    calc
      _ = (( (Ideal.absNorm I : ℝ) ^ (-(1 / 2 : ℝ)) *
          (Ideal.absNorm J : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) :=
        congrArg (fun x : ℝ => (x : ℂ)) hnorm
      _ = _ := by simp
  calc
    gamma D S A j (I * J) ((c * d : Fˣ) : F) =
        ((Ideal.absNorm (I * J) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) * gaussSum χIJ ψIJ := by
          simpa [χIJ, ψIJ] using hgammaIJ
    _ = ((Ideal.absNorm (I * J) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
          (chiIdealPow D I (d : F) j * chiIdealPow D J (c : F) j *
            gaussSum χI ψI * gaussSum χJ ψJ) := by rw [hgauss]
    _ = chiIdealPow D I (d : F) j * chiIdealPow D J (c : F) j *
          gamma D S A j I c * gamma D S A j J d := by
      rw [hgammaI', hgammaJ', hnormC]
      ring


end ArtinPrimitiveRoots.A1
