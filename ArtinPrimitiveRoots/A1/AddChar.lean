import ArtinPrimitiveRoots.A1.Hilbert
import ArtinPrimitiveRoots.A1.Proofs.A1_DUAL.PairingCore

/-!
# A1 interface, §4: additive character and Gauss sums

Frozen interface of part A1 (paper §§2, 2a, 3, App. 10). Each `sorry` is owned by a package of
`research/design/A1-DESIGN.md` §3, named in its docstring. Design: `research/design/A1-Interface.lean`
(Opus A1 sub-agent, 2026-10-07).
-/

set_option autoImplicit false

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
    (hI : S.IsExterior I) (c : F) (hc : S.IsGen c I) (n : 𝓞 F) (hn : n ∈ I) :
    algebraMap (𝓞 F) F n / c ∈ S.R := by
  sorry

private theorem mem_ideal_of_div_mem_R (S : SData F CE condη) (I : Ideal (𝓞 F))
    (hI : S.IsExterior I) (c : F) (hc : S.IsGen c I) (n : 𝓞 F)
    (hn : algebraMap (𝓞 F) F n / c ∈ S.R) : n ∈ I := by
  sorry

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
    have hdiv := integral_div_gen S I hI c hc (n * d) hnd
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

/-- eq:gauss-crt (02:428–435). Package P-ARITH-GAUSS. -/
theorem gamma_crt (D : FieldData F) (S : SData F CE condη) (A : AddCharData F) (H : HilbertData F)
    (Bd : BData S H) (j : ℤ) (I J : Ideal (𝓞 F)) (hI : S.IsExterior I) (hJ : S.IsExterior J)
    (hIs : Squarefree I) (hJs : Squarefree J) (hIJ : IsCoprime I J) (c d : Fˣ)
    (hc : S.IsGen (c : F) I ∧ Bd.Allowed c) (hd : S.IsGen (d : F) J ∧ Bd.Allowed d) :
    gamma D S A j (I * J) ((c * d : Fˣ) : F) =
      chiIdealPow D I (d : F) j * chiIdealPow D J (c : F) j *
        gamma D S A j I c * gamma D S A j J d := by
  sorry


end ArtinPrimitiveRoots.A1
