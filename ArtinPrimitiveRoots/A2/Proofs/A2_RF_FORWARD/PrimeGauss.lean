import ArtinPrimitiveRoots.A2.Reflection.Nodes
import ArtinPrimitiveRoots.A2.Proofs.A2_RF_FORWARD.FiniteMass
import ArtinPrimitiveRoots.Proofs.qs_nq0_sol.ResidueUnits

set_option autoImplicit false
set_option maxHeartbeats 800000

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A2

theorem gamma_prime_norm_one {F : Type} [Field F] [NumberField F]
    {CE : ℕ} {condη : Ideal (𝓞 F)}
    (D : FieldData F) (S : SData F CE condη) (A : AddCharData F)
    (v : FinPlace F) (hv : v ∉ S.Sf)
    (p : Fˣ) (hp : S.IsGen (p : F) v.asIdeal) :
    ‖gamma D S A 2 v.asIdeal (p : F)‖ = 1 := by
  classical
  letI : IsTotallyComplex F := D.isTotallyComplex
  have rf_trace_eq_pair_sum_re (z : F) :
      (Algebra.trace ℚ F z : ℂ) =
        ∑ w : InfinitePlace F, (w.embedding z + ComplexEmbedding.conjugate w.embedding z) := by
    classical
    have htrace := trace_eq_sum_embeddings (K := ℚ) (L := F) (E := ℂ) (x := z)
    have hring : (∑ φ : F →+* ℂ, φ z) = ∑ σ : F →ₐ[ℚ] ℂ, σ z := by
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
      apply IsTotallyComplex.complexEmbedding_not_isReal w.embedding
      rw [ComplexEmbedding.isReal_iff]
      exact h.symm
    have hset : Finset.univ.filter (fun φ : F →+* ℂ => InfinitePlace.mk φ = w) =
        ({w.embedding, ComplexEmbedding.conjugate w.embedding} : Finset (F →+* ℂ)) := by
      ext φ
      simp [hmk]
    change (∑ φ ∈ Finset.univ.filter (fun φ : F →+* ℂ => InfinitePlace.mk φ = w), φ z) = _
    rw [hset, Finset.sum_pair hneq]

  have rf_trace_eq_two_real_sum (z : F) :
      (Algebra.trace ℚ F z : ℂ) =
        (2 : ℂ) * ∑ w : InfinitePlace F, ((w.embedding z).re : ℂ) := by
    rw [rf_trace_eq_pair_sum_re]
    simp only [ComplexEmbedding.conjugate_coe_eq, Complex.add_conj]
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
    rw [Finset.mul_sum]

  have rf_arch_exp_eq_trace (z : F) :
      (∏ w : InfinitePlace F,
          Complex.exp (-(4 * Real.pi * Complex.I * ((w.embedding z).re : ℂ)))) =
        Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ))) := by
    rw [← Complex.exp_sum]
    apply congrArg Complex.exp
    calc
      ∑ w : InfinitePlace F, -(4 * Real.pi * Complex.I * ((w.embedding z).re : ℂ)) =
          -(4 * Real.pi * Complex.I *
            ∑ w : InfinitePlace F, ((w.embedding z).re : ℂ)) := by
              rw [Finset.sum_neg_distrib, Finset.mul_sum]
      _ = -(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ)) := by
        rw [rf_trace_eq_two_real_sum]
        ring

  have rf_local_additive_phase_congr (v : FinPlace F) (p : Fˣ)
      (hp : HeightOneSpectrum.valuation F v (p : F) = WithZero.exp (-1 : ℤ))
      (a b : 𝓞 F) (hab : a - b ∈ v.asIdeal) :
      A.ψ v (algebraMap F (v.adicCompletion F) ((a : F) / (p : F))) =
        A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / (p : F))) := by
    have hvalNum : HeightOneSpectrum.valuation F v ((a : F) - b) ≤
        WithZero.exp (-1 : ℤ) := by
      change v.valuation F (algebraMap (𝓞 F) F (a - b)) ≤ WithZero.exp (-1 : ℤ)
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      apply (v.intValuation_le_pow_iff_mem (a - b) 1).2
      simpa using hab
    have hvalDiv : HeightOneSpectrum.valuation F v (((a : F) - b) / (p : F)) ≤ 1 := by
      rw [map_div₀, hp]
      have hexpPos : 0 < WithZero.exp (-1 : ℤ) :=
        lt_of_le_of_ne zero_le (Ne.symm WithZero.exp_ne_zero)
      exact (div_le_one₀ hexpPos).2 hvalNum
    have hlocal :
        algebraMap F (v.adicCompletion F) (((a : F) - b) / (p : F)) ∈
          v.adicCompletionIntegers F := by
      change ((((a : F) - b) / (p : F) : F) : v.adicCompletion F) ∈
        v.adicCompletionIntegers F
      rw [HeightOneSpectrum.mem_adicCompletionIntegers,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact hvalDiv
    have harg : algebraMap F (v.adicCompletion F) (((a : F) - b) / (p : F)) =
        algebraMap F (v.adicCompletion F) ((a : F) / (p : F)) -
          algebraMap F (v.adicCompletion F) ((b : F) / (p : F)) := by
      have hF : ((a : F) - b) / (p : F) =
          (a : F) / (p : F) - (b : F) / (p : F) := by
        field_simp [Units.ne_zero p]
      rw [hF, map_sub]
    have hdiv := (A.ψ v).map_sub_eq_div
      (algebraMap F (v.adicCompletion F) ((a : F) / (p : F)))
      (algebraMap F (v.adicCompletion F) ((b : F) / (p : F)))
    have hbne : A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / (p : F))) ≠ 0 :=
      (AddChar.val_isUnit (A.ψ v)
        (algebraMap F (v.adicCompletion F) ((b : F) / (p : F)))).ne_zero
    calc
      A.ψ v (algebraMap F (v.adicCompletion F) ((a : F) / (p : F))) =
          (A.ψ v (algebraMap F (v.adicCompletion F) ((a : F) / (p : F))) /
            A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / (p : F)))) *
              A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / (p : F))) :=
        (div_mul_cancel₀ _ hbne).symm
      _ = A.ψ v (algebraMap F (v.adicCompletion F) (((a : F) - b) / (p : F))) *
            A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / (p : F))) := by
        rw [← hdiv, ← harg]
      _ = A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / (p : F))) := by
        rw [A.integral v _ hlocal, one_mul]

  let Q := 𝓞 F ⧸ v.asIdeal
  letI : Field Q := bridgeResidueField v
  letI : Fintype Q := bridgeResidueFintype v
  obtain ⟨χ₁, hχ₁ord, hχ₁⟩ := (a2_bridge_FINITE_CHAR D S A v hv p hp).2.1
  obtain ⟨ψ, hψprim, hψspec⟩ := (a2_bridge_FINITE_CHAR D S A v hv p hp).2.2
  let χ : MulChar Q ℂ := χ₁ ^ 2
  have hχval (x : Q) : χ x = chiPow D v (algebraMap (𝓞 F) F x.out) 2 := by
    change (χ₁ ^ 2) x = chiPow D v (algebraMap (𝓞 F) F x.out) 2
    rw [MulChar.pow_apply' χ₁ (by norm_num : (2 : ℕ) ≠ 0) x]
    by_cases hx : x = 0
    · subst x
      have hres := (a2_bridge_SYMBOL D S).residue_algebraMap v (0 : 𝓞 F)
      simp only [map_zero] at hres
      simp [hχ₁, chiPow, hres]
    · have hres := (a2_bridge_SYMBOL D S).residue_algebraMap v x.out
      have hr : residue v (algebraMap (𝓞 F) F x.out) ≠ 0 := by
        rw [hres, Ideal.Quotient.mk_out]
        exact hx
      rw [hχ₁ x,
        (a2_bridge_SYMBOL D S).chiPow_nonzero v
          (algebraMap (𝓞 F) F x.out) 1 hr,
        (a2_bridge_SYMBOL D S).chiPow_nonzero v
          (algebraMap (𝓞 F) F x.out) 2 hr]
      simp
  have hχne : χ ≠ 1 := by
    intro h
    have hpow : χ₁ ^ 2 = 1 := by simpa [χ] using h
    have hdiv : orderOf χ₁ ∣ 2 := orderOf_dvd_of_pow_eq_one hpow
    rw [hχ₁ord] at hdiv
    norm_num at hdiv
  have hψne : ψ ≠ 1 := by
    intro h
    have hs := hψprim (a := (1 : Q)) (by simp)
    apply hs
    ext x
    simp [h]
  have hψinvprim : (ψ⁻¹).IsPrimitive := AddChar.IsPrimitive.of_ne_one (by
    intro h
    have h' : ψ = 1 := by
      ext x
      have hx := congrArg (fun φ : AddChar Q ℂ => φ x) h
      rw [AddChar.inv_apply'] at hx
      exact inv_eq_one.mp hx
    exact hψne h')
  have hvalP (w : FinPlace F) (hw : w ∉ S.Sf) (hwv : w ≠ v) :
      HeightOneSpectrum.valuation F w (p : F) = 1 := by
    have hcount : FractionalIdeal.count F w
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p : F)) = 0 := by
      calc
        _ = FractionalIdeal.count F w
            (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := hp.2.2 w hw
        _ = 0 := FractionalIdeal.count_maximal_coprime F w
          (w := v) hwv.symm
    have hlog : WithZero.log (HeightOneSpectrum.valuation F w (p : F)) = 0 := by
      have h := qs_nq0_count_spanSingleton_eq_neg_log_valuation w (p : F) p.ne_zero
      rw [hcount] at h
      simpa only [neg_eq_zero] using h.symm
    have hne : HeightOneSpectrum.valuation F w (p : F) ≠ 0 :=
      (w.valuation F).ne_zero_iff.mpr p.ne_zero
    calc
      HeightOneSpectrum.valuation F w (p : F) =
          WithZero.exp (WithZero.log (HeightOneSpectrum.valuation F w (p : F))) :=
        (WithZero.exp_log hne).symm
      _ = 1 := by simp [hlog]
  have hcountP : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p : F)) = 1 := by
    calc
      _ = FractionalIdeal.count F v
          (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := hp.2.2 v hv
      _ = 1 := FractionalIdeal.count_self F v
  have hlogP : WithZero.log (HeightOneSpectrum.valuation F v (p : F)) = -1 := by
    have h := qs_nq0_count_spanSingleton_eq_neg_log_valuation v (p : F) p.ne_zero
    rw [hcountP] at h
    linarith
  have hvalPV : HeightOneSpectrum.valuation F v (p : F) = WithZero.exp (-1 : ℤ) := by
    have hne : HeightOneSpectrum.valuation F v (p : F) ≠ 0 :=
      (v.valuation F).ne_zero_iff.mpr p.ne_zero
    calc
      HeightOneSpectrum.valuation F v (p : F) =
          WithZero.exp (WithZero.log (HeightOneSpectrum.valuation F v (p : F))) :=
        (WithZero.exp_log hne).symm
      _ = WithZero.exp (-1 : ℤ) := by rw [hlogP]
  have hSadd (x : Q) :
      S.e A (S.diag (algebraMap (𝓞 F) F x.out / (p : F))) = ψ⁻¹ x := by
    let z : F := algebraMap (𝓞 F) F x.out / (p : F)
    let f : FinPlace F → ℂ := fun w => A.ψ w (algebraMap F (w.adicCompletion F) z)
    have hvalz (w : FinPlace F) (hw : w ∉ S.Sf) (hwv : w ≠ v) :
        HeightOneSpectrum.valuation F w z ≤ 1 := by
      by_cases hx : x.out = 0
      · simp [z, hx]
      have hxval : HeightOneSpectrum.valuation F w
          (algebraMap (𝓞 F) F x.out) ≤ 1 := w.valuation_le_one x.out
      calc
        HeightOneSpectrum.valuation F w z =
            HeightOneSpectrum.valuation F w (algebraMap (𝓞 F) F x.out) /
              HeightOneSpectrum.valuation F w (p : F) := by
                dsimp [z]
                rw [map_div₀]
        _ = HeightOneSpectrum.valuation F w (algebraMap (𝓞 F) F x.out) := by
              rw [hvalP w hw hwv, div_one]
        _ ≤ 1 := hxval
    have hsupport : Function.mulSupport f ⊆
        ((insert v S.Sf : Finset (FinPlace F)) : Set (FinPlace F)) := by
      intro w hw
      simp only [Function.mem_mulSupport] at hw
      by_cases hws : w ∈ S.Sf
      · exact Finset.mem_insert_of_mem hws
      · by_cases hwv : w = v
        · simp [hwv]
        · have hmem : (algebraMap F (w.adicCompletion F) z) ∈
              w.adicCompletionIntegers F := by
            rw [HeightOneSpectrum.mem_adicCompletionIntegers,
              HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
              Algebra.algebraMap_self, RingHom.id_apply,
              w.valuedAdicCompletion_eq_valuation']
            exact hvalz w hws hwv
          exact (hw (A.integral w _ hmem)).elim
    have hfinprod : (∏ᶠ w : FinPlace F, f w) = ∏ w ∈ insert v S.Sf, f w :=
      finprod_eq_prod_of_mulSupport_subset f hsupport
    have hglobal := (A.trivial_on_F z).2
    have hattach : (∏ w : S.Sf, f w) = ∏ w ∈ S.Sf, f w := by
      simp [Finset.prod_attach]
    have hglobal' : f v *
        ((∏ w : S.Sf, f w) *
          Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ)))) = 1 := by
      rw [hfinprod, Finset.prod_insert (by simpa using hv)] at hglobal
      rw [← hattach] at hglobal
      simpa [f, z, mul_assoc] using hglobal
    have hSprod : (∏ w : S.Sf, f w) *
        Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ))) =
          (f v)⁻¹ := by
      have hcomm :
          ((∏ w : S.Sf, f w) *
            Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ)))) * f v = 1 := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hglobal'
      exact eq_inv_of_mul_eq_one_left hcomm
    have hE : S.e A (S.diag z) =
        (∏ w : S.Sf, f w) *
          Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ))) := by
      change (∏ w : S.Sf, f w) *
          ∏ w : InfinitePlace F,
            Complex.exp (-(4 * Real.pi * Complex.I * ((w.embedding z).re : ℂ))) = _
      rw [rf_arch_exp_eq_trace z]
    have honeOut : (1 : Q).out - 1 ∈ v.asIdeal := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub, Ideal.Quotient.mk_out]
      simp
    have hrepMul : x.out * (1 : Q).out - x.out ∈ v.asIdeal := by
      have h := v.asIdeal.mul_mem_left x.out honeOut
      convert h using 1 <;> ring
    have hψx : ψ x = A.ψ v (algebraMap F (v.adicCompletion F)
        (algebraMap (𝓞 F) F x.out / (p : F))) := by
      calc
        ψ x = ψ (1 * x) := by simp
        _ = A.ψ v (algebraMap F (v.adicCompletion F)
            (algebraMap (𝓞 F) F x.out * algebraMap (𝓞 F) F (1 : Q).out / (p : F))) :=
              hψspec 1 x
        _ = A.ψ v (algebraMap F (v.adicCompletion F)
            (algebraMap (𝓞 F) F (x.out * (1 : Q).out) / (p : F))) := by
              simp only [map_mul]
        _ = A.ψ v (algebraMap F (v.adicCompletion F)
            (algebraMap (𝓞 F) F x.out / (p : F))) :=
              rf_local_additive_phase_congr v p hvalPV _ _ hrepMul
    rw [hE, hSprod, AddChar.inv_apply', hψx]
  have hideal (x : Q) :
      chiIdealPow D v.asIdeal (algebraMap (𝓞 F) F x.out) 2 = χ x := by
    have hvprime : Prime v.asIdeal := (Ideal.prime_iff_isPrime v.ne_bot).2 v.isPrime
    rw [chiIdealPow, UniqueFactorizationMonoid.normalizedFactors_irreducible
      hvprime.irreducible]
    simp [χ, hχval, v.isPrime, v.ne_bot]
  have hsum :
      (∑ᶠ x : Q, chiIdealPow D v.asIdeal (algebraMap (𝓞 F) F x.out) 2 *
        S.e A (S.diag (algebraMap (𝓞 F) F x.out / (p : F)))) =
      gaussSum χ (ψ⁻¹) := by
    rw [finsum_eq_sum_of_fintype, gaussSum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [hideal x, hSadd x]
  have hqcard : (Ideal.absNorm v.asIdeal : ℝ) = (Fintype.card Q : ℝ) := by
    exact_mod_cast (by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card])
  have hGprod : gaussSum χ (ψ⁻¹) * star (gaussSum χ (ψ⁻¹)) =
      (Fintype.card Q : ℂ) := by
    calc
      _ = gaussSum χ (ψ⁻¹) * gaussSum χ⁻¹ (ψ⁻¹)⁻¹ := by
        rw [star_gaussSum_eq]
      _ = _ := gaussSum_mul_gaussSum_eq_card hχne hψinvprim
  have hnormsq : ‖gaussSum χ (ψ⁻¹)‖ ^ 2 = (Fintype.card Q : ℝ) := by
    have hC : ((‖gaussSum χ (ψ⁻¹)‖ ^ 2 : ℝ) : ℂ) = (Fintype.card Q : ℂ) := by
      simpa [Complex.mul_conj'] using hGprod
    exact_mod_cast hC
  have hqpos : 0 < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v))
  have hscale : ‖(((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) := by
    calc
      _ = |(Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ))| := Complex.norm_real _
      _ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) :=
        abs_of_nonneg (Real.rpow_nonneg hqpos.le _)
  have hgammasum : gamma D S A 2 v.asIdeal (p : F) =
      (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * gaussSum χ (ψ⁻¹) := by
    simp only [gamma]
    rw [hsum]
  have hgammasq : ‖gamma D S A 2 v.asIdeal (p : F)‖ ^ 2 = 1 := by
    rw [hgammasum, norm_mul, hscale, mul_pow, hnormsq, ← hqcard]
    have hpw : ((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 * (Ideal.absNorm v.asIdeal : ℝ) = 1 := by
      calc
        ((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 * (Ideal.absNorm v.asIdeal : ℝ) =
            (Ideal.absNorm v.asIdeal : ℝ) ^ ((-(1 / 2 : ℝ)) * (2 : ℝ)) * (Ideal.absNorm v.asIdeal : ℝ) := by
              rw [← Real.rpow_mul_natCast hqpos.le (-(1 / 2 : ℝ)) 2]
              congr 1
        _ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-1 : ℝ) * (Ideal.absNorm v.asIdeal : ℝ) := by
          congr 1
          norm_num
        _ = 1 := by
          rw [Real.rpow_neg hqpos.le, Real.rpow_one]
          exact inv_mul_cancel₀ (ne_of_gt hqpos)
    exact hpw
  have hnonneg := norm_nonneg (gamma D S A 2 v.asIdeal (p : F))
  nlinarith [hgammasq]


end ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
