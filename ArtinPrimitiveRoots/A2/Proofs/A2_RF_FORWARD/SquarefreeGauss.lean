import ArtinPrimitiveRoots.A2.Proofs.A2_RF_FORWARD.PrimeGauss

set_option autoImplicit false
set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A2

theorem gamma_sqf_norm_le_one {F : Type} [Field F] [NumberField F]
    {CE : ℕ} {condη : Ideal (𝓞 F)}
    (D : FieldData F) (S : SData F CE condη) (H : HilbertData F)
    (Bd : BData S H) (A : AddCharData F)
    (I : Ideal (𝓞 F)) (hI : S.IsExterior I) (hsq : Squarefree I)
    (c : Fˣ) (hc : S.IsGen (c : F) I ∧ Bd.Allowed c) :
    ‖gamma D S A 2 I (c : F)‖ ≤ 1 := by
  classical
  let SB := a2_bridge_SYMBOL D S
  have htop (a : Fˣ) (ha : S.IsGen (a : F) ⊤) :
      gamma D S A 2 (⊤ : Ideal (𝓞 F)) (a : F) = 1 := by
    let Q := 𝓞 F ⧸ (⊤ : Ideal (𝓞 F))
    letI : Finite Q := Ring.HasFiniteQuotients.finiteQuotient top_ne_bot
    letI : Fintype Q := Fintype.ofFinite Q
    letI : Unique Q :=
      { default := 0
        uniq := fun x => by
          calc
            x = Ideal.Quotient.mk (⊤ : Ideal (𝓞 F)) x.out :=
              (Ideal.Quotient.mk_out x).symm
            _ = 0 := (Ideal.Quotient.eq_zero_iff_mem).2 Submodule.mem_top }
    have hterm (x : Q) :
        chiIdealPow D (⊤ : Ideal (𝓞 F)) (algebraMap (𝓞 F) F x.out) 2 *
          S.e A (S.diag (algebraMap (𝓞 F) F x.out / (a : F))) = 1 := by
      have he := (SData.e_pairing_perfect D S A ⊤ ha.1 (a : F) ha).1
        x.out Submodule.mem_top 1
      rw [SB.ideal_one]
      simpa using he
    rw [gamma, finsum_eq_sum_of_fintype]
    simp only [Fintype.sum_unique]
    simpa using hterm (default : Q)
  have hgenMul {J K : Ideal (𝓞 F)} (hJK : S.IsExterior (J * K))
      (a b : Fˣ) (ha : S.IsGen (a : F) J) (hb : S.IsGen (b : F) K) :
      S.IsGen ((a * b : Fˣ) : F) (J * K) := by
    refine ⟨hJK, (a * b).ne_zero, ?_⟩
    intro v hv
    have hJ0 : (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr
        (by simpa only [Ideal.zero_eq_bot] using ha.1.1)
    have hK0 : (K : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr
        (by simpa only [Ideal.zero_eq_bot] using hb.1.1)
    rw [Units.val_mul, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
      FractionalIdeal.count_mul F v
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr a.ne_zero)
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr b.ne_zero),
      ha.2.2 v hv, hb.2.2 v hv, FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.count_mul F v hJ0 hK0]
  have hallowedMul (a b : Fˣ) (ha : Bd.Allowed a) (hb : Bd.Allowed b) :
      Bd.Allowed (a * b) := by
    change QuotientGroup.mk (S.diagU (a * b)) ∈ Bd.B
    rw [map_mul, QuotientGroup.mk_mul]
    exact Bd.B.mul_mem ha hb
  have hgenUS (e : S.US) : S.IsGen ((e : Fˣ) : F) ⊤ := by
    refine ⟨⟨top_ne_bot, ?_⟩, (e : Fˣ).ne_zero, ?_⟩
    · intro v hv hle
      exact v.isPrime.ne_top (top_le_iff.mp hle)
    · intro v hv
      have hval : v.valuation F ((e : Fˣ) : F) = 1 :=
        Set.unit_valuation_eq_one (S := (S.Sf : Set (FinPlace F))) (K := F) e hv
      rw [qs_nq0_count_spanSingleton_eq_neg_log_valuation v _ (e : Fˣ).ne_zero, hval]
      simpa using (FractionalIdeal.count_one F v).symm
  have hallowedSix (e : Fˣ) : Bd.Allowed (e ^ (6 : ℕ)) := by
    change QuotientGroup.mk (S.diagU (e ^ (6 : ℕ))) ∈ Bd.B
    have hclass : QuotientGroup.mk (S.diagU (e ^ (6 : ℕ))) = (1 : S.V) := by
      rw [map_pow]
      exact (QuotientGroup.eq_one_iff _).2 ⟨S.diagU e, rfl⟩
    rw [hclass]
    exact Bd.B.one_mem
  have hchange {J : Ideal (𝓞 F)} (hJ : S.IsExterior J) (hJsq : Squarefree J)
      (a b : Fˣ) (ha : S.IsGen (a : F) J ∧ Bd.Allowed a)
      (hb : S.IsGen (b : F) J ∧ Bd.Allowed b)
      (hnorm : ‖gamma D S A 2 J (b : F)‖ ≤ 1) :
      ‖gamma D S A 2 J (a : F)‖ ≤ 1 := by
    obtain ⟨e, he, hab⟩ := Bd.allowed_unique J a b ha hb
    let u : S.US := ⟨e, he⟩
    let e6 : Fˣ := ((u ^ (6 : ℕ) : S.US) : Fˣ)
    have he6gen : S.IsGen (e6 : F) ⊤ := hgenUS (u ^ 6)
    have he6allowed : Bd.Allowed e6 := by
      simpa only [e6, SubgroupClass.coe_pow] using hallowedSix e
    have htopSq : Squarefree (⊤ : Ideal (𝓞 F)) := by
      simpa only [Ideal.one_eq_top] using (squarefree_one : Squarefree (1 : Ideal (𝓞 F)))
    have hcoprime : IsCoprime (⊤ : Ideal (𝓞 F)) J := by
      rw [Ideal.isCoprime_iff_add]
      simp
    have hcrt := gamma_crt D S A H Bd 2 ⊤ J he6gen.1 hJ htopSq hJsq
      hcoprime e6 b ⟨he6gen, he6allowed⟩ hb
    have haeq : a = e6 * b := by simpa [e6, u] using hab
    have heq : gamma D S A 2 J (a : F) =
        chiIdealPow D J (e6 : F) 2 * gamma D S A 2 J (b : F) := by
      simpa only [Ideal.top_mul, SB.ideal_one, htop e6 he6gen, one_mul, mul_one,
        ← haeq] using hcrt
    rw [heq, norm_mul]
    exact mul_le_one₀ (SB.ideal_norm_le J _ 2) (norm_nonneg _) hnorm
  have hall : ∀ J : Ideal (𝓞 F), S.IsExterior J → Squarefree J →
      ∀ a : Fˣ, S.IsGen (a : F) J ∧ Bd.Allowed a →
        ‖gamma D S A 2 J (a : F)‖ ≤ 1 := by
    intro J
    induction J using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ =>
        intro hJ
        exact (hJ.1 (by simp)).elim
    | h₂ J hunit =>
        intro hJ hJsq a ha
        have hJtop : J = ⊤ := Ideal.isUnit_iff.mp hunit
        subst J
        simpa only [htop a ha.1, norm_one] using (le_refl (1 : ℝ))
    | h₃ J P hJ0 hP ih =>
        intro hPJ hPJsq a ha
        have hPext : S.IsExterior P := by
          refine ⟨by simpa only [Ideal.zero_eq_bot] using hP.ne_zero, ?_⟩
          intro v hv hPle
          exact hPJ.2 v hv (Ideal.mul_le_left.trans hPle)
        have hJext : S.IsExterior J := by
          refine ⟨by simpa only [Ideal.zero_eq_bot] using hJ0, ?_⟩
          intro v hv hJle
          exact hPJ.2 v hv (Ideal.mul_le_right.trans hJle)
        let v : FinPlace F := ⟨P, Ideal.isPrime_of_prime hP,
          by simpa only [Ideal.zero_eq_bot] using hP.ne_zero⟩
        have hv : v ∉ S.Sf := fun hv => hPext.2 v hv le_rfl
        have hcoprime : IsCoprime P J := by
          apply Ideal.coprime_of_no_prime_ge
          intro T hPT hJT hT
          have hTP : T = P := (v.isMaximal.eq_of_le hT.ne_top hPT).symm
          subst T
          exact hP.not_isUnit ((IsRelPrime.of_squarefree_mul hPJsq)
            dvd_rfl (Ideal.dvd_iff_le.mpr hJT))
        obtain ⟨p, hp⟩ := Bd.exists_allowed P hPext
        obtain ⟨b, hb⟩ := Bd.exists_allowed J hJext
        have hpNorm : ‖gamma D S A 2 P (p : F)‖ = 1 :=
          gamma_prime_norm_one D S A v hv p hp.1
        have hbNorm := ih hJext hPJsq.of_mul_right b hb
        have hcrt := gamma_crt D S A H Bd 2 P J hPext hJext hP.squarefree
          hPJsq.of_mul_right hcoprime p b hp hb
        have hprodNorm : ‖gamma D S A 2 (P * J) ((p * b : Fˣ) : F)‖ ≤ 1 := by
          rw [hcrt, norm_mul, norm_mul, norm_mul, hpNorm, mul_one]
          exact mul_le_one₀
            (mul_le_one₀ (SB.ideal_norm_le P _ 2) (norm_nonneg _)
              (SB.ideal_norm_le J _ 2)) (norm_nonneg _) hbNorm
        exact hchange hPJ hPJsq a (p * b) ha
          ⟨hgenMul hPJ p b hp.1 hb.1, hallowedMul p b hp.2 hb.2⟩ hprodNorm
  exact hall I hI hsq c hc

end ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
