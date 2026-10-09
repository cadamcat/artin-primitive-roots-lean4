import ArtinPrimitiveRoots.A2.Interface
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicative

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol

open ArtinPrimitiveRoots A1 A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Every nonzero S-integer supplies the arithmetic data of a reflection row. -/
theorem probe_reflection_row_lift (S : SData F CE condη)
    (m : S.R) (hm : m ≠ 0) :
    ∃ r : ReflectionRow S, r.m = m := by
  have hmF : (m : F) ≠ 0 := by
    intro h
    exact hm (Subtype.ext h)
  have hexterior : ∃ I : S.ExtIdeal, S.IsGen (m : F) I.1 := by
    let principal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F :=
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (m : F)
    let counts : FinPlace F → ℤ := fun v => FractionalIdeal.count F v principal
    have hfinite : {v : FinPlace F | counts v ≠ 0}.Finite := by
      simpa only [Filter.eventually_cofinite, counts, ne_eq] using
        FractionalIdeal.finite_factors principal
    let support := hfinite.toFinset
    let exponentFun : FinPlace F → ℤ := fun v => if v ∉ S.Sf then counts v else 0
    have hsupport : ∀ v, exponentFun v ≠ 0 → v ∈ support := by
      intro v hv
      by_cases hvS : v ∈ S.Sf
      · simp [exponentFun, hvS] at hv
      · exact hfinite.mem_toFinset.mpr (by simpa [exponentFun, hvS] using hv)
    let exponent : FinPlace F →₀ ℤ := Finsupp.onFinset support exponentFun hsupport
    have hexponent_nonneg (v : FinPlace F) : 0 ≤ exponent v := by
      rw [Finsupp.onFinset_apply]
      by_cases hvS : v ∈ S.Sf
      · simp [exponentFun, hvS]
      · have hlog : WithZero.log (v.valuation F (m : F)) ≤ 0 := by
          apply (WithZero.log_le_iff_le_exp ((v.valuation F).ne_zero_iff.mpr hmF)).2
          simpa using m.property v hvS
        change 0 ≤ exponentFun v
        simp only [exponentFun, ite_eq_left hvS]
        dsimp [counts, principal]
        rw [qs_nq0_count_spanSingleton_eq_neg_log_valuation v (m : F) hmF]
        linarith
    let Jfrac : FractionalIdeal (nonZeroDivisors (𝓞 F)) F :=
      exponent.prod (HeightOneSpectrum.asIdeal · ^ ·)
    have hJle : Jfrac ≤ 1 := by
      dsimp [Jfrac]
      rw [Finsupp.prod]
      apply Finset.prod_le_one
      intro v hv
      obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (hexponent_nonneg v)
      rw [hn, zpow_natCast]
      exact Left.pow_le_one_of_le FractionalIdeal.coeIdeal_le_one _
    have hJne : Jfrac ≠ 0 := by
      dsimp [Jfrac]
      rw [Finsupp.prod]
      apply Finset.prod_ne_zero_iff.mpr
      intro v hv
      exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)
    have hcountJ (v : FinPlace F) : FractionalIdeal.count F v Jfrac = exponent v := by
      simpa [Jfrac] using FractionalIdeal.count_finsuppProd F v exponent
    obtain ⟨I, hIco⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hJle
    have hIne : I ≠ ⊥ := by
      intro h
      apply hJne
      rw [← hIco, h, FractionalIdeal.coeIdeal_bot]
    have hIexterior : S.IsExterior I := by
      refine ⟨hIne, ?_⟩
      intro v hvS hle
      have hleFrac : Jfrac ≤
          (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
        rw [← hIco]
        exact (FractionalIdeal.coeIdeal_le_coeIdeal F).2 hle
      have hmono := FractionalIdeal.count_mono (K := F) (v := v) hJne hleFrac
      have hexpZero : exponent v = 0 := by simp [exponent, exponentFun, hvS]
      have hbad : (1 : ℤ) ≤ 0 := by
        calc
          1 = FractionalIdeal.count F v
              (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
            (FractionalIdeal.count_self F v).symm
          _ ≤ FractionalIdeal.count F v Jfrac := hmono
          _ = exponent v := hcountJ v
          _ = 0 := hexpZero
      norm_num at hbad
    refine ⟨⟨I, hIexterior⟩, hIexterior, hmF, ?_⟩
    intro v hvS
    change counts v = FractionalIdeal.count F v
      (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    rw [hIco, hcountJ]
    simp [exponent, exponentFun, hvS]
  have hrel (x y : Ideal (𝓞 F)) : IsRelPrime x y ↔ IsCoprime x y := by
    rw [← gcd_isUnit_iff_isRelPrime, Ideal.isUnit_iff, Ideal.isCoprime_iff_gcd,
      Ideal.one_eq_top]
  have hpowerOne : IsPowerful (1 : Ideal (𝓞 F)) := by
    intro v hv
    exact (v.irreducible.not_isUnit (isUnit_of_dvd_one hv)).elim
  have hsplit : ∀ I : Ideal (𝓞 F), I ≠ 0 →
      ∃ h d : Ideal (𝓞 F), I = h * d ∧
        IsPowerful h ∧ Squarefree d ∧ IsCoprime h d := by
    intro I
    induction I using UniqueFactorizationMonoid.induction_on_coprime with
    | h0 => intro h; exact (h rfl).elim
    | h1 hx =>
      intro hne
      refine ⟨1, _, by simp, hpowerOne, hx.squarefree, ?_⟩
      exact isCoprime_one_left
    | @hpr p n hp =>
      intro hne
      by_cases hn : n ≤ 1
      · have hsq : Squarefree (p ^ n) := by
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl
          · simpa only [pow_zero] using (squarefree_one : Squarefree (1 : Ideal (𝓞 F)))
          · simpa only [pow_one] using hp.squarefree
        refine ⟨1, p ^ n, by simp, hpowerOne, hsq, ?_⟩
        exact isCoprime_one_left
      · have hn2 : 2 ≤ n := by omega
        refine ⟨p ^ n, 1, by simp, ?_, squarefree_one, ?_⟩
        · intro v hv
          have hvp : v.asIdeal ∣ p := v.prime.dvd_of_dvd_pow hv
          have hpv : p ∣ v.asIdeal := v.irreducible.dvd_symm hp.irreducible hvp
          have heq : v.asIdeal = p :=
            le_antisymm (Ideal.le_of_dvd hpv) (Ideal.le_of_dvd hvp)
          rw [heq]
          exact pow_dvd_pow p hn2
        · exact isCoprime_one_right
    | @hcp x y hxy ihx ihy =>
      intro hne
      obtain ⟨hx, dx, hxfac, hxpower, dxsq, hxcp⟩ := ihx (left_ne_zero_of_mul hne)
      obtain ⟨hy, dy, hyfac, hypower, dysq, hycp⟩ := ihy (right_ne_zero_of_mul hne)
      have hxycp := (hrel x y).mp hxy
      rw [hxfac, hyfac] at hxycp
      have hhd : IsCoprime hx dy := hxycp.of_mul_left_left.of_mul_right_right
      have hdh : IsCoprime dx hy := hxycp.of_mul_left_right.of_mul_right_left
      have hdd : IsCoprime dx dy := hxycp.of_mul_left_right.of_mul_right_right
      refine ⟨hx * hy, dx * dy, ?_, ?_, ?_, ?_⟩
      · rw [hxfac, hyfac]
        ac_rfl
      · intro v hv
        rcases v.prime.dvd_or_dvd hv with hvx | hvy
        · exact dvd_mul_of_dvd_left (hxpower v hvx) hy
        · exact dvd_mul_of_dvd_right (hypower v hvy) hx
      · exact squarefree_mul_iff.mpr ⟨(hrel dx dy).mpr hdd, dxsq, dysq⟩
      · exact (hxcp.mul_right hhd).mul_left (hdh.symm.mul_right hycp)
  obtain ⟨I, hgen⟩ := hexterior
  obtain ⟨h, d, hfac, hpower, hsq, hcp⟩ :=
    hsplit I.1 (by simpa only [Ideal.zero_eq_bot] using I.2.1)
  have hhext : S.IsExterior h := by
    have hhdiv : h ∣ I.1 := ⟨d, hfac⟩
    refine ⟨?_, ?_⟩
    · intro hz
      apply I.2.1
      simp [hfac, hz]
    · intro v hv hle
      exact I.2.2 v hv (le_trans (Ideal.le_of_dvd hhdiv) hle)
  have hdext : S.IsExterior d := by
    have hddiv : d ∣ I.1 := ⟨h, by simpa [mul_comm] using hfac⟩
    refine ⟨?_, ?_⟩
    · intro hz
      apply I.2.1
      simp [hfac, hz]
    · intro v hv hle
      exact I.2.2 v hv (le_trans (Ideal.le_of_dvd hddiv) hle)
  exact ⟨⟨m, I, ⟨h, hhext⟩, ⟨d, hdext⟩, hgen, hfac, hpower, hsq, hcp⟩, rfl⟩

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
