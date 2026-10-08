import ArtinPrimitiveRoots.Hecke.Boundary
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EULER.upstairs_rhp_euler_identity
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EULER.dedekindZetaSharp_meromorphic
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EULER.dedekindZetaSharp_eq
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EULER.dedekindZetaSharp_analyticAt

set_option autoImplicit false
open scoped NumberField BigOperators
open scoped Topology
open NumberField IsDedekindDomain
noncomputable section
namespace ArtinPrimitiveRoots.Splitting
open ClassFieldTheory ArtinPrimitiveRoots.Hecke
open ArtinPrimitiveRoots.HeckeBoundary
open Filter

/-- The nontrivial entire Hecke factors give a holomorphic sharp-zeta quotient.
Guide: ../sol-thin-s7/PROOFS.md:475–523. Uses the shared Euler core,
`LSeriesRay_entire`, change of modulus, and the sharp-zeta dictionary.
The correction is `E * s7BaseDeletion`; at one both sharp functions equal zero.
Feeds `sp_quotient_factor`. -/
theorem quotient_factor_of_euler_identity (B T : Type*)
    [Field B] [NumberField B] [Field T] [NumberField T]
    [Algebra B T] [IsAbelianGalois B T] [IsTotallyComplex B] :
    ∃ Q : ℂ → ℂ,
      DifferentiableOn ℂ Q {s : ℂ | 1 - δ₀ < s.re} ∧
      (∀ s : ℂ, 1 - δ₀ < s.re →
        dedekindZetaSharp T s = dedekindZetaSharp B s * Q s) := by
  classical
  let H : Set ℂ := {s | 1 - δ₀ < s.re}
  have hδlt : δ₀ < 1 := by norm_num [δ₀]
  have hHpos : H ⊆ {s : ℂ | 0 < s.re} := by
    intro s hs
    dsimp [H] at hs ⊢
    linarith
  have hHopen : IsOpen H := isOpen_lt continuous_const Complex.continuous_re
  have hHpre : IsPreconnected H :=
    (convex_halfSpace_re_gt (1 - δ₀)).isPreconnected
  have htwo : (2 : ℂ) ∈ H := by
    dsimp [H]
    norm_num [δ₀]

  obtain ⟨m, Art, hArtSurj, hFrob, hE, hEne, hEuler⟩ :=
    upstairs_rhp_euler_identity B T
  let E : ℂ → ℂ := s7UpstairsCorrection B T m
  let X : Finset ((T ≃ₐ[B] T) →* ℂˣ) := Finset.univ
  have hEulerX : ∀ s : ℂ, 1 < s.re →
      NumberField.dedekindZeta T s = E s * ∏ χ ∈ X, LSeriesRay (χ.comp Art) s := by
    simpa only [X] using hEuler
  let ηm : RayClassGroup m →* ℂˣ := 1
  let m0 : RayClassModulus B := ⟨0, ∅⟩
  let η0 : RayClassGroup m0 →* ℂˣ := 1

  have hprimeCop (n : RayClassModulus B) (v : HeightOneSpectrum (𝓞 B))
      (hv : v ∉ n.finitePart.support) : IsCoprimeTo n v.asIdeal := by
    refine ⟨v.ne_bot, ?_⟩
    change ∀ w, w ∈ n.finitePart.support →
      FractionalIdeal.count B w
        ((idealUnit v.asIdeal v.ne_bot : NumberFieldFractionalIdealGroup B) :
          FractionalIdeal (nonZeroDivisors (𝓞 B)) B) = 0
    intro w hw
    have hwv : w ≠ v := by
      intro h
      exact hv (h ▸ hw)
    simpa [idealUnit] using
      (FractionalIdeal.count_maximal_coprime B w (Ne.symm hwv))
  have hcharOne (n : RayClassModulus B) (I : Ideal (𝓞 B))
      (hI : IsCoprimeTo n I) :
      charValue (1 : RayClassGroup n →* ℂˣ) I = 1 := by
    simp [ArtinPrimitiveRoots.Hecke.charValue, hI]
  have hAgree : ∀ v : HeightOneSpectrum (𝓞 B), v ∉ m.finitePart.support →
      charValue ηm v.asIdeal = charValue η0 v.asIdeal := by
    intro v hv
    have hm := hcharOne m v.asIdeal (hprimeCop m v hv)
    have h0 := hcharOne m0 v.asIdeal (hprimeCop m0 v (by simp [m0]))
    simpa [ηm, η0] using hm.trans h0.symm
  have hbaseProd (s : ℂ) :
      (∏ v ∈ m.finitePart.support,
        (1 - charValue η0 v.asIdeal *
          ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))) =
        s7BaseDeletion B m s := by
    unfold s7BaseDeletion
    apply Finset.prod_congr rfl
    intro v hv
    have h0 := hcharOne m0 v.asIdeal (hprimeCop m0 v (by simp [m0]))
    rw [show charValue η0 v.asIdeal = 1 by simpa [η0] using h0]
    ring
  have hbaseEuler : ∀ s : ℂ, 1 < s.re →
      LSeriesRay ηm s = NumberField.dedekindZeta B s * s7BaseDeletion B m s := by
    intro s hs
    calc
      LSeriesRay ηm s = LSeriesRay η0 s *
          ∏ v ∈ m.finitePart.support,
            (1 - charValue η0 v.asIdeal *
              ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) :=
        LSeriesRay_change_modulus (η := ηm) (η' := η0) hAgree hs
      _ = NumberField.dedekindZeta B s * s7BaseDeletion B m s := by
        rw [show η0 = (1 : RayClassGroup m0 →* ℂˣ) by rfl,
          LSeriesRay_trivial_eq_dedekindZeta (K := B) s, hbaseProd s]

  have htrivChar :
      (1 : (T ≃ₐ[B] T) →* ℂˣ).comp Art = (1 : RayClassGroup m →* ℂˣ) := by
    ext c
    simp
  let Y : Finset ((T ≃ₐ[B] T) →* ℂˣ) := X.erase 1
  have hcompNe : ∀ χ, χ ∈ Y → χ.comp Art ≠ 1 := by
    intro χ hχ hcomp
    have hχone : χ = 1 := by
      ext g
      obtain ⟨c, hc⟩ := hArtSurj g
      have hval := congrArg (fun ψ : RayClassGroup m →* ℂˣ => ψ c) hcomp
      simpa [MonoidHom.comp_apply, hc] using hval
    exact (Finset.mem_erase.mp hχ).1 hχone
  have hLall : ∀ χ : (T ≃ₐ[B] T) →* ℂˣ, ∃ L : ℂ → ℂ,
      (χ ∈ Y → Differentiable ℂ L ∧
        ∀ s : ℂ, 1 < s.re → L s = LSeriesRay (χ.comp Art) s) := by
    intro χ
    by_cases hχ : χ ∈ Y
    · obtain ⟨L, hLd, hLeq⟩ := LSeriesRay_entire (χ.comp Art) (hcompNe χ hχ)
      exact ⟨L, fun _ => ⟨hLd, hLeq⟩⟩
    · exact ⟨fun _ => 0, fun h => (hχ h).elim⟩
  choose L hLdiff hLeq using hLall

  let Q : ℂ → ℂ := fun s =>
    (E s * s7BaseDeletion B m s) * ∏ χ ∈ Y, L χ s
  have hEanalytic : ∀ s ∈ H, AnalyticAt ℂ E s := by
    intro s hs
    apply hE.analyticAt
    exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (hHpos hs)
  have hEdiff : DifferentiableOn ℂ E H := by
    intro s hs
    exact (hEanalytic s hs).differentiableAt.differentiableWithinAt
  have hBdelDiff : Differentiable ℂ (s7BaseDeletion B m) := by
    unfold s7BaseDeletion
    refine Differentiable.fun_finsetProd ?_
    intro v hv
    have hNnat : Ideal.absNorm v.asIdeal ≠ 0 := by
      intro h
      exact v.ne_bot ((Ideal.absNorm_eq_zero_iff).mp h)
    have hN : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast hNnat
    have hpow : Differentiable ℂ
        (fun s : ℂ => ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) := by
      intro s
      exact (differentiableAt_id.neg).const_cpow (Or.inl hN)
    exact (differentiable_const (1 : ℂ)).sub hpow
  have hLprodDiff : DifferentiableOn ℂ (fun s => ∏ χ ∈ Y, L χ s) H := by
    apply DifferentiableOn.fun_finsetProd
    intro χ hχ
    exact (hLdiff χ hχ).differentiableOn
  have hQdiff : DifferentiableOn ℂ Q H := by
    change DifferentiableOn ℂ
      (fun s => (E s * s7BaseDeletion B m s) * ∏ χ ∈ Y, L χ s) H
    exact (hEdiff.mul hBdelDiff.differentiableOn).mul hLprodDiff
  have hQanalytic : AnalyticOnNhd ℂ Q H := hQdiff.analyticOnNhd hHopen

  have hsharpT : Meromorphic (dedekindZetaSharp T) := dedekindZetaSharp_meromorphic T
  have hsharpB : Meromorphic (dedekindZetaSharp B) := dedekindZetaSharp_meromorphic B
  have hsharpTOn : MeromorphicOn (dedekindZetaSharp T) H := fun s _ => hsharpT s
  have hsharpBOn : MeromorphicOn (dedekindZetaSharp B) H := fun s _ => hsharpB s
  have hDmer : MeromorphicOn
      (fun s => dedekindZetaSharp T s - dedekindZetaSharp B s * Q s) H := by
    exact hsharpTOn.sub (hsharpBOn.mul hQanalytic.meromorphicOn)

  have hEulerQuotient : ∀ s : ℂ, 1 < s.re →
      NumberField.dedekindZeta T s = NumberField.dedekindZeta B s * Q s := by
    intro s hs
    have hprodSplit :
        (∏ χ ∈ X, LSeriesRay (χ.comp Art) s) =
          LSeriesRay ((1 : (T ≃ₐ[B] T) →* ℂˣ).comp Art) s *
            ∏ χ ∈ Y, LSeriesRay (χ.comp Art) s := by
      have hmem : (1 : (T ≃ₐ[B] T) →* ℂˣ) ∈ X := by simp [X]
      calc
        (∏ χ ∈ X, LSeriesRay (χ.comp Art) s) =
            (∏ χ ∈ Y, LSeriesRay (χ.comp Art) s) *
              LSeriesRay ((1 : (T ≃ₐ[B] T) →* ℂˣ).comp Art) s := by
          have h := Finset.prod_erase_mul X (fun χ => LSeriesRay (χ.comp Art) s) hmem
          simpa [Y] using h.symm
        _ = LSeriesRay ((1 : (T ≃ₐ[B] T) →* ℂˣ).comp Art) s *
              ∏ χ ∈ Y, LSeriesRay (χ.comp Art) s := by ring
    have hLprod : (∏ χ ∈ Y, L χ s) =
        ∏ χ ∈ Y, LSeriesRay (χ.comp Art) s := by
      apply Finset.prod_congr rfl
      intro χ hχ
      exact hLeq χ hχ s hs
    calc
      NumberField.dedekindZeta T s = E s * ∏ χ ∈ X, LSeriesRay (χ.comp Art) s :=
        hEulerX s hs
      _ = E s * (LSeriesRay ((1 : (T ≃ₐ[B] T) →* ℂˣ).comp Art) s *
            ∏ χ ∈ Y, LSeriesRay (χ.comp Art) s) := by rw [hprodSplit]
      _ = NumberField.dedekindZeta B s * Q s := by
        rw [htrivChar, hbaseEuler s hs]
        dsimp [Q]
        rw [← hLprod]
        ring

  have hDtwo : meromorphicOrderAt
      (fun s => dedekindZetaSharp T s - dedekindZetaSharp B s * Q s) 2 = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    have hnear : (fun s : ℂ => dedekindZetaSharp T s -
        dedekindZetaSharp B s * Q s) =ᶠ[𝓝 2] 0 := by
      filter_upwards [
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
          (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with s hs
      have hT := dedekindZetaSharp_eq T hs
      have hB := dedekindZetaSharp_eq B hs
      change dedekindZetaSharp T s - dedekindZetaSharp B s * Q s = 0
      rw [hT, hB, hEulerQuotient s hs]
      exact sub_self _
    exact hnear.filter_mono nhdsWithin_le_nhds
  have hDorder : ∀ s ∈ H,
      meromorphicOrderAt
        (fun z => dedekindZetaSharp T z - dedekindZetaSharp B z * Q z) s = ⊤ := by
    intro s hs
    exact hDmer.meromorphicOrderAt_eq_top_of_isPreconnected hHpre htwo hs hDtwo

  refine ⟨Q, ?_, ?_⟩
  · simpa [H] using hQdiff
  · intro s hs
    by_cases hs1 : s = 1
    · subst s
      simp [dedekindZetaSharp]
    · have hsH : s ∈ H := hs
      have hDnear : (fun z => dedekindZetaSharp T z -
          dedekindZetaSharp B z * Q z) =ᶠ[𝓝[≠] s] 0 :=
        meromorphicOrderAt_eq_top_iff.mp (hDorder s hsH)
      have hloc : (fun z => dedekindZetaSharp T z) =ᶠ[𝓝[≠] s]
          (fun z => dedekindZetaSharp B z * Q z) := by
        filter_upwards [hDnear] with z hz
        exact sub_eq_zero.mp hz
      have hTanalytic := dedekindZetaSharp_analyticAt T (hHpos hsH) hs1
      have hBanalytic := dedekindZetaSharp_analyticAt B (hHpos hsH) hs1
      have hQanalyticAt : AnalyticAt ℂ Q s := hQdiff.analyticAt (hHopen.mem_nhds hsH)
      have hRanalytic : AnalyticAt ℂ (fun z => dedekindZetaSharp B z * Q z) s :=
        hBanalytic.mul hQanalyticAt
      have hTtend : Tendsto (fun z => dedekindZetaSharp T z) (𝓝[≠] s)
          (𝓝 (dedekindZetaSharp T s)) :=
        hTanalytic.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have hRtend : Tendsto (fun z => dedekindZetaSharp B z * Q z) (𝓝[≠] s)
          (𝓝 (dedekindZetaSharp B s * Q s)) :=
        hRanalytic.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      exact tendsto_nhds_unique (hTtend.congr' hloc) hRtend

end ArtinPrimitiveRoots.Splitting
end
