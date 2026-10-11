import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.sectionSpace_family_spanning
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.analyticFamily_rtr
import ArtinPrimitiveRoots.Proofs.th_res_whit_b.CommonFourier
import ArtinPrimitiveRoots.Proofs.th_res_whit_b.IntertwineLinear

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}
variable {P : CoverPackage D S H A} {G : GlobalDatum P}
  {μ : ∀ v : FinPlace F, LocHaar v}

/-- A descended residue functional is Whittaker on the theta space. Translate generators,
commute the local root past g, apply residue equivariance, and extend by span induction.
Uses: sectionSpace_family_spanning, analyticFamily_rtr, intertwine_rtr,
ThetaResidueLaws.linearTranslate, ThetaResidueLaws.fourierCoeff, ThetaResidueLaws.equiv, CoverPackage.emb_n.
Feeds: theta_exterior_whittaker. -/
theorem theta_lambda_whittaker (Fam : AnalyticFamily P G μ) (v0 : FinPlace F)
    (hv0 : v0 ∉ S.Sf) (g : P.tc.G)
    (hg : ∀ h : (P.loc v0).L, g * P.emb v0 h = P.emb v0 h * g)
    (laws : ThetaResidueLaws P G μ)
    (Λ : ((P.loc v0).L → (G.T v0).V) →ₗ[ℂ] ℂ)
    (hΛ : ∀ (Fam' : AnalyticFamily P G μ) (C' : ContinuedEis Fam'),
      ExteriorFamily Fam v0 Fam' →
        thetaWhit C' g = Λ (intertwine (P.loc v0) (μ v0) ((Fam'.sec (1 / 6)).f v0))) :
    IsWhittakerOn (P.loc v0) A (thetaSpace (P.loc v0) (G.T v0) (μ v0)) Λ := by
  classical
  let L := P.loc v0
  let T := G.T v0
  let s0 : ℂ := 1 / 6
  let M : sectionSpace L T s0 →ₗ[ℂ] (L.L → T.V) :=
    intertwineSectionLinear L T (μ v0) s0 (by norm_num [s0])
  have hGen (F' : AnalyticFamily P G μ) (hExt : ExteriorFamily Fam v0 F')
      (C : ContinuedEis F') (t : v0.adicCompletion F) :
      Λ (rtr (L.n (Multiplicative.ofAdd t))
          (intertwine L (μ v0) ((F'.sec s0).f v0))) =
        A.ψ v0 t * Λ (intertwine L (μ v0) ((F'.sec s0).f v0)) := by
    let h := L.n (Multiplicative.ofAdd t)
    have hv0' : v0 ∈ F'.T0 := by
      rw [hExt.1]
      simp
    obtain ⟨F'', hT'', hOff'', hAt''⟩ := analyticFamily_rtr F' v0 hv0' h
    have hExt'' : ExteriorFamily Fam v0 F'' := by
      refine ⟨hT''.trans hExt.1, ?_⟩
      intro s v hv
      exact (hOff'' s v hv).trans (hExt.2 s v hv)
    let C'' : ContinuedEis F'' := Classical.choice (laws.continuation F'')
    have hMtrans : intertwine L (μ v0) ((F''.sec s0).f v0) =
        rtr h (intertwine L (μ v0) ((F'.sec s0).f v0)) := by
      rw [hAt'' s0, intertwine_rtr]
    have hΛbase := hΛ F' C hExt
    have hΛtrans := hΛ F'' C'' hExt''
    have hTranslate' := thetaWhit_translate_family F' F'' v0 h hOff'' hAt'' C C'' g laws
    have hE : P.emb v0 h = P.tc.n v0 (Multiplicative.ofAdd t) := P.emb_n v0 hv0 _
    have hCom : g * P.emb v0 h = P.emb v0 h * g := hg h
    have hEq := (laws.equiv F' C).2.2 v0 hv0 t g
    calc
      Λ (rtr h (intertwine L (μ v0) ((F'.sec s0).f v0))) =
          Λ (intertwine L (μ v0) ((F''.sec s0).f v0)) := by rw [← hMtrans]
      _ = thetaWhit C'' g := hΛtrans.symm
      _ = thetaWhit C (g * P.emb v0 h) := hTranslate'
      _ = thetaWhit C (P.emb v0 h * g) := by rw [hCom]
      _ = A.ψ v0 t * thetaWhit C g := by simpa [hE] using hEq
      _ = A.ψ v0 t * Λ (intertwine L (μ v0) ((F'.sec s0).f v0)) := by rw [hΛbase]
  have hSection : ∀ f : L.L → T.V, IsSection L T s0 f → ∀ t,
      Λ (rtr (L.n (Multiplicative.ofAdd t)) (intertwine L (μ v0) f)) =
        A.ψ v0 t * Λ (intertwine L (μ v0) f) := by
    intro f hf t
    obtain ⟨n, c, fams, hExts, hsum⟩ :=
      sectionSpace_family_spanning Fam v0 f hf
    let famSection : Fin n → sectionSpace L T s0 := fun j =>
      ⟨((fams j).sec s0).f v0, ((fams j).sec s0).f_sec v0⟩
    have hsub : (⟨f, hf⟩ : sectionSpace L T s0) =
        ∑ j, c j • famSection j := by
      apply Subtype.ext
      simpa [famSection, s0] using hsum
    have hMsum : M ⟨f, hf⟩ = ∑ j, c j • M (famSection j) := by
      rw [hsub]
      simp [M, intertwineSectionLinear, famSection]
    have hMfun : M ⟨f, hf⟩ = intertwine L (μ v0) f := rfl
    have hrtrSum : rtr (L.n (Multiplicative.ofAdd t))
        (∑ j, c j • M (famSection j)) =
      ∑ j, c j • rtr (L.n (Multiplicative.ofAdd t)) (M (famSection j)) := by
      funext x
      simp [rtr, Finset.sum_apply]
    calc
      Λ (rtr (L.n (Multiplicative.ofAdd t)) (intertwine L (μ v0) f)) =
          Λ (∑ j, c j • rtr (L.n (Multiplicative.ofAdd t))
            (M (famSection j))) := by
              rw [← hMfun, hMsum, hrtrSum]
      _ = ∑ j, c j • Λ (rtr (L.n (Multiplicative.ofAdd t))
            (M (famSection j))) := by simp
      _ = ∑ j, c j • (A.ψ v0 t * Λ (M (famSection j))) := by
            apply Finset.sum_congr rfl
            intro j hj
            convert congrArg (fun z : ℂ => c j • z)
              (hGen (fams j) (hExts j)
                (Classical.choice (laws.continuation (fams j))) t) using 1 <;>
              simp [M, intertwineSectionLinear, famSection]
      _ = A.ψ v0 t * Λ (∑ j, c j • M (famSection j)) := by
            calc
              (∑ j, c j • (A.ψ v0 t * Λ (M (famSection j)))) =
                  ∑ j, A.ψ v0 t * (c j • Λ (M (famSection j))) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    simp only [smul_eq_mul]
                    ring
              _ = A.ψ v0 t * ∑ j, c j • Λ (M (famSection j)) := by
                    rw [← Finset.mul_sum]
              _ = A.ψ v0 t * Λ (∑ j, c j • M (famSection j)) := by
                    rw [map_sum]
                    simp
      _ = A.ψ v0 t * Λ (intertwine L (μ v0) f) := by
            rw [← hMsum]
            rfl
  change ∀ f ∈ Submodule.span ℂ
      (intertwine L (μ v0) '' {f | IsSection L T s0 f}), ∀ t,
        Λ (rtr (L.n (Multiplicative.ofAdd t)) f) = A.ψ v0 t * Λ f
  intro f hf
  refine Submodule.span_induction
    (p := fun f _ => ∀ t, Λ (rtr (L.n (Multiplicative.ofAdd t)) f) =
      A.ψ v0 t * Λ f) ?_ ?_ ?_ ?_ hf
  · rintro f ⟨f₀, hf₀, rfl⟩
    exact hSection f₀ hf₀
  · intro t
    have hz : rtr (L.n (Multiplicative.ofAdd t)) (0 : L.L → T.V) = 0 := by
      ext x
      rfl
    rw [hz]
    simp
  · intro f f' hf hf' h₁ h₂ t
    have h₁t := h₁ t
    have h₂t := h₂ t
    have hr : rtr (L.n (Multiplicative.ofAdd t)) (f + f') =
        rtr (L.n (Multiplicative.ofAdd t)) f +
          rtr (L.n (Multiplicative.ofAdd t)) f' := by
      ext x
      rfl
    rw [hr]
    simp only [map_add]
    rw [h₁t, h₂t]
    ring
  · intro c f hf h₁ t
    have h₁t := h₁ t
    have hr : rtr (L.n (Multiplicative.ofAdd t)) (c • f) =
        c • rtr (L.n (Multiplicative.ofAdd t)) f := by
      ext x
      rfl
    rw [hr]
    simp only [map_smul]
    rw [h₁t]
    simp only [smul_eq_mul]
    ring

end ArtinPrimitiveRoots.A1.Theta
