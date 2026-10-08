import ArtinPrimitiveRoots.Theta.Proofs.TH_DECOMPOSE.ScalarSupport
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Evaluation at a fixed adelic point preserves parameter analyticity. -/
theorem scalarOf_parameter_analytic (P : CoverPackage D S H A) (G : GlobalDatum P)
    (sec : ∀ s : ℂ, GlobalSection P G s) (T0 : Finset (FinPlace F))
    (hT0 : ∀ s, (sec s).T0 = T0) (hC : ∀ s w, (sec s).fC w = sphC s)
    (han : ∀ v (g : (P.loc v).L),
      AnalyticOnNhd ℂ (fun s => (sec s).f v g) {s | 0 < s.re}) (g : P.tc.G) :
    AnalyticOnNhd ℂ (fun s => scalarOf P G (sec s).f (sec s).fC g) {s | 0 < s.re} := by
  obtain ⟨r, rfl⟩ := P.q_surj g
  let T := T0 ∪ (P.comp_restricted r).toFinset
  have hone (s : ℂ) (v : FinPlace F) (hv : v ∉ T) :
      G.lam v ((sec s).f v (P.compF v r)) = 1 := by
    have hvT0 : v ∉ T0 := fun h => hv (Finset.mem_union_left _ h)
    have hvsec : v ∉ (sec s).T0 := by simpa only [hT0 s] using hvT0
    have hvS : v ∉ S.Sf := fun h => hvsec ((sec s).sub h)
    have hK : P.compF v r ∈ (P.tame v hvS).Kmax := by
      by_contra h
      exact hv (Finset.mem_union_right _
        ((P.comp_restricted r).mem_toFinset.mpr ⟨hvS, h⟩))
    have hval : (sec s).f v (P.compF v r) = (G.B v hvS).e 0 := by
      calc
        _ = (sec s).f v 1 := by
          simpa only [one_mul] using (sec s).f_sph v hvsec |>.2 1 (P.compF v r) hK
        _ = _ := (sec s).f_sph v hvsec |>.1
    rw [hval, G.lam_tame]
    simp
  have hformula (s : ℂ) : scalarOf P G (sec s).f (sec s).fC (P.q r) =
      (∏ v ∈ T, G.lam v ((sec s).f v (P.compF v r))) *
        ∏ w, sphC s (P.compC w r) := by
    have hsupport : Function.mulSupport (fun v => G.lam v ((sec s).f v (P.compF v r))) ⊆
        (T : Set (FinPlace F)) := by
      intro v hv
      by_contra h
      exact hv (hone s v h)
    rw [(scalarOf_q P G (sec s) r).2,
      finprod_eq_prod_of_mulSupport_subset _ hsupport]
    congr 1
    exact Finset.prod_congr rfl (fun w _ => congrFun (hC s w) (P.compC w r))
  have hsph (u : PGL2 ℂ) (s : ℂ) : AnalyticAt ℂ (fun t => sphC t u) s := by
    let k := Quotient.out u
    have hdet : (k : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 :=
      Matrix.GeneralLinearGroup.det_ne_zero k
    have hrow : (k : Matrix (Fin 2) (Fin 2) ℂ) 1 0 ≠ 0 ∨
        (k : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0 := by
      by_contra! h
      apply hdet
      simp [Matrix.det_fin_two, h.1, h.2]
    have hden : 0 < ‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
        ‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 := by
      rcases hrow with h | h
      · exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.mpr h)) (sq_nonneg _)
      · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (norm_pos_iff.mpr h))
    let b : ℂ := ((‖(k : Matrix (Fin 2) (Fin 2) ℂ).det‖ /
      (‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
        ‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2) : ℝ) : ℂ)
    have hb : b ≠ 0 := Complex.ofReal_ne_zero.mpr
      (div_pos (norm_pos_iff.mpr hdet) hden).ne'
    change AnalyticAt ℂ (fun t => b ^ (1 + 2 * t)) s
    simp_rw [Complex.cpow_def_of_ne_zero hb]
    exact (analyticAt_const.mul
      (analyticAt_const.add (analyticAt_const.mul analyticAt_id))).cexp'
  have hfinite : AnalyticOnNhd ℂ
      (fun s => ∏ v ∈ T, G.lam v ((sec s).f v (P.compF v r))) {s | 0 < s.re} := by
    apply Finset.analyticOnNhd_fun_prod
    intro v _ s hs
    exact ((G.lam v).toContinuousLinearMap.analyticAt _).comp
      (han v (P.compF v r) s hs)
  have hinf : AnalyticOnNhd ℂ (fun s => ∏ w, sphC s (P.compC w r)) {s | 0 < s.re} := by
    exact Finset.analyticOnNhd_fun_prod Finset.univ (fun w _ s _ => hsph (P.compC w r) s)
  rw [show (fun s => scalarOf P G (sec s).f (sec s).fC (P.q r)) =
      (fun s => (∏ v ∈ T, G.lam v ((sec s).f v (P.compF v r))) *
        ∏ w, sphC s (P.compC w r)) from funext hformula]
  exact hfinite.mul hinf

end ArtinPrimitiveRoots.A1.Theta
