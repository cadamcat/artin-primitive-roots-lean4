import ArtinPrimitiveRoots.A2.Defs
import ArtinPrimitiveRoots.A2.QuadraticSieve
import ArtinPrimitiveRoots.A1.Coefficients
import ArtinPrimitiveRoots.A2.Reflection.Missing
import ArtinPrimitiveRoots.A2.Proofs.A2_RF_MOMENT.Angular
import ArtinPrimitiveRoots.A2.Proofs.A2_RF_MOMENT.Generator

/-!
# Section 4: reflected second moment and quadratic large sieve
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open NumberField IsDedekindDomain
open scoped Classical
open ArtinPrimitiveRoots.Proofs.a2_rf_mom_p

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- **prop:reflection** (02a-coefficient-family.tex:101-121; 04-reflection.tex:1027-1228).
For the fixed arithmetic data and compact sets, the reflected coefficient family has the stated
dyadic second moment.  The same constant works for every norm-one translate in the fixed compact
set `T`; the total bound is included as the paper's immediate consequence. -/
theorem prop_reflection
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (A : ArtinPrimitiveRoots.A1.AddCharData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H)
    (η Λ G : ArtinPrimitiveRoots.A1.HeckeChar F)
    (hηfin : IsOfFinOrder η)
    (hηoutsideS : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F,
      v ∉ S.Sf → η.UnramifiedAt v)
    (hΛunit : ∀ x, ‖((Λ x : ℂˣ) : ℂ)‖ = 1)
    (hGfin : IsOfFinOrder G)
    (hGauss : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, v ∉ S.Sf →
      Λ.UnramifiedAt v ∧ G.UnramifiedAt v ∧
      ∀ p : Fˣ, S.IsGen (p : F) v.asIdeal → Bd.Allowed p →
        ArtinPrimitiveRoots.A1.gamma D S A 1 v.asIdeal p *
          ArtinPrimitiveRoots.A1.gamma D S A 2 v.asIdeal p =
            -(Λ.primeValue v * G.primeValue v))
    (cgen : S.SqfExtIdeal → F)
    (hcgen : ∀ I, ∃ c : Fˣ, (c : F) = cgen I ∧ S.IsGen (c : F) I.1 ∧ Bd.Allowed c)
    (K T : Set S.FSˣ) (hK : IsCompact K) (hT : IsCompact T)
    (hTnorm : ∀ t ∈ T, S.absS (t : S.FS) = 1) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (Z P Dlen : ℝ), (hZ : 2 ≤ Z) → 1 ≤ P → 1 ≤ Dlen →
        ∀ t ∈ T,
          (∑' r : {r : ReflectionRow S // InReflectionBox D S K t Z (by linarith) r ∧
              P ≤ idealNorm r.h.1 ∧ idealNorm r.h.1 < 2 * P ∧
              Dlen ≤ idealNorm r.d.1 ∧ idealNorm r.d.1 < 2 * Dlen},
            ‖ArtinPrimitiveRoots.A1.Bm D S A
              (ArtinPrimitiveRoots.A1.vartheta Λ G η) cgen (r.1.m : F) Z‖ ^ 2) ≤
              C * Real.rpow Z ε * Real.rpow P (1 / 2 : ℝ) *
                (Dlen + Dlen ^ 2 * P / Z) ∧
          (∑' r : {r : ReflectionRow S // InReflectionBox D S K t Z (by linarith) r},
            ‖ArtinPrimitiveRoots.A1.Bm D S A
              (ArtinPrimitiveRoots.A1.vartheta Λ G η) cgen (r.1.m : F) Z‖ ^ 2) ≤
              C * Real.rpow Z (2 * M0 - 1 + ε) := by
  classical
  intro ε hε
  letI : IsTotallyComplex F := D.isTotallyComplex
  obtain ⟨Kbal, hKbal, hKnorm, hbalanced⟩ := Bd.exists_balanced D
  have hchoose : ∀ I : ArtinPrimitiveRoots.A1.SData.ExtIdeal S,
      ∃ a : Fˣ,
        S.IsGen (a : F) I.1 ∧ Bd.Allowed a ∧
          S.diag (a : F) * S.ell D (idealNorm I.1)⁻¹ (by
            have hnorm : 0 < Ideal.absNorm I.1 :=
              Ideal.absNorm_pos_of_nonZeroDivisors
                ⟨I.1, mem_nonZeroDivisors_iff_ne_zero.mpr
                  (by simpa [Ideal.zero_eq_bot] using I.2.1)⟩
            have hnormR : 0 < (Ideal.absNorm I.1 : ℝ) := by exact_mod_cast hnorm
            exact inv_pos.mpr (by simpa [idealNorm] using hnormR)) ∈ Kbal := by
    intro I
    exact hbalanced I.1 I.2
  let gen : ArtinPrimitiveRoots.A1.SData.ExtIdeal S → Fˣ :=
    fun I => Classical.choose (hchoose I)
  have hgen (I : ArtinPrimitiveRoots.A1.SData.ExtIdeal S) :
      S.IsGen (gen I : F) I.1 := (Classical.choose_spec (hchoose I)).1
  have hallowed (I : ArtinPrimitiveRoots.A1.SData.ExtIdeal S) :
      Bd.Allowed (gen I) := (Classical.choose_spec (hchoose I)).2.1
  have hbal (I : ArtinPrimitiveRoots.A1.SData.ExtIdeal S) :
      S.diag (gen I : F) * S.ell D (idealNorm I.1)⁻¹ (by
        have hnorm : 0 < Ideal.absNorm I.1 :=
          Ideal.absNorm_pos_of_nonZeroDivisors
            ⟨I.1, mem_nonZeroDivisors_iff_ne_zero.mpr
              (by simpa [Ideal.zero_eq_bot] using I.2.1)⟩
        have hnormR : 0 < (Ideal.absNorm I.1 : ℝ) := by exact_mod_cast hnorm
        exact inv_pos.mpr (by simpa [idealNorm] using hnormR)) ∈ Kbal :=
    (Classical.choose_spec (hchoose I)).2.2
  let bc : BalancedChoices D S H Bd := {
    Kbal := Kbal
    Kbal_compact := hKbal
    Kbal_normOne := hKnorm
    gen := gen
    gen_spec := fun I => ⟨hgen I, hallowed I⟩
    gen_balanced := hbal
  }
  let μ : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F,
      ArtinPrimitiveRoots.A1.Theta.LocHaar v :=
    fun v => Classical.choice (ArtinPrimitiveRoots.A1.Theta.LocHaar.nonempty v)
  let v0 : InfinitePlace F := Classical.choice (inferInstance : Nonempty (InfinitePlace F))
  have hΛangular := reflection_lambda_angular_of_gauss D S H Bd A Λ G
    hΛunit hGfin hGauss
  let R : ReflectionSetup D S H Bd A (ArtinPrimitiveRoots.A1.vartheta Λ G η) bc μ v0 :=
    Classical.choice (reflectionSetup_exists D S H Bd A bc μ v0 η Λ G
      hηfin hηoutsideS hΛunit hΛangular hGfin hGauss)
  have hBm (m : F) (Z : ℝ) :
      ArtinPrimitiveRoots.A1.Bm D S A (ArtinPrimitiveRoots.A1.vartheta Λ G η)
        cgen m Z =
      ArtinPrimitiveRoots.A1.Bm D S A (ArtinPrimitiveRoots.A1.vartheta Λ G η)
        (ArtinPrimitiveRoots.A2.cgen R) m Z :=
    reflection_Bm_eq_balanced D S H Bd A (ArtinPrimitiveRoots.A1.vartheta Λ G η)
      bc μ v0 R cgen hcgen m Z
  have hrowInj : Function.Injective (fun r : ReflectionRow S => (r.m : F)) :=
    reflection_row_element_injective
  obtain ⟨Cdyad, hCdyad, hdyad⟩ :=
    rf_reflection_dyadic_assembly R K T hK hT hTnorm ε hε
  obtain ⟨Ctotal, hCtotal, htotal⟩ :=
    rf_reflection_assembly R K T hK hT hTnorm ε hε
  let C : ℝ := Cdyad + Ctotal
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro Z P Dlen hZ hP hD t ht
  have hZpos : 0 < Z := by linarith
  constructor
  · let Pred (r : ReflectionRow S) :=
      InReflectionBox D S K t Z (by linarith) r ∧
        P ≤ idealNorm r.h.1 ∧ idealNorm r.h.1 < 2 * P ∧
        Dlen ≤ idealNorm r.d.1 ∧ idealNorm r.d.1 < 2 * Dlen
    let f (r : ReflectionRow S) :=
      ‖ArtinPrimitiveRoots.A1.Bm D S A (ArtinPrimitiveRoots.A1.vartheta Λ G η)
        cgen (r.m : F) Z‖ ^ 2
    let B : ℝ := Cdyad * Real.rpow Z ε * Real.rpow P (1 / 2 : ℝ) *
      (Dlen + Dlen ^ 2 * P / Z)
    have hfin (rows : Finset (ReflectionRow S))
        (hrows : ∀ r ∈ rows, Pred r) :
        (∑ r ∈ rows, f r) ≤ B := by
      have hinj : Set.InjOn (fun r : ReflectionRow S => (r.m : F))
          (↑rows : Set (ReflectionRow S)) := by
        intro r hr r' hr' heq
        exact hrowInj heq
      have hb := hdyad Z hZ P Dlen hP hD t ht rows hinj hrows
      simpa [B, f, Pred, hBm] using hb
    have htsum := finite_to_tsum Pred f B (by intro r; positivity) hfin
    have hbase : 0 ≤ Real.rpow Z ε * Real.rpow P (1 / 2 : ℝ) :=
      mul_nonneg (Real.rpow_nonneg hZpos.le _) (Real.rpow_nonneg (by linarith [hP]) _)
    have hshape : 0 ≤ Dlen + Dlen ^ 2 * P / Z := by
      apply add_nonneg
      · linarith
      · exact div_nonneg
          (mul_nonneg (sq_nonneg Dlen) (by linarith [hP])) hZpos.le
    have hscale : 0 ≤ Real.rpow Z ε * Real.rpow P (1 / 2 : ℝ) *
        (Dlen + Dlen ^ 2 * P / Z) := mul_nonneg hbase hshape
    calc
      (∑' r : {r : ReflectionRow S // Pred r}, f r.1) ≤ B := htsum.2
      _ ≤ C * Real.rpow Z ε * Real.rpow P (1 / 2 : ℝ) *
          (Dlen + Dlen ^ 2 * P / Z) := by
        dsimp [B, C]
        calc
          Cdyad * Real.rpow Z ε * Real.rpow P (1 / 2 : ℝ) *
              (Dlen + Dlen ^ 2 * P / Z) = Cdyad *
                (Real.rpow Z ε * Real.rpow P (1 / 2 : ℝ) *
                  (Dlen + Dlen ^ 2 * P / Z)) := by ring
          _ ≤ (Cdyad + Ctotal) *
                (Real.rpow Z ε * Real.rpow P (1 / 2 : ℝ) *
                  (Dlen + Dlen ^ 2 * P / Z)) :=
              mul_le_mul_of_nonneg_right (by linarith [hCtotal.le]) hscale
          _ = (Cdyad + Ctotal) * Real.rpow Z ε * Real.rpow P (1 / 2 : ℝ) *
                (Dlen + Dlen ^ 2 * P / Z) := by ring
  · let Pred (r : ReflectionRow S) := InReflectionBox D S K t Z (by linarith) r
    let f (r : ReflectionRow S) :=
      ‖ArtinPrimitiveRoots.A1.Bm D S A (ArtinPrimitiveRoots.A1.vartheta Λ G η)
        cgen (r.m : F) Z‖ ^ 2
    let B : ℝ := Ctotal * Real.rpow Z (2 * M0 - 1 + ε)
    have hfin (rows : Finset (ReflectionRow S))
        (hrows : ∀ r ∈ rows, Pred r) :
        (∑ r ∈ rows, f r) ≤ B := by
      have hinj : Set.InjOn (fun r : ReflectionRow S => (r.m : F))
          (↑rows : Set (ReflectionRow S)) := by
        intro r hr r' hr' heq
        exact hrowInj heq
      have hb := htotal Z hZ t ht rows hinj hrows
      simpa [B, f, Pred, hBm] using hb
    have htsum := finite_to_tsum Pred f B (by intro r; positivity) hfin
    have hshape : 0 ≤ Real.rpow Z (2 * M0 - 1 + ε) :=
      Real.rpow_nonneg hZpos.le _
    calc
      (∑' r : {r : ReflectionRow S // Pred r}, f r.1) ≤ B := htsum.2
      _ ≤ C * Real.rpow Z (2 * M0 - 1 + ε) := by
        dsimp [B, C]
        exact mul_le_mul_of_nonneg_right (by linarith [hCdyad.le]) hshape

end ArtinPrimitiveRoots.A2
