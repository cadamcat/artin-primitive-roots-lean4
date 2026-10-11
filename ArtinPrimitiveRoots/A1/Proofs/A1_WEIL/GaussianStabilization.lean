import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.LocalAbsolute
import ArtinPrimitiveRoots.A1.Proofs.A1_LATTICE.Core

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

local instance measurableGaussianStabilization (v : FinPlace F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance borelGaussianStabilization (v : FinPlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

private def wbBall (v : FinPlace F) (n : ℤ) : Set (v.adicCompletion F) :=
  {x | Valued.v x ≤ WithZero.exp n}

private theorem wb_localBall_image (v : FinPlace F) (n : ℤ) :
    {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp n} =
      (fun x : v.adicCompletion F =>
        (((Classical.choose (v.valuation_exists_uniformizer F) : F) : v.adicCompletion F) ^ (-n)) * x) ''
          (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  classical
  let K := v.adicCompletion F
  let πF : F := Classical.choose (v.valuation_exists_uniformizer F)
  have hπF : v.valuation F πF = WithZero.exp (-1 : ℤ) :=
    Classical.choose_spec (v.valuation_exists_uniformizer F)
  have hπvalF : Valued.v (πF : K) = WithZero.exp (-1 : ℤ) := by
    rw [v.valuedAdicCompletion_eq_valuation']
    exact hπF
  have hπne : (πF : K) ≠ 0 := by
    intro h
    rw [h, map_zero] at hπvalF
    exact (WithZero.exp_ne_zero : WithZero.exp (-1 : ℤ) ≠ 0) hπvalF.symm
  let c : K := (πF : K) ^ (-n)
  have hcval : Valued.v c = WithZero.exp n := by
    dsimp [c]
    rw [map_zpow₀, hπvalF, ← WithZero.exp_zsmul]
    congr 1
    simp
  have hcne : c ≠ 0 := by
    intro h
    rw [h, map_zero] at hcval
    exact (WithZero.exp_ne_zero : WithZero.exp n ≠ 0) hcval.symm
  change {x : K | Valued.v x ≤ WithZero.exp n} =
    (fun x : K => c * x) ''
      (v.adicCompletionIntegers F : Set K)
  ext x
  constructor
  · intro hx
    refine ⟨c⁻¹ * x, ?_, ?_⟩
    · change Valued.v (c⁻¹ * x) ≤ 1
      rw [map_mul, map_inv₀, hcval]
      calc
        _ = WithZero.exp (-n) * Valued.v x := by simp
        _ ≤ WithZero.exp (-n) * WithZero.exp n :=
          mul_le_mul_of_nonneg_left hx WithZero.exp_pos.le
        _ = 1 := by rw [← WithZero.exp_add]; simp
    · change c * (c⁻¹ * x) = x
      calc
        _ = (c * c⁻¹) * x := by rw [mul_assoc]
        _ = 1 * x := by rw [mul_inv_cancel₀ hcne]
        _ = x := by simp
  · rintro ⟨x, hx, rfl⟩
    change Valued.v (c * x) ≤ WithZero.exp n
    rw [map_mul, hcval]
    calc
      _ ≤ WithZero.exp n * 1 := by
        have hx' : Valued.v x ≤ (1 : WithZero (Multiplicative ℤ)) := by
          change Valued.v x ≤ 1 at hx
          exact hx
        exact mul_le_mul_of_nonneg_left hx' WithZero.exp_pos.le
      _ = WithZero.exp n := by simp

private theorem wb_localBall_compact (v : FinPlace F) (n : ℕ) :
    IsCompact (localBall v n) := by
  change IsCompact {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp (n : ℤ)}
  rw [wb_localBall_image v (n : ℤ)]
  exact ArtinPrimitiveRoots.Proofs.A1_LATTICE.adicCompletionIntegers_compact v |>.image (by fun_prop)

private theorem wb_ball_compact (v : FinPlace F) (n : ℤ) : IsCompact (wbBall v n) := by
  change IsCompact {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp n}
  rw [wb_localBall_image v n]
  exact ArtinPrimitiveRoots.Proofs.A1_LATTICE.adicCompletionIntegers_compact v |>.image (by fun_prop)

private theorem wb_ball_open (v : FinPlace F) (n : ℤ) : IsOpen (wbBall v n) := by
  change IsOpen {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp n}
  rw [wb_localBall_image v n]
  let K := v.adicCompletion F
  let πF : F := Classical.choose (v.valuation_exists_uniformizer F)
  have hπne : (πF : K) ≠ 0 := by
    have hπval : Valued.v (πF : K) = WithZero.exp (-1 : ℤ) := by
      rw [v.valuedAdicCompletion_eq_valuation']
      exact Classical.choose_spec (v.valuation_exists_uniformizer F)
    intro h
    rw [h, map_zero] at hπval
    exact (WithZero.exp_ne_zero : WithZero.exp (-1 : ℤ) ≠ 0) hπval.symm
  let c : K := (πF : K) ^ (-n)
  have hcne : c ≠ 0 := zpow_ne_zero _ hπne
  change IsOpen ((fun x : K => c * x) '' (v.adicCompletionIntegers F : Set K))
  exact (Homeomorph.mulLeft₀ c hcne).isOpenMap _ (Valued.isOpen_valuationSubring K)

private theorem wb_ball_clopen (v : FinPlace F) (n : ℤ) : IsClopen (wbBall v n) :=
  ⟨(wb_ball_compact v n).isClosed, wb_ball_open v n⟩

private theorem wb_ball_add (v : FinPlace F) (n : ℤ) {x y : v.adicCompletion F}
    (hx : x ∈ wbBall v n) (hy : y ∈ wbBall v n) : x + y ∈ wbBall v n := by
  change Valued.v (x + y) ≤ WithZero.exp n
  exact (Valued.v.map_add x y).trans (max_le hx hy)

private theorem wb_ball_neg (v : FinPlace F) (n : ℤ) {x : v.adicCompletion F}
  (hx : x ∈ wbBall v n) : -x ∈ wbBall v n := by
  change Valued.v (-x) ≤ WithZero.exp n
  rw [Valuation.map_neg]
  exact hx

private theorem wb_ball_translate_iff (v : FinPlace F) (n : ℤ) (z : v.adicCompletion F)
    (hz : z ∈ wbBall v n) (x : v.adicCompletion F) : x + z ∈ wbBall v n ↔ x ∈ wbBall v n := by
  constructor
  · intro hx
    have h := wb_ball_add v n hx (wb_ball_neg v n hz)
    simpa [add_assoc] using h
  · intro hx
    exact wb_ball_add v n hx hz

private theorem wb_setIntegral_translate (v : FinPlace F) (μ : Measure (v.adicCompletion F))
    (hμ : Measure.IsAddHaarMeasure μ)
    (S : Set (v.adicCompletion F)) (f : v.adicCompletion F → ℂ)
    (z : v.adicCompletion F) (hS : ∀ x, x + z ∈ S ↔ x ∈ S)
    (hSmeas : MeasurableSet S) :
    ∫ x in S, f (x + z) ∂μ = ∫ x in S, f x ∂μ := by
  calc
    ∫ x in S, f (x + z) ∂μ = ∫ x, S.indicator (fun x => f (x + z)) x ∂μ :=
      (integral_indicator hSmeas).symm
    _ = ∫ x, S.indicator f (x + z) ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ S
      · have hx' : x + z ∈ S := (hS x).2 hx
        simp [Set.indicator_of_mem, hx, hx']
      · have hx' : x + z ∉ S := fun h => hx ((hS x).1 h)
        simp [Set.indicator_of_notMem, hx, hx']
    _ = ∫ x, S.indicator f x ∂μ := by
      letI : Measure.IsAddHaarMeasure μ := hμ
      simpa [add_comm] using (integral_add_left_eq_self (μ := μ) (S.indicator f) z)
    _ = ∫ x in S, f x ∂μ := integral_indicator hSmeas

private def wbShell (v : FinPlace F) (m : ℤ) : Set (v.adicCompletion F) :=
  wbBall v m \ wbBall v (m - 1)

private theorem wb_ball_mono (v : FinPlace F) {m n : ℤ} (hmn : m ≤ n) :
    wbBall v m ⊆ wbBall v n := by
  intro x hx
  change Valued.v x ≤ WithZero.exp n
  exact hx.trans ((WithZero.exp_le_exp).2 hmn)

private theorem wbShell_compact (v : FinPlace F) (m : ℤ) : IsCompact (wbShell v m) := by
  dsimp [wbShell]
  exact (wb_ball_compact v m).diff (wb_ball_open v (m - 1))

private theorem wbShell_clopen (v : FinPlace F) (m : ℤ) : IsClopen (wbShell v m) := by
  exact (wb_ball_clopen v m).diff (wb_ball_clopen v (m - 1))

private theorem wbShell_translate_iff (v : FinPlace F) (m e : ℤ)
    (hm : 1 ≤ m) (he : e ≤ 0) (z : v.adicCompletion F) (hz : z ∈ wbBall v e)
    (x : v.adicCompletion F) : x + z ∈ wbShell v m ↔ x ∈ wbShell v m := by
  have heinner : e ≤ m - 1 := by omega
  simp only [wbShell, Set.mem_sdiff]
  rw [wb_ball_translate_iff v m z (wb_ball_mono v (by omega) hz) x,
    wb_ball_translate_iff v (m - 1) z (wb_ball_mono v heinner hz) x]

private theorem wb_integral_swap_sets (v : FinPlace F) (μ : Measure (v.adicCompletion F))
    (hμ : Measure.IsAddHaarMeasure μ) (S B : Set (v.adicCompletion F))
    (hScompact : IsCompact S) (hBcompact : IsCompact B)
    (hSclopen : IsClopen S) (hBclopen : IsClopen B)
    (g : v.adicCompletion F → v.adicCompletion F → ℂ)
    (hg : Continuous (fun p : v.adicCompletion F × v.adicCompletion F => g p.1 p.2)) :
    ∫ x in S, ∫ z in B, g x z ∂μ ∂μ =
      ∫ z in B, ∫ x in S, g x z ∂μ ∂μ := by
  classical
  letI : Measure.IsAddHaarMeasure μ := hμ
  let f : v.adicCompletion F → v.adicCompletion F → ℂ := fun x z =>
    (S ×ˢ B).indicator (fun p => g p.1 p.2) (x, z)
  have hcont : Continuous f.uncurry := by
    change Continuous ((S ×ˢ B).indicator (fun p => g p.1 p.2))
    exact (hSclopen.prod hBclopen).continuous_indicator hg
  have hsupport : Function.support f.uncurry ⊆ S ×ˢ B := by
    intro p hp
    change f.uncurry p ≠ 0 at hp
    by_contra hp'
    have hfzero : f.uncurry p = 0 := by
      change (S ×ˢ B).indicator (fun p => g p.1 p.2) p = 0
      simp [hp']
    exact hp hfzero
  have hcompact : HasCompactSupport f.uncurry :=
    HasCompactSupport.of_support_subset_isCompact (hScompact.prod hBcompact) hsupport
  have hswap :=
    MeasureTheory.integral_integral_swap_of_hasCompactSupport (μ := μ) (ν := μ) hcont hcompact
  have hSmeas : MeasurableSet S := hSclopen.isClosed.measurableSet
  have hBmeas : MeasurableSet B := hBclopen.isClosed.measurableSet
  have hleft : (∫ x, ∫ z, f x z ∂μ ∂μ) = ∫ x in S, ∫ z in B, g x z ∂μ ∂μ := by
    calc
      (∫ x, ∫ z, f x z ∂μ ∂μ) =
          ∫ x, (if hx : x ∈ S then ∫ z in B, g x z ∂μ else 0) ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : x ∈ S
        · have hfiber : ∀ z, f x z = B.indicator (fun z => g x z) z := by
            intro z
            by_cases hz : z ∈ B <;> simp [f, hx, hz]
          simp_rw [hfiber, integral_indicator hBmeas, dif_pos hx]
        · have hfiber : ∀ z, f x z = 0 := by
            intro z
            by_cases hz : z ∈ B <;> simp [f, hx, hz]
          simp [hfiber, hx]
      _ = ∫ x in S, ∫ z in B, g x z ∂μ ∂μ := by
        change ∫ x, S.indicator (fun x => ∫ z in B, g x z ∂μ) x ∂μ = _
        exact integral_indicator hSmeas
  have hright : (∫ z, ∫ x, f x z ∂μ ∂μ) =
      ∫ z in B, ∫ x in S, g x z ∂μ ∂μ := by
    calc
      (∫ z, ∫ x, f x z ∂μ ∂μ) =
          ∫ z, (if hz : z ∈ B then ∫ x in S, g x z ∂μ else 0) ∂μ := by
        apply integral_congr_ae
        filter_upwards with z
        by_cases hz : z ∈ B
        · have hfiber : ∀ x, f x z = S.indicator (fun x => g x z) x := by
            intro x
            by_cases hx : x ∈ S <;> simp [f, hx, hz]
          simp_rw [hfiber, integral_indicator hSmeas, dif_pos hz]
        · have hfiber : ∀ x, f x z = 0 := by
            intro x
            by_cases hx : x ∈ S <;> simp [f, hx, hz]
          simp [hfiber, hz]
      _ = ∫ z in B, ∫ x in S, g x z ∂μ ∂μ := by
        change ∫ z, B.indicator (fun z => ∫ x in S, g x z ∂μ) z ∂μ = _
        exact integral_indicator hBmeas
  calc
    ∫ x in S, ∫ z in B, g x z ∂μ ∂μ = ∫ x, ∫ z, f x z ∂μ ∂μ := hleft.symm
    _ = ∫ z, ∫ x, f x z ∂μ ∂μ := hswap
    _ = ∫ z in B, ∫ x in S, g x z ∂μ ∂μ := hright

private theorem wb_exp_mul_square (m n : ℤ) :
    WithZero.exp m * WithZero.exp n ^ 2 = WithZero.exp (m + 2 * n) := by
  rw [← WithZero.exp_nsmul 2 n, ← WithZero.exp_add]
  congr 1

private theorem wbShell_val (v : FinPlace F) (m : ℤ) {x : v.adicCompletion F}
    (hx : x ∈ wbShell v m) : Valued.v x = WithZero.exp m := by
  change x ∈ wbBall v m \ wbBall v (m - 1) at hx
  have hxOuter := hx.1
  have hxNotInner := hx.2
  change Valued.v x ≤ WithZero.exp m at hxOuter
  change ¬ Valued.v x ≤ WithZero.exp (m - 1) at hxNotInner
  have hxne : x ≠ 0 := by
    intro hx0
    subst x
    apply hxNotInner
    simp [wbBall]
  have hvne : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hxne
  have hlogle : WithZero.log (Valued.v x) ≤ m := by
    have h := hxOuter
    rw [← WithZero.exp_log hvne] at h
    exact (WithZero.exp_le_exp).1 h
  have hlognot : ¬ WithZero.log (Valued.v x) ≤ m - 1 := by
    intro h
    apply hxNotInner
    rw [← WithZero.exp_log hvne]
    exact (WithZero.exp_le_exp).2 h
  have hlog : WithZero.log (Valued.v x) = m := by omega
  rw [← WithZero.exp_log hvne, hlog]

private theorem wb_quadratic_shell_integral_zero (A : AddCharData F)
    (v : FinPlace F) (μ : Measure (v.adicCompletion F)) (hμ : Measure.IsAddHaarMeasure μ)
    (hψ : LocalCharacterRegular A v) (a : (v.adicCompletion F)ˣ)
    (m e : ℤ) (hm : 1 ≤ m) (he : e ≤ 0)
    (hquad : ∀ z, z ∈ wbBall v e →
      Valued.v ((a : v.adicCompletion F) * z ^ 2) ≤ 1)
    (hcross : ∀ z z₀, z ∈ wbBall v e → z₀ ∈ wbBall v e →
      Valued.v (2 * (a : v.adicCompletion F) * z * z₀) ≤ 1)
    (y : v.adicCompletion F) (hy : A.ψ v y ≠ 1)
    (hlinear : ∀ x, x ∈ wbShell v m →
      ∃ z₀ ∈ wbBall v e, A.ψ v (2 * (a : v.adicCompletion F) * x * z₀) ≠ 1) :
    ∫ x in wbShell v m, A.ψ v ((a : v.adicCompletion F) * x ^ 2) ∂μ = 0 := by
  classical
  letI : Measure.IsAddHaarMeasure μ := hμ
  let K := v.adicCompletion F
  let S := wbShell v m
  let B := wbBall v e
  let q : K → ℂ := fun x => A.ψ v ((a : K) * x ^ 2)
  let g : K → K → ℂ := fun x z => A.ψ v ((a : K) * (x + z) ^ 2)
  have hScompact : IsCompact S := wbShell_compact v m
  have hBcompact : IsCompact B := wb_ball_compact v e
  have hSclopen : IsClopen S := wbShell_clopen v m
  have hBclopen : IsClopen B := wb_ball_clopen v e
  have hSmeas : MeasurableSet S := hSclopen.isClosed.measurableSet
  have hBmeas : MeasurableSet B := hBclopen.isClosed.measurableSet
  have hSstable (z : K) (hz : z ∈ B) (x : K) : x + z ∈ S ↔ x ∈ S := by
    exact wbShell_translate_iff v m e hm he z (by simpa [B] using hz) x
  have hqcont : Continuous q := by
    dsimp [q]
    exact hψ.1.comp (by fun_prop)
  have hgcont : Continuous (fun p : K × K => g p.1 p.2) := by
    dsimp [g]
    exact hψ.1.comp (by fun_prop)
  have hinnerZero (x : K) (hx : x ∈ S) : ∫ z in B, g x z ∂μ = 0 := by
    obtain ⟨z₀, hz₀, hc⟩ := hlinear x (by simpa [S] using hx)
    let c : ℂ := A.ψ v (2 * (a : K) * x * z₀)
    have hBtranslate (z : K) : z + z₀ ∈ B ↔ z ∈ B :=
      wb_ball_translate_iff v e z₀ (by simpa [B] using hz₀) z
    have hphase (z : K) (hz : z ∈ B) :
        g x (z + z₀) = c * g x z := by
      have hpoly :
          (a : K) * (x + (z + z₀)) ^ 2 =
            (a : K) * (x + z) ^ 2 +
              (2 * (a : K) * x * z₀) + (2 * (a : K) * z * z₀) + (a : K) * z₀ ^ 2 := by
        ring
      calc
        g x (z + z₀) =
            A.ψ v ((a : K) * (x + z) ^ 2 +
              (2 * (a : K) * x * z₀) +
              (2 * (a : K) * z * z₀) + (a : K) * z₀ ^ 2) := by
                simp [g, hpoly]
        _ = A.ψ v ((a : K) * (x + z) ^ 2) *
              A.ψ v (2 * (a : K) * x * z₀) *
              A.ψ v (2 * (a : K) * z * z₀) *
              A.ψ v ((a : K) * z₀ ^ 2) := by
                simp only [AddChar.map_add_eq_mul]
        _ = c * g x z := by
          rw [A.integral v _ (hcross z z₀ (by simpa [B] using hz) (by simpa [B] using hz₀)),
            A.integral v _ (hquad z₀ (by simpa [B] using hz₀))]
          simpa [c, g] using
            (mul_comm (A.ψ v ((a : K) * (x + z) ^ 2))
              (A.ψ v (2 * (a : K) * x * z₀)))
    have hshift := wb_setIntegral_translate v μ hμ B (fun z => g x z) z₀
      hBtranslate hBmeas
    have hscale : (∫ z in B, g x z ∂μ) =
        c * ∫ z in B, g x z ∂μ := by
      calc
        _ = ∫ z in B, g x (z + z₀) ∂μ := hshift.symm
        _ = ∫ z in B, c * g x z ∂μ := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem hBmeas] with z hz
          exact hphase z hz
        _ = c * ∫ z in B, g x z ∂μ := integral_const_mul _ _
    have hprod : (1 - c) * (∫ z in B, g x z ∂μ) = 0 := by
      calc
        _ = (∫ z in B, g x z ∂μ) - c * (∫ z in B, g x z ∂μ) := by ring
        _ = 0 := sub_eq_zero.mpr hscale
    have hc' : 1 - c ≠ 0 := by
      intro h
      apply hc
      exact (sub_eq_zero.mp h).symm
    exact (mul_eq_zero.mp hprod).resolve_left hc'
  have hleftZero : ∫ x in S, ∫ z in B, g x z ∂μ ∂μ = 0 := by
    calc
      ∫ x in S, ∫ z in B, g x z ∂μ ∂μ = ∫ x in S, (0 : ℂ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hSmeas] with x hx
        exact hinnerZero x hx
      _ = 0 := by simp
  have hrightConst : ∫ z in B, ∫ x in S, g x z ∂μ ∂μ =
      ∫ z in B, (∫ x in S, q x ∂μ) ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hBmeas] with z hz
    have ht := wb_setIntegral_translate v μ hμ S q z
      (fun x => hSstable z (by simpa [B] using hz) x) hSmeas
    simpa [g, q] using ht
  have hrightVal : ∫ z in B, ∫ x in S, g x z ∂μ ∂μ =
      (μ.real B) • (∫ x in S, q x ∂μ) := by
    rw [hrightConst]
    simp [integral_const]
  have hswap := wb_integral_swap_sets v μ hμ S B hScompact hBcompact hSclopen hBclopen g hgcont
  have hmass : 0 < μ.real B := by
    have hBnonempty : B.Nonempty := ⟨0, by simp [B, wbBall]⟩
    have hpos := hμ.open_pos B (wb_ball_open v e) hBnonempty
    have htop : μ B ≠ ⊤ := hBcompact.measure_lt_top.ne
    exact ENNReal.toReal_pos hpos htop
  have hzeroSmul : (μ.real B) • (∫ x in S, q x ∂μ) = 0 := by
    calc
      _ = ∫ z in B, ∫ x in S, g x z ∂μ ∂μ := hrightVal.symm
      _ = ∫ x in S, ∫ z in B, g x z ∂μ ∂μ := hswap.symm
      _ = 0 := hleftZero
  rcases smul_eq_zero.mp hzeroSmul with hm | hI
  · exact False.elim ((ne_of_gt hmass) hm)
  · simpa [S, q] using hI

/-- Stabilize the actual ball integral by cancelling all sufficiently remote shells.
Uses: A.integral; LocalCharacterRegular; valuation balls; Haar translation. -/
theorem quadratic_integral_stabilizes (A : AddCharData F) (v : FinPlace F) (μ : Measure (v.adicCompletion F))
    (hμ : Measure.IsAddHaarMeasure μ) (hψ : LocalCharacterRegular A v)
    (a : (v.adicCompletion F)ˣ) : ∃ N, StabilizesAt A v μ a N := by
  classical
  letI : Measure.IsAddHaarMeasure μ := hμ
  let K := v.adicCompletion F
  have hyExists : ∃ y : K, A.ψ v y ≠ 1 := by
    by_contra h
    push_neg at h
    apply hψ.2.1
    ext y
    exact h y
  obtain ⟨y, hy⟩ := hyExists
  have hyne : y ≠ 0 := by
    intro h0
    subst y
    simpa using hy
  have h2ne : (2 : K) ≠ 0 := by norm_num
  have hane : (a : K) ≠ 0 := Units.ne_zero a
  have hv2 : Valued.v (2 : K) ≠ 0 := (Valuation.ne_zero_iff _).2 h2ne
  have hva : Valued.v (a : K) ≠ 0 := (Valuation.ne_zero_iff _).2 hane
  have hvy : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hyne
  let t₂ : ℤ := WithZero.log (Valued.v (2 : K))
  let tₐ : ℤ := WithZero.log (Valued.v (a : K))
  let tᵧ : ℤ := WithZero.log (Valued.v y)
  have h2val : Valued.v (2 : K) = WithZero.exp t₂ := by
    dsimp [t₂]
    exact (WithZero.exp_log hv2).symm
  have haval : Valued.v (a : K) = WithZero.exp tₐ := by
    dsimp [tₐ]
    exact (WithZero.exp_log hva).symm
  have hyval : Valued.v y = WithZero.exp tᵧ := by
    dsimp [tᵧ]
    exact (WithZero.exp_log hvy).symm
  have h2le : Valued.v (2 : K) ≤ 1 := by
    calc
      Valued.v (2 : K) = Valued.v ((1 : K) + 1) := by norm_num
      _ ≤ max (Valued.v (1 : K)) (Valued.v (1 : K)) := Valued.v.map_add _ _
      _ = 1 := by simp
  have ht₂ : t₂ ≤ 0 := by
    rw [h2val] at h2le
    exact (WithZero.exp_le_exp).1 (by simpa using h2le)
  let r : ℤ := max 0 tₐ
  have hr0 : 0 ≤ r := le_max_left _ _
  have hrₐ : tₐ ≤ 2 * r := by
    dsimp [r]
    by_cases hₐ : 0 ≤ tₐ
    · rw [max_eq_right hₐ]
      omega
    · have hₐ' : tₐ ≤ 0 := le_of_not_ge hₐ
      rw [max_eq_left hₐ']
      omega
  have hquad : ∀ z, z ∈ wbBall v (-r) →
      Valued.v ((a : K) * z ^ 2) ≤ 1 := by
    intro z hz
    have hvalz : Valued.v z ≤ WithZero.exp (-r) := hz
    calc
      Valued.v ((a : K) * z ^ 2) = Valued.v (a : K) * Valued.v z ^ 2 := by
        simp only [map_mul, map_pow]
      _ ≤ WithZero.exp tₐ * WithZero.exp (-r) ^ 2 := by
        rw [haval]
        gcongr
      _ = WithZero.exp (tₐ - 2 * r) := by
        rw [wb_exp_mul_square]
        congr 1
        ring
      _ ≤ 1 := by
        rw [← WithZero.exp_zero]
        exact (WithZero.exp_le_exp).2 (by omega)
  have hcross : ∀ z z₀, z ∈ wbBall v (-r) → z₀ ∈ wbBall v (-r) →
      Valued.v (2 * (a : K) * z * z₀) ≤ 1 := by
    intro z z₀ hz hz₀
    have hzval : Valued.v z ≤ WithZero.exp (-r) := hz
    have hz₀val : Valued.v z₀ ≤ WithZero.exp (-r) := hz₀
    calc
      Valued.v (2 * (a : K) * z * z₀) =
          (Valued.v (2 : K) * Valued.v (a : K)) * (Valued.v z * Valued.v z₀) := by
            calc
              _ = Valued.v ((2 : K) * (a : K) * z) * Valued.v z₀ := by rw [map_mul]
              _ = (Valued.v ((2 : K) * (a : K)) * Valued.v z) * Valued.v z₀ := by rw [map_mul]
              _ = ((Valued.v (2 : K) * Valued.v (a : K)) * Valued.v z) * Valued.v z₀ := by
                rw [map_mul]
              _ = _ := by rw [mul_assoc]
      _ = (WithZero.exp t₂ * WithZero.exp tₐ) * (Valued.v z * Valued.v z₀) := by
        rw [h2val, haval]
      _ = WithZero.exp (t₂ + tₐ) * (Valued.v z * Valued.v z₀) := by
        rw [← WithZero.exp_add]
      _ ≤ WithZero.exp (t₂ + tₐ) * (WithZero.exp (-r) * WithZero.exp (-r)) := by
        gcongr
      _ = WithZero.exp (t₂ + tₐ - 2 * r) := by
        calc
          _ = WithZero.exp (t₂ + tₐ) * WithZero.exp (-r) ^ 2 := by rw [pow_two]
          _ = WithZero.exp (t₂ + tₐ - 2 * r) := by
            rw [wb_exp_mul_square]
            congr 1
            ring
      _ ≤ 1 := by
        rw [← WithZero.exp_zero]
        exact (WithZero.exp_le_exp).2 (by omega)
  let m₀ : ℤ := max 1 (tᵧ - t₂ - tₐ + r)
  have hm₀ : 1 ≤ m₀ := le_max_left _ _
  have hmᵧ : tᵧ - t₂ - tₐ + r ≤ m₀ := le_max_right _ _
  let cutoffZ : ℤ := m₀ - 1
  have hcutoffZ : 0 ≤ cutoffZ := by dsimp [cutoffZ]; omega
  let N : ℕ := Int.toNat cutoffZ
  have hNcast : (N : ℤ) = cutoffZ := by
    dsimp [N]
    exact Int.toNat_of_nonneg hcutoffZ
  have hlinear (m : ℤ) (hm : m₀ ≤ m) : ∀ x, x ∈ wbShell v m →
      ∃ z₀ ∈ wbBall v (-r), A.ψ v (2 * (a : K) * x * z₀) ≠ 1 := by
    intro x hx
    have hxval : Valued.v x = WithZero.exp m := wbShell_val v m hx
    have hxne : x ≠ 0 := by
      intro hx0
      subst x
      exact hx.2 (by simp [wbShell, wbBall])
    have hdenne : (2 : K) * (a : K) * x ≠ 0 :=
      mul_ne_zero (mul_ne_zero h2ne hane) hxne
    have hdenval : Valued.v ((2 : K) * (a : K) * x) =
        WithZero.exp (t₂ + tₐ + m) := by
      calc
        Valued.v ((2 : K) * (a : K) * x) =
            Valued.v (2 : K) * Valued.v (a : K) * Valued.v x := by simp [map_mul]
        _ = WithZero.exp t₂ * WithZero.exp tₐ * WithZero.exp m := by
          rw [h2val, haval, hxval]
        _ = WithZero.exp (t₂ + tₐ + m) := by
          rw [← WithZero.exp_add, ← WithZero.exp_add]
    let z₀ : K := y / ((2 : K) * (a : K) * x)
    have hz₀val : Valued.v z₀ = WithZero.exp (tᵧ - (t₂ + tₐ + m)) := by
      calc
        Valued.v z₀ = Valued.v y / Valued.v ((2 : K) * (a : K) * x) := by
          dsimp [z₀]
          rw [map_div₀]
        _ = WithZero.exp tᵧ / WithZero.exp (t₂ + tₐ + m) := by
          rw [hyval, hdenval]
        _ = WithZero.exp (tᵧ - (t₂ + tₐ + m)) := by
          rw [← WithZero.exp_sub]
    have hz₀mem : z₀ ∈ wbBall v (-r) := by
      change Valued.v z₀ ≤ WithZero.exp (-r)
      rw [hz₀val]
      apply (WithZero.exp_le_exp).2
      have hmᵧ' : tᵧ - t₂ - tₐ + r ≤ m := le_trans hmᵧ hm
      omega
    have hlin : (2 : K) * (a : K) * x * z₀ = y := by
      dsimp [z₀]
      exact mul_div_cancel₀ y hdenne
    refine ⟨z₀, hz₀mem, ?_⟩
    simpa [hlin] using hy
  have hIntBall (j : ℕ) :
      IntegrableOn (fun x : K => A.ψ v ((a : K) * x ^ 2)) (localBall v j) μ := by
    have hfcont : Continuous (fun x : K => A.ψ v ((a : K) * x ^ 2)) :=
      hψ.1.comp (by fun_prop)
    exact hfcont.continuousOn.integrableOn_compact (wb_localBall_compact v j)
  have hstep (n : ℕ) (hn : N ≤ n) :
      quadraticIntegral A v μ a (n + 1) = quadraticIntegral A v μ a n := by
    have hm₀n : m₀ ≤ (n : ℤ) + 1 := by
      have hn' : cutoffZ ≤ (n : ℤ) := by rw [← hNcast]; exact_mod_cast hn
      dsimp [cutoffZ] at hn'
      omega
    have hshell :
        ∫ x in localBall v (n + 1) \ localBall v n,
          A.ψ v ((a : K) * x ^ 2) ∂μ = 0 := by
      have h := wb_quadratic_shell_integral_zero A v μ hμ hψ a
        ((n : ℤ) + 1) (-r) (by omega) (by omega) hquad hcross y hy
        (hlinear ((n : ℤ) + 1) hm₀n)
      simpa [wbShell, wbBall, localBall] using h
    have hsubset : localBall v n ⊆ localBall v (n + 1) := by
      intro x hx
      change x ∈ wbBall v (n : ℤ) at hx
      change x ∈ wbBall v ((n + 1 : ℕ) : ℤ)
      exact wb_ball_mono v (by omega) hx
    have hdiff := setIntegral_sdiff
      ((wb_localBall_compact v n).isClosed.measurableSet) (hIntBall (n + 1)) hsubset
    have hzero :
        quadraticIntegral A v μ a (n + 1) - quadraticIntegral A v μ a n = 0 := by
      calc
        _ = ∫ x in localBall v (n + 1) \ localBall v n,
              A.ψ v ((a : K) * x ^ 2) ∂μ := hdiff.symm
        _ = 0 := hshell
    simpa [quadraticIntegral] using sub_eq_zero.mp hzero
  refine ⟨N, ?_⟩
  intro M hNM
  induction hNM with
  | refl => rfl
  | @step n hn ih =>
      calc
        quadraticIntegral A v μ a (n + 1) = quadraticIntegral A v μ a n := hstep n hn
        _ = quadraticIntegral A v μ a N := ih

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
