import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.ProbeLogRegularity
import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.ProbeRowWindow
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false
set_option maxHeartbeats 800000
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol

open ArtinPrimitiveRoots A1 A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {μ : ∀ v : FinPlace F, Theta.LocHaar v} {v0 : InfinitePlace F}

/-- The logarithmic probe family has one compact unit row support, a fixed interval
with vanishing endpoint data, and uniform bounds for its value and second derivative. -/
theorem probe_log_family (D : FieldData F) (S : SData F CE condη)
    (G : SheetGeometry D S μ v0) (f0 : S.FS → ℂ) (f1 : ℝ → ℂ)
    (hf0compact : HasCompactSupport f0)
    (hf0units : ∀ x ∈ tsupport f0, IsUnit x)
    (hf1compact : HasCompactSupport f1)
    (hf1positive : tsupport f1 ⊆ Set.Ioi 0)
    (hf1continuous : Continuous f1) (hf1nonzero : ∃ v, f1 v ≠ 0)
    (hregular :
      (∀ x : S.FS, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : ℝ => probeLogKernel D S G f0 f1 u x)) ∧
        ∀ n : ℕ, Continuous (fun p : ℝ × S.FS =>
          iteratedDeriv n (fun u : ℝ => probeLogKernel D S G f0 f1 u p.2) p.1)) :
    ∃ lo hi C0 C2 : ℝ, lo < hi ∧ 0 < C0 ∧ 0 < C2 ∧
      ∃ K : Set S.FSˣ, IsCompact K ∧
        (∀ v ∈ tsupport f1, Real.log v ∈ Set.Ioo lo hi) ∧
        (∀ x : S.FS, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun u => probeLogKernel D S G f0 f1 u x)) ∧
        Continuous (fun p : ℝ × S.FS => probeLogKernel D S G f0 f1 p.1 p.2) ∧
        Continuous (fun p : ℝ × S.FS =>
          iteratedDeriv 2 (fun u => probeLogKernel D S G f0 f1 u p.2) p.1) ∧
        (∀ x u, u ∈ Set.Icc lo hi →
          ‖probeLogKernel D S G f0 f1 u x‖ ≤ C0 ∧
          ‖iteratedDeriv 2 (fun v => probeLogKernel D S G f0 f1 v x) u‖ ≤ C2) ∧
        (∀ x, probeLogKernel D S G f0 f1 lo x = 0 ∧
          probeLogKernel D S G f0 f1 hi x = 0 ∧
          deriv (fun u => probeLogKernel D S G f0 f1 u x) lo = 0 ∧
          deriv (fun u => probeLogKernel D S G f0 f1 u x) hi = 0) ∧
        (∀ x, x ∉ (Units.val : S.FSˣ → S.FS) '' K →
          ∀ u, probeLogKernel D S G f0 f1 u x = 0) := by
  obtain ⟨L, B, C, hL, hB, hC, hinterval, _⟩ :=
    probe_denominator_control S f1 hf1compact hf1positive hf1continuous hf1nonzero
  obtain ⟨v, hv⟩ := hf1nonzero
  have hvSupport : v ∈ tsupport f1 := subset_closure (Function.mem_support.mpr hv)
  have hLB : L ≤ B := (hinterval v hvSupport).1.trans (hinterval v hvSupport).2
  have hlogs : Real.log L ≤ Real.log B := Real.log_le_log hL hLB
  let lo : ℝ := Real.log L - 1
  let hi : ℝ := Real.log B + 1
  have hlohi : lo < hi := by dsimp [lo, hi]; linarith
  have hlogSupport (v : ℝ) (hv : v ∈ tsupport f1) :
      Real.log v ∈ Set.Ioo lo hi := by
    have hvpos : 0 < v := hf1positive hv
    have hlow := Real.log_le_log hL (hinterval v hv).1
    have hhigh := Real.log_le_log hvpos (hinterval v hv).2
    constructor <;> dsimp [lo, hi] <;> linarith
  have hlogBounds (u : ℝ) (hu : f1 (Real.exp u) ≠ 0) :
      u ∈ Set.Icc (Real.log L) (Real.log B) := by
    have hs : Real.exp u ∈ tsupport f1 := subset_closure (Function.mem_support.mpr hu)
    have hl := Real.log_le_log hL (hinterval _ hs).1
    have hh := Real.log_le_log (Real.exp_pos u) (hinterval _ hs).2
    simpa only [Real.log_exp, Set.mem_Icc] using And.intro hl hh
  obtain ⟨K, hK, hwindow⟩ := probe_row_window D S G f0 f1 hf0compact hf0units
    hf1compact hf1positive hf1continuous ⟨v, hv⟩
  have hrowZero (x : S.FS) (hx : x ∉ (Units.val : S.FSˣ → S.FS) '' K)
      (u : ℝ) : probeLogKernel D S G f0 f1 u x = 0 := by
    by_contra hn
    have hf1 : f1 (Real.exp u) ≠ 0 := by
      intro h
      exact hn (by simp only [probeLogKernel, h, mul_zero, zero_mul])
    have hf0 : f0 (x * ((G.ellU (Real.exp u))⁻¹ : S.FSˣ).val) ≠ 0 := by
      intro h
      exact hn (by simp only [probeLogKernel, h, mul_zero])
    have htwo : (0 : ℝ) < 2 := by norm_num
    have htwob : 0 < (2 : ℝ) ^ b := Real.rpow_pos_of_pos htwo b
    have hN : 0 < (2 : ℝ) ^ M0 := Real.rpow_pos_of_pos htwo M0
    let q : ℝ := Real.exp u * (2 : ℝ) ^ b
    have hq : f1 (q / (2 : ℝ) ^ b) ≠ 0 := by
      simpa [q, htwob.ne'] using hf1
    have hscale : q * (2 : ℝ) ^ a = (2 : ℝ) ^ M0 * Real.exp u := by
      rw [M0, Real.rpow_add htwo]
      dsimp [q]
      ring
    have hscalePos : 0 < q * (2 : ℝ) ^ a := by
      rw [hscale]
      exact mul_pos hN (Real.exp_pos u)
    have hell : G.ellU (q * (2 : ℝ) ^ a) =
        G.ellU ((2 : ℝ) ^ M0) * G.ellU (Real.exp u) := by
      apply Units.ext
      rw [Units.val_mul, G.ellU_val _ hscalePos, G.ellU_val _ hN,
        G.ellU_val _ (Real.exp_pos u)]
      simp only [SData.ell, hscale, Real.mul_rpow hN.le (Real.exp_pos u).le]
      ext j <;> simp
    let row : S.FS := (G.ellU ((2 : ℝ) ^ M0) : S.FS) * x
    have hrow : row * ((1 * G.ellU (q * (2 : ℝ) ^ a))⁻¹ : S.FSˣ).val =
        x * ((G.ellU (Real.exp u))⁻¹ : S.FSˣ).val := by
      rw [one_mul, hell, mul_inv_rev, Units.val_mul]
      dsimp [row]
      calc
        _ = ((G.ellU ((2 : ℝ) ^ M0) : S.FS) *
            ((G.ellU ((2 : ℝ) ^ M0))⁻¹ : S.FSˣ).val) *
            (x * ((G.ellU (Real.exp u))⁻¹ : S.FSˣ).val) := by ac_rfl
        _ = _ := by simp [← Units.val_mul]
    have hf0row : f0 (row * ((1 * G.ellU (q * (2 : ℝ) ^ a))⁻¹ : S.FSˣ).val) ≠ 0 := by
      rw [hrow]
      exact hf0
    obtain ⟨y, hyK, hy⟩ := hwindow 2 (by norm_num) 1 q hq row hf0row
    have hxeq : x = (y : S.FS) := by
      have hy' : row = (G.ellU ((2 : ℝ) ^ M0) : S.FS) * (y : S.FS) := by
        simpa only [one_mul, G.ellU_val _ hN] using hy
      calc
        x = ((G.ellU ((2 : ℝ) ^ M0))⁻¹ : S.FSˣ).val * row := by
          dsimp [row]
          rw [← mul_assoc, ← Units.val_mul]
          simp
        _ = (y : S.FS) := by
          rw [hy', ← mul_assoc, ← Units.val_mul]
          simp
    exact hx ⟨y, hyK, hxeq.symm⟩
  have htimeZero (u : ℝ) (hu : u < Real.log L ∨ Real.log B < u) (x : S.FS) :
      probeLogKernel D S G f0 f1 u x = 0 := by
    by_cases hf : f1 (Real.exp u) = 0
    · simp [probeLogKernel, hf]
    · have hbounds := hlogBounds u hf
      rcases hu with hu | hu <;> linarith [hbounds.1, hbounds.2]
  have hendpoint (u : ℝ) (hu : u < Real.log L ∨ Real.log B < u) (x : S.FS) :
      probeLogKernel D S G f0 f1 u x = 0 ∧
        deriv (fun t => probeLogKernel D S G f0 f1 t x) u = 0 := by
    refine ⟨htimeZero u hu x, ?_⟩
    have heq : (fun t => probeLogKernel D S G f0 f1 t x) =ᶠ[𝓝 u] (fun _ => 0) := by
      rcases hu with hu | hu
      · filter_upwards [eventually_lt_nhds hu] with t ht
        exact htimeZero t (Or.inl ht) x
      · filter_upwards [eventually_gt_nhds hu] with t ht
        exact htimeZero t (Or.inr ht) x
    simpa using heq.deriv_eq
  have hcontinuous : Continuous (fun p : ℝ × S.FS => probeLogKernel D S G f0 f1 p.1 p.2) := by
    simpa only [iteratedDeriv_zero] using hregular.2 0
  have hcontinuous2 := hregular.2 2
  have hcompact : IsCompact (Set.Icc lo hi ×ˢ ((Units.val : S.FSˣ → S.FS) '' K)) :=
    isCompact_Icc.prod (hK.image Units.continuous_val)
  obtain ⟨B0, hB0⟩ := hcompact.exists_bound_of_continuousOn hcontinuous.continuousOn
  obtain ⟨B2, hB2⟩ := hcompact.exists_bound_of_continuousOn hcontinuous2.continuousOn
  let C0 : ℝ := max B0 0 + 1
  let C2 : ℝ := max B2 0 + 1
  have hC0 : 0 < C0 := by dsimp [C0]; positivity
  have hC2 : 0 < C2 := by dsimp [C2]; positivity
  have hB0C0 : B0 ≤ C0 := by dsimp [C0]; linarith [le_max_left B0 0]
  have hB2C2 : B2 ≤ C2 := by dsimp [C2]; linarith [le_max_left B2 0]
  refine ⟨lo, hi, C0, C2, hlohi, hC0, hC2, K, hK, hlogSupport, hregular.1,
    hcontinuous, hcontinuous2, ?_, ?_, hrowZero⟩
  · intro x u hu
    by_cases hx : x ∈ (Units.val : S.FSˣ → S.FS) '' K
    · exact ⟨(hB0 (u, x) ⟨hu, hx⟩).trans hB0C0, (hB2 (u, x) ⟨hu, hx⟩).trans hB2C2⟩
    · have heq : (fun t => probeLogKernel D S G f0 f1 t x) = (0 : ℝ → ℂ) :=
        funext fun t => hrowZero x hx t
      rw [hrowZero x hx u, heq]
      simpa using And.intro hC0.le hC2.le
  · intro x
    have hl : lo < Real.log L := by dsimp [lo]; linarith
    have hh : Real.log B < hi := by dsimp [hi]; linarith
    have hleft := hendpoint lo (Or.inl hl) x
    have hright := hendpoint hi (Or.inr hh) x
    exact ⟨hleft.1, hright.1, hleft.2, hright.2⟩

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
