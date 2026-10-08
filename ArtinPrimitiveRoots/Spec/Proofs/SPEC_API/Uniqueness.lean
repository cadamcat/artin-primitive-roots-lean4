import ArtinPrimitiveRoots.Spec.Domain
import ArtinPrimitiveRoots.Spec.Interface
import ArtinPrimitiveRoots.Spec.Geometry

set_option autoImplicit false

open NumberField Matrix MeasureTheory Filter Topology Metric
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

lemma contDomain_mono {s₁ ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) :
    contDomain s₁ ε₁ ⊆ contDomain s₁ ε₂ := by
  intro z hz
  simp only [contDomain, Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff] at hz ⊢
  rcases hz with (h1 | h2) | ⟨hball, hne⟩
  · left; left; exact h1
  · left; right; exact h2
  · right; exact ⟨Metric.ball_subset_ball h hball, hne⟩

lemma convBall_subset_contDomain {s₁ ε : ℝ} :
    Metric.ball (5 / 2 : ℂ) (1 / 2) ⊆ contDomain s₁ ε := by
  intro z hz
  simp only [contDomain, Set.mem_union]
  left; right; exact hz

lemma center_mem_convBall : (5 / 2 : ℂ) ∈ Metric.ball (5 / 2 : ℂ) (1 / 2) := by
  simp [Metric.mem_ball]

lemma coordsX_mem_posSet {F : Type} [Field F] [NumberField F] [IsTotallyComplex F] (z : X F) :
    coordsX F z ∈ posSet F := by
  obtain ⟨e, _, hsymm⟩ := (G1_h3_basics (F := F)).2.2.2.2.2.2.2.2.2.2.2
  rw [← hsymm z]
  exact (e.symm z).2

lemma ptX_coordsX {F : Type} [Field F] [NumberField F] [IsTotallyComplex F] (z : X F) :
    ptX F (coordsX F z) = z :=
  (G1_h3_basics (F := F)).2.2.2.2.2.2.2.1 z

lemma closure_ball_diff_singleton {x : ℂ} {r : ℝ} (hr : 0 < r) :
    Metric.ball x r ⊆ closure (Metric.ball x r \ {x}) := by
  intro y hy
  rcases eq_or_ne x y with rfl | hne
  · rw [Metric.mem_closure_iff]
    intro ε hε
    let δ : ℝ := min (ε / 2) (r / 2)
    have hδ : 0 < δ := lt_min (by linarith) (by linarith)
    have hδ_le_r : δ < r := (min_le_right _ _).trans_lt (by linarith)
    have hδ_le_ε : δ < ε := (min_le_left _ _).trans_lt (by linarith)
    have hnorm : ‖(δ : ℂ)‖ = δ := by
      rw [Complex.norm_real, Real.norm_of_nonneg hδ.le]
    refine ⟨x + (δ : ℂ), ?_, ?_⟩
    · simp only [Set.mem_sdiff, Metric.mem_ball, Set.mem_singleton_iff]
      refine ⟨?_, ?_⟩
      · rw [dist_eq_norm, add_sub_cancel_left, hnorm]
        exact hδ_le_r
      · intro heq
        have : (δ : ℂ) = 0 := by
          apply add_left_cancel (a := x)
          simpa using heq
        have : δ = 0 := by exact_mod_cast this
        linarith
    · rw [dist_eq_norm, sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg, hnorm]
      exact hδ_le_ε
  · apply subset_closure
    exact ⟨hy, Set.mem_singleton_iff.not.mpr (Ne.symm hne)⟩

/-- Uniqueness of continued Eisenstein series: two continuations agree on the common domain and have equal residues. -/
theorem continuedEisenstein_E_eq {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    {Γ : Subgroup SL(2, 𝓞 F)} {σ : SL(2,F)} {s₁ : ℝ}
    (d d' : ContinuedEisenstein F Γ σ s₁) (h₁ : s₁ ≤ 1 / 2) :
    (∀ s ∈ contDomain s₁ (min d.ε d'.ε), d.E s = d'.E s) ∧ d.res = d'.res := by
  have hs₀ : 0 < s₁ := d.ε_pos.trans_le d.ε_le
  have hs₁_lt : s₁ < 4 := by linarith [h₁]
  let εc : ℝ := min d.ε d'.ε
  have hεc_pos : 0 < εc := lt_min d.ε_pos d'.ε_pos
  have hC1 := C1_domain s₁ εc hs₀ hs₁_lt hεc_pos
  have h_open : IsOpen (contDomain s₁ εc) := hC1.1
  have h_conn : IsPreconnected (contDomain s₁ εc) := hC1.2
  have hmono_d : contDomain s₁ εc ⊆ contDomain s₁ d.ε := contDomain_mono (min_le_left d.ε d'.ε)
  have hmono_d' : contDomain s₁ εc ⊆ contDomain s₁ d'.ε := contDomain_mono (min_le_right d.ε d'.ε)
  have heq_on_z : ∀ (z : X F) (s : ℂ), s ∈ contDomain s₁ εc → d.E s z = d'.E s z := by
    intro z
    let p₀ : Coord F := coordsX F z
    have hp₀ : p₀ ∈ posSet F := coordsX_mem_posSet z
    let K : Set (Coord F) := {p₀}
    have hK : IsCompact K := isCompact_singleton
    have hKP : K ⊆ posSet F := Set.singleton_subset_iff.mpr hp₀
    let v₀ : Fin 0 → Coord F := Fin.elim0
    let pt₀ : K := ⟨p₀, Set.mem_singleton p₀⟩

    obtain ⟨Φ, hΦ, hΦ_val⟩ := d.E_analytic K hK hKP 0 v₀
    have hΦ_eval : AnalyticOnNhd ℂ (fun s => Φ s pt₀) (contDomain s₁ d.ε) := by
      have h := (BoundedContinuousFunction.evalCLM (𝕜 := ℂ) pt₀).comp_analyticOnNhd hΦ
      exact h
    have hΦ_eval_c : AnalyticOnNhd ℂ (fun s => Φ s pt₀) (contDomain s₁ εc) := hΦ_eval.mono hmono_d

    have hd_eq_Φ : ∀ s ∈ contDomain s₁ εc, d.E s z = Φ s pt₀ := by
      intro s hs
      have hs_d : s ∈ contDomain s₁ d.ε := hmono_d hs
      have hval := hΦ_val s hs_d pt₀
      rw [iteratedFDeriv_zero_apply v₀] at hval
      rw [hval]
      have h_pt : ptX F pt₀.1 = z := ptX_coordsX z
      rw [h_pt]

    have hd_an : AnalyticOnNhd ℂ (fun s => d.E s z) (contDomain s₁ εc) := by
      intro s hs
      have hnhd : contDomain s₁ εc ∈ 𝓝 s := h_open.mem_nhds hs
      have heq : (fun s => Φ s pt₀) =ᶠ[𝓝 s] (fun s => d.E s z) :=
        Filter.Eventually.mono hnhd (fun t ht => (hd_eq_Φ t ht).symm)
      exact (hΦ_eval_c s hs).congr heq

    obtain ⟨Φ', hΦ', hΦ'_val⟩ := d'.E_analytic K hK hKP 0 v₀
    have hΦ'_eval : AnalyticOnNhd ℂ (fun s => Φ' s pt₀) (contDomain s₁ d'.ε) := by
      have h := (BoundedContinuousFunction.evalCLM (𝕜 := ℂ) pt₀).comp_analyticOnNhd hΦ'
      exact h
    have hΦ'_eval_c : AnalyticOnNhd ℂ (fun s => Φ' s pt₀) (contDomain s₁ εc) := hΦ'_eval.mono hmono_d'

    have hd'_eq_Φ' : ∀ s ∈ contDomain s₁ εc, d'.E s z = Φ' s pt₀ := by
      intro s hs
      have hs_d' : s ∈ contDomain s₁ d'.ε := hmono_d' hs
      have hval := hΦ'_val s hs_d' pt₀
      rw [iteratedFDeriv_zero_apply v₀] at hval
      rw [hval]
      have h_pt : ptX F pt₀.1 = z := ptX_coordsX z
      rw [h_pt]

    have hd'_an : AnalyticOnNhd ℂ (fun s => d'.E s z) (contDomain s₁ εc) := by
      intro s hs
      have hnhd : contDomain s₁ εc ∈ 𝓝 s := h_open.mem_nhds hs
      have heq : (fun s => Φ' s pt₀) =ᶠ[𝓝 s] (fun s => d'.E s z) :=
        Filter.Eventually.mono hnhd (fun t ht => (hd'_eq_Φ' t ht).symm)
      exact (hΦ'_eval_c s hs).congr heq

    have hball_open : IsOpen (Metric.ball (5 / 2 : ℂ) (1 / 2)) := Metric.isOpen_ball
    have h52_mem : (5 / 2 : ℂ) ∈ Metric.ball (5 / 2 : ℂ) (1 / 2) := center_mem_convBall
    have h52_nhd : Metric.ball (5 / 2 : ℂ) (1 / 2) ∈ 𝓝 (5 / 2 : ℂ) := hball_open.mem_nhds h52_mem
    have heq_ball : ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2), d.E s z = d'.E s z := by
      intro s hs
      rw [d.E_series s hs z, d'.E_series s hs z]
    have heventually : (fun s => d.E s z) =ᶠ[𝓝 (5 / 2 : ℂ)] (fun s => d'.E s z) :=
      Filter.Eventually.mono h52_nhd heq_ball
    have h52_in_c : (5 / 2 : ℂ) ∈ contDomain s₁ εc := convBall_subset_contDomain h52_mem

    have heq_on : Set.EqOn (fun s => d.E s z) (fun s => d'.E s z) (contDomain s₁ εc) :=
      AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hd_an hd'_an h_conn h52_in_c heventually
    intro s hs
    exact heq_on hs

  have hE_eq : ∀ s ∈ contDomain s₁ εc, d.E s = d'.E s := by
    intro s hs
    ext z
    exact heq_on_z z s hs

  refine ⟨hE_eq, ?_⟩
  ext z
  let p₀ : Coord F := coordsX F z
  have hp₀ : p₀ ∈ posSet F := coordsX_mem_posSet z
  let K : Set (Coord F) := {p₀}
  have hK : IsCompact K := isCompact_singleton
  have hKP : K ⊆ posSet F := Set.singleton_subset_iff.mpr hp₀
  let v₀ : Fin 0 → Coord F := Fin.elim0
  let pt₀ : K := ⟨p₀, Set.mem_singleton p₀⟩

  obtain ⟨Ψ, hΨ, hΨ_center, hΨ_val⟩ := d.laurent K hK hKP 0 v₀
  obtain ⟨Ψ', hΨ', hΨ'_center, hΨ'_val⟩ := d'.laurent K hK hKP 0 v₀
  let f : ℂ → ℂ := fun s => Ψ s pt₀
  let g : ℂ → ℂ := fun s => Ψ' s pt₀
  have hf_an : AnalyticOnNhd ℂ f (Metric.ball (s₁ : ℂ) εc) := by
    have h := (BoundedContinuousFunction.evalCLM (𝕜 := ℂ) pt₀).comp_analyticOnNhd hΨ
    exact h.mono (Metric.ball_subset_ball (min_le_left d.ε d'.ε))
  have hg_an : AnalyticOnNhd ℂ g (Metric.ball (s₁ : ℂ) εc) := by
    have h := (BoundedContinuousFunction.evalCLM (𝕜 := ℂ) pt₀).comp_analyticOnNhd hΨ'
    exact h.mono (Metric.ball_subset_ball (min_le_right d.ε d'.ε))
  have hf_cont : ContinuousOn f (Metric.ball (s₁ : ℂ) εc) := hf_an.continuousOn
  have hg_cont : ContinuousOn g (Metric.ball (s₁ : ℂ) εc) := hg_an.continuousOn
  have hW_sub : (Metric.ball (s₁ : ℂ) εc \ {(s₁ : ℂ)}) ⊆ Metric.ball (s₁ : ℂ) εc :=
    Set.sdiff_subset
  have hclose : Metric.ball (s₁ : ℂ) εc ⊆ closure (Metric.ball (s₁ : ℂ) εc \ {(s₁ : ℂ)}) :=
    closure_ball_diff_singleton hεc_pos

  have heq_W : Set.EqOn f g (Metric.ball (s₁ : ℂ) εc \ {(s₁ : ℂ)}) := by
    intro s hs
    simp only [Set.mem_sdiff, Set.mem_singleton_iff] at hs
    rcases hs with ⟨hs_ball, hs_ne⟩
    have hs_c : s ∈ contDomain s₁ εc := by
      simp only [contDomain, Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff]
      right; exact ⟨hs_ball, hs_ne⟩
    have hval_d := hΨ_val s (Metric.ball_subset_ball (min_le_left d.ε d'.ε) hs_ball) hs_ne pt₀
    rw [iteratedFDeriv_zero_apply v₀] at hval_d
    have hval_d' := hΨ'_val s (Metric.ball_subset_ball (min_le_right d.ε d'.ε) hs_ball) hs_ne pt₀
    rw [iteratedFDeriv_zero_apply v₀] at hval_d'
    dsimp [f, g]
    rw [hval_d, hval_d']
    have h_pt : ptX F pt₀.1 = z := ptX_coordsX z
    rw [h_pt]
    have hE := heq_on_z z s hs_c
    rw [hE]

  have heq_ball : Set.EqOn f g (Metric.ball (s₁ : ℂ) εc) :=
    Set.EqOn.of_subset_closure heq_W hf_cont hg_cont hW_sub hclose
  have hs₁_in_ball : (s₁ : ℂ) ∈ Metric.ball (s₁ : ℂ) εc := by
    simp [Metric.mem_ball, hεc_pos]
  have heq_s₁ := heq_ball hs₁_in_ball
  dsimp [f, g] at heq_s₁
  have hc_d := hΨ_center pt₀
  rw [iteratedFDeriv_zero_apply v₀, ptX_coordsX z] at hc_d
  have hc_d' := hΨ'_center pt₀
  rw [iteratedFDeriv_zero_apply v₀, ptX_coordsX z] at hc_d'
  rw [hc_d] at heq_s₁
  rw [hc_d'] at heq_s₁
  exact heq_s₁

end ArtinPrimitiveRoots.A1.Spec
