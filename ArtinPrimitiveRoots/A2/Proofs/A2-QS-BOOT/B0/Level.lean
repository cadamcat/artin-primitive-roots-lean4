import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-BOOT».B0.Residual

/-!
# B0: one descent level

For fixed `M, κ` and column length `X ≥ 1`:
`B₂(M, X, κ) ≤ L(X) (A_triv + #{N g ≤ G} C₄ (N(bad) G)^8 (MX)^{δ₄} S + C_d X^{η'} B₂(M, 2X/G, κ))`
with `L(X) = h_m (⌈log₂ X⌉₊ + 1)`: class/dyad slicing; parts of dyad `n' < G` by the trivial bound;
otherwise the gcd expansion, the residual form + C4 for `N g ≤ G` (then `n'/N g ≥ 1`), and the
descent for `N g > G`.
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2.QSB0

open QSC2 QSC3

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

/-- Count of nonzero... (all) ideals of norm `≤ ⌊X⌋`. -/
abbrev idealCount (K : Type) [Field K] [NumberField K] (X : ℝ) : ℝ :=
  ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊X⌋₊).toFinset.card : ℝ)

theorem sum_parts_le {parts : Finset (Finset (Ideal (𝓞 K)))} {U : Finset (Ideal (𝓞 K))}
    (hsub : ∀ P ∈ parts, P ⊆ U) (hdisj : ∀ P ∈ parts, ∀ Q ∈ parts, P ≠ Q → Disjoint P Q)
    (f : Ideal (𝓞 K) → ℝ) (hf : ∀ c, 0 ≤ f c) :
    ∑ P ∈ parts, ∑ c ∈ P, f c ≤ ∑ c ∈ U, f c := by
  classical
  rw [← Finset.sum_biUnion (fun P hP Q hQ hPQ => hdisj P hP Q hQ hPQ)]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun c _ _ => hf c
  intro c hc
  rw [Finset.mem_biUnion] at hc
  obtain ⟨P, hP, hcP⟩ := hc
  exact hsub P hP hcP

open Classical in
theorem level_bound (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥)
    (W : ℝ → ℝ) (hW : IsCapWeight W) (α : ℝ) {Wm : ℝ} (hWm : ∀ x : ℝ, 0 ≤ x → W x ≤ Wm)
    {C₄ δ₄ θ Cd η' : ℝ} (hC₄ : 0 < C₄) (hδ₄ : 0 ≤ δ₄) (hCd : 0 < Cd) (hη' : 0 ≤ η')
    (hC4 : ∀ (M n κ : ℝ) (𝔮 : Ideal (𝓞 K)) (cols : Finset (Ideal (𝓞 K))) (z : Ideal (𝓞 K) → ℂ),
        1 ≤ n → 1 ≤ κ → 2 * κ ≤ M → QSBlockCols m qS 𝔮 n cols →
        qsN 𝔮 * n ^ 2 * (M * n) ^ θ ≤ κ * M →
        ‖qsResidualBlock F W M κ 𝔮 cols z‖ ≤
          C₄ * qsN 𝔮 ^ 8 * (M * n) ^ δ₄ * qsBlockShape M n κ α * ∑ c ∈ cols, ‖z c‖ ^ 2)
    (hdesc : ∀ (M N G κ : ℝ) (cols : Finset (Ideal (𝓞 K))) (z : Ideal (𝓞 K) → ℂ),
      0 < M → 1 ≤ N → 1 ≤ G →
      (∀ c ∈ cols, QSAdm m qS c ∧ qsN c ≤ 2 * N) →
      ‖∑ g ∈ ((cols ×ˢ cols).image (fun p => p.1 ⊔ p.2)).filter (fun g => G < qsN g),
          qsGcdBlock F W M κ g cols z‖ ≤
        Cd * N ^ η' * qsHighNorm F W M (2 * N / G) κ * ∑ c ∈ cols, ‖z c‖ ^ 2)
    (M κ X G Sh : ℝ) (hM : 0 < M) (hX : 1 ≤ X) (hG : 1 ≤ G) (hκ : 1 ≤ κ) (hκM : 2 * κ ≤ M)
    (hmargin : ∀ (g : Ideal (𝓞 K)) (n : ℝ), 0 < qsN g → qsN g ≤ G → 1 ≤ n → n * qsN g ≤ X →
      qsN (qsBadRad m qS * g) * n ^ 2 * (M * n) ^ θ ≤ κ * M)
    (hshape : ∀ n : ℝ, 1 ≤ n → n ≤ X → qsBlockShape M n κ α ≤ Sh) (hSh : 0 ≤ Sh) :
    qsHighNorm F W M X κ ≤
      (Nat.card (ClassFieldTheory.RayClassGroup m) : ℝ) *
          ((Nat.ceil (Real.logb 2 X) + 1 : ℕ) : ℝ) *
        ((rowSet K (5 / 2 * M)).card * (Wm * idealCount K (2 * G)) +
          idealCount K G * (C₄ * (qsN (qsBadRad m qS) * G) ^ 8 * (M * X) ^ δ₄ * Sh) +
          Cd * X ^ η' * qsHighNorm F W M (2 * X / G) κ) := by
  have hWm0 : 0 ≤ Wm := le_trans (hW.2.1 0) (hWm 0 le_rfl)
  set H₁ := qsHighNorm F W M (2 * X / G) κ with hH₁
  have hH₁0 : 0 ≤ H₁ := by rw [hH₁, qsHighNorm]; positivity
  set A' := (rowSet K (5 / 2 * M)).card * (Wm * idealCount K (2 * G)) +
    idealCount K G * (C₄ * (qsN (qsBadRad m qS) * G) ^ 8 * (M * X) ^ δ₄ * Sh) +
    Cd * X ^ η' * H₁ with hA'
  have hA'0 : 0 ≤ A' := by
    have : 0 ≤ qsN (qsBadRad m qS) := Nat.cast_nonneg _
    positivity
  set Lg := (Nat.card (ClassFieldTheory.RayClassGroup m) : ℝ) *
    ((Nat.ceil (Real.logb 2 X) + 1 : ℕ) : ℝ) with hLg
  have hLg0 : 0 ≤ Lg := by positivity
  refine (qs_high_norm_energy_S0 F W hW M X κ hM).2 (Lg * A') (by positivity) fun z => ?_
  obtain ⟨parts, hcard, hsub, hdisj, hdyad, hclass, hE⟩ :=
    qs_class_dyad_slice_pos_S0 F W hW M X κ hM hX z
  -- per-part bound
  have hpart : ∀ P ∈ parts, qsHighEnergy F W M κ P z ≤ A' * ∑ c ∈ P, ‖z c‖ ^ 2 := by
    intro P hP
    have hPadm : ∀ c ∈ P, QSAdm m qS c := fun c hc => (mem_qsUpTo.mp (hsub P hP hc)).1
    have hPX : ∀ c ∈ P, qsN c ≤ X := fun c hc => (mem_qsUpTo.mp (hsub P hP hc)).2
    obtain ⟨j, hj⟩ := hdyad P hP
    set n' := X / 2 ^ (j + 1) with hn'
    have hn'pos : 0 < n' := by positivity
    have hPd : ∀ c ∈ P, QSAdm m qS c ∧ n' < qsN c ∧ qsN c ≤ 2 * n' := by
      intro c hc
      refine ⟨hPadm c hc, (hj c hc).1, ?_⟩
      have := (hj c hc).2
      rw [hn', pow_succ]
      calc qsN c ≤ X / 2 ^ j := this
        _ = 2 * (X / (2 ^ j * 2)) := by field_simp
    have hSz0 : 0 ≤ ∑ c ∈ P, ‖z c‖ ^ 2 := Finset.sum_nonneg fun c _ => sq_nonneg _
    by_cases hsmall : n' < G
    · -- trivial bound
      have htriv := energy_trivial F hW hWm hM (κ := κ) P hPadm z
      have hcardP : (P.card : ℝ) ≤ idealCount K (2 * G) := by
        have : P ⊆ (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊2 * G⌋₊).toFinset := by
          intro c hc
          rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
          exact Nat.le_floor (by have := (hPd c hc).2.2; simp only [qsN] at this; linarith)
        exact_mod_cast Finset.card_le_card this
      refine htriv.trans ?_
      have h1 : (rowSet K (5 / 2 * M)).card * (Wm * ((P.card : ℝ) * ∑ c ∈ P, ‖z c‖ ^ 2)) ≤
          (rowSet K (5 / 2 * M)).card * (Wm * idealCount K (2 * G)) * ∑ c ∈ P, ‖z c‖ ^ 2 := by
        rw [show (rowSet K (5 / 2 * M)).card * (Wm * ((P.card : ℝ) * ∑ c ∈ P, ‖z c‖ ^ 2)) =
          (rowSet K (5 / 2 * M)).card * (Wm * (P.card : ℝ)) * ∑ c ∈ P, ‖z c‖ ^ 2 by ring]
        gcongr
      refine h1.trans (mul_le_mul_of_nonneg_right ?_ hSz0)
      rw [hA']
      have : 0 ≤ idealCount K G * (C₄ * (qsN (qsBadRad m qS) * G) ^ 8 * (M * X) ^ δ₄ * Sh) := by
        have : 0 ≤ qsN (qsBadRad m qS) := Nat.cast_nonneg _
        positivity
      have : 0 ≤ Cd * X ^ η' * H₁ := by positivity
      linarith
    · push Not at hsmall
      set I := (P ×ˢ P).image (fun p => p.1 ⊔ p.2) with hI
      have hexp := qs_gcd_expansion_S0 F W hW M κ hM P hPadm z
      have hE0 : 0 ≤ qsHighEnergy F W M κ P z := by
        unfold qsHighEnergy
        refine tsum_nonneg fun a => ?_
        split_ifs
        · exact mul_nonneg (hW.2.1 _) (sq_nonneg _)
        · exact le_rfl
      have hnormE : qsHighEnergy F W M κ P z = ‖((qsHighEnergy F W M κ P z : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_of_nonneg hE0]
      rw [hnormE, hexp, ← Finset.sum_filter_add_sum_filter_not I (fun g => G < qsN g)]
      have hlarge := hdesc M X G κ P z hM hX hG fun c hc => ⟨hPadm c hc, by linarith [hPX c hc]⟩
      set Bnd := C₄ * (qsN (qsBadRad m qS) * G) ^ 8 * (M * X) ^ δ₄ * Sh with hBnd
      have hsmallg : ∀ g ∈ I.filter (fun g => ¬ G < qsN g),
          ‖qsGcdBlock F W M κ g P z‖ ≤ Bnd * ∑ c ∈ P, ‖z c‖ ^ 2 := by
        intro g hg
        rw [Finset.mem_filter] at hg
        obtain ⟨hgI, hgG⟩ := hg
        push Not at hgG
        rw [hI, Finset.mem_image] at hgI
        obtain ⟨⟨c, d⟩, hcd, rfl⟩ := hgI
        rw [Finset.mem_product] at hcd
        have hgdvd : c ⊔ d ∣ c := Ideal.dvd_iff_le.mpr le_sup_left
        have hgA : QSAdm m qS (c ⊔ d) := QSAdm_of_dvd (hPadm c hcd.1) hgdvd
        have hg0 := ne_bot_of_QSAdm hgA
        have hgpos := qsN_pos hg0
        obtain ⟨cols', z', hcols', _, hblock⟩ :=
          qs_residual_form_S0 F hrf hqS W hW M κ hM (c ⊔ d) P hPadm z
        rw [hblock]
        set n := n' / qsN (c ⊔ d) with hn
        have hn1 : 1 ≤ n := by rw [hn, le_div_iff₀ hgpos]; linarith
        have hnX : n ≤ X := by
          have h1 : n ≤ n' := div_le_self hn'pos.le (by
            have := one_le_qsN hg0; linarith)
          have h2 : n' ≤ X := by
            rw [hn']; exact div_le_self (by linarith) (one_le_pow₀ (by norm_num))
          linarith
        have hnN : n * qsN (c ⊔ d) ≤ X := by
          rw [hn, div_mul_cancel₀ _ hgpos.ne']
          rw [hn']; exact div_le_self (by linarith) (one_le_pow₀ (by norm_num))
        have hBC : QSBlockCols m qS (qsBadRad m qS * (c ⊔ d)) n cols' :=
          residual_blockCols hqS hPd (hclass P hP) ⟨c, hcd.1, d, hcd.2, rfl⟩
            fun c' hc' => ⟨(hcols' c' hc').1, (hcols' c' hc').2.1, (hcols' c' hc').2.2.1⟩
        have hC4' := hC4 M n κ (qsBadRad m qS * (c ⊔ d)) cols' z' hn1 hκ hκM hBC
          (hmargin (c ⊔ d) n hgpos hgG hn1 hnN)
        refine hC4'.trans ?_
        have hz' := residual_energy_le hg0 z z' fun c' hc' => ⟨(hcols' c' hc').2.2.1,
          (hcols' c' hc').2.2.2⟩
        have hN8 : qsN (qsBadRad m qS * (c ⊔ d)) ^ 8 ≤ (qsN (qsBadRad m qS) * G) ^ 8 := by
          rw [qsN_mul]
          exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hgG
            (Nat.cast_nonneg _)) 8
        have hMn : (M * n) ^ δ₄ ≤ (M * X) ^ δ₄ :=
          Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hnX hM.le) hδ₄
        have hsh := hshape n hn1 hnX
        have hsh0 : 0 ≤ qsBlockShape M n κ α := by
          unfold qsBlockShape
          have : 0 ≤ κ ^ (α - 1/2) := Real.rpow_nonneg (by linarith) _
          positivity
        rw [hBnd]
        have hz'0 : 0 ≤ ∑ c ∈ cols', ‖z' c‖ ^ 2 := Finset.sum_nonneg fun c _ => sq_nonneg _
        gcongr
      have hcount : ((I.filter (fun g => ¬ G < qsN g)).card : ℝ) ≤ idealCount K G := by
        have : I.filter (fun g => ¬ G < qsN g) ⊆
            (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊G⌋₊).toFinset := by
          intro g hg
          rw [Finset.mem_filter] at hg
          rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
          exact Nat.le_floor (not_lt.mp hg.2)
        exact_mod_cast Finset.card_le_card this
      have hBnd0 : 0 ≤ Bnd := by
        rw [hBnd]
        have : 0 ≤ qsN (qsBadRad m qS) := Nat.cast_nonneg _
        positivity
      calc ‖∑ g ∈ I.filter (fun g => G < qsN g), qsGcdBlock F W M κ g P z +
            ∑ g ∈ I.filter (fun g => ¬ G < qsN g), qsGcdBlock F W M κ g P z‖
          ≤ ‖∑ g ∈ I.filter (fun g => G < qsN g), qsGcdBlock F W M κ g P z‖ +
            ∑ g ∈ I.filter (fun g => ¬ G < qsN g), ‖qsGcdBlock F W M κ g P z‖ :=
            (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
        _ ≤ Cd * X ^ η' * H₁ * ∑ c ∈ P, ‖z c‖ ^ 2 +
            ∑ g ∈ I.filter (fun g => ¬ G < qsN g), Bnd * ∑ c ∈ P, ‖z c‖ ^ 2 :=
            add_le_add hlarge (Finset.sum_le_sum hsmallg)
        _ = Cd * X ^ η' * H₁ * ∑ c ∈ P, ‖z c‖ ^ 2 +
            ((I.filter (fun g => ¬ G < qsN g)).card : ℝ) * Bnd * ∑ c ∈ P, ‖z c‖ ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ Cd * X ^ η' * H₁ * ∑ c ∈ P, ‖z c‖ ^ 2 +
            idealCount K G * Bnd * ∑ c ∈ P, ‖z c‖ ^ 2 := by gcongr
        _ ≤ A' * ∑ c ∈ P, ‖z c‖ ^ 2 := by
            have hA'eq : A' = (rowSet K (5 / 2 * M)).card * (Wm * idealCount K (2 * G)) +
                idealCount K G * Bnd + Cd * X ^ η' * H₁ := by rw [hA', hBnd]
            have hAt : 0 ≤ ((rowSet K (5 / 2 * M)).card : ℝ) * (Wm * idealCount K (2 * G)) :=
              mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hWm0 (Nat.cast_nonneg _))
            rw [hA'eq]
            have hexp' : (((rowSet K (5 / 2 * M)).card : ℝ) * (Wm * idealCount K (2 * G)) +
                idealCount K G * Bnd + Cd * X ^ η' * H₁) * ∑ c ∈ P, ‖z c‖ ^ 2 =
                ((rowSet K (5 / 2 * M)).card : ℝ) * (Wm * idealCount K (2 * G)) *
                  ∑ c ∈ P, ‖z c‖ ^ 2 + idealCount K G * Bnd * ∑ c ∈ P, ‖z c‖ ^ 2 +
                  Cd * X ^ η' * H₁ * ∑ c ∈ P, ‖z c‖ ^ 2 := by ring
            rw [hexp']
            have := mul_nonneg hAt hSz0
            linarith
  -- assemble the parts
  have hdisj' := hdisj
  calc qsHighEnergy F W M κ (qsUpTo m qS X) z
      ≤ (parts.card : ℝ) * ∑ P ∈ parts, qsHighEnergy F W M κ P z := hE
    _ ≤ (parts.card : ℝ) * ∑ P ∈ parts, A' * ∑ c ∈ P, ‖z c‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpart) (Nat.cast_nonneg _)
    _ = (parts.card : ℝ) * A' * ∑ P ∈ parts, ∑ c ∈ P, ‖z c‖ ^ 2 := by
        rw [← Finset.mul_sum]; ring
    _ ≤ Lg * A' * ∑ c ∈ qsUpTo m qS X, ‖z c‖ ^ 2 := by
        have h1 := sum_parts_le hsub hdisj (fun c => ‖z c‖ ^ 2) (fun c => sq_nonneg _)
        have h2 : (parts.card : ℝ) ≤ Lg := hcard
        have h3 : 0 ≤ ∑ P ∈ parts, ∑ c ∈ P, ‖z c‖ ^ 2 :=
          Finset.sum_nonneg fun P _ => Finset.sum_nonneg fun c _ => sq_nonneg _
        calc (parts.card : ℝ) * A' * ∑ P ∈ parts, ∑ c ∈ P, ‖z c‖ ^ 2
            ≤ Lg * A' * ∑ P ∈ parts, ∑ c ∈ P, ‖z c‖ ^ 2 := by gcongr
          _ ≤ Lg * A' * ∑ c ∈ qsUpTo m qS X, ‖z c‖ ^ 2 :=
              mul_le_mul_of_nonneg_left h1 (mul_nonneg hLg0 hA'0)

end ArtinPrimitiveRoots.A2.QSB0
