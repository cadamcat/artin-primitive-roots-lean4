import ArtinPrimitiveRoots.A1.Proofs.A1_FOURIER.LatticeSummable

/-!
# A1-FOURIER part `a1_fourier_tensor_majorant` (IMPL)

The explicit summable majorant for lattice translates of a tensor sum, uniform on compacts.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private theorem f_f_schwartz_decay
    (Φ : SchwartzMap (InfinitePlace F → ℂ) ℂ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ y : InfinitePlace F → ℂ,
      ‖Φ y‖ ≤ c * (1 + ‖y‖) ^ (-((Module.finrank ℚ F + 1 : ℕ) : ℝ)) := by
  let k : ℕ := Module.finrank ℚ F + 1
  let c : ℝ := (2 : ℝ) ^ k *
    (Finset.Iic (k, 0)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) Φ
  have hraw (y : InfinitePlace F → ℂ) :
      (1 + ‖y‖) ^ k * ‖Φ y‖ ≤ c := by
    simpa [c, k, norm_iteratedFDeriv_zero] using
      (SchwartzMap.one_add_le_sup_seminorm_apply (m := (k, 0)) (k := k) (n := 0)
        le_rfl le_rfl Φ y)
  have hc : 0 ≤ c := by
    have h0 := hraw 0
    have hnonneg : 0 ≤ (1 + ‖(0 : InfinitePlace F → ℂ)‖) ^ k * ‖Φ 0‖ := by positivity
    exact le_trans hnonneg h0
  refine ⟨c, hc, ?_⟩
  intro y
  have hbase : 0 < 1 + ‖y‖ := by positivity
  have hpow : 0 < (1 + ‖y‖) ^ k := pow_pos hbase _
  have hdiv : ‖Φ y‖ ≤ c / (1 + ‖y‖) ^ k :=
    (le_div_iff₀ hpow).2 (by simpa [mul_comm] using hraw y)
  calc
    ‖Φ y‖ ≤ c / (1 + ‖y‖) ^ k := hdiv
    _ = c * (1 + ‖y‖) ^ (-((k : ℕ) : ℝ)) := by
      rw [Real.rpow_neg (by positivity) (k : ℝ), Real.rpow_natCast]
      simp [div_eq_mul_inv]

/-- For a tensor sum `g` and a compact `C ⊆ F_S` there is a summable `b : R → ℝ` with
`‖g(x + m)‖ ≤ b m` for all `m ∈ R`, `x ∈ C`.

Proof hint: reduce to one tensor `(∏ φ_v) ⊗ Φ` (finite sums of majorants). The finite factor is
bounded (continuous, compact support) and vanishes unless `(diag m).1 ∈ Cf := tsupport-product
- (C).1`, compact. Schwartz decay (`SchwartzMap.one_add_le_sup_seminorm_apply` or
`le_seminorm`) gives `‖Φ y‖ ≤ c (1 + ‖y‖)^{-M}`, M = finrank ℚ F + 1; and for `x ∈ C`,
`1 + ‖m_∞‖ ≤ (1 + ‖x_∞‖)(1 + ‖x_∞ + m_∞‖)` (Peetre), so `b m = c' · indicator · (1+‖m_∞‖)^{-M}`,
summable by `a1_fourier_lattice_summable`.
Guide: `runs/lanes/sol-thin-a1/PROOFS.md` 188–190 (explicit majorant).
Uses: `a1_fourier_lattice_summable`. Used by: the glue of `SData.poisson` (`A1/SLattice.lean`). -/
theorem a1_fourier_tensor_majorant (S : SData F CE condη) (D : FieldData F)
    (g : S.FS → ℂ) (hg : S.IsFSTensorSum g) (C : Set S.FS) (hC : IsCompact C) :
    ∃ b : S.R → ℝ, Summable b ∧
      ∀ m : S.R, ∀ x ∈ C, ‖g (x + S.diag (m : F))‖ ≤ b m := by
  classical
  obtain ⟨n, φ, Φ, hφ, hrepr⟩ := hg
  let k : ℕ := Module.finrank ℚ F + 1
  let r : ℝ := k
  have hr : (Module.finrank ℚ F : ℝ) < r := by
    dsimp [r, k]
    exact_mod_cast Nat.lt_succ_self (Module.finrank ℚ F)
  obtain ⟨R0, hR0⟩ := (hC.image continuous_snd).isBounded.exists_norm_le
  let R : ℝ := max R0 0
  have hR (x : S.FS) (hx : x ∈ C) : ‖x.2‖ ≤ R := by
    apply (hR0 x.2 ?_).trans (le_max_left _ _)
    exact ⟨x, hx, rfl⟩
  have hRnonneg : 0 ≤ R := le_max_right _ _
  have hfiniteBound : ∀ i v, ∃ B : ℝ, 0 ≤ B ∧
      ∀ z : v.1.adicCompletion F, ‖φ i v z‖ ≤ B := by
    intro i v
    obtain ⟨B, hB⟩ := (hφ i v).2.1.exists_bound_of_continuous (hφ i v).1
    refine ⟨max B 0, le_max_right _ _, ?_⟩
    intro z
    exact (hB z).trans (le_max_left _ _)
  choose B hB0 hB using hfiniteBound
  have hKcomp : ∀ i : Fin n,
      IsCompact {y : (∀ v : S.Sf, v.1.adicCompletion F) |
        ∀ v, y v ∈ tsupport (φ i v)} := by
    intro i
    apply isCompact_pi_infinite
    intro v
    change IsCompact (tsupport (φ i v))
    exact (hφ i v).2.1
  let Cfin : Set (∀ v : S.Sf, v.1.adicCompletion F) := Prod.fst '' C
  have hCfin : IsCompact Cfin := hC.image continuous_fst
  let Kfin (i : Fin n) : Set (∀ v : S.Sf, v.1.adicCompletion F) :=
    {y | ∀ v, y v ∈ tsupport (φ i v)}
  let Cf (i : Fin n) : Set (∀ v : S.Sf, v.1.adicCompletion F) :=
    (fun p : (∀ v : S.Sf, v.1.adicCompletion F) ×
        (∀ v : S.Sf, v.1.adicCompletion F) => p.1 - p.2) ''
      (Kfin i ×ˢ Cfin)
  have hCf : ∀ i : Fin n, IsCompact (Cf i) := by
    intro i
    dsimp [Cf]
    exact ((hKcomp i).prod hCfin).image (continuous_fst.sub continuous_snd)
  have hdecay : ∀ i : Fin n, ∃ A : ℝ, 0 ≤ A ∧
      ∀ y : InfinitePlace F → ℂ,
        ‖Φ i y‖ ≤ A * (1 + ‖y‖) ^ (-((k : ℕ) : ℝ)) := by
    intro i
    exact f_f_schwartz_decay (F := F) (Φ i)
  choose A hA0 hA using hdecay
  let coeff (i : Fin n) : ℝ :=
    (∏ v : S.Sf, B i v) * A i * (1 + R) ^ k
  let weight (m : S.R) : ℝ :=
    (1 + ‖(S.diag (m : F)).2‖) ^ (-r)
  let indicatorSet (i : Fin n) : Set S.R :=
    {m | (S.diag (m : F)).1 ∈ Cf i}
  let major (i : Fin n) (m : S.R) : ℝ :=
    coeff i * Set.indicator (indicatorSet i) weight m
  let b (m : S.R) : ℝ := ∑ i : Fin n, major i m
  have hprodB0 (i : Fin n) : 0 ≤ ∏ v : S.Sf, B i v :=
    Finset.prod_nonneg fun v _ => hB0 i v
  have hcoeff0 (i : Fin n) : 0 ≤ coeff i := by
    dsimp [coeff]
    exact mul_nonneg (mul_nonneg (hprodB0 i) (hA0 i))
      (pow_nonneg (by linarith : 0 ≤ 1 + R) k)
  have hmajorSummable (i : Fin n) : Summable (major i) := by
    dsimp [major, indicatorSet, weight]
    exact (a1_fourier_lattice_summable S D (Cf i) (hCf i) r hr).mul_left (coeff i)
  have hb : Summable b := by
    dsimp [b]
    exact summable_sum fun i _ => hmajorSummable i
  refine ⟨b, hb, ?_⟩
  intro m x hx
  rw [hrepr]
  calc
    ‖∑ i : Fin n, (∏ v : S.Sf, φ i v ((x + S.diag (m : F)).1 v)) *
        Φ i (x + S.diag (m : F)).2‖
      ≤ ∑ i : Fin n, ‖(∏ v : S.Sf, φ i v ((x + S.diag (m : F)).1 v)) *
          Φ i (x + S.diag (m : F)).2‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin n, major i m := by
      apply Finset.sum_le_sum
      intro i _
      dsimp [major, indicatorSet, weight]
      by_cases hprod : (∏ v : S.Sf, φ i v ((x + S.diag (m : F)).1 v)) = 0
      · have hprod0 :
            (∏ v ∈ S.Sf.attach, φ i v (x.1 v + (S.diag (m : F)).1 v)) = 0 := by
          simpa using hprod
        have htermzero :
            ‖(∏ v ∈ S.Sf.attach, φ i v (x.1 v + (S.diag (m : F)).1 v)) *
              (Φ i) (x.2 + (S.diag (m : F)).2)‖ = 0 := by
          rw [hprod0]
          simp
        have hind0 : 0 ≤ Set.indicator
            {m' : S.R | (S.diag (m' : F)).1 ∈ Cf i}
            (fun m' => (1 + ‖(S.diag (m' : F)).2‖) ^ (-r)) m := by
          by_cases hm : m ∈ {m' : S.R | (S.diag (m' : F)).1 ∈ Cf i}
          · rw [Set.indicator_of_mem hm]
            positivity
          · rw [Set.indicator_of_notMem hm]
        rw [htermzero]
        exact mul_nonneg (hcoeff0 i) hind0
      · have hmCf : (S.diag (m : F)).1 ∈ Cf i := by
          dsimp [Cf]
          refine ⟨((x + S.diag (m : F)).1, x.1), ?_, ?_⟩
          · constructor
            · intro v
              apply subset_closure
              intro hzero
              apply hprod
              rw [Finset.prod_eq_zero (Finset.mem_univ v) hzero]
            · exact ⟨x, hx, rfl⟩
          · ext v
            simp [SData.diag]
        have hmI : m ∈ {m' : S.R | (S.diag (m' : F)).1 ∈ Cf i} := hmCf
        rw [Set.indicator_of_mem hmI]
        have hfinite : ‖∏ v : S.Sf, φ i v ((x + S.diag (m : F)).1 v)‖ ≤
            ∏ v : S.Sf, B i v := by
          rw [norm_prod]
          exact Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) (fun v _ => hB i v _)
        have harch : ‖Φ i (x + S.diag (m : F)).2‖ ≤
            A i * (1 + R) ^ k * weight m := by
          have hpeetre :
              1 + ‖(S.diag (m : F)).2‖ ≤
                (1 + ‖x.2‖) * (1 + ‖(x + S.diag (m : F)).2‖) := by
            have hnorm : ‖(S.diag (m : F)).2‖ ≤
                ‖x.2‖ + ‖(x + S.diag (m : F)).2‖ := by
              have hv : (x + S.diag (m : F)).2 - x.2 = (S.diag (m : F)).2 := by
                change x.2 + (S.diag (m : F)).2 - x.2 = (S.diag (m : F)).2
                abel
              calc
                ‖(S.diag (m : F)).2‖ =
                    ‖(x + S.diag (m : F)).2 - x.2‖ := by rw [hv]
                _ ≤ _ := by
                  simpa [add_comm] using (norm_sub_le (x + S.diag (m : F)).2 x.2)
            nlinarith [mul_nonneg (norm_nonneg x.2)
              (norm_nonneg (x + S.diag (m : F)).2)]
          have hV : 1 + ‖x.2‖ ≤ 1 + R := by linarith [hR x hx]
          have hpow :
              (1 + ‖(S.diag (m : F)).2‖) ^ k ≤
                (1 + ‖x.2‖) ^ k * (1 + ‖(x + S.diag (m : F)).2‖) ^ k := by
            calc
              _ ≤ ((1 + ‖x.2‖) * (1 + ‖(x + S.diag (m : F)).2‖)) ^ k :=
                pow_le_pow_left₀ (by positivity) hpeetre k
              _ = _ := mul_pow _ _ _
          have hdiv :
              (1 : ℝ) / (1 + ‖(x + S.diag (m : F)).2‖) ^ k ≤
                (1 + ‖x.2‖) ^ k / (1 + ‖(S.diag (m : F)).2‖) ^ k := by
            apply (div_le_div_iff₀ (pow_pos (by positivity) k)
              (pow_pos (by positivity) k)).2
            calc
              (1 : ℝ) * (1 + ‖(S.diag (m : F)).2‖) ^ k = _ := by ring
              _ ≤ (1 + ‖x.2‖) ^ k * (1 + ‖(x + S.diag (m : F)).2‖) ^ k := hpow
          have hdec := hA i (x + S.diag (m : F)).2
          have hdiv' :
              ((1 + ‖(x + S.diag (m : F)).2‖) ^ k)⁻¹ ≤
                (1 + ‖x.2‖) ^ k / (1 + ‖(S.diag (m : F)).2‖) ^ k := by
            simpa [one_div] using hdiv
          calc
            ‖Φ i (x + S.diag (m : F)).2‖ ≤
                A i / (1 + ‖(x + S.diag (m : F)).2‖) ^ k := by
              calc
                _ ≤ A i * (1 + ‖(x + S.diag (m : F)).2‖) ^ (-((k : ℕ) : ℝ)) := hdec
                _ = _ := by
                  rw [Real.rpow_neg (by positivity) (k : ℝ), Real.rpow_natCast]
                  simp [div_eq_mul_inv]
            _ ≤ A i * ((1 + ‖x.2‖) ^ k /
                  (1 + ‖(S.diag (m : F)).2‖) ^ k) := by
              exact mul_le_mul_of_nonneg_left hdiv' (hA0 i)
            _ ≤ A i * ((1 + R) ^ k /
                  (1 + ‖(S.diag (m : F)).2‖) ^ k) := by
              exact mul_le_mul_of_nonneg_left
                (div_le_div_of_nonneg_right
                  (pow_le_pow_left₀ (by positivity) hV k)
                  (le_of_lt (pow_pos (by positivity) k))) (hA0 i)
            _ = A i * (1 + R) ^ k * weight m := by
              have hweight : weight m =
                  ((1 + ‖(S.diag (m : F)).2‖) ^ k)⁻¹ := by
                dsimp [weight, r]
                rw [Real.rpow_neg (by positivity) (k : ℝ), Real.rpow_natCast]
              rw [hweight, div_eq_mul_inv]
              ring
        calc
          ‖(∏ v : S.Sf, φ i v ((x + S.diag (m : F)).1 v)) *
              Φ i (x + S.diag (m : F)).2‖
            = ‖∏ v : S.Sf, φ i v ((x + S.diag (m : F)).1 v)‖ *
                ‖Φ i (x + S.diag (m : F)).2‖ := norm_mul _ _
          _ ≤ (∏ v : S.Sf, B i v) * (A i * (1 + R) ^ k * weight m) :=
            mul_le_mul hfinite harch (norm_nonneg _) (hprodB0 i)
          _ = coeff i * weight m := by simp [coeff]; ring
    _ = b m := rfl

end ArtinPrimitiveRoots.A1
