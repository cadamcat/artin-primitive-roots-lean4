import ArtinPrimitiveRoots.Hecke.Dedekind

/-!
Local glue extracting the simple pole of `dedekindZeta` from the completed zeta.
The two gamma recurrences remove the apparent division by `s` at the origin.
-/

set_option autoImplicit false

open scoped NumberField
open scoped Topology
open NumberField IsDedekindDomain
open Complex
open Filter

noncomputable section

namespace ArtinPrimitiveRoots.Hecke

private theorem inv_pow_mul_pow_eq_one {g : ℂ} (hg : g ≠ 0) (n : ℕ) :
    g⁻¹ ^ n * g ^ n = 1 := by
  rw [← mul_pow, inv_mul_cancel₀ hg, one_pow]

private theorem inv_gamma_recurrence_cancel {g gShift s A : ℂ} (n : ℕ)
    (hg : g ≠ 0) (hs : s ≠ 0) (hA : A ≠ 0)
    (hrec : gShift = g * s / A) :
    gShift⁻¹ * A⁻¹ * g⁻¹ ^ n * (s * g ^ (n + 1)) = 1 := by
  have hp : g⁻¹ ^ n * g ^ n = 1 := inv_pow_mul_pow_eq_one hg n
  rw [hrec, pow_succ]
  calc
    (g * s / A)⁻¹ * A⁻¹ * g⁻¹ ^ n * (s * (g ^ n * g)) =
        (g * s / A)⁻¹ * A⁻¹ * s * g * (g⁻¹ ^ n * g ^ n) := by ring
    _ = 1 := by rw [hp]; field_simp [hg, hs, hA]

private theorem differentiable_nat_pow_complex {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (n : ℕ) :
    Differentiable ℂ (fun s => f s ^ n) := by
  induction n with
  | zero => fun_prop
  | succ n ih =>
    change Differentiable ℂ ((fun s : ℂ => f s ^ n) * f)
    exact ih.mul hf

/-- The standard simple-pole factor `(s - 1) ζ_K(s)` has an entire continuation with the
Mathlib residue as its value at `1`. -/
theorem dedekindZeta_simple_pole_continuation (K : Type*) [Field K] [NumberField K] :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      (∀ s : ℂ, 1 < s.re → G s = (s - 1) * dedekindZeta K s) ∧
      G 1 = (NumberField.dedekindZeta_residue K : ℂ) := by
  classical
  obtain ⟨ξ, hξ, hξeq, hξfe, hξ1⟩ := dedekind_completed K
  have harch : 0 < InfinitePlace.nrComplexPlaces K ∨ 0 < InfinitePlace.nrRealPlaces K := by
    have hrank := InfinitePlace.card_add_two_mul_card_eq_rank K
    have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
    omega
  let D : ℂ := ((|discr K| : ℝ) : ℂ)
  have hDreal : (|discr K| : ℝ) ≠ 0 := by
    exact_mod_cast (abs_ne_zero.mpr (NumberField.discr_ne_zero K))
  have hD : D ≠ 0 := Complex.ofReal_ne_zero.mpr hDreal
  let A : ℂ := (2 * Real.pi : ℂ)
  have hA : A ≠ 0 := by
    apply mul_ne_zero
    · norm_num
    · exact_mod_cast Real.pi_ne_zero
  rcases harch with hC | hR
  · let n : ℕ := InfinitePlace.nrComplexPlaces K - 1
    have hn : n + 1 = InfinitePlace.nrComplexPlaces K := by
      dsimp [n]
      exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hC))
    let q : ℂ → ℂ := fun s => D ^ (-s / 2) *
      (((Complex.Gammaℂ (s + 1))⁻¹ * A⁻¹) *
        ((Complex.Gammaℝ s)⁻¹ ^ InfinitePlace.nrRealPlaces K *
          (Complex.Gammaℂ s)⁻¹ ^ n))
    have hDdiff : Differentiable ℂ (fun s : ℂ => D ^ (-s / 2)) := by
      intro s
      exact (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow (Or.inl hD)
    have hqdiff : Differentiable ℂ q := by
      change Differentiable ℂ (fun s : ℂ => D ^ (-s / 2) *
        (((Complex.Gammaℂ (s + 1))⁻¹ * A⁻¹) *
          ((Complex.Gammaℝ s)⁻¹ ^ InfinitePlace.nrRealPlaces K *
            (Complex.Gammaℂ s)⁻¹ ^ n)))
      have hCinv : Differentiable ℂ (fun s : ℂ => (Complex.Gammaℂ s)⁻¹) :=
        Complex.differentiable_Gammaℂ_inv
      have hRinv : Differentiable ℂ (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) :=
        Complex.differentiable_Gammaℝ_inv
      have hCshift : Differentiable ℂ
          (fun s : ℂ => (Complex.Gammaℂ (s + 1))⁻¹) :=
        hCinv.comp (by fun_prop)
      have hRpow := differentiable_nat_pow_complex hRinv (InfinitePlace.nrRealPlaces K)
      have hCpow := differentiable_nat_pow_complex hCinv n
      have hhead : Differentiable ℂ
          (fun s : ℂ => (Complex.Gammaℂ (s + 1))⁻¹ * A⁻¹) :=
        hCshift.mul (differentiable_const (A⁻¹))
      exact hDdiff.mul (hhead.mul (hRpow.mul hCpow))
    have hQ : ∀ s : ℂ, 1 < s.re → q s * (s * dedekindPrefactor K s) = 1 := by
      intro s hs
      have hs0 : s ≠ 0 := by
        intro hz
        rw [hz] at hs
        norm_num [Complex.zero_re] at hs
      have hsp : 0 < s.re := by linarith
      have hR : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hsp
      have hbaseC : (2 * Real.pi : ℂ) ≠ 0 := hA
      have hCval : Complex.Gammaℂ s ≠ 0 := by
        rw [Complex.Gammaℂ_def]
        exact mul_ne_zero (mul_ne_zero two_ne_zero
          (Complex.cpow_ne_zero_iff.mpr (Or.inl hbaseC)))
          (Complex.Gamma_ne_zero_of_re_pos hsp)
      have hDcancel : D ^ (-s / 2) * D ^ (s / 2) = 1 := by
        rw [← Complex.cpow_add _ _ hD]
        have hz : -s / 2 + s / 2 = (0 : ℂ) := by ring
        rw [hz, Complex.cpow_zero]
      have hrec : Complex.Gammaℂ (s + 1) = Complex.Gammaℂ s * s / A := by
        rw [Complex.Gammaℂ_add_one hs0]
        dsimp [A]
        ring
      have hCcancel := inv_gamma_recurrence_cancel n hCval hs0 hA hrec
      have hRcancel := inv_pow_mul_pow_eq_one hR (InfinitePlace.nrRealPlaces K)
      rw [dedekindPrefactor_eq_completedZetaPrefactor K s,
        DedekindResidue.completedZetaPrefactor, DedekindResidue.gammaFactor, ← hn]
      change (D ^ (-s / 2) *
          (((Complex.Gammaℂ (s + 1))⁻¹ * A⁻¹) *
            ((Complex.Gammaℝ s)⁻¹ ^ InfinitePlace.nrRealPlaces K *
              (Complex.Gammaℂ s)⁻¹ ^ n))) *
        (s * (D ^ (s / 2) *
          (Complex.Gammaℝ s ^ InfinitePlace.nrRealPlaces K *
            Complex.Gammaℂ s ^ (n + 1)))) = 1
      calc
        (D ^ (-s / 2) *
            (((Complex.Gammaℂ (s + 1))⁻¹ * A⁻¹) *
              ((Complex.Gammaℝ s)⁻¹ ^ InfinitePlace.nrRealPlaces K *
                (Complex.Gammaℂ s)⁻¹ ^ n))) *
          (s * (D ^ (s / 2) *
            (Complex.Gammaℝ s ^ InfinitePlace.nrRealPlaces K *
              Complex.Gammaℂ s ^ (n + 1))))
          = (D ^ (-s / 2) * D ^ (s / 2)) *
              (((Complex.Gammaℂ (s + 1))⁻¹ * A⁻¹ *
                  (Complex.Gammaℂ s)⁻¹ ^ n *
                  (s * Complex.Gammaℂ s ^ (n + 1))) *
                ((Complex.Gammaℝ s)⁻¹ ^ InfinitePlace.nrRealPlaces K *
                  Complex.Gammaℝ s ^ InfinitePlace.nrRealPlaces K)) := by ring
        _ = 1 := by rw [hDcancel, hRcancel, hCcancel]; ring
    let G : ℂ → ℂ := fun s => ξ s * q s
    have hGdiff : Differentiable ℂ G := by
      dsimp [G]
      exact hξ.mul hqdiff
    have hGeq : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * dedekindZeta K s := by
      intro s hs
      change ξ s * q s = (s - 1) * dedekindZeta K s
      rw [hξeq s hs]
      have hq := hQ s hs
      calc
        (s * (s - 1) * dedekindPrefactor K s * dedekindZeta K s) * q s =
            (s - 1) * dedekindZeta K s * (q s * (s * dedekindPrefactor K s)) := by ring
        _ = (s - 1) * dedekindZeta K s := by rw [hq, mul_one]
    have hcont : ContinuousAt G (1 : ℂ) := hGdiff.continuous.continuousAt
    have hcast : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 1) (𝓝 (1 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
    have hGlim : Tendsto (fun x : ℝ => G (x : ℂ)) (𝓝[>] 1) (𝓝 (G 1)) :=
      hcont.tendsto.comp hcast
    have hResidue : Tendsto
        (fun x : ℝ => ((x : ℂ) - 1) * dedekindZeta K (x : ℂ)) (𝓝[>] 1)
        (𝓝 (NumberField.dedekindZeta_residue K : ℂ)) :=
      NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K
    have hmatch : (fun x : ℝ => G (x : ℂ)) =ᶠ[𝓝[>] 1]
        (fun x : ℝ => ((x : ℂ) - 1) * dedekindZeta K (x : ℂ)) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact hGeq x (by simpa using hx)
    have hResidueG : Tendsto (fun x : ℝ => G (x : ℂ)) (𝓝[>] 1)
        (𝓝 (NumberField.dedekindZeta_residue K : ℂ)) := by
      apply hResidue.congr'
      exact hmatch.symm
    refine ⟨G, hGdiff, hGeq, ?_⟩
    exact tendsto_nhds_unique hGlim hResidueG
  · let n : ℕ := InfinitePlace.nrRealPlaces K - 1
    have hn : n + 1 = InfinitePlace.nrRealPlaces K := by
      dsimp [n]
      exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hR))
    let q : ℂ → ℂ := fun s => D ^ (-s / 2) *
      (((Complex.Gammaℝ (s + 2))⁻¹ * A⁻¹) *
        ((Complex.Gammaℝ s)⁻¹ ^ n *
          (Complex.Gammaℂ s)⁻¹ ^ InfinitePlace.nrComplexPlaces K))
    have hDdiff : Differentiable ℂ (fun s : ℂ => D ^ (-s / 2)) := by
      intro s
      exact (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow (Or.inl hD)
    have hqdiff : Differentiable ℂ q := by
      change Differentiable ℂ (fun s : ℂ => D ^ (-s / 2) *
        (((Complex.Gammaℝ (s + 2))⁻¹ * A⁻¹) *
          ((Complex.Gammaℝ s)⁻¹ ^ n *
            (Complex.Gammaℂ s)⁻¹ ^ InfinitePlace.nrComplexPlaces K)))
      have hCinv : Differentiable ℂ (fun s : ℂ => (Complex.Gammaℂ s)⁻¹) :=
        Complex.differentiable_Gammaℂ_inv
      have hRinv : Differentiable ℂ (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) :=
        Complex.differentiable_Gammaℝ_inv
      have hRshift : Differentiable ℂ
          (fun s : ℂ => (Complex.Gammaℝ (s + 2))⁻¹) :=
        hRinv.comp (by fun_prop)
      have hRpow := differentiable_nat_pow_complex hRinv n
      have hCpow := differentiable_nat_pow_complex hCinv (InfinitePlace.nrComplexPlaces K)
      have hhead : Differentiable ℂ
          (fun s : ℂ => (Complex.Gammaℝ (s + 2))⁻¹ * A⁻¹) :=
        hRshift.mul (differentiable_const (A⁻¹))
      exact hDdiff.mul (hhead.mul (hRpow.mul hCpow))
    have hQ : ∀ s : ℂ, 1 < s.re → q s * (s * dedekindPrefactor K s) = 1 := by
      intro s hs
      have hs0 : s ≠ 0 := by
        intro hz
        rw [hz] at hs
        norm_num [Complex.zero_re] at hs
      have hsp : 0 < s.re := by linarith
      have hRval : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hsp
      have hbaseC : (2 * Real.pi : ℂ) ≠ 0 := hA
      have hCval : Complex.Gammaℂ s ≠ 0 := by
        rw [Complex.Gammaℂ_def]
        exact mul_ne_zero (mul_ne_zero two_ne_zero
          (Complex.cpow_ne_zero_iff.mpr (Or.inl hbaseC)))
          (Complex.Gamma_ne_zero_of_re_pos hsp)
      have hDcancel : D ^ (-s / 2) * D ^ (s / 2) = 1 := by
        rw [← Complex.cpow_add _ _ hD]
        have hz : -s / 2 + s / 2 = (0 : ℂ) := by ring
        rw [hz, Complex.cpow_zero]
      have hrec : Complex.Gammaℝ (s + 2) = Complex.Gammaℝ s * s / A := by
        rw [Complex.Gammaℝ_add_two hs0]
        dsimp [A]
        ring
      have hRcancel := inv_gamma_recurrence_cancel n hRval hs0 hA hrec
      have hCcancel := inv_pow_mul_pow_eq_one hCval (InfinitePlace.nrComplexPlaces K)
      rw [dedekindPrefactor_eq_completedZetaPrefactor K s,
        DedekindResidue.completedZetaPrefactor, DedekindResidue.gammaFactor, ← hn]
      change (D ^ (-s / 2) *
          (((Complex.Gammaℝ (s + 2))⁻¹ * A⁻¹) *
            ((Complex.Gammaℝ s)⁻¹ ^ n *
              (Complex.Gammaℂ s)⁻¹ ^ InfinitePlace.nrComplexPlaces K))) *
        (s * (D ^ (s / 2) *
          (Complex.Gammaℝ s ^ (n + 1) *
            Complex.Gammaℂ s ^ InfinitePlace.nrComplexPlaces K))) = 1
      calc
        (D ^ (-s / 2) *
            (((Complex.Gammaℝ (s + 2))⁻¹ * A⁻¹) *
              ((Complex.Gammaℝ s)⁻¹ ^ n *
                (Complex.Gammaℂ s)⁻¹ ^ InfinitePlace.nrComplexPlaces K))) *
          (s * (D ^ (s / 2) *
            (Complex.Gammaℝ s ^ (n + 1) *
              Complex.Gammaℂ s ^ InfinitePlace.nrComplexPlaces K)))
          = (D ^ (-s / 2) * D ^ (s / 2)) *
              (((Complex.Gammaℝ (s + 2))⁻¹ * A⁻¹ *
                  (Complex.Gammaℝ s)⁻¹ ^ n *
                  (s * Complex.Gammaℝ s ^ (n + 1))) *
                ((Complex.Gammaℂ s)⁻¹ ^ InfinitePlace.nrComplexPlaces K *
                  Complex.Gammaℂ s ^ InfinitePlace.nrComplexPlaces K)) := by ring
        _ = 1 := by rw [hDcancel, hRcancel, hCcancel]; ring
    let G : ℂ → ℂ := fun s => ξ s * q s
    have hGdiff : Differentiable ℂ G := by
      dsimp [G]
      exact hξ.mul hqdiff
    have hGeq : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * dedekindZeta K s := by
      intro s hs
      change ξ s * q s = (s - 1) * dedekindZeta K s
      rw [hξeq s hs]
      have hq := hQ s hs
      calc
        (s * (s - 1) * dedekindPrefactor K s * dedekindZeta K s) * q s =
            (s - 1) * dedekindZeta K s * (q s * (s * dedekindPrefactor K s)) := by ring
        _ = (s - 1) * dedekindZeta K s := by rw [hq, mul_one]
    have hcont : ContinuousAt G (1 : ℂ) := hGdiff.continuous.continuousAt
    have hcast : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 1) (𝓝 (1 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
    have hGlim : Tendsto (fun x : ℝ => G (x : ℂ)) (𝓝[>] 1) (𝓝 (G 1)) :=
      hcont.tendsto.comp hcast
    have hResidue : Tendsto
        (fun x : ℝ => ((x : ℂ) - 1) * dedekindZeta K (x : ℂ)) (𝓝[>] 1)
        (𝓝 (NumberField.dedekindZeta_residue K : ℂ)) :=
      NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K
    have hmatch : (fun x : ℝ => G (x : ℂ)) =ᶠ[𝓝[>] 1]
        (fun x : ℝ => ((x : ℂ) - 1) * dedekindZeta K (x : ℂ)) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact hGeq x (by simpa using hx)
    have hResidueG : Tendsto (fun x : ℝ => G (x : ℂ)) (𝓝[>] 1)
        (𝓝 (NumberField.dedekindZeta_residue K : ℂ)) := by
      apply hResidue.congr'
      exact hmatch.symm
    refine ⟨G, hGdiff, hGeq, ?_⟩
    exact tendsto_nhds_unique hGlim hResidueG

end ArtinPrimitiveRoots.Hecke
