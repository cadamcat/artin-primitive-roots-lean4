import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.LabeledAdditiveSieve
import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.ProbeAdditiveCandidates
import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.ProbeAdditiveMass

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol

open ArtinPrimitiveRoots A1 A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- The normalized additive residue row has square mass O((N + Y²)/Y),
uniformly over residue factors of norm at most one that vanish on nonunits. -/
theorem probe_residue_additive_sieve {D : FieldData F} {S : SData F CE condη}
    {H : HilbertData F} {Bd : BData S H} {bc : BalancedChoices D S H Bd}
    (A : AddCharData F) (E : ExteriorArithmetic D S H Bd bc)
    (K : Set S.FS) (hK : IsCompact K) (f : ℝ → ℂ)
    (hcompact : HasCompactSupport f) (hpositive : tsupport f ⊆ Set.Ioi 0)
    (hcontinuous : Continuous f) (hnonzero : ∃ v, f v ≠ 0) :
    ∃ B C : ℝ, 2 ≤ B ∧ 0 < C ∧ ∀ Y N : ℝ, 1 ≤ Y → (hN : 2 ≤ N) →
      ∃ P : Finset S.ExtIdeal,
        (∀ s : S.ExtIdeal, s ∈ P ↔ f (qI s.1 / Y) ≠ 0) ∧
        ∀ ρ : ∀ s : S.ExtIdeal, ResidueRing E s → ℂ,
          (∀ s d, ‖ρ s d‖ ≤ 1) →
          (∀ s d, ¬ IsUnit d → ρ s d = 0) →
          (∑' m : {m : S.R // InAdditiveWindow D S K N (by linarith [hN]) m},
            ‖∑ s ∈ P, ∑ᶠ d : ResidueRing E s,
              (Y : ℂ)⁻¹ * ((qI s.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ρ s d *
                S.e A (S.diag (-(m.1 : F) * (d.out : F) / (bc.gen s : F)))‖ ^ 2) ≤
            C * (N + (B * Y) ^ 2) / Y := by
  have headd (x y : S.FS) : S.e A (x + y) = S.e A x * S.e A y := by
    unfold SData.e
    have hfin : (∏ v : S.Sf, A.ψ v.1 ((x + y).1 v)) =
        (∏ v : S.Sf, A.ψ v.1 (x.1 v)) * ∏ v : S.Sf, A.ψ v.1 (y.1 v) := by
      calc
        _ = ∏ v : S.Sf, A.ψ v.1 (x.1 v) * A.ψ v.1 (y.1 v) := by
          apply Finset.prod_congr rfl
          intro v _
          exact (A.ψ v.1).map_add_eq_mul (x.1 v) (y.1 v)
        _ = _ := Finset.prod_mul_distrib
    have harch : (∏ w : InfinitePlace F, psiC ((x + y).2 w)) =
        (∏ w : InfinitePlace F, psiC (x.2 w)) * ∏ w : InfinitePlace F, psiC (y.2 w) := by
      calc
        _ = ∏ w : InfinitePlace F, psiC (x.2 w) * psiC (y.2 w) := by
          apply Finset.prod_congr rfl
          intro w _
          dsimp [psiC]
          have harg : -(4 * Real.pi * Complex.I *
              (((x.2 w).re : ℂ) + ((y.2 w).re : ℂ))) =
                -(4 * Real.pi * Complex.I * ((x.2 w).re : ℂ)) +
                -(4 * Real.pi * Complex.I * ((y.2 w).re : ℂ)) := by ring
          rw [Complex.ofReal_add, harg, Complex.exp_add]
        _ = _ := Finset.prod_mul_distrib
    rw [hfin, harch]
    ring
  have heone (r : S.R) : S.e A (S.diag (r : F)) = 1 := by
    have hr : S.diag (r : F) ∈ S.diagR := ⟨r, rfl⟩
    have hann : S.diag (r : F) ∈ S.annihilator A S.diagR := by
      rw [← S.diagR_eq_annihilator D A]
      exact hr
    have h1 : S.diag (1 : F) ∈ S.diagR := ⟨1, rfl⟩
    simpa [SData.diag] using hann (S.diag (1 : F)) h1
  obtain ⟨lo, B1, C1, hlo, hB1, hC1, hinterval, _⟩ :=
    probe_denominator_control S f hcompact hpositive hcontinuous hnonzero
  obtain ⟨Cm, hCm, hmass⟩ :=
    probe_additive_mass E f hcompact hpositive hcontinuous hnonzero
  obtain ⟨Ca, hCa, hsieve⟩ := additive_sieve_labeled D S H A Bd bc K hK
  let B : ℝ := max 2 B1
  have hB : 2 ≤ B := le_max_left _ _
  have hB1B : B1 ≤ B := le_max_right _ _
  refine ⟨B, Ca * Cm, hB, mul_pos hCa hCm, ?_⟩
  intro Y N hY hN
  have hYpos : 0 < Y := by linarith
  have hBY : 2 ≤ B * Y := by nlinarith
  obtain ⟨P, hP, hmassP⟩ := hmass Y hY
  have hcutoff (s : S.ExtIdeal) (hs : s ∈ P) : idealNorm s.1 ≤ B * Y := by
    have hsupport : qI s.1 / Y ∈ tsupport f :=
      subset_closure (Function.mem_support.mpr ((hP s).mp hs))
    have hupper := ((hinterval _ hsupport).2).trans hB1B
    exact (div_le_iff₀ hYpos).mp hupper
  let (s : S.ExtIdeal) : Fintype (ResidueRing E s) := E.residueFinite s
  let L := Σ s : {s : S.ExtIdeal // s ∈ P},
    {d : ResidueRing E s.1 // IsUnit d}
  let : Fintype L := inferInstance
  obtain ⟨α, hinj, hcandidate, hmod, Q, hQ, hQsep⟩ :=
    probe_additive_candidates E P (B * Y) hcutoff
  have hnegative (p : L) : -α p ∈ AdditiveCandidates D S bc (B * Y) := by
    rcases hcandidate p with hzero | ⟨s, hs, d, hd, hα⟩
    · exact Or.inl (by simp [hzero])
    · refine Or.inr ⟨s, hs, -d, ?_, ?_⟩
      · simpa only [Ideal.span_singleton_neg] using hd
      · rw [hα]
        simp only [map_neg, neg_div]
  have hseparate (p q : L) (hne : p ≠ q) :
      ¬ SameModuloSIntegers S (-α p) (-α q) := by
    intro hpq
    apply hQsep (α p) ((hQ _).mpr ⟨p, rfl⟩)
      (α q) ((hQ _).mpr ⟨q, rfl⟩) (fun h => hne (hinj h))
    obtain ⟨r, hr⟩ := hpq
    refine ⟨-r, ?_⟩
    change α p - α q = S.diag (-(r : F))
    rw [map_neg]
    simpa only [neg_sub, neg_sub_neg] using
      congrArg (fun z : S.FS => -z) hr
  have hphase (m : S.R) (p : L) : additivePhase S A m (-α p) =
      S.e A (S.diag (-(m : F) * (p.2.1.out : F) / (bc.gen p.1.1 : F))) := by
    obtain ⟨r, hr⟩ := hmod p
    have hnegativeDiag :
        S.diag (-(m : F) * (p.2.1.out : F) / (bc.gen p.1.1 : F)) =
          -(S.diag (m : F) * S.diag ((p.2.1.out : F) / (bc.gen p.1.1 : F))) := by
      rw [← map_mul, ← map_neg]
      congr 1
      ring
    have hdelta : S.diag (m : F) * (-α p) -
        S.diag (-(m : F) * (p.2.1.out : F) / (bc.gen p.1.1 : F)) =
          S.diag ((-(m * r) : S.R) : F) := by
      calc
        _ = -(S.diag (m : F) *
            (α p - S.diag ((p.2.1.out : F) / (bc.gen p.1.1 : F)))) := by
          rw [hnegativeDiag]
          ring
        _ = -(S.diag (m : F) * S.diag (r : F)) := by rw [hr]
        _ = _ := by rw [← map_mul, ← map_neg]; rfl
    have harg : S.diag (m : F) * (-α p) =
        S.diag (-(m : F) * (p.2.1.out : F) / (bc.gen p.1.1 : F)) +
          S.diag ((-(m * r) : S.R) : F) := by
      linear_combination hdelta
    unfold additivePhase
    rw [harg, headd, heone, mul_one]
  refine ⟨P, hP, ?_⟩
  intro ρ hρ hmask
  let c (p : L) : ℂ :=
    (Y : ℂ)⁻¹ * ((qI p.1.1.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ρ p.1.1 p.2.1
  have hrow (m : S.R) : (∑ p : L, c p * additivePhase S A m (-α p)) =
      ∑ s ∈ P, ∑ᶠ d : ResidueRing E s,
        (Y : ℂ)⁻¹ * ((qI s.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ρ s d *
          S.e A (S.diag (-(m : F) * (d.out : F) / (bc.gen s : F))) := by
    rw [Fintype.sum_sigma]
    calc
      _ = ∑ s : {s : S.ExtIdeal // s ∈ P}, ∑ᶠ d : ResidueRing E s.1,
          (Y : ℂ)⁻¹ * ((qI s.1.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ρ s.1 d *
            S.e A (S.diag (-(m : F) * (d.out : F) / (bc.gen s.1 : F))) := by
        apply Finset.sum_congr rfl
        intro s _
        simp only [c, hphase, finsum_eq_sum_of_fintype]
        symm
        apply Finset.sum_congr_set {d : ResidueRing E s.1 | IsUnit d}
        · intro d hd
          rfl
        · intro d hd
          simp only [Set.mem_ofPred_eq] at hd
          rw [hmask s.1 d hd, mul_zero, zero_mul]
      _ = _ := Finset.sum_coe_sort P (fun s => ∑ᶠ d : ResidueRing E s,
        (Y : ℂ)⁻¹ * ((qI s.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ρ s d *
          S.e A (S.diag (-(m : F) * (d.out : F) / (bc.gen s : F))))
  have hmassL : (∑ p : L, ‖c p‖ ^ 2) ≤ Cm / Y := by
    calc
      _ = ∑ s ∈ P, ∑ᶠ d : ResidueRing E s,
          ‖(Y : ℂ)⁻¹ * ((qI s.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ρ s d‖ ^ 2 := by
        rw [Fintype.sum_sigma]
        calc
          _ = ∑ s : {s : S.ExtIdeal // s ∈ P}, ∑ᶠ d : ResidueRing E s.1,
              ‖(Y : ℂ)⁻¹ * ((qI s.1.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ρ s.1 d‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro s _
            simp only [c, finsum_eq_sum_of_fintype]
            symm
            apply Finset.sum_congr_set {d : ResidueRing E s.1 | IsUnit d}
            · intro d hd
              rfl
            · intro d hd
              simp only [Set.mem_ofPred_eq] at hd
              simp only [hmask s.1 d hd, mul_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
          _ = _ := Finset.sum_coe_sort P (fun s => ∑ᶠ d : ResidueRing E s,
            ‖(Y : ℂ)⁻¹ * ((qI s.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ρ s d‖ ^ 2)
      _ ≤ _ := hmassP ρ hρ
  have hbound := hsieve N (B * Y) hN hBY L (fun p => -α p) hnegative hseparate c
  calc
    _ = ∑' m : {m : S.R // InAdditiveWindow D S K N (by linarith [hN]) m},
        ‖∑ p : L, c p * additivePhase S A m.1 (-α p)‖ ^ 2 := by
      apply tsum_congr
      intro m
      rw [hrow]
    _ ≤ Ca * (N + (B * Y) ^ 2) * ∑ p : L, ‖c p‖ ^ 2 := hbound
    _ ≤ Ca * (N + (B * Y) ^ 2) * (Cm / Y) :=
      mul_le_mul_of_nonneg_left hmassL (by positivity)
    _ = _ := by ring

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
