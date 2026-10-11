import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ArtinPrimitiveRoots.A1.Proofs.A1_DUAL.AnnihilatorCore

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open Filter
open scoped Topology

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private theorem wb_annihilator_subset_diag (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) (y : S.FS)
    (hyann : ∀ r : S.R, S.e A (S.diag (r : F) * y) = 1) :
    ∃ r : S.R, y = S.diag (r : F) := by
  classical
  letI : IsTotallyComplex F := D.isTotallyComplex
  obtain ⟨r₀, happrox⟩ :=
    ArtinPrimitiveRoots.Proofs.a1_dual_p.s_integer_finite_approx S y.1
  let y₁ : S.FS := y - S.diag (r₀ : F)
  have hyann₁ : ∀ r : S.R, S.e A (S.diag (r : F) * y₁) = 1 := by
    simpa [y₁] using
      (ArtinPrimitiveRoots.Proofs.a1_dual_p.sub_diag_preserves_annihilator
        D S A y hyann r₀)
  have hfinite₁ : ∀ v : S.Sf, y₁.1 v ∈ v.1.adicCompletionIntegers F := by
    intro v
    simpa [y₁, SData.diag] using happrox v
  have harch₁ :=
    ArtinPrimitiveRoots.Proofs.a1_dual_p.arch_condition_of_integral_finite_annihilator
      S A y₁ hfinite₁ hyann₁
  obtain ⟨t, htArch, htR⟩ :=
    ArtinPrimitiveRoots.Proofs.a1_dual_p.arch_trace_dual_lattice D S y₁.2 harch₁
  let tR : S.R := ⟨t, htR⟩
  let y₂ : S.FS := y₁ - S.diag (tR : F)
  have hyann₂ : ∀ r : S.R, S.e A (S.diag (r : F) * y₂) = 1 := by
    simpa [y₂] using
      (ArtinPrimitiveRoots.Proofs.a1_dual_p.sub_diag_preserves_annihilator
        D S A y₁ hyann₁ tR)
  have harch₂ : ∀ w : InfinitePlace F, y₂.2 w = 0 := by
    intro w
    change y₁.2 w - w.embedding t = 0
    rw [← htArch w]
    exact sub_self _
  have hfiniteR : ∀ r : S.R,
      (∏ v : S.Sf,
        A.ψ v.1 (algebraMap F (v.1.adicCompletion F) (r : F) * y₂.1 v)) = 1 :=
    ArtinPrimitiveRoots.Proofs.a1_dual_p.finite_character_condition_of_zero_arch
      S A y₂ hyann₂ harch₂
  have hfiniteAll :=
    ArtinPrimitiveRoots.Proofs.a1_dual_p.finite_character_trivial_of_s_integer
      S A y₂.1 hfiniteR
  have hcoords : ∀ v : S.Sf, y₂.1 v = 0 := by
    intro v
    apply ArtinPrimitiveRoots.Proofs.a1_dual_p.psi_local_nondegenerate D S A v
    intro x
    exact ArtinPrimitiveRoots.Proofs.a1_dual_p.finite_component_from_trivial
      S A y₂.1 hfiniteAll v x
  have hy₂zero : y₂ = 0 := by
    apply Prod.ext
    · exact funext hcoords
    · exact funext harch₂
  have hy₁eq : y - S.diag (r₀ : F) = S.diag (tR : F) := by
    change (y - S.diag (r₀ : F)) - S.diag (tR : F) = 0 at hy₂zero
    exact sub_eq_zero.mp hy₂zero
  have hyadd : y = S.diag (r₀ : F) + S.diag (tR : F) := by
    calc
      y = (y - S.diag (r₀ : F)) + S.diag (r₀ : F) := by abel
      _ = S.diag (tR : F) + S.diag (r₀ : F) := by rw [hy₁eq]
      _ = S.diag (r₀ : F) + S.diag (tR : F) := by abel
  refine ⟨r₀ + tR, ?_⟩
  calc
    y = S.diag (r₀ : F) + S.diag (tR : F) := hyadd
    _ = S.diag ((r₀ + tR : F)) := (map_add _ _ _).symm

/-- Continuity, nontriviality, and unit modulus of the frozen local additive character.
Uses: A.integral; A.trivial_on_F; A.unramified; A1-DUAL; weak approximation. -/
theorem local_character_regular (D : FieldData F) (A : AddCharData F)
    (v : FinPlace F) : LocalCharacterRegular A v := by
  classical
  have hcontinuous : Continuous (A.ψ v) := by
    apply IsLocallyConstant.continuous
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨{y | y - x ∈ (v.adicCompletionIntegers F : Set _)}, ?_, ?_, ?_⟩
    · exact (Valued.isOpen_valuationSubring _).preimage
        (continuous_id.sub continuous_const)
    · simp
    · intro y hy
      have hyO : y - x ∈ v.adicCompletionIntegers F := hy
      calc
        A.ψ v y = A.ψ v (x + (y - x)) := by congr 1 <;> abel
        _ = A.ψ v x * A.ψ v (y - x) := (A.ψ v).map_add_eq_mul _ _
        _ = A.ψ v x := by rw [A.integral v (y - x) hyO, mul_one]

  have hnontrivial : A.ψ v ≠ 1 := by
    intro htriv
    obtain ⟨S⟩ := A1.SData.nonempty (F := F) 0 v.asIdeal v.ne_bot
    have hvS : v ∈ S.Sf := S.cond_mem v le_rfl
    let vS : S.Sf := ⟨v, hvS⟩
    let y : S.FS := (fun u => if u = vS then 1 else 0, fun _ => 0)
    have hyann : ∀ r : S.R, S.e A (S.diag (r : F) * y) = 1 := by
      intro r
      have hfinite : (∏ u : S.Sf,
          A.ψ u.1 ((S.diag (r : F) * y).1 u)) = 1 := by
        apply Finset.prod_eq_one
        intro u hu
        by_cases huv : u = vS
        · subst u
          have hvalue : A.ψ v (algebraMap F (v.adicCompletion F) (r : F)) = 1 := by
            have h := congrArg (fun ψ => ψ (algebraMap F (v.adicCompletion F) (r : F))) htriv
            simpa using h
          simpa [A1.SData.diag, y, vS] using hvalue
        · simp [A1.SData.diag, y, huv]
      have harch : (∏ w : InfinitePlace F,
          psiC ((S.diag (r : F) * y).2 w)) = 1 := by
        apply Finset.prod_eq_one
        intro w hw
        simp [A1.SData.diag, y, psiC]
      change (∏ u : S.Sf,
          A.ψ u.1 ((S.diag (r : F) * y).1 u)) *
        (∏ w : InfinitePlace F, psiC ((S.diag (r : F) * y).2 w)) = 1
      rw [hfinite, harch]
      norm_num
    obtain ⟨r, hr⟩ := wb_annihilator_subset_diag D S A y hyann
    let w : InfinitePlace F := Classical.choice (inferInstance : Nonempty (InfinitePlace F))
    have hrzero : (r : F) = 0 := by
      have hw := congrArg (fun z : S.FS => z.2 w) hr.symm
      have hmap : w.embedding (r : F) = 0 := by
        simpa [A1.SData.diag, y] using hw
      exact w.embedding.injective (by simpa using hmap)
    have hvcoord := congrArg (fun z : S.FS => z.1 vS) hr.symm
    have hcoord : algebraMap F (v.adicCompletion F) (r : F) = 1 := by
      simpa [A1.SData.diag, y, vS] using hvcoord
    rw [hrzero] at hcoord
    norm_num at hcoord

  have hunit : ∀ x, ‖A.ψ v x‖ = 1 := by
    intro x
    letI : NeZero v.asIdeal := ⟨v.ne_bot⟩
    let p : ℕ := Ideal.absNorm (Ideal.under ℤ v.asIdeal)
    have hp : Nat.Prime p := by
      dsimp [p]
      exact Nat.absNorm_under_prime v.asIdeal
    have hpO : (p : 𝓞 F) ∈ v.asIdeal := by
      dsimp [p]
      exact Int.absNorm_under_mem v.asIdeal
    let q : v.adicCompletion F := (p : F)
    have hqval : Valued.v q < 1 := by
      change Valued.v ((p : F) : v.adicCompletion F) < 1
      rw [IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe]
      exact (v.valuation_lt_one_iff_mem (K := F) (p : 𝓞 F)).2 hpO
    have hqpow : Tendsto (fun k : ℕ => q ^ k) atTop (𝓝 (0 : v.adicCompletion F)) :=
      Valued.tendsto_zero_pow_of_v_lt_one hqval
    have hOopen : IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
      Valued.isOpen_valuationSubring _
    have hevent : ∀ᶠ k : ℕ in atTop,
        q ^ k * x ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
      have ht := hqpow.mul_const x
      have hmem : (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ∈
          𝓝 ((0 : v.adicCompletion F) * x) := by
        exact hOopen.mem_nhds (by simp)
      exact ht.eventually_mem hmem
    obtain ⟨k, hk⟩ := Filter.Eventually.exists hevent
    have hcast : (p : v.adicCompletion F) = q := by
      dsimp [q]
      exact (map_natCast (algebraMap F (v.adicCompletion F)) p).symm
    have hsmul : (p ^ k : ℕ) • x = q ^ k * x := by
      calc
        (p ^ k : ℕ) • x = (p ^ k : v.adicCompletion F) * x := by
          simp [nsmul_eq_mul]
        _ = q ^ k * x := by
          congr 1
          rw [hcast]
    have hchar : (A.ψ v x) ^ (p ^ k) = 1 := by
      calc
        (A.ψ v x) ^ (p ^ k) = A.ψ v ((p ^ k : ℕ) • x) :=
          (A.ψ v).map_nsmul_eq_pow (p ^ k) x |>.symm
        _ = 1 := A.integral v _ (by rw [hsmul]; exact hk)
    exact Complex.norm_eq_one_of_pow_eq_one hchar (pow_ne_zero _ hp.ne_zero)

  exact ⟨hcontinuous, hnontrivial, hunit⟩

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
