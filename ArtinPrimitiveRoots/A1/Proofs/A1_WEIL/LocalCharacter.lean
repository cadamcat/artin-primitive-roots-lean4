import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ArtinPrimitiveRoots.A1.SLattice

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open Filter
open scoped Topology

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Continuity, nontriviality, and unit modulus of the frozen local additive character.
Guide: PROOFS.md:464–466. Uses: A.integral; A.trivial_on_F; A.unramified; A1-DUAL; weak approximation. -/
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
    have hyann : y ∈ S.annihilator A S.diagR := by
      change ∀ z : S.FS, z ∈ S.diagR → S.e A (z * y) = 1
      intro z hz
      change ∃ r : S.R, S.diag (r : F) = z at hz
      obtain ⟨r, rfl⟩ := hz
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
    have hdiag : y ∈ S.diagR := by
      rw [S.diagR_eq_annihilator D A]
      exact hyann
    change ∃ r : S.R, S.diag (r : F) = y at hdiag
    obtain ⟨r, hr⟩ := hdiag
    let w : InfinitePlace F := Classical.choice (inferInstance : Nonempty (InfinitePlace F))
    have hrzero : (r : F) = 0 := by
      have hw := congrArg (fun z : S.FS => z.2 w) hr
      have hmap : w.embedding (r : F) = 0 := by
        simpa [A1.SData.diag, y] using hw
      exact w.embedding.injective (by simpa using hmap)
    have hvcoord := congrArg (fun z : S.FS => z.1 vS) hr
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
