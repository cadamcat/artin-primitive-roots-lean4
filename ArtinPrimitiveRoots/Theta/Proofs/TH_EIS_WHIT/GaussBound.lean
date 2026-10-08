import ArtinPrimitiveRoots.Theta.LocalWhit

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-- Integral triviality forces every finite-place character value to have norm one. -/
theorem whit_psi_norm (A : AddCharData F) (v : FinPlace F) (x : v.adicCompletion F) :
    ‖A.ψ v x‖ = 1 := by
  classical
  let K := v.adicCompletion F
  let _ : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).RankOne := inferInstance
  let _ : NormedField K := inferInstance
  let _ : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  have hproper : ProperSpace K :=
    (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F)),
        inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)))⟩
  have hcompact : IsCompact (v.adicCompletionIntegers F : Set K) := by
    have hset : (v.adicCompletionIntegers F : Set K) = Metric.closedBall (0 : K) 1 := by
      change (↑((Valued.v : Valuation K (WithZero (Multiplicative ℤ))).integer) : Set K) =
        Metric.closedBall (0 : K) 1
      exact Valued.toNormedField.setOfPred_mem_integer_eq_closedBall (L := K)
    rw [hset]
    exact hproper.isCompact_closedBall 0 1
  letI : CompactSpace (v.adicCompletionIntegers F) :=
    isCompact_iff_compactSpace.mp hcompact
  have hopen : IsOpen (v.adicCompletionIntegers F : Set K) :=
    Valued.isOpen_valuationSubring K
  have hpsi : IsLocallyConstant (A.ψ v) := by
    apply (IsLocallyConstant.iff_exists_open _).2
    intro t
    refine ⟨{y : K | y - t ∈ v.adicCompletionIntegers F},
      hopen.preimage (continuous_id.sub continuous_const), ?_, ?_⟩
    · change t - t ∈ v.adicCompletionIntegers F
      rw [sub_self]
      exact (v.adicCompletionIntegers F).zero_mem
    · intro y hy
      have hi := A.integral v (y - t) hy
      simpa only [sub_add_cancel, hi, one_mul] using
        (A.ψ v).map_add_eq_mul (y - t) t
  let φ : v.adicCompletionIntegers F → ℂ := fun t => A.ψ v (x * (t : K))
  have hφ : IsLocallyConstant φ :=
    hpsi.comp_continuous (continuous_const.mul continuous_subtype_val)
  have hfinite := hφ.range_finite
  have hmem (n : ℕ) : A.ψ v x ^ n ∈ Set.range φ := by
    refine ⟨(n : v.adicCompletionIntegers F), ?_⟩
    change A.ψ v (x * (n : K)) = A.ψ v x ^ n
    rw [mul_comm, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]
  obtain ⟨m, n, hmn, heq⟩ := hfinite.exists_lt_map_eq_of_forall_mem
    (f := fun n : ℕ => A.ψ v x ^ n) hmem
  have hne : A.ψ v x ≠ 0 := ((A.ψ v).val_isUnit x).ne_zero
  have hroot : A.ψ v x ^ (n - m) = 1 := by
    apply mul_left_cancel₀ (pow_ne_zero m hne)
    calc
      A.ψ v x ^ m * A.ψ v x ^ (n - m) = A.ψ v x ^ n := by
        rw [← pow_add]
        congr 1
        omega
      _ = A.ψ v x ^ m * 1 := by rw [← heq, mul_one]
  exact Complex.norm_eq_one_of_pow_eq_one hroot (Nat.sub_pos_of_lt hmn).ne'

/-- The triangle bound for the normalized residue Gauss sum. -/
theorem whit_gaussLoc_norm_le (D : FieldData F) (A : AddCharData F)
    (v : FinPlace F) (j : ℤ) :
    ‖gaussLoc D A v j‖ ≤ Real.sqrt (qv v) := by
  sorry

/-- The terminal coefficient in the exponent-zero spherical Jacquet vector is bounded by one. -/
theorem whit_shellTerm_one_norm_le (D : FieldData F) (A : AddCharData F)
    (v : FinPlace F) : ‖shellTerm D A v 1‖ ≤ 1 := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
