import ArtinPrimitiveRoots.A1.Field

/-! Compactness of the valuation ring in a finite completion. -/

set_option autoImplicit false
open NumberField IsDedekindDomain Filter Topology
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.th_cover_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]

/-- The valuation ring of a number-field finite completion is compact. -/
theorem compact_adicCompletionIntegers (v : FinPlace F) :
    CompactSpace (v.adicCompletionIntegers F) := by
  classical
  let K := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  let V : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  let j : 𝓞 F →+* O := algebraMap (𝓞 F) O
  let ρ : 𝓞 F →+* IsLocalRing.ResidueField O := (IsLocalRing.residue O).comp j
  have hker (r : 𝓞 F) (hr : r ∈ v.asIdeal) : ρ r = 0 := by
    change IsLocalRing.residue O (j r) = 0
    rw [IsLocalRing.residue_eq_zero_iff]
    apply (Valuation.mem_maximalIdeal_iff (K := K) (v := V)).mpr
    change Valued.v ((algebraMap (𝓞 F) F r : F) : v.adicCompletion F) < 1
    rw [v.valuedAdicCompletion_eq_valuation' (algebraMap (𝓞 F) F r)]
    exact (v.valuation_lt_one_iff_mem (K := F) r).mpr hr
  let q : (𝓞 F ⧸ v.asIdeal) →+* IsLocalRing.ResidueField O :=
    Ideal.Quotient.lift v.asIdeal ρ hker
  have hq : Function.Surjective q := by
    intro z
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
    let U : Set K := {x | V.restrict (x - (a : K)) < 1}
    have hUopen : IsOpen U :=
      (Valued.isOpen_ball K 1).preimage (continuous_id.sub continuous_const)
    have hUne : U.Nonempty := ⟨a, by simp [U]⟩
    obtain ⟨y, hy⟩ := (v.denseRange_algebraMap F).exists_mem_open hUopen hUne
    have hyclose : V (algebraMap F K y - (a : K)) < 1 :=
      V.restrict_lt_one_iff.mp hy
    have hyint : v.valuation F y ≤ 1 := by
      have hval : V (algebraMap F K y) ≤ 1 := by
        calc
          _ = V ((algebraMap F K y - (a : K)) + (a : K)) := by rw [sub_add_cancel]
          _ ≤ 1 := V.map_add_le hyclose.le a.property
      exact (v.valuedAdicCompletion_eq_valuation' y) ▸ hval
    obtain ⟨r, hr⟩ := v.exists_valuation_sub_lt_of_integer hyint
      (1 : (WithZero (Multiplicative ℤ))ˣ)
    have herr : V (algebraMap F K (algebraMap (𝓞 F) F r - y)) < 1 := by
      change Valued.v ((algebraMap (𝓞 F) F r - y : F) : v.adicCompletion F) < 1
      rw [v.valuedAdicCompletion_eq_valuation' (algebraMap (𝓞 F) F r - y)]
      simpa using hr
    have hrclose : V (((j r : O) : K) - algebraMap F K y) < 1 := by
      change V (algebraMap F K (algebraMap (𝓞 F) F r) - algebraMap F K y) < 1
      rw [← map_sub]
      exact herr
    have hra : V (((j r : O) : K) - (a : K)) < 1 := by
      have hsum := (V.map_add (((j r : O) : K) - algebraMap F K y)
        (algebraMap F K y - (a : K))).trans_lt (max_lt hrclose hyclose)
      simpa only [sub_add_sub_cancel] using hsum
    have heq : ρ r = IsLocalRing.residue O a := by
      change IsLocalRing.residue O (j r) = IsLocalRing.residue O a
      apply sub_eq_zero.mp
      rw [← map_sub, IsLocalRing.residue_eq_zero_iff]
      exact (Valuation.mem_maximalIdeal_iff (K := K) (v := V)).mpr hra
    exact ⟨Ideal.Quotient.mk v.asIdeal r, by simpa only [q, Ideal.Quotient.lift_mk] using heq⟩
  let : Finite (𝓞 F ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  let : Finite (IsLocalRing.ResidueField O) := Finite.of_surjective q hq
  let : Finite (Valued.ResidueField K) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField O))
  let : CompleteSpace (Valued.integer K) := (Valued.isClosed_integer K).isComplete.completeSpace_coe
  let : IsDiscreteValuationRing (Valued.integer K) :=
    inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F))
  exact (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
    (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr ⟨inferInstance, inferInstance, inferInstance⟩

end ArtinPrimitiveRoots.Proofs.th_cover_sol
