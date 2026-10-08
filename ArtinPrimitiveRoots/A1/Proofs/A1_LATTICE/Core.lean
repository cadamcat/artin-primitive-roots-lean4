import ArtinPrimitiveRoots.A1.Field

/-!
Helper interfaces for the A1 S-lattice proof.  This module is intentionally separate from
`SLattice`, so the arithmetic/topological statements can be developed without an import cycle.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical nonZeroDivisors

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.A1_LATTICE

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

theorem exists_principal_power_generator (v : HeightOneSpectrum (𝓞 F)) :
    ∃ a : 𝓞 F,
      Ideal.span {a} = v.asIdeal ^ Fintype.card (ClassGroup (𝓞 F)) := by
  let p0 : (Ideal (𝓞 F))⁰ :=
    ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩
  let n := Fintype.card (ClassGroup (𝓞 F))
  have hClass : ClassGroup.mk0 p0 ^ n = 1 := by
    simpa [n] using (pow_card_eq_one (x := ClassGroup.mk0 p0))
  have hn0 : v.asIdeal ^ n ≠ 0 := pow_ne_zero _ v.ne_bot
  have hClassPow :
      ClassGroup.mk0 ⟨v.asIdeal ^ n, mem_nonZeroDivisors_iff_ne_zero.mpr hn0⟩ = 1 := by
    change ClassGroup.mk0 (p0 ^ n) = 1
    rw [map_pow]
    exact hClass
  have hPrincipal : (v.asIdeal ^ n).IsPrincipal :=
    (ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_iff_ne_zero.mpr hn0)).mp hClassPow
  obtain ⟨a, ha⟩ := hPrincipal.principal
  exact ⟨a, ha.symm⟩

theorem s_integer_finite_approx (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (x : ∀ v : S.Sf, v.1.adicCompletion F) :
    ∃ r : S.R, ∀ v : S.Sf,
      x v - algebraMap F (v.1.adicCompletion F) (r : F) ∈
        v.1.adicCompletionIntegers F := by
  sorry

theorem arch_integer_compact_reduction (D : ArtinPrimitiveRoots.A1.FieldData F) :
    ∃ C : Set (InfinitePlace F → ℂ), IsCompact C ∧
      ∀ z : InfinitePlace F → ℂ, ∃ a : 𝓞 F, ∃ p ∈ C,
        z = (fun w => w.embedding (a : F)) + p := by
  sorry

theorem diagR_isDiscrete (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (D : ArtinPrimitiveRoots.A1.FieldData F) :
    IsDiscrete (Set.range fun r : S.R => S.diag (r : F)) := by
  sorry

theorem diagR_has_compact_cover (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (D : ArtinPrimitiveRoots.A1.FieldData F) :
    ∃ K : Set S.FS, IsCompact K ∧ ∀ x : S.FS, ∃ r : S.R, ∃ k ∈ K,
      x = S.diag (r : F) + k := by
  sorry

end ArtinPrimitiveRoots.Proofs.A1_LATTICE
