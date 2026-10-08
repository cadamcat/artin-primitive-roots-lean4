import ArtinPrimitiveRoots.Theta.Proofs.TH_COVER.Congruence
import ArtinPrimitiveRoots.Theta.Proofs.TH_COVER.CompletionCompact

/-! Compactness of canonical GL₂ congruence subgroups. -/

set_option autoImplicit false
open NumberField IsDedekindDomain Filter Topology
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.th_cover_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]

/-- Positive-level congruence sets in canonical GL₂ are compact. -/
theorem congruenceCompact (v : FinPlace F) (m : ℕ) (hm : 1 ≤ m) :
    IsCompact {g : GL (Fin 2) (v.adicCompletion F) | ∀ i j,
      Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j -
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) ≤
        WithZero.exp (-(m : ℤ))} := by
  classical
  let K := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  let : CompactSpace O := compact_adicCompletionIntegers v
  let : CompactSpace (Matrix (Fin 2) (Fin 2) O) :=
    inferInstanceAs (CompactSpace (Fin 2 → Fin 2 → O))
  let j : O →+* K := O.subtype
  let ιM : Matrix (Fin 2) (Fin 2) O →+* Matrix (Fin 2) (Fin 2) K := RingHom.mapMatrix j
  let ι : GL (Fin 2) O →* GL (Fin 2) K := Matrix.GeneralLinearGroup.map j
  have hj : Continuous j := continuous_subtype_val
  have hM : Continuous ιM := continuous_id.matrix_map hj
  have hι : Continuous ι := hM.units_map ιM.toMonoidHom
  have hc : IsCompact (Set.range ι) := isCompact_range hι
  let V : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  let r := WithZero.exp (-(m : ℤ))
  let S : Set (GL (Fin 2) K) := {g | ∀ i j,
    V ((g : Matrix (Fin 2) (Fin 2) K) i j -
      (1 : Matrix (Fin 2) (Fin 2) K) i j) ≤ r}
  have hr : r < 1 := by
    dsimp [r]
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have scalarClosed : IsClosed {x : K | V x ≤ r} := by
    obtain ⟨π, hπ⟩ := v.valuedAdicCompletion_surjective F r
    convert Valued.isClosed_closedBall K (V.restrict π) using 1
    ext x
    change V x ≤ r ↔ V.restrict x ≤ V.restrict π
    rw [V.restrict_le_iff, hπ]
  have hclosed : IsClosed S := by
    have hval : Continuous (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) :=
      Units.continuous_val
    have he (i j : Fin 2) : IsClosed {g : GL (Fin 2) K |
        V ((g : Matrix (Fin 2) (Fin 2) K) i j -
          (1 : Matrix (Fin 2) (Fin 2) K) i j) ≤ r} :=
      scalarClosed.preimage ((hval.matrix_elem i j).sub continuous_const)
    have hi := isClosed_iInter fun i => isClosed_iInter fun j => he i j
    convert hi using 1
    ext g
    simp [S]
  have integralEntries (g : GL (Fin 2) K) (hg : g ∈ S) :
      ∀ i j, V ((g : Matrix (Fin 2) (Fin 2) K) i j) ≤ 1 := by
    intro i j
    have hδ : V ((1 : Matrix (Fin 2) (Fin 2) K) i j) ≤ 1 := by
      fin_cases i <;> fin_cases j <;> simp
    have hbound := V.map_add_le ((hg i j).trans hr.le) hδ
    simpa only [sub_add_cancel] using hbound
  obtain ⟨Uc, hUc⟩ := exists_congruenceSubgroup v m hm
  have hsub : S ⊆ Set.range ι := by
    intro g hg
    have hinv : g⁻¹ ∈ S := (hUc g⁻¹).mp (Uc.inv_mem ((hUc g).mpr hg))
    let A : Matrix (Fin 2) (Fin 2) O := fun i j =>
      ⟨(g : Matrix (Fin 2) (Fin 2) K) i j, integralEntries g hg i j⟩
    let B : Matrix (Fin 2) (Fin 2) O := fun i j =>
      ⟨((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j,
        integralEntries g⁻¹ hinv i j⟩
    have hA : ιM A = (g : Matrix (Fin 2) (Fin 2) K) := rfl
    have hB : ιM B = ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := rfl
    have hMinj : Function.Injective ιM := Matrix.map_injective Subtype.val_injective
    let u : GL (Fin 2) O := {
      val := A
      inv := B
      val_inv := by
        apply hMinj
        rw [map_mul, map_one, hA, hB]
        exact g.mul_inv
      inv_val := by
        apply hMinj
        rw [map_mul, map_one, hA, hB]
        exact g.inv_mul
    }
    refine ⟨u, ?_⟩
    apply Units.ext
    change ιM A = (g : Matrix (Fin 2) (Fin 2) K)
    exact hA
  exact hc.of_isClosed_subset hclosed hsub

end ArtinPrimitiveRoots.Proofs.th_cover_sol
