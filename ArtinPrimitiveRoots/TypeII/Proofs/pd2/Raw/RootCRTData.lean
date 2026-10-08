import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootCRTCharacters

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

lemma pd2a_rootCRT_first_val (u S : ℕ) (hSq : Squarefree S) [NeZero (u * S)] (z : ZMod (u * S)) :
    (pd2a_rootCRTEquiv u S hSq z).1 = (z.val : ZMod (u * pd2a_rootShared u S)) := by
  calc
    _ = (pd2a_rootCRTEquiv u S hSq (z.val : ZMod (u * S))).1 :=
      congrArg (fun t : ZMod (u * S) => (pd2a_rootCRTEquiv u S hSq t).1) (ZMod.natCast_zmod_val z).symm
    _ = _ := by rw [map_natCast]; rfl

lemma pd2a_rootCRT_second_val (u S : ℕ) (hSq : Squarefree S) [NeZero (u * S)] (z : ZMod (u * S)) :
    (pd2a_rootCRTEquiv u S hSq z).2 = (z.val : ZMod (pd2a_rootUnshared u S)) := by
  calc
    _ = (pd2a_rootCRTEquiv u S hSq (z.val : ZMod (u * S))).2 :=
      congrArg (fun t : ZMod (u * S) => (pd2a_rootCRTEquiv u S hSq t).2) (ZMod.natCast_zmod_val z).symm
    _ = _ := by rw [map_natCast]; rfl

lemma pd2a_rootGraph_split_data (u S : ℕ) (hu : 0 < u) (hS : 0 < S)
    [NeZero (u * S)] (hSq : Squarefree S)
    (g₀ : Matrix (Fin 2) (Fin 2) (ZMod S)) (hdet : Matrix.det g₀ = 1)
    (hu₀ : (u : ZMod S) = g₀ 0 0) :
    ∃ αA : (ZMod (u * pd2a_rootShared u S))ˣ,
      (αA : ZMod (u * pd2a_rootShared u S)) = (u : ZMod (u * pd2a_rootShared u S)) *
        ((g₀ 1 1).val : ZMod (u * pd2a_rootShared u S)) - 1 ∧
      ∀ z : ZMod (u * S) × ZMod (u * S), z ∈ pd2a_rootGraph u S g₀ ↔
        (pd2a_rootCRTEquiv u S hSq z.1).1 * (pd2a_rootCRTEquiv u S hSq z.2).1 = (αA : ZMod (u * pd2a_rootShared u S)) ∧
        (pd2a_rootCRTEquiv u S hSq z.1).2 = ((g₀ 0 1).val : ZMod (pd2a_rootUnshared u S)) ∧
        (pd2a_rootCRTEquiv u S hSq z.2).2 = ((g₀ 1 0).val : ZMod (pd2a_rootUnshared u S)) ∧
        ZMod.castHom (dvd_mul_left (pd2a_rootShared u S) u) (ZMod (pd2a_rootShared u S))
          (pd2a_rootCRTEquiv u S hSq z.1).1 = ((g₀ 0 1).val : ZMod (pd2a_rootShared u S)) := by
  letI : NeZero S := ⟨hS.ne'⟩
  let D := pd2a_rootShared u S
  let M := u * D
  let e := pd2a_rootCRTEquiv u S hSq
  let eT := pd2a_rootCRTResidueEquiv u S hSq
  let f : ZMod M →+* ZMod D := ZMod.castHom (dvd_mul_left D u) (ZMod D)
  let r : ZMod (u * S) →+* ZMod S := ZMod.castHom (dvd_mul_left S u) (ZMod S)
  let α : ZMod (u * S) := (u : ZMod (u * S)) * ((g₀ 1 1).val : ZMod (u * S)) - 1
  have hαUnit : IsUnit ((u : ZMod M) * ((g₀ 1 1).val : ZMod M) - 1) := by
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_one] using
      pd2a_root_inverse_rhs_unit u S hu ((g₀ 1 1).val : ℤ)
  obtain ⟨αA, hαA⟩ := hαUnit
  refine ⟨αA, hαA, ?_⟩
  have hα : (e α).1 = (αA : ZMod M) := by
    simp only [α, map_sub, map_mul, map_natCast, map_one, Prod.fst_sub, Prod.fst_mul,
      Prod.fst_natCast, Prod.fst_one]
    exact hαA.symm
  have hres₁ : ∀ t : ZMod S, (eT t).1 = (t.val : ZMod D) := by
    intro t
    calc
      _ = (eT (t.val : ZMod S)).1 := congrArg (fun y : ZMod S => (eT y).1) (ZMod.natCast_zmod_val t).symm
      _ = _ := by rw [map_natCast]; rfl
  have hres₂ : ∀ t : ZMod S, (eT t).2 = (t.val : ZMod (pd2a_rootUnshared u S)) := by
    intro t
    calc
      _ = (eT (t.val : ZMod S)).2 := congrArg (fun y : ZMod S => (eT y).2) (ZMod.natCast_zmod_val t).symm
      _ = _ := by rw [map_natCast]; rfl
  have hcUnit : IsUnit (eT (g₀ 0 1)).1 := by
    rw [hres₁]
    exact pd2a_root_shared_entry_unit u S hS hSq g₀ hdet hu₀
  have hαr : r α = g₀ 0 1 * g₀ 1 0 := by
    have hdet' : g₀ 0 0 * g₀ 1 1 - g₀ 0 1 * g₀ 1 0 = 1 := by simpa only [Matrix.det_fin_two] using hdet
    change r ((u : ZMod (u * S)) * ((g₀ 1 1).val : ZMod (u * S)) - 1) = _
    rw [map_sub, map_mul, map_natCast, map_natCast, map_one, ZMod.natCast_zmod_val, hu₀]
    linear_combination hdet'
  have hrCast : ∀ z : ZMod (u * S), r z = (z.val : ZMod S) := by
    intro z
    conv_lhs => rw [← ZMod.natCast_zmod_val z]
    rw [map_natCast]
  intro z
  have hpre := pd2a_crt_inverse_predicate e eT f r (pd2a_rootCRT_commute u S hSq) α αA hα
    (g₀ 0 1) (g₀ 1 0) hαr hcUnit z
  simpa only [pd2a_rootGraph, Finset.mem_filter, Finset.mem_univ, true_and, hrCast, α, hres₁, hres₂] using hpre

end ArtinPrimitiveRoots.TypeII.PD
