import ArtinPrimitiveRoots.TypeII.Proofs.«PD-LOW».KernelSupport
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-LOW».OpNormSupport
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».pd5_scale_facts
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-LOW».GhostDomination
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-LOW».ValidSupport
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-LOW».NormSupport
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-LOW».SignSupport
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-LOW».SchurSupport
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-LOW».pd5_boundary_norm_near_one
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-LOW».pd5_ghostBirthTwist_preserves_sym
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-LOW».pd5_edgeBirthTwist_preserves_sym
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-LOW».pd5_twisted_edge_schur
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-LOW».Defs
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».pd5_chronological_model

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open ArtinPrimitiveRoots.TypeII
noncomputable section

/-- Symmetry and quantitative bounds for birth-twisted ghosts and full edges. The edge proof
must use positive raw-plus-comparison choice sums before subtraction; a signed-kernel bound
alone is insufficient. Guide `runs/lanes/sol-thin-pd5/PROOFS.md:657–770`; uses memorySym,
finite weighted Schur, ghost sign parity, and the positive edge row/column estimates.
Feeds low-rank iteration and frozen history_rank_low. LEAD. -/
theorem pd5_modified_ops_symmetry_domination (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁)
    (K : ℕ) (F : PDFix K) (hF : F.Valid) (ρ : ℝ) (hρ : IsMemoryRho F.q_d ρ)
    (hghost : PD5GhostCrudeAvailable δ c₁ c₂ F ρ) :
    PD5ModifiedBoundsAvailable δ c₁ c₂ F ρ := by
  rcases hghost with ⟨v, C_K, xG, hv, hC_K, hxG, hG⟩
  rcases pd5_twisted_edge_schur δ c₁ c₂ hδ hc₁ K F hF ρ hρ v hv with
    ⟨Ccr, xE, hCcr, hxE, hE⟩
  rcases pd5_boundary_norm_near_one δ c₁ c₂ K F hF with ⟨xB, hxB, hB⟩
  rcases pd5_scale_facts K F hF with ⟨xA, hxA, hA⟩
  let x₀ := max xG (max xE (max xB xA))
  refine ⟨C_K, Ccr, x₀, hC_K, hCcr, le_trans hxG (le_max_left _ _), ?_⟩
  intro S hS hx w hw W hW
  have hxg : xG ≤ S.x := (le_max_left _ _).trans hx
  have hxe : xE ≤ S.x := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hx
  have hxb : xB ≤ S.x :=
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans hx
  have hxa : xA ≤ S.x :=
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans hx
  have hμ := (hB S hS hxb).1
  rcases hA S hxa with ⟨hL, _, _, _, _, _, _, hband⟩
  have hv0 : 0 < v := lt_trans (by norm_num) hv
  have hV : ∀ i, 0 ≤ bandMass S.x (F.a i) := by
    intro i
    exact le_trans (div_nonneg (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le (by norm_num))
      (hband i).1
  have hν : ∀ i p, p ∈ primeBand S.x (F.a i) → 0 ≤ memoryNu S.x K F.a F.q_d i p := by
    intro i p hp
    exact ((hband i).2.2.2 p hp).1
  have hbox := pd5_envBox_finite_of_valid hS hw
  constructor
  · intro j hj
    have hη := (pd5_memoryEta_bounds (x := S.x) hF.2.1 hF.2.2.1 j).1
    have hq : 0 ≤ memoryQ S.x F.q_d j := by
      unfold memoryQ
      split_ifs
      · exact Real.sqrt_nonneg _
      · exact hF.2.1.le
    rcases hG S hS hxg w hw j hj with ⟨hrow, hcol⟩
    refine ⟨?_, fun f hf => pd5_ghostBirthTwist_preserves_sym F S ρ j W f hf⟩
    apply pd5_twisted_ghost_norm F S ρ hρ.1 j (memoryCutoff S) W hW v C_K
      hv0 hC_K.le hμ hη hq hV hν hrow hcol
    intro T f hf hT s hs hsize
    exact pd5_ghost_supported_kernel F S ρ j (memoryCutoff S) W T f hf hT s
  · intro j hj
    rcases hE S hS hxe w hw j hj W hW with ⟨hrow, hcol⟩
    refine ⟨?_, fun f hf => pd5_edgeBirthTwist_preserves_sym F S ρ w j W f hf⟩
    change MemOpNormLE F S (memoryCutoff S)
      (fun f => pd5_edgeBirthTwist F S ρ w j W (memorySym f)) (Real.rpow S.L Ccr)
    apply pd5_memOpNormLE_of_schur F S (memoryCutoff S)
      (fun f => pd5_edgeBirthTwist F S ρ w j W (memorySym f)) v (Real.rpow S.L Ccr)
      hv0 (Real.rpow_nonneg (le_trans (by norm_num) hL) _) hμ hrow hcol
    · intro s hs t ht
      exact pd5_twisted_edge_kernel_invalid F S ρ w j W s t hs ht
    · intro T f hf hT s hs hsize
      exact pd5_edge_supported_kernel F S ρ w j W T f hf hbox s


end
end ArtinPrimitiveRoots.TypeII.PD
