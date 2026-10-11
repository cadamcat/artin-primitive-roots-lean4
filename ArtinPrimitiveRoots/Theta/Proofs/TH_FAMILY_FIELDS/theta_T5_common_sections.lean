import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.Defs
import ArtinPrimitiveRoots.Vendor.TauCeti.NumberTheory.LocalField.PowerSubgroup.Open
import ArtinPrimitiveRoots.Vendor.TauCeti.NumberTheory.LocalField.PowerSubgroup.Basic
import ArtinPrimitiveRoots.Vendor.TauCeti.NumberTheory.LocalField.UnitFiltration.Basic
import ArtinPrimitiveRoots.Vendor.TauCeti.NumberTheory.LocalField.UnitFiltration.Pow
import Mathlib.Topology.Algebra.IsOpenUnits
import ArtinPrimitiveRoots.Vendor.TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

private theorem character_trivial_on_subgroup_of_near_one
    {G : Type} [Group G] (χ : G →* ℂˣ) (U : Subgroup G)
    (hunit : ∀ x ∈ U, ‖(χ x : ℂ)‖ = 1)
    (hnear : ∀ x ∈ U, ‖(χ x : ℂ) - 1‖ < 1) :
    ∀ x ∈ U, χ x = 1 := by
  intro x hx
  by_contra hχ
  have hxval : (χ x : ℂ) ≠ 1 := by
    intro h
    apply hχ
    exact Units.ext h
  let z : ℂ := (χ x : ℂ)
  have hz : z ≠ 1 := by simpa [z] using hxval
  have hzNorm : ‖z‖ = 1 := by simpa [z] using hunit x hx
  have hδ : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  obtain ⟨n, hn⟩ := exists_nat_gt (4 / ‖z - 1‖)
  have hnposR : (0 : ℝ) < (n : ℝ) := lt_trans (by positivity) hn
  have hnpos : 0 < n := by exact_mod_cast hnposR
  let S : ℂ := ∑ k ∈ Finset.range n, z ^ k
  have hterm (k : ℕ) : (1 / 2 : ℝ) < (z ^ k).re := by
    have hxk : x ^ k ∈ U := U.pow_mem hx k
    have hclose := hnear (x ^ k) hxk
    have hunitk := hunit (x ^ k) hxk
    have hpow : (χ (x ^ k) : ℂ) = z ^ k := by simp [z, map_pow]
    have hclose' : ‖z ^ k - 1‖ < 1 := by simpa [hpow] using hclose
    have hunit' : ‖z ^ k‖ = 1 := by simpa [hpow] using hunitk
    have hsquare := Complex.norm_sub_one_sq_eq_of_norm_eq_one hunit'
    have hnonneg : 0 ≤ ‖z ^ k - 1‖ := norm_nonneg _
    nlinarith
  have hsumTerms : (n : ℝ) / 2 < ∑ k ∈ Finset.range n, (z ^ k).re := by
    have hsum := Finset.sum_lt_sum
      (s := Finset.range n)
      (fun k _ => (hterm k).le)
      ⟨0, Finset.mem_range.mpr hnpos, hterm 0⟩
    simpa [div_eq_mul_inv] using hsum
  have hsumRe : S.re = ∑ k ∈ Finset.range n, (z ^ k).re := by
    simp [S, Complex.re_sum]
  have hsum : (n : ℝ) / 2 < S.re := by rw [hsumRe]; exact hsumTerms
  have hgeom : S * (z - 1) = z ^ n - 1 := by
    simpa [S] using (geom_sum_mul z n)
  have hnormGeom : ‖S‖ * ‖z - 1‖ = ‖z ^ n - 1‖ := by
    rw [← norm_mul, hgeom]
  have hpowNorm : ‖z ^ n‖ = 1 := by rw [norm_pow, hzNorm, one_pow]
  have htri : ‖z ^ n - 1‖ ≤ 2 := by
    calc
      ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [hpowNorm]; norm_num
  have hprodBound : ‖S‖ * ‖z - 1‖ ≤ 2 := by rw [hnormGeom]; exact htri
  have hupper : ‖S‖ ≤ 2 * ‖z - 1‖⁻¹ := by
    calc
      ‖S‖ = (‖S‖ * ‖z - 1‖) * ‖z - 1‖⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hδ.ne', mul_one]
      _ ≤ 2 * ‖z - 1‖⁻¹ :=
        mul_le_mul_of_nonneg_right hprodBound (inv_nonneg.mpr (norm_nonneg _))
  have hn' : 4 * ‖z - 1‖⁻¹ < (n : ℝ) := by
    simpa [div_eq_mul_inv] using hn
  have hlarge : 2 * ‖z - 1‖⁻¹ < (n : ℝ) / 2 := by nlinarith [hn']
  have hlower : (n : ℝ) / 2 < ‖S‖ := lt_of_lt_of_le hsum (Complex.re_le_norm S)
  linarith

private def finiteUnitEmbed :
    (∀ v : S.Sf, (v.1.adicCompletion F)ˣ) →* S.FSˣ where
  toFun u :=
    { val := (fun v => (u v : v.1.adicCompletion F), fun _ => 1)
      inv := (fun v => ((u v)⁻¹ : v.1.adicCompletion F), fun _ => 1)
      val_inv := by
        apply Prod.ext
        · funext v
          simp
        · funext w
          simp
      inv_val := by
        apply Prod.ext
        · funext v
          simp
        · funext w
          simp }
  map_one' := by
    apply Units.ext
    apply Prod.ext
    · funext v
      simp
    · funext w
      simp
  map_mul' := by
    intro u u'
    apply Units.ext
    apply Prod.ext
    · funext v
      simp
    · funext w
      simp

private theorem continuous_finiteUnitEmbed :
    Continuous (fun u : ∀ v : S.Sf, (v.1.adicCompletion F)ˣ => finiteUnitEmbed u) := by
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun u : ∀ v : S.Sf, (v.1.adicCompletion F)ˣ =>
      (fun v => (u v : v.1.adicCompletion F), fun _ : InfinitePlace F => (1 : ℂ)))
    exact (continuous_pi fun v => Units.continuous_val.comp (continuous_apply v)).prodMk
      (show Continuous (fun _ : (∀ v : S.Sf, (v.1.adicCompletion F)ˣ) =>
        (fun _ : InfinitePlace F => (1 : ℂ))) from continuous_const)
  · change Continuous (fun u : ∀ v : S.Sf, (v.1.adicCompletion F)ˣ =>
      (fun v => ((u v)⁻¹ : v.1.adicCompletion F), fun _ : InfinitePlace F => (1 : ℂ)))
    refine (continuous_pi fun v => ?_).prodMk
      (show Continuous (fun _ : (∀ v : S.Sf, (v.1.adicCompletion F)ˣ) =>
        (fun _ : InfinitePlace F => (1 : ℂ))) from continuous_const)
    have heval : Continuous
        (fun u : ∀ i : S.Sf, (i.1.adicCompletion F)ˣ => u v) := continuous_apply v
    have hinv : Continuous (fun u : (v.1.adicCompletion F)ˣ =>
        ((u⁻¹ : (v.1.adicCompletion F)ˣ) : v.1.adicCompletion F)) :=
      Units.continuous_coe_inv
    convert hinv.comp heval using 1
    funext u
    exact (Units.val_inv_eq_inv_val (u v)).symm

private structure LocalSixthSubgroup (K : Type*) [Field K] [TopologicalSpace K]
    (v : Valuation K (WithZero (Multiplicative ℤ))) where
  U : Subgroup Kˣ
  open_U : IsOpen (U : Set Kˣ)
  compact_U : IsCompact (U : Set Kˣ)
  valued_one : ∀ u ∈ U, v (u : K) = 1
  sixth : U ≤ (powMonoidHom 6 : Kˣ →* Kˣ).range

private theorem exists_localSixthSubgroup_inside (v : S.Sf) (O :
    Set (v.1.adicCompletion F)ˣ) (hOopen : IsOpen O) (hOone : (1 : (v.1.adicCompletion F)ˣ) ∈ O) :
    ∃ U : LocalSixthSubgroup (v.1.adicCompletion F)
      (Valued.v : Valuation (v.1.adicCompletion F) (WithZero (Multiplicative ℤ))),
      (U.U : Set (v.1.adicCompletion F)ˣ) ⊆ O := by
  let K := v.1.adicCompletion F
  have h6 : (6 : K) ≠ 0 := by norm_num
  have hopen : IsOpen ((powMonoidHom 6 : Kˣ →* Kˣ).range : Set Kˣ) :=
    TauCeti.isOpen_range_powMonoidHom (n := 6) h6
  have hone : (1 : Kˣ) ∈ (powMonoidHom 6 : Kˣ →* Kˣ).range := by
    exact ⟨1, by simp⟩
  have hIopen : IsOpen (O ∩ (powMonoidHom 6 : Kˣ →* Kˣ).range) := hOopen.inter hopen
  have hIone : (1 : Kˣ) ∈ O ∩ (powMonoidHom 6 : Kˣ →* Kˣ).range := ⟨hOone, hone⟩
  obtain ⟨i, -, hi⟩ :=
    (TauCeti.hasBasis_nhds_one_unitFiltration (K := K)).mem_iff.mp (hIopen.mem_nhds hIone)
  let U : Subgroup Kˣ := TauCeti.unitFiltration K i
  have hUunit : ∀ u ∈ U, (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) (u : K) = 1 := by
    intro u hu
    have hu0 : u ∈ TauCeti.unitFiltration K 0 :=
      TauCeti.unitFiltration_antitone (K := K) (Nat.zero_le i) hu
    have hval := (TauCeti.mem_unitFiltration_zero (K := K) u).mp hu0
    have heq := ValuativeRel.isEquiv
      (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) (ValuativeRel.valuation K)
    exact heq.eq_one_iff_eq_one.mpr hval
  refine ⟨⟨U, TauCeti.isOpen_unitFiltration (K := K) i,
    TauCeti.isCompact_unitFiltration (K := K) i, hUunit, ?_⟩, ?_⟩
  · intro u hu
    exact (hi hu).2
  · intro u hu
    exact (hi hu).1

private theorem exists_common_local_neighborhood (𝓛 : Finset (SChar S)) :
    ∃ Uv : ∀ v : S.Sf, Set (v.1.adicCompletion F),
      (∀ v, IsOpen (Uv v)) ∧
      (∀ v, IsCompact (Uv v)) ∧
      (∀ v, (1 : v.1.adicCompletion F) ∈ Uv v) ∧
      (∀ v y, y ∈ Uv v → Valued.v y = 1) ∧
      (∀ v y, y ∈ Uv v →
        ∃ c : (v.1.adicCompletion F)ˣ,
          y = ((c ^ 6 : (v.1.adicCompletion F)ˣ) : v.1.adicCompletion F)) ∧
      (∀ L ∈ 𝓛, ∀ y : S.FSˣ,
        (∀ v, (y : S.FS).1 v ∈ Uv v) →
        (∀ w, (y : S.FS).2 w = 1) → L.L y = 1) := by
  classical
  let E : Type := ∀ v : S.Sf, (v.1.adicCompletion F)ˣ
  let W : Set E := ⋂ L ∈ 𝓛, {u | ((L.L (finiteUnitEmbed u) : ℂˣ) : ℂ) ∈ Metric.ball 1 1}
  have hWopen : IsOpen W := by
    apply isOpen_biInter_finset
    intro L hL
    exact Metric.isOpen_ball.preimage (L.cont.comp continuous_finiteUnitEmbed)
  have hWone : (1 : E) ∈ W := by
    simp [W, Metric.mem_ball]
  obtain ⟨O, hO, hBox⟩ := (isOpen_pi_iff'.mp hWopen) (1 : E) hWone
  have hsubExists : ∀ v : S.Sf,
      ∃ Q : LocalSixthSubgroup (v.1.adicCompletion F)
        (Valued.v : Valuation (v.1.adicCompletion F) (WithZero (Multiplicative ℤ))),
        (Q.U : Set (v.1.adicCompletion F)ˣ) ⊆ O v := by
    intro v
    exact exists_localSixthSubgroup_inside v (O v) (hO v).1 (hO v).2
  choose Q hQ using hsubExists
  let Uv : ∀ v : S.Sf, Set (v.1.adicCompletion F) := fun v =>
    Units.val '' ((Q v).U : Set (v.1.adicCompletion F)ˣ)
  have hopen (v : S.Sf) : IsOpen (Uv v) := by
    change IsOpen (Units.val '' ((Q v).U : Set (v.1.adicCompletion F)ˣ))
    letI : IsOpenUnits (v.1.adicCompletion F) := inferInstance
    exact IsOpenUnits.isOpenEmbedding_unitsVal.isOpenMap _ (Q v).open_U
  have hcompact (v : S.Sf) : IsCompact (Uv v) := by
    change IsCompact (Units.val '' ((Q v).U : Set (v.1.adicCompletion F)ˣ))
    exact (Q v).compact_U.image Units.continuous_val
  have hone (v : S.Sf) : (1 : v.1.adicCompletion F) ∈ Uv v := by
    exact ⟨1, (Q v).U.one_mem, by simp⟩
  have hunit (v : S.Sf) (y : v.1.adicCompletion F) (hy : y ∈ Uv v) :
      Valued.v y = 1 := by
    rcases hy with ⟨u, hu, rfl⟩
    exact (Q v).valued_one u hu
  have hsix (v : S.Sf) (y : v.1.adicCompletion F) (hy : y ∈ Uv v) :
      ∃ c : (v.1.adicCompletion F)ˣ,
        y = ((c ^ 6 : (v.1.adicCompletion F)ˣ) : v.1.adicCompletion F) := by
    rcases hy with ⟨u, hu, rfl⟩
    obtain ⟨c, hc⟩ := (Q v).sixth hu
    have hc' : c ^ 6 = u := by simpa [powMonoidHom_apply] using hc
    exact ⟨c, congrArg (fun z : (v.1.adicCompletion F)ˣ => (z : v.1.adicCompletion F)) hc'.symm⟩
  let H : Subgroup E := {
    carrier := {u | ∀ v, u v ∈ (Q v).U}
    one_mem' := by intro v; exact (Q v).U.one_mem
    mul_mem' := by
      intro u u' hu hu' v
      exact (Q v).U.mul_mem (hu v) (hu' v)
    inv_mem' := by
      intro u hu v
      exact (Q v).U.inv_mem (hu v)
  }
  have hkernel (L : SChar S) (hL : L ∈ 𝓛) (y : S.FSˣ)
      (hy : ∀ v, (y : S.FS).1 v ∈ Uv v) (hC : ∀ w, (y : S.FS).2 w = 1) :
      L.L y = 1 := by
    have hcoord_ne (v : S.Sf) : (y : S.FS).1 v ≠ 0 := by
      intro hz
      rcases hy v with ⟨u, hu, huy⟩
      have hv : Valued.v ((u : (v.1.adicCompletion F)ˣ) : v.1.adicCompletion F) = 1 :=
        (Q v).valued_one u hu
      rw [huy] at hv
      simp [hz] at hv
    let z : E := fun v => Units.mk0 ((y : S.FS).1 v) (hcoord_ne v)
    have hzH : z ∈ H := by
      intro v
      rcases hy v with ⟨u, hu, huy⟩
      have hz : z v = u := by
        apply Units.ext
        dsimp [z]
        exact huy.symm
      rw [hz]
      exact hu
    have hzbox : z ∈ Set.univ.pi O := by
      intro v _
      exact hQ v (hzH v)
    have hzW : z ∈ W := hBox hzbox
    have hnear : ∀ z' ∈ H,
        ‖((L.L (finiteUnitEmbed z' : S.FSˣ) : ℂˣ) : ℂ) - 1‖ < 1 := by
      intro z' hz'
      have hz'box : z' ∈ Set.univ.pi O := by
        intro v _
        exact hQ v (hz' v)
      have hz'W : z' ∈ W := hBox hz'box
      have hb : ((L.L (finiteUnitEmbed z') : ℂˣ) : ℂ) ∈ Metric.ball 1 1 :=
        (Set.mem_iInter₂.mp hz'W) L hL
      simpa [Metric.mem_ball, dist_eq_norm] using hb
    have htrivial := character_trivial_on_subgroup_of_near_one
      (L.L.comp finiteUnitEmbed) H
      (by intro z' hz'; exact L.unitary (finiteUnitEmbed z')) hnear
    have hzEq : finiteUnitEmbed z = y := by
      apply Units.ext
      apply Prod.ext
      · funext v
        rfl
      · funext w
        exact (hC w).symm
    rw [← hzEq]
    exact htrivial z hzH
  refine ⟨Uv, hopen, hcompact, hone, hunit, hsix, ?_⟩
  intro L hL y hy hC
  exact hkernel L hL y hy hC

private theorem exists_bigCellFamily (P : CoverPackage D S H A)
    (N : ThetaNormalizationInput P)
    (φ : ∀ v : S.Sf, v.1.adicCompletion F → (N.G.T v.1).V)
    (hφ : ∀ v, IsLocallyConstant (φ v))
    (hc : ∀ v, HasCompactSupport (φ v)) :
    ∃ Fam : AnalyticFamily P N.G N.μ, Fam.T0 = S.Sf ∧
      (∀ v : S.Sf, ∀ s, (Fam.sec s).f v.1 =
        bigCell (P.loc v.1) (N.G.T v.1) s (φ v)) ∧
      (∀ s w, w ∉ S.Sf → (Fam.sec s).f w = (N.Fam.sec s).f w) := by
  classical
  let updateAt := fun (Fam : AnalyticFamily P N.G N.μ) (v : S.Sf) =>
    Classical.choose (analyticFamily_bigCell_rtr Fam v.1 (φ v) (hφ v) (hc v) 1)
  have updateAt_spec (Fam : AnalyticFamily P N.G N.μ) (v : S.Sf) :
      ExteriorFamily Fam v.1 (updateAt Fam v) ∧
        ∀ s, ((updateAt Fam v).sec s).f v.1 =
          rtr 1 (bigCell (P.loc v.1) (N.G.T v.1) s (φ v)) :=
    Classical.choose_spec (analyticFamily_bigCell_rtr Fam v.1 (φ v) (hφ v) (hc v) 1)
  have build : ∀ l : List (S.Sf), l.Nodup →
      ∀ Fam0 : AnalyticFamily P N.G N.μ, Fam0.T0 = S.Sf →
      (∀ s w, w ∉ S.Sf → (Fam0.sec s).f w = (N.Fam.sec s).f w) →
      ∃ Fam : AnalyticFamily P N.G N.μ, Fam.T0 = S.Sf ∧
        (∀ v : S.Sf, v ∈ l → ∀ s, (Fam.sec s).f v.1 =
          bigCell (P.loc v.1) (N.G.T v.1) s (φ v)) ∧
        (∀ s w, w ∉ S.Sf → (Fam.sec s).f w = (N.Fam.sec s).f w) := by
    intro l
    induction l with
    | nil =>
        intro hnd Fam0 hlevel hext
        refine ⟨Fam0, hlevel, ?_, hext⟩
        intro v hv s
        simp at hv
    | cons v vs ih =>
        intro hnd Fam0 hlevel hext
        obtain ⟨hvnot, hndTail⟩ := List.nodup_cons.mp hnd
        obtain ⟨Ftail, hTailLevel, hTailCells, hTailExt⟩ :=
          ih hndTail Fam0 hlevel hext
        let Fnew := updateAt Ftail v
        have hUpdate := updateAt_spec Ftail v
        refine ⟨Fnew, ?_, ?_, ?_⟩
        · calc
            Fnew.T0 = insert v.1 Ftail.T0 := hUpdate.1.1
            _ = insert v.1 S.Sf := by rw [hTailLevel]
            _ = S.Sf := Finset.insert_eq_of_mem v.2
        · intro u hu s
          rcases List.mem_cons.mp hu with huv | huTail
          · have huEq : u = v := by simpa using huv
            subst u
            calc
              ((Fnew).sec s).f v.1 =
                  rtr 1 (bigCell (P.loc v.1) (N.G.T v.1) s (φ v)) := by
                    simpa [Fnew] using hUpdate.2 s
              _ = bigCell (P.loc v.1) (N.G.T v.1) s (φ v) := by
                    funext g
                    simp [rtr]
          · have hne : u.1 ≠ v.1 := by
              intro h
              have : u = v := Subtype.ext h
              subst u
              exact hvnot huTail
            rw [hUpdate.1.2 s u.1 hne]
            exact hTailCells u huTail s
        · intro s w hw
          have hne : w ≠ v.1 := by
            intro h
            subst w
            exact hw v.2
          rw [hUpdate.1.2 s w hne]
          exact hTailExt s w hw
  obtain ⟨Fam, hLevel, hCells, hExt⟩ :=
    build S.Sf.attach.toList (Finset.nodup_toList S.Sf.attach) N.Fam N.level
      (by intro s w hw; rfl)
  refine ⟨Fam, hLevel, ?_, hExt⟩
  intro v s
  exact hCells v (by simp) s

/-- Choose one product neighborhood in sixth powers and all character kernels, and its analytic big-cell family.
Uses ThetaNormalizationInput, exists_T5_section and exists_continuedEis. -/
theorem theta_T5_common_sections (P : CoverPackage D S H A)
    (N : ThetaNormalizationInput P) (𝓛 : Finset (SChar S)) :
    Nonempty (ThetaCommonSections P N 𝓛) := by
  classical
  obtain ⟨Uv, hOpen, hCompact, hOne, hUnit, hSix, hCharacter⟩ :=
    exists_common_local_neighborhood (F := F) (S := S) 𝓛
  let localChoice (v : S.Sf) :=
    exists_T5_section (P.loc v.1) (N.G.T v.1) A (N.μ v.1) (1 / 6 : ℂ)
      (Uv v) (hCompact v) (hOpen v) (hUnit v) (hSix v) (N.x v)
  let φ : ∀ v : S.Sf, v.1.adicCompletion F → (N.G.T v.1).V :=
    fun v => Classical.choose (localChoice v)
  have hφ (v : S.Sf) : IsLocallyConstant (φ v) ∧ HasCompactSupport (φ v) ∧
      ∀ y : (v.1.adicCompletion F)ˣ,
        jacquet (P.loc v.1) A (N.μ v.1)
          (rtr ((P.loc v.1).a y)
            (bigCell (P.loc v.1) (N.G.T v.1) (1 / 6 : ℂ) (φ v))) =
          (Uv v).indicator (fun _ => N.x v) (y : v.1.adicCompletion F) :=
    Classical.choose_spec (localChoice v)
  obtain ⟨Fam, hLevel, hCells, hExterior⟩ := exists_bigCellFamily P N φ
    (fun v => (hφ v).1) (fun v => (hφ v).2.1)
  let C : ContinuedEis Fam := Classical.choice (exists_continuedEis Fam)
  refine ⟨{
    Uv := Uv
    open_Uv := hOpen
    compact_Uv := hCompact
    one_Uv := hOne
    unit_Uv := hUnit
    sixth_Uv := hSix
    character_kernel := hCharacter
    φ := φ
    locally_constant := fun v => (hφ v).1
    compact_support := fun v => (hφ v).2.1
    Fam := Fam
    C := C
    level := hLevel
    finite_section := fun s v => hCells v s
    exterior_section := hExterior
    jacquet_indicator := ?_
  }⟩
  intro v y
  rw [hCells v (1 / 6 : ℂ)]
  exact (hφ v).2.2 y
end ArtinPrimitiveRoots.A1.Theta
