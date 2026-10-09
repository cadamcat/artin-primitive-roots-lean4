import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.e_f.LocalSectors
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.LocalParameterNorms

set_option autoImplicit false
set_option maxHeartbeats 800000
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.e_f
open ArtinPrimitiveRoots A1 A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
  (η : HeckeChar F) (U : FrequencyData S D η)

private theorem prime_norm_ge_two (v : FinPlace F) : 2 ≤ qI v.asIdeal := by
  change 2 ≤ (Ideal.absNorm v.asIdeal : ℝ)
  exact_mod_cast (Nat.succ_le_of_lt (NumberField.HeightOneSpectrum.one_lt_absNorm v))

private theorem geometric_rpow_summable (a : ℝ) (ha : a < 0) :
    Summable (fun n : ℕ => (2 : ℝ) ^ (a * (n : ℝ))) := by
  have h := summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) a)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) ha)
  exact h.congr (fun n => (Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2) a n).symm)

private def lowMajorant (Q0 : ℝ) (i : Fin 2 × ℕ × ℕ × ℕ) : ℝ :=
  Q0 ^ (1 / 2 : ℝ) *
    ((2 : ℝ) ^ (-(97 / 100 : ℝ) * (i.2.1 : ℝ)) *
      ((2 : ℝ) ^ (-(1 / 500 : ℝ) * (i.2.2.1 : ℝ)) *
        (2 : ℝ) ^ (-(95 / 100 : ℝ) * (i.2.2.2 : ℝ))))

private theorem lowMajorant_nonneg (Q0 : ℝ) (hQ0 : 0 ≤ Q0)
    (i : Fin 2 × ℕ × ℕ × ℕ) : 0 ≤ lowMajorant Q0 i := by
  unfold lowMajorant
  positivity

private theorem lowMajorant_summable (Q0 : ℝ) (hQ0 : 0 ≤ Q0) :
    Summable (lowMajorant Q0) := by
  let gL : ℕ → ℝ := fun n => (2 : ℝ) ^ (-(97 / 100 : ℝ) * (n : ℝ))
  let gK : ℕ → ℝ := fun n => (2 : ℝ) ^ (-(1 / 500 : ℝ) * (n : ℝ))
  let gM : ℕ → ℝ := fun n => (2 : ℝ) ^ (-(95 / 100 : ℝ) * (n : ℝ))
  have hL : Summable gL := geometric_rpow_summable _ (by norm_num)
  have hK : Summable gK := geometric_rpow_summable _ (by norm_num)
  have hM : Summable gM := geometric_rpow_summable _ (by norm_num)
  have hLn (n : ℕ) : 0 ≤ gL n := by dsimp [gL]; positivity
  have hKn (n : ℕ) : 0 ≤ gK n := by dsimp [gK]; positivity
  have hMn (n : ℕ) : 0 ≤ gM n := by dsimp [gM]; positivity
  have hKM := hK.mul_of_nonneg hM hKn hMn
  have hLKM := hL.mul_of_nonneg hKM hLn
    (fun km => mul_nonneg (hKn km.1) (hMn km.2))
  have hFin : Summable (fun _ : Fin 2 => Q0 ^ (1 / 2 : ℝ)) := Summable.of_finite
  exact hFin.mul_of_nonneg hLKM (fun _ => Real.rpow_nonneg hQ0 _)
    (fun lkm => mul_nonneg (hLn lkm.1) (mul_nonneg (hKn lkm.2.1) (hMn lkm.2.2)))

private theorem term_le_lowMajorant (Q0 : ℝ) (hQ0 : 1 < Q0)
    (u : U.U) (v : FinPlace F) (hv : v ∉ S.Sf) (p : Triple)
    (hp : eulerNeighborhood p) (hQ : qI v.asIdeal ≤ Q0)
    (i : Fin 2 × ℕ × ℕ × ℕ) :
    ‖localEulerTerm R η U u v hv (p 0) (p 1) (p 2) i‖ ≤ lowMajorant Q0 i := by
  have hξ : 99 / 100 < (p 0).re := by
    rcases hp with ⟨hξ, hw, hz⟩ | ⟨hξ, hw, hz⟩ <;> linarith
  have hw : 1 / 500 < (p 1).re := by
    rcases hp with ⟨hξ, hw, hz⟩ | ⟨hξ, hw, hz⟩ <;> linarith
  have hz : 95 / 100 < 6 * (p 2).re := by
    rcases hp with ⟨hξ, hw, hz⟩ | ⟨hξ, hw, hz⟩ <;> linarith
  let q := qI v.asIdeal
  have hq₂ : 2 ≤ q := prime_norm_ge_two v
  have hq : 1 ≤ q := by linarith
  have hqpos : 0 < q := by linarith
  have hdecay (a b : ℝ) (hb : b ≤ 0) (hab : a ≤ b) : q ^ a ≤ (2 : ℝ) ^ b :=
    (Real.rpow_le_rpow_of_exponent_le hq hab).trans
      (Real.rpow_le_rpow_of_nonpos (by norm_num) hq₂ hb)
  have hL : q ^ ((i.2.1 : ℝ) * (2 - 3 * (p 0).re)) ≤
      (2 : ℝ) ^ (-(97 / 100 : ℝ) * (i.2.1 : ℝ)) := by
    apply hdecay
    · nlinarith [Nat.cast_nonneg (α := ℝ) i.2.1]
    · nlinarith [Nat.cast_nonneg (α := ℝ) i.2.1]
  have hK : q ^ (-(i.2.2.1 : ℝ) * (p 1).re) ≤
      (2 : ℝ) ^ (-(1 / 500 : ℝ) * (i.2.2.1 : ℝ)) := by
    apply hdecay
    · nlinarith [Nat.cast_nonneg (α := ℝ) i.2.2.1]
    · nlinarith [Nat.cast_nonneg (α := ℝ) i.2.2.1]
  have hM : q ^ (-6 * (i.2.2.2 : ℝ) * (p 2).re) ≤
      (2 : ℝ) ^ (-(95 / 100 : ℝ) * (i.2.2.2 : ℝ)) := by
    apply hdecay
    · nlinarith [Nat.cast_nonneg (α := ℝ) i.2.2.2]
    · nlinarith [Nat.cast_nonneg (α := ℝ) i.2.2.2]
  have hS : q ^ (1 / 2 : ℝ) ≤ Q0 ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow hqpos.le hQ (by norm_num)
  calc
    _ ≤ q ^ (1 / 2 + (i.2.1 : ℝ) * (2 - 3 * (p 0).re) -
        (i.2.2.1 : ℝ) * (p 1).re - 6 * (i.2.2.2 : ℝ) * (p 2).re) :=
      term_norm_le R η U u v hv (p 0) (p 1) (p 2) (by linarith) i
    _ = q ^ (1 / 2 : ℝ) *
        (q ^ ((i.2.1 : ℝ) * (2 - 3 * (p 0).re)) *
          (q ^ (-(i.2.2.1 : ℝ) * (p 1).re) *
            q ^ (-6 * (i.2.2.2 : ℝ) * (p 2).re))) := by
      rw [← Real.rpow_add hqpos, ← Real.rpow_add hqpos, ← Real.rpow_add hqpos]
      congr 1
      ring
    _ ≤ lowMajorant Q0 i := by
      unfold lowMajorant
      gcongr

theorem low_prime_bound (Q0 : ℝ) (hQ0 : 1 < Q0) (hE : EulerHypotheses R η) :
    ∃ B : ℝ, 0 < B ∧ ∀ u v hv p, qI v.asIdeal ≤ Q0 → eulerNeighborhood p →
      ‖normalizedLocal R η U u v hv (p 0) (p 1) (p 2)‖ ≤ B := by
  let M := ∑' i, lowMajorant Q0 i
  let d := 1 - (2 : ℝ) ^ (-(99 / 100 : ℝ))
  have hQ0pos : 0 < Q0 := by linarith
  have hd : 0 < d := by
    dsimp [d]
    exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  have hM : 0 ≤ M := tsum_nonneg (lowMajorant_nonneg Q0 hQ0pos.le)
  refine ⟨4 / d * (M + 1), by positivity, ?_⟩
  intro u v hv p hQ hp
  have hξ : 99 / 100 < (p 0).re := by
    rcases hp with ⟨hξ, hw, hz⟩ | ⟨hξ, hw, hz⟩ <;> linarith
  have hw : 0 < (p 1).re := by
    rcases hp with ⟨hξ, hw, hz⟩ | ⟨hξ, hw, hz⟩ <;> linarith
  have hz : 0 < (p 2).re := by
    rcases hp with ⟨hξ, hw, hz⟩ | ⟨hξ, hw, hz⟩ <;> linarith
  have hL : ‖localEuler R η U u v hv (p 0) (p 1) (p 2)‖ ≤ M :=
    tsum_of_norm_bounded (lowMajorant_summable Q0 hQ0pos.le).hasSum
      (term_le_lowMajorant R η U Q0 hQ0 u v hv p hp hQ)
  obtain ⟨hV, hW, hD, hEv⟩ := a2_euler_sol.local_parameter_norms R η U hE u v hv
    (p 0) (p 1) (p 2)
  have hq := (qI_prime_gt_one v).le
  have hq₂ := prime_norm_ge_two v
  have hqpos : 0 < qI v.asIdeal := by linarith
  have hV1 : ‖localV v (p 2)‖ ≤ 1 := hV.trans
    (Real.rpow_le_one_of_one_le_of_nonpos hq (by linarith))
  have hW1 : ‖localWvar η U u v (p 1)‖ ≤ 1 := hW.trans
    (Real.rpow_le_one_of_one_le_of_nonpos hq (by linarith))
  have hD1 : ‖localDvar η U u v (p 0)‖ ≤ (2 : ℝ) ^ (-(99 / 100 : ℝ)) :=
    hD.trans ((Real.rpow_le_rpow_of_exponent_le hq (by linarith)).trans
      (Real.rpow_le_rpow_of_nonpos (by norm_num) hq₂ (by norm_num)))
  have hV2 : ‖1 - localV v (p 2)‖ ≤ 2 := by
    have ht := norm_sub_le (1 : ℂ) (localV v (p 2))
    norm_num at ht
    linarith
  have hW2 : ‖1 - localWvar η U u v (p 1)‖ ≤ 2 := by
    have ht := norm_sub_le (1 : ℂ) (localWvar η U u v (p 1))
    norm_num at ht
    linarith
  have hDen : d ≤ ‖1 - localDvar η U u v (p 0)‖ := by
    have ht := norm_sub_norm_le (1 : ℂ) (localDvar η U u v (p 0))
    norm_num at ht
    dsimp [d]
    linarith
  have hNum : ‖1 - localV v (p 2)‖ * ‖1 - localWvar η U u v (p 1)‖ ≤ 4 := by
    calc
      _ ≤ 2 * 2 := mul_le_mul hV2 hW2 (norm_nonneg _) (by norm_num)
      _ = 4 := by norm_num
  have hDiv : ‖1 - localV v (p 2)‖ * ‖1 - localWvar η U u v (p 1)‖ /
      ‖1 - localDvar η U u v (p 0)‖ ≤ 4 / d := by
    calc
      _ ≤ 4 / ‖1 - localDvar η U u v (p 0)‖ :=
        div_le_div_of_nonneg_right hNum (norm_nonneg _)
      _ ≤ 4 / d := div_le_div_of_nonneg_left (by norm_num) hd hDen
  rw [normalizedLocal, norm_mul, norm_div, norm_mul]
  calc
    _ ≤ 4 / d * M := mul_le_mul hDiv hL (norm_nonneg _) (by positivity)
    _ ≤ 4 / d * (M + 1) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end ArtinPrimitiveRoots.Proofs.e_f
