import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.e_f.BadPrimeNorm
import Mathlib.Analysis.SpecialFunctions.Log.Summable

set_option autoImplicit false
set_option maxHeartbeats 800000
open NumberField IsDedekindDomain MeasureTheory Filter
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

private theorem finite_small_primes (Q : ℝ) (hQ : 0 ≤ Q) :
    {v : FinPlace F | qI v.asIdeal ≤ Q}.Finite := by
  apply Set.Finite.of_injOn (f := fun v : FinPlace F => v.asIdeal)
    (s := {v : FinPlace F | qI v.asIdeal ≤ Q})
    (t := {I : Ideal (𝓞 F) | Ideal.absNorm I ≤ ⌊Q⌋₊}) ?_ ?_
    (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊Q⌋₊)
  · intro v hv
    exact (Nat.le_floor_iff hQ).mpr hv
  · intro v hv w hw heq
    exact HeightOneSpectrum.ext heq

private theorem norm_finsetProd {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∏ i ∈ s, f i‖ = ∏ i ∈ s, ‖f i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, norm_mul, ih]

theorem growth_from_low_bound (HC : EulerCorrection R η U) (C Q0 B0 : ℝ)
    (hb : HasPoHLocalBounds R η U C Q0) (hB0 : 0 < B0)
    (hlow : ∀ u v hv p, qI v.asIdeal ≤ Q0 → eulerNeighborhood p →
      ‖normalizedLocal R η U u v hv (p 0) (p 1) (p 2)‖ ≤ B0)
    (hs : ∀ u p, eulerNeighborhood p → Summable
      (fun v : {v : FinPlace F // v ∉ S.Sf} =>
        ‖normalizedLocal R η U u v.1 v.2 (p 0) (p 1) (p 2) - 1‖)) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 < B ∧
      ∀ u p, eulerNeighborhood p → ‖HC.H u p‖ ≤ B * U.q u ^ ε := by
  classical
  intro ε hε
  let P := {v : FinPlace F // v ∉ S.Sf}
  let g : P → ℝ := fun v => C * qI v.1.asIdeal ^ (-1 - 1 / 4000 : ℝ)
  let M := max 1 B0
  have hM : 1 ≤ M := le_max_left _ _
  have hC : 0 < C := hb.1
  have hQ0 : 1 < Q0 := hb.2.1
  have hgn (v : P) : 0 ≤ g v := by
    exact mul_nonneg hC.le (Real.rpow_nonneg (lt_trans zero_lt_one
      (qI_prime_gt_one v.1)).le _)
  have hpinj : Function.Injective (fun v : P => R.exterior.prime v.1 v.2) := by
    intro v w heq
    apply Subtype.ext
    apply HeightOneSpectrum.asIdeal_injective
    simpa only [R.exterior.prime_val] using congrArg (fun I : S.ExtIdeal => I.1) heq
  have hg : Summable g := by
    have h := (a2_bridge_COUNT_summable S (1 + 1 / 4000) (by norm_num)).comp_injective hpinj
    have he : -(1 + 1 / 4000 : ℝ) = -1 - 1 / 4000 := by ring
    have h' : Summable (fun v : P => qI v.1.asIdeal ^ (-(1 + 1 / 4000 : ℝ))) := by
      simpa only [Function.comp_def, idealNorm, qI, R.exterior.prime_val,
        Real.rpow_eq_pow] using h
    simpa only [g, he] using h'.mul_left C
  have hfinite : {v : P | qI v.1.asIdeal ≤ Q0}.Finite := by
    exact (finite_small_primes Q0 (by linarith)).preimage Subtype.coe_injective.injOn
  let small : Finset P := hfinite.toFinset
  let L := M ^ small.card
  let G := Real.exp (∑' v, g v)
  obtain ⟨K, hK, hsmallProd⟩ := a2_bridge_SMALL_PRIME_decay (F := F)
    C (1 / 4000) hC.le (by norm_num) ε hε
  have hKpos : 0 < K := by linarith
  have hLpos : 0 < L := pow_pos (by linarith) _
  have hGpos : 0 < G := Real.exp_pos _
  refine ⟨L * G * K, by positivity, ?_⟩
  intro u p hp
  let n : P → ℂ := fun v => normalizedLocal R η U u v.1 v.2 (p 0) (p 1) (p 2)
  let a : P → ℝ := fun v => if qI v.1.asIdeal ≤ Q0 then M else 1
  let b : P → ℝ := fun v => if frequencyValuation η U u v.1 = 0 then 1
    else 1 + C * qI v.1.asIdeal ^ (-1 / 4000 : ℝ)
  have han (v : P) : 1 ≤ a v := by dsimp [a]; split_ifs <;> linarith
  have hbn (v : P) : 1 ≤ b v := by
    dsimp [b]
    split_ifs
    · exact le_rfl
    · have hn : 0 ≤ C * qI v.1.asIdeal ^ (-1 / 4000 : ℝ) :=
        mul_nonneg hC.le (Real.rpow_nonneg (lt_trans zero_lt_one
          (qI_prime_gt_one v.1)).le _)
      linarith
  have hen (v : P) : 1 ≤ Real.exp (g v) := Real.one_le_exp_iff.mpr (hgn v)
  have hpoint (v : P) : ‖n v‖ ≤ a v * Real.exp (g v) * b v := by
    by_cases hq : qI v.1.asIdeal ≤ Q0
    · have hn := hlow u v.1 v.2 p hq hp
      have hnm : ‖n v‖ ≤ M := hn.trans (le_max_right _ _)
      calc
        _ ≤ M := hnm
        _ ≤ M * Real.exp (g v) := by
          simpa using mul_le_mul_of_nonneg_left (hen v) (zero_le_one.trans hM)
        _ ≤ M * Real.exp (g v) * b v := by
          simpa using mul_le_mul_of_nonneg_left (hbn v)
            (mul_nonneg (zero_le_one.trans hM) (Real.exp_pos _).le)
        _ = _ := by simp [a, hq]
    · have hd := (hb.2.2 u v.1 v.2 p (lt_of_not_ge hq) hp).2
      have hn : ‖n v‖ ≤ 1 + C * qI v.1.asIdeal ^
          (if frequencyValuation η U u v.1 = 0 then (-1 - 1 / 4000 : ℝ)
            else (-1 / 4000 : ℝ)) := by
        have ht := norm_add_le (n v - 1) (1 : ℂ)
        simp only [sub_add_cancel, norm_one] at ht
        dsimp [n] at *
        linarith
      by_cases hj : frequencyValuation η U u v.1 = 0
      · simp only [hj, if_true] at hn
        calc
          _ ≤ 1 + g v := hn
          _ ≤ Real.exp (g v) := by simpa [add_comm] using Real.add_one_le_exp (g v)
          _ = _ := by simp [a, hq, b, hj]
      · simp only [hj, if_false] at hn
        calc
          _ ≤ b v := by simpa [b, hj] using hn
          _ ≤ Real.exp (g v) * b v := by
            simpa using mul_le_mul_of_nonneg_right (hen v) (zero_le_one.trans (hbn v))
          _ = _ := by simp [a, hq]
  have hApart (X : Finset P) : (∏ v ∈ X, a v) ≤ L := by
    let T := X.filter (fun v => qI v.1.asIdeal ≤ Q0)
    have hsub : T ⊆ small := by
      intro v hv
      exact hfinite.mem_toFinset.mpr (Finset.mem_filter.mp hv).2
    have heq : (∏ v ∈ X, a v) = M ^ T.card := by
      dsimp [a, T]
      rw [← Finset.prod_filter, Finset.prod_const]
    rw [heq]
    exact pow_le_pow_right₀ hM (Finset.card_le_card hsub)
  have hGpart (X : Finset P) : (∏ v ∈ X, Real.exp (g v)) ≤ G := by
    rw [← Real.exp_sum]
    exact Real.exp_le_exp.mpr (hg.sum_le_tsum X (fun v hv => hgn v))
  have hBpart (X : Finset P) : (∏ v ∈ X, b v) ≤ K * U.q u ^ ε := by
    let Xbad := X.filter (fun v => frequencyValuation η U u v.1 ≠ 0)
    let T : Finset (FinPlace F) := Xbad.image Subtype.val
    have hout : ∀ v ∈ T, v ∉ S.Sf := by
      intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      exact w.2
    have hbad : ∀ v ∈ T, frequencyValuation η U u v ≠ 0 := by
      intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hw).2
    have heq : (∏ v ∈ X, b v) =
        ∏ v ∈ T, (1 + C * qI v.asIdeal ^ (-1 / 4000 : ℝ)) := by
      rw [show T = Xbad.image Subtype.val by rfl, Finset.prod_image
        (fun v hv w hw heq => Subtype.coe_injective heq)]
      dsimp [Xbad, b]
      rw [Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro v hv
      by_cases hj : frequencyValuation η U u v.1 = 0 <;> simp [hj]
    rw [heq]
    calc
      _ ≤ K * (∏ v ∈ T, qI v.asIdeal) ^ ε := by
        simpa only [idealNorm, qI, neg_div, Real.rpow_eq_pow] using hsmallProd T
      _ ≤ K * U.q u ^ ε := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Finset.prod_nonneg (fun v hv =>
          (lt_trans zero_lt_one (qI_prime_gt_one v)).le))
          (bad_norm_product_le η U u T hout hbad) hε.le) hKpos.le
  have hpartial (X : Finset P) : ‖∏ v ∈ X, n v‖ ≤ (L * G * K) * U.q u ^ ε := by
    rw [norm_finsetProd]
    calc
      _ ≤ ∏ v ∈ X, (a v * Real.exp (g v) * b v) :=
        Finset.prod_le_prod₀ (fun v hv => norm_nonneg _) (fun v hv => hpoint v)
      _ = (∏ v ∈ X, a v) * (∏ v ∈ X, Real.exp (g v)) * (∏ v ∈ X, b v) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
      _ ≤ L * G * (K * U.q u ^ ε) := by
        exact mul_le_mul
          (mul_le_mul (hApart X) (hGpart X)
            (Finset.prod_nonneg (fun v hv => (Real.exp_pos _).le)) hLpos.le)
          (hBpart X) (Finset.prod_nonneg (fun v hv => zero_le_one.trans (hbn v)))
          (mul_nonneg hLpos.le hGpos.le)
      _ = _ := by ring
  have hm : Multipliable n := by
    have h := multipliable_one_add_of_summable (f := fun v : P => n v - 1) (hs u p hp)
    convert h using 1
    ext v
    ring
  have hprod : HasProd n (HC.H u p) := by
    rw [HC.H_eq]
    exact hm.hasProd
  have hlim := (continuous_norm.tendsto (HC.H u p)).comp hprod
  exact le_of_tendsto' hlim hpartial

end ArtinPrimitiveRoots.Proofs.e_f
