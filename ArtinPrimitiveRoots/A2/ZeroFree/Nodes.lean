import ArtinPrimitiveRoots.A2.ZeroFree.Results
import ArtinPrimitiveRoots.A2.FSide
import ArtinPrimitiveRoots.A2.Proofs.«A2-ZERO-SHIFT».ReciprocalBridge
import ArtinPrimitiveRoots.A2.Proofs.A2_ZERO_DETECT.Detect
import ArtinPrimitiveRoots.A2.Proofs.«A2-FE-GLUE».CharacterBridge
import ArtinPrimitiveRoots.A2.Proofs.«A2-FE-GLUE».GammaRatio
import ArtinPrimitiveRoots.A2.Proofs.«A2-FE-GLUE».ConvexityPartial
import ArtinPrimitiveRoots.A2.Proofs.ZF_CONVEXITY.GammaReal
import ArtinPrimitiveRoots.Hecke.Dedekind
import ArtinPrimitiveRoots.Hecke.Convexity
import ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_fe_export_to_ext_hecke_continuation
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.Hadamard
import OAI.NumberTheory.DirichletL.GammaZeroDetector
import OAI.NumberTheory.DirichletL.LogarithmicControl

/-!
# Section 6: conductor growth, convexity, and zero detection
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open NumberField.Units Filter MeasureTheory Asymptotics
open scoped Classical
open scoped Topology

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- **zf:convexity** (06-zero-free.tex:139-163): the conductor-uniform Hecke convexity bound,
with the number-field-dependent height exponent chosen before `ε`. Uses the corrected nonzero
primitive-conductor predicate from rev-a2. -/
theorem zf_convexity :
    ∃ A_F : ℝ, 0 < A_F ∧
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
        ∀ (ω : ArtinPrimitiveRoots.A1.HeckeChar F), IsOfFinOrder ω → ω ≠ 1 →
          ∀ 𝔣 : Ideal (𝓞 F), IsPrimitiveConductor ω 𝔣 →
            ∀ Λ : ℂ → ℂ,
              Differentiable ℂ Λ ∧
              (∀ s : ℂ, 1 < s.re → Λ s = heckeLSeries ω s) →
              (∀ s : ℂ, 3 / 1000 ≤ s.re → s.re ≤ 4 →
                ‖Λ s‖ ≤ C * Real.rpow (Ideal.absNorm 𝔣 : ℝ) (1 / 2 + ε) *
                  Real.rpow (2 + |s.im|) A_F) ∧
              (∀ s : ℂ, 3 / 1000 ≤ s.re → s.re ≤ 4 →
                ‖(s - 1) * NumberField.dedekindZeta F s‖ ≤
                  C * Real.rpow (2 + |s.im|) A_F) := by
  by_cases hTC : IsTotallyComplex F
  · exact ArtinPrimitiveRoots.Proofs.A2FreqP.zf_convexity_totallyComplex hTC
  · sorry

/-- Convert zf:convexity (06:139-163) to the exact growth hypothesis used in the corrected
detector statements; the chosen height exponent remains the same. -/
theorem zf_convexity_growth_bound :
    ∃ A_F : ℝ, 0 < A_F ∧ ConductorHeightBound (F := F) A_F := by
  obtain ⟨A_F, hAF, hconv⟩ := zf_convexity (F := F)
  refine ⟨A_F, hAF, ?_⟩
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := hconv ε hε
  refine ⟨C, hC, ?_⟩
  intro ω hω hnon 𝔣 h𝔣 L s hleft hright
  have hL := hbound ω hω hnon 𝔣 h𝔣 L.value
    ⟨L.differentiable, L.agrees⟩
  exact hL.1 s hleft hright

/-- **zf:row-conductor-family** (06-zero-free.tex:13-30): dyadic frequency rows have linear
count, conductor `O(q_u)`, pairwise distinct primitive twists, and only finitely many fixed
S-components. Corrected per rev-a2 to require the quantitative frequency hypotheses; its adapter
from the complete `FrequencyData` dictionary is proved in this declaration. -/
theorem zf_row_conductor_family
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (η : ArtinPrimitiveRoots.A1.HeckeChar F) (hη : IsOfFinOrder η)
    (fd : FrequencyData S D η) :
    ∃ Ccount Ccond : ℝ, 0 < Ccount ∧ 0 < Ccond ∧
      ∃ 𝓛S : Finset (SLocalCharacter S),
        ∀ U : ℝ, 2 ≤ U →
          (∀ E : Finset fd.U, (∀ u ∈ E, U ≤ fd.q u ∧ fd.q u < 2 * U) →
            (E.card : ℝ) ≤ Ccount * U) ∧
          (∀ u, U ≤ fd.q u → fd.q u < 2 * U →
            ∃ 𝔣 : Ideal (𝓞 F), IsPrimitiveConductor (fd.omega u) 𝔣 ∧
              (Ideal.absNorm 𝔣 : ℝ) ≤ Ccond * U ∧
              SComponent S (fd.omega u) ∈ 𝓛S) ∧
          (∀ u v, U ≤ fd.q u → fd.q u < 2 * U →
            U ≤ fd.q v → fd.q v < 2 * U → fd.omega u = fd.omega v → u = v) ∧
              (∀ u, fd.kummer u = 1 ↔ u = fd.one) := by
  obtain ⟨Ccount, hCcount, hcount⟩ := fd.dyadic_count
  obtain ⟨Cf, hCf, hcond⟩ := fd.conductor_bound
  obtain ⟨LS, hLS⟩ := fd.local_components_finite
  refine ⟨Ccount, 2 * Cf, hCcount, by positivity, LS, ?_⟩
  intro U hU
  obtain ⟨hfinite, hbound⟩ := hcount U hU
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro E hE
    let shell : Set fd.U := {u | U ≤ fd.q u ∧ fd.q u < 2 * U}
    have hsubset : (E : Set fd.U) ⊆ shell := by
      intro u hu
      exact hE u hu
    have hcardle := Set.ncard_le_ncard hsubset hfinite
    calc
      (E.card : ℝ) = (Set.ncard (E : Set fd.U) : ℝ) := by simp
      _ ≤ (Set.ncard shell : ℝ) := by exact_mod_cast hcardle
      _ ≤ Ccount * U := hbound
  · intro u hu hu2
    obtain ⟨f, hprim, hnorm⟩ := hcond u
    refine ⟨f, hprim, ?_, hLS u⟩
    calc
      (Ideal.absNorm f : ℝ) ≤ Cf * fd.q u := hnorm
      _ ≤ Cf * (2 * U) := by nlinarith [hCf]
      _ = (2 * Cf) * U := by ring
  · intro u v hu hu2 hv hv2 heq
    exact fd.omega_injective u v heq
  · exact fd.kummer_principal_iff

/-- **ext:ideal-count** (06-zero-free.tex:144): the number of integral ideals of norm at most
`t` is `O_F(t)`. -/
theorem ext_ideal_count :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊t⌋₊).toFinset.card : ℝ) ≤ C * t := by
  classical
  let L : ℝ :=
    (2 ^ NumberField.InfinitePlace.nrRealPlaces F *
        (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces F *
        regulator F * NumberField.classNumber F) /
      (torsionOrder F * Real.sqrt |NumberField.discr F|)
  have hlim : Filter.Tendsto
      (fun s : ℝ =>
        (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I ≤ s} : ℝ) / s)
      Filter.atTop (𝓝 L) := by
    simpa [L] using (Ideal.tendsto_norm_le_div_atTop F)
  have hcard (t : ℝ) (ht : 0 ≤ t) :
      ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊t⌋₊).toFinset.card : ℝ) =
        (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I ≤ t} : ℝ) := by
    have hsub :
        {I : Ideal (𝓞 F) // Ideal.absNorm I ≤ t} ≃
          {I : Ideal (𝓞 F) // Ideal.absNorm I ≤ ⌊t⌋₊} :=
      Equiv.subtypeEquivRight fun I => by
        exact (Nat.le_floor_iff ht).symm
    have hset :
        ({I : Ideal (𝓞 F) | Ideal.absNorm I ≤ ⌊t⌋₊} : Set (Ideal (𝓞 F))).Finite :=
      Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊t⌋₊
    have hnat :
        Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I ≤ ⌊t⌋₊} =
          (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊t⌋₊).toFinset.card := by
      change Nat.card ({I : Ideal (𝓞 F) | Ideal.absNorm I ≤ ⌊t⌋₊} : Set (Ideal (𝓞 F))) = _
      rw [Nat.card_coe_set_eq,
        Set.ncard_eq_toFinset_card
          ({I : Ideal (𝓞 F) | Ideal.absNorm I ≤ ⌊t⌋₊} : Set (Ideal (𝓞 F))) hset]
    calc
      _ = (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I ≤ ⌊t⌋₊} : ℝ) := by
        exact_mod_cast hnat.symm
      _ = _ := by exact_mod_cast (Nat.card_congr hsub).symm
  have hnear_event : ∀ᶠ s : ℝ in Filter.atTop,
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I ≤ s} : ℝ) / s ∈ Metric.ball L 1 :=
    hlim.eventually (Metric.ball_mem_nhds L (by norm_num : (0 : ℝ) < 1))
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 hnear_event
  let T₀ : ℝ := max T 1
  let B₀ : ℝ :=
    ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊T₀⌋₊).toFinset.card : ℝ)
  let C : ℝ := max (|L| + 2) (B₀ + 1)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro t ht
    by_cases hTt : T ≤ t
    · have hnear := hT t hTt
      have hnear' : |(Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I ≤ t} : ℝ) / t - L| < 1 := by
        simpa only [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hnear
      have hratio :
          (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I ≤ t} : ℝ) / t ≤ |L| + 1 := by
        rcases abs_lt.mp hnear' with ⟨_, hright⟩
        linarith [le_abs_self L]
      have ht0 : 0 ≤ t := le_trans (by norm_num) ht
      have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
      have hC : |L| + 1 ≤ C := by dsimp [C]; linarith [le_max_left (|L| + 2) (B₀ + 1)]
      have hmul := mul_le_mul_of_nonneg_right (hratio.trans hC) ht0
      calc
        ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊t⌋₊).toFinset.card : ℝ) =
            (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I ≤ t} : ℝ) := hcard t ht0
        _ = ((Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I ≤ t} : ℝ) / t) * t := by
          field_simp
        _ ≤ C * t := hmul
    · have hlt : t < T := lt_of_not_ge hTt
      have htT : t ≤ T₀ := by dsimp [T₀]; exact le_trans hlt.le (le_max_left T 1)
      have hfloor : ⌊t⌋₊ ≤ ⌊T₀⌋₊ := Nat.floor_mono htT
      have hfinset :
          (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊t⌋₊).toFinset ⊆
            (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊T₀⌋₊).toFinset := by
        intro I hI
        simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hI ⊢
        exact hI.trans hfloor
      have hcount :
          ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊t⌋₊).toFinset.card : ℝ) ≤ B₀ := by
        dsimp [B₀]
        exact_mod_cast (Finset.card_le_card hfinset)
      have hC : B₀ ≤ C := by dsimp [C]; exact le_max_of_le_right (le_of_lt (by linarith))
      have hmul := le_trans hcount hC
      exact hmul.trans (by nlinarith [ht, le_of_lt (by positivity : 0 < C)])

private theorem detector_ideal_rpow_partial_sum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
      (∑ I ∈ (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) X).toFinset,
        if I = ⊥ then 0 else Real.rpow (Ideal.absNorm I : ℝ) (-1 / 2)) ≤
          C * Real.sqrt X := by
  classical
  obtain ⟨Ccount, hCcount, hcount⟩ := ext_ideal_count (F := F)
  let q : ℝ := Real.sqrt 2
  have hqpos : 0 < q := by positivity
  have hqone : 1 < q := by
    dsimp [q]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  let C : ℝ := Ccount * 2 * q / (q - 1)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro X hX
    let Cut (n : ℕ) : Finset (Ideal (𝓞 F)) :=
      (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) n).toFinset
    let T : Finset (Ideal (𝓞 F)) := (Cut X).filter (fun I => I ≠ ⊥)
    let w (I : Ideal (𝓞 F)) : ℝ := Real.rpow (Ideal.absNorm I : ℝ) (-1 / 2)
    let m : ℕ := Nat.log 2 X
    have hXne : X ≠ 0 := by omega
    have hTsum :
        (∑ I ∈ Cut X, if I = ⊥ then 0 else w I) = ∑ I ∈ T, w I := by
      calc
        _ = ∑ I ∈ Cut X, if I ≠ ⊥ then w I else 0 := by
          apply Finset.sum_congr rfl
          intro I hI
          by_cases hbot : I = ⊥ <;> simp [hbot]
        _ = ∑ I ∈ T, w I := by
          simpa [T, Cut] using
            (Finset.sum_filter (s := Cut X) (p := fun I => I ≠ ⊥) (f := w)).symm
    have hmap : ∀ I ∈ T, Nat.log 2 (Ideal.absNorm I) ∈ Finset.range (m + 1) := by
      intro I hI
      have hmem := Finset.mem_filter.mp hI
      have hnormne : Ideal.absNorm I ≠ 0 := by
        intro hn
        exact hmem.2 (Ideal.absNorm_eq_zero_iff.mp hn)
      have hnormle : Ideal.absNorm I ≤ X := by
        simpa [Cut] using hmem.1
      have hpow : 2 ^ Nat.log 2 (Ideal.absNorm I) ≤ Ideal.absNorm I :=
        Nat.pow_log_le_self 2 hnormne
      have hlogle : Nat.log 2 (Ideal.absNorm I) ≤ m := by
        dsimp [m]
        exact Nat.le_log_of_pow_le Nat.one_lt_two (hpow.trans hnormle)
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le hlogle)
    have hfiber :
        (∑ k ∈ Finset.range (m + 1),
          ∑ I ∈ T with Nat.log 2 (Ideal.absNorm I) = k, w I) =
        ∑ I ∈ T, w I :=
      Finset.sum_fiberwise_of_maps_to hmap w
    have hqroot (k : ℕ) : q ^ k = Real.sqrt ((2 : ℝ) ^ k) := by
      induction k with
      | zero => simp [q]
      | succ k ih =>
        calc
          q ^ (k + 1) = q ^ k * q := by rw [pow_succ]
          _ = Real.sqrt ((2 : ℝ) ^ k) * Real.sqrt 2 := by rw [ih]
          _ = Real.sqrt ((2 : ℝ) ^ k * 2) :=
            (Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k) 2).symm
          _ = Real.sqrt ((2 : ℝ) ^ (k + 1)) := by rw [pow_succ]
    have hshell (k : ℕ) (hk : k ∈ Finset.range (m + 1)) :
        (∑ I ∈ T with Nat.log 2 (Ideal.absNorm I) = k, w I) ≤
          2 * Ccount * q ^ k := by
      let shell : Finset (Ideal (𝓞 F)) := T.filter
        (fun I => Nat.log 2 (Ideal.absNorm I) = k)
      let all : Finset (Ideal (𝓞 F)) :=
        (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F)
          ⌊(2 : ℝ) ^ (k + 1)⌋₊).toFinset
      have hsub : shell ⊆ all := by
        intro I hI
        have hmem := Finset.mem_filter.mp hI
        have hlt : Ideal.absNorm I < 2 ^ (k + 1) := by
          simpa [hmem.2] using
            (Nat.lt_pow_succ_log_self Nat.one_lt_two (Ideal.absNorm I))
        have hltReal : (Ideal.absNorm I : ℝ) < (2 : ℝ) ^ (k + 1) := by
          exact_mod_cast hlt
        have hnormleFloor : Ideal.absNorm I ≤ ⌊(2 : ℝ) ^ (k + 1)⌋₊ :=
          (Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (k + 1))).2 hltReal.le
        have hall : I ∈ all := by
          change I ∈ (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F)
            ⌊(2 : ℝ) ^ (k + 1)⌋₊).toFinset
          simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hnormleFloor
        simpa [all] using hall
      have hcard : (shell.card : ℝ) ≤ Ccount * (2 ^ (k + 1) : ℝ) := by
        have hcardNat : shell.card ≤ all.card := Finset.card_le_card hsub
        have hcardReal : (shell.card : ℝ) ≤ all.card := by exact_mod_cast hcardNat
        have hcountk := hcount ((2 : ℝ) ^ (k + 1))
          (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
        have hcountAll : (all.card : ℝ) ≤ Ccount * (2 ^ (k + 1) : ℝ) := by
          change ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F)
            ⌊(2 : ℝ) ^ (k + 1)⌋₊).toFinset.card : ℝ) ≤
              Ccount * ((2 : ℝ) ^ (k + 1))
          exact hcountk
        exact hcardReal.trans hcountAll
      have hweight (I : Ideal (𝓞 F)) (hI : I ∈ shell) :
          w I ≤ Real.rpow (2 ^ k : ℝ) (-1 / 2) := by
        have hmem := Finset.mem_filter.mp hI
        have hT := Finset.mem_filter.mp hmem.1
        have hnormpos : 0 < Ideal.absNorm I := by
          exact Nat.pos_of_ne_zero (by
            intro hn
            exact hT.2 (Ideal.absNorm_eq_zero_iff.mp hn))
        have hpowNat : 2 ^ k ≤ Ideal.absNorm I := by
          rw [← hmem.2]
          exact Nat.pow_log_le_self 2 (Nat.ne_of_gt hnormpos)
        have hpowReal : (2 : ℝ) ^ k ≤ (Ideal.absNorm I : ℝ) := by
          exact_mod_cast hpowNat
        dsimp [w]
        rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num]
        rw [Real.rpow_neg (by positivity : 0 ≤ (Ideal.absNorm I : ℝ)) (1 / 2),
          Real.rpow_neg (by positivity : 0 ≤ (2 : ℝ) ^ k) (1 / 2),
          ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
        simpa only [one_div] using
          (one_div_le_one_div_of_le (Real.sqrt_pos.2 (by positivity))
            (Real.sqrt_le_sqrt hpowReal))
      have hsum :
          (∑ I ∈ shell, w I) ≤
            (shell.card : ℝ) * Real.rpow (2 ^ k : ℝ) (-1 / 2) := by
        calc
          _ ≤ ∑ I ∈ shell, Real.rpow (2 ^ k : ℝ) (-1 / 2) :=
            Finset.sum_le_sum fun I hI => hweight I hI
          _ = _ := by simp
      have hprod :
          (2 ^ (k + 1) : ℝ) * Real.rpow (2 ^ k : ℝ) (-1 / 2) = 2 * q ^ k := by
        have hpowHalf : Real.rpow (2 ^ k : ℝ) (-1 / 2) = (q ^ k)⁻¹ := by
          calc
            Real.rpow (2 ^ k : ℝ) (-1 / 2) =
                (Real.rpow (2 ^ k : ℝ) (1 / 2))⁻¹ := by
              rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num]
              exact Real.rpow_neg (by positivity) (1 / 2)
            _ = (Real.sqrt ((2 : ℝ) ^ k))⁻¹ :=
              congrArg Inv.inv (Real.sqrt_eq_rpow _).symm
            _ = (q ^ k)⁻¹ := by rw [hqroot k]
        rw [pow_succ, hpowHalf]
        have hqpow : (q ^ k) ^ 2 = (2 : ℝ) ^ k := by
          calc
            (q ^ k) ^ 2 = q ^ (k * 2) := by rw [← pow_mul]
            _ = (q ^ 2) ^ k := by rw [Nat.mul_comm, pow_mul]
            _ = (2 : ℝ) ^ k := by
              rw [show q ^ 2 = 2 by dsimp [q]; exact Real.sq_sqrt (by norm_num)]
        have hqkpos : 0 < q ^ k := pow_pos hqpos k
        rw [← hqpow]
        field_simp [ne_of_gt hqkpos]
      calc
        _ = ∑ I ∈ shell, w I := by rfl
        _ ≤ _ := hsum.trans (mul_le_mul_of_nonneg_right hcard
          (Real.rpow_nonneg (by positivity) _))
        _ = 2 * Ccount * q ^ k := by rw [mul_assoc, hprod]; ring
    have hgeom :
        (∑ k ∈ Finset.range (m + 1), q ^ k) ≤ q ^ (m + 1) / (q - 1) := by
      have hgeomEq := geom_sum_mul_of_one_le (le_of_lt hqone) (m + 1)
      apply (le_div_iff₀ (sub_pos.mpr hqone)).2
      nlinarith [hgeomEq, pow_nonneg (le_of_lt hqpos) (m + 1)]
    have hpowUpper : 2 ^ (m + 1) ≤ 2 * X := by
      have hm : 2 ^ m ≤ X := Nat.pow_log_le_self 2 hXne
      rw [pow_succ]
      omega
    have hrootUpper : q ^ (m + 1) ≤ q * Real.sqrt X := by
      calc
        q ^ (m + 1) = Real.sqrt ((2 : ℝ) ^ (m + 1)) := hqroot (m + 1)
        _ ≤ Real.sqrt (2 * X) := by
          apply Real.sqrt_le_sqrt
          exact_mod_cast hpowUpper
        _ = q * Real.sqrt X := by
          dsimp [q]
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hsumBound : (∑ I ∈ T, w I) ≤ C * Real.sqrt X := by
      rw [← hfiber]
      calc
        _ ≤ ∑ k ∈ Finset.range (m + 1), 2 * Ccount * q ^ k :=
          Finset.sum_le_sum fun k hk => hshell k hk
        _ = 2 * Ccount * ∑ k ∈ Finset.range (m + 1), q ^ k := by rw [Finset.mul_sum]
        _ ≤ 2 * Ccount * (q ^ (m + 1) / (q - 1)) := by
          exact mul_le_mul_of_nonneg_left hgeom (by positivity)
        _ ≤ 2 * Ccount * (q * Real.sqrt X / (q - 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact div_le_div_of_nonneg_right hrootUpper (by positivity)
        _ = C * Real.sqrt X := by dsimp [C]; ring
    calc
      _ = ∑ I ∈ T, w I := hTsum
      _ ≤ C * Real.sqrt X := hsumBound

private theorem detector_mollifier_norm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : ℝ), 2 ≤ U →
      ∀ (ω : ArtinPrimitiveRoots.A1.HeckeChar F), IsOfFinOrder ω →
        ∀ s : ℂ, 1 / 2 ≤ s.re →
          ‖mollifier U ω.idealValue s‖ ≤ C * U := by
  obtain ⟨Cpartial, hCpartial, hpartial⟩ :=
    detector_ideal_rpow_partial_sum_bound (F := F)
  refine ⟨Cpartial, hCpartial, ?_⟩
  intro U hU ω hω s hs
  classical
  let X : ℕ := ⌊U ^ 2⌋₊
  let S : Finset (Ideal (𝓞 F)) :=
    (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) X).toFinset
  have hUpos : 0 < U := by linarith
  have hXone : 1 ≤ X := by
    have hU2 : (1 : ℝ) ≤ U ^ 2 := by nlinarith
    exact (Nat.le_floor_iff (show 0 ≤ U ^ 2 by positivity)).2 (by exact_mod_cast hU2)
  have hXle : (X : ℝ) ≤ U ^ 2 := by
    dsimp [X]
    exact Nat.floor_le (by positivity)
  have hroot : Real.sqrt (X : ℝ) ≤ U := by
    have hXnonneg : 0 ≤ (X : ℝ) := by positivity
    have hsquare := Real.sq_sqrt hXnonneg
    have hUnonneg : 0 ≤ U := le_of_lt hUpos
    nlinarith
  have hterm (I : Ideal (𝓞 F)) :
      ‖(idealMoebius I : ℂ) * ω.idealValue I *
          ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)‖ ≤
        if I = ⊥ then 0 else Real.rpow (Ideal.absNorm I : ℝ) (-1 / 2) := by
    by_cases hI : I = ⊥
    · simp [hI, ArtinPrimitiveRoots.A2.idealMoebius]
    · have hNnat : 0 < Ideal.absNorm I := by
        exact Ideal.absNorm_pos_of_nonZeroDivisors
          ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr (by
            simpa [Ideal.zero_eq_bot] using hI)⟩
      have hN : (1 : ℝ) ≤ (Ideal.absNorm I : ℝ) := by exact_mod_cast hNnat
      have hmu : ‖(idealMoebius I : ℂ)‖ ≤ 1 := by
        unfold ArtinPrimitiveRoots.A2.idealMoebius
        split_ifs <;> simp
      have hωI : ‖ω.idealValue I‖ ≤ 1 :=
        ArtinPrimitiveRoots.A2.Proofs.A2ZeroDetect.idealValue_norm_le_one_of_finOrder
          ω hω I
      have hpowNorm :
          ‖((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)‖ =
            Real.rpow (Ideal.absNorm I : ℝ) (-s.re) := by
        rw [← Complex.ofReal_natCast,
          Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hNnat)]
        simp
      have hpow :
          Real.rpow (Ideal.absNorm I : ℝ) (-s.re) ≤
            Real.rpow (Ideal.absNorm I : ℝ) (-1 / 2) := by
        apply Real.rpow_le_rpow_of_exponent_le hN
        linarith
      have hpowNonneg : 0 ≤ Real.rpow (Ideal.absNorm I : ℝ) (-s.re) :=
        Real.rpow_nonneg (by positivity) _
      rw [if_neg hI]
      calc
        _ = ‖(idealMoebius I : ℂ)‖ * ‖ω.idealValue I‖ *
              ‖((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)‖ := by simp [norm_mul, mul_assoc]
        _ ≤ 1 * 1 * Real.rpow (Ideal.absNorm I : ℝ) (-1 / 2) := by
          rw [hpowNorm]
          gcongr
        _ = _ := by ring
  have hsum :
      ‖mollifier U ω.idealValue s‖ ≤
        ∑ I ∈ S, if I = ⊥ then 0 else Real.rpow (Ideal.absNorm I : ℝ) (-1 / 2) := by
    unfold mollifier
    calc
      _ ≤ ∑ I ∈ S,
            ‖(idealMoebius I : ℂ) * ω.idealValue I *
              ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)‖ := norm_sum_le _ _
      _ ≤ _ := Finset.sum_le_sum fun I hI => hterm I
  have hpartialU := hpartial X hXone
  have hnormB :
      (∑ I ∈ S, if I = ⊥ then 0 else Real.rpow (Ideal.absNorm I : ℝ) (-1 / 2)) ≤
        Cpartial * U := by
    calc
      _ = (∑ I ∈ (Ideal.finite_setOfPred_absNorm_le
          (S := 𝓞 F) X).toFinset,
            if I = ⊥ then 0 else Real.rpow (Ideal.absNorm I : ℝ) (-1 / 2)) := by rfl
      _ ≤ Cpartial * Real.sqrt X := hpartialU
      _ ≤ Cpartial * U := mul_le_mul_of_nonneg_left hroot hCpartial.le
  exact hsum.trans hnormB

namespace Proofs.A2Z1
open Filter Topology
open scoped BigOperators Classical
open UniqueFactorizationMonoid

variable {F : Type} [Field F] [NumberField F]

private def divisorFinset (I : Ideal (𝓞 F)) : Finset (Ideal (𝓞 F)) :=
  (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) (Ideal.absNorm I)).toFinset.filter
    (fun J => J ∣ I)

private def divisorSupport (I : Ideal (𝓞 F)) : Finset (Ideal (𝓞 F)) :=
  (normalizedFactors I).toFinset

private def divisorCount (I : Ideal (𝓞 F)) : ℕ :=
  Set.ncard {J : Ideal (𝓞 F) | J ∣ I}

private lemma divisor_ne_bot {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ∣ I) : J ≠ ⊥ := by
  intro hz
  have hd : (0 : Ideal (𝓞 F)) ∣ I := by simpa [hz] using hJ
  rw [zero_dvd_iff] at hd
  exact hI hd

private lemma divisors_finset_card (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    divisorCount I = (divisorFinset I).card := by
  have hnormI : 0 < Ideal.absNorm I := by
    apply Nat.pos_iff_ne_zero.mpr
    intro h
    exact hI (Ideal.absNorm_eq_zero_iff.mp h)
  have hfinite : {J : Ideal (𝓞 F) | J ∣ I}.Finite := by
    refine (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) (Ideal.absNorm I)).subset ?_
    intro J hJ
    simp only [Set.mem_setOf_eq]
    exact Nat.le_of_dvd hnormI (map_dvd Ideal.absNorm hJ)
  have hfinset : hfinite.toFinset = divisorFinset I := by
    ext J
    simp only [divisorFinset, Set.Finite.mem_toFinset, Finset.mem_filter,
      Set.mem_ofPred_eq, Set.mem_setOf_eq]
    constructor
    · intro hJ
      exact ⟨Nat.le_of_dvd hnormI (map_dvd Ideal.absNorm hJ), hJ⟩
    · exact And.right
  unfold divisorCount
  rw [Set.ncard_eq_toFinset_card _ hfinite, hfinset]

private lemma divisor_card_le_factor_product (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    (divisorFinset I).card ≤
      ∏ P ∈ divisorSupport I, ((normalizedFactors I).count P + 1) := by
  change (divisorFinset I).card ≤
    ∏ P ∈ (normalizedFactors I).toFinset, ((normalizedFactors I).count P + 1)
  rw [← Multiset.card_Iic]
  apply Finset.card_le_card_of_injOn normalizedFactors
  · intro J hJ
    change normalizedFactors J ∈ Finset.Iic (normalizedFactors I)
    rw [Finset.mem_Iic]
    exact (dvd_iff_normalizedFactors_le_normalizedFactors
      (divisor_ne_bot hI (Finset.mem_filter.mp hJ).2) hI).mp
        (Finset.mem_filter.mp hJ).2
  · intro J hJ K hK he
    calc
      J = (normalizedFactors J).prod :=
        (Ideal.prod_normalizedFactors_eq_self
          (divisor_ne_bot hI (Finset.mem_filter.mp hJ).2)).symm
      _ = (normalizedFactors K).prod := congrArg Multiset.prod he
      _ = K := Ideal.prod_normalizedFactors_eq_self
        (divisor_ne_bot hI (Finset.mem_filter.mp hK).2)

private lemma support_prime {I P : Ideal (𝓞 F)} (hP : P ∈ divisorSupport I) : Prime P :=
  prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)

private lemma support_norm_two_le {I P : Ideal (𝓞 F)} (hP : P ∈ divisorSupport I) :
    2 ≤ Ideal.absNorm P := by
  have hp := support_prime hP
  have h0 : Ideal.absNorm P ≠ 0 := by
    intro h
    exact hp.ne_zero (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm P ≠ 1 := by
    intro h
    have ht := Ideal.absNorm_eq_one_iff.mp h
    apply hp.not_isUnit
    rw [ht]
    simpa only [Ideal.one_eq_top] using (show IsUnit (1 : Ideal (𝓞 F)) from isUnit_one)
  omega

private lemma norm_factor_product (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    (∏ P ∈ divisorSupport I,
      (Ideal.absNorm P : ℝ) ^ (normalizedFactors I).count P) =
      (Ideal.absNorm I : ℝ) := by
  have he := congrArg (fun J : Ideal (𝓞 F) => (Ideal.absNorm J : ℝ))
    (Ideal.prod_normalizedFactors_eq_self hI)
  rw [Finset.prod_multiset_count] at he
  simpa only [divisorSupport, map_prod, map_pow, Nat.cast_prod, Nat.cast_pow] using he

private lemma linear_le_geometric (b : ℝ) (hb : 1 < b) (n : ℕ) :
    (n : ℝ) + 1 ≤ (1 + (b - 1)⁻¹) * b ^ n := by
  have hδ : 0 < b - 1 := sub_pos.mpr hb
  have hn := one_add_mul_sub_le_pow (show (-1 : ℝ) ≤ b by linarith) n
  have hn' : (n : ℝ) ≤ b ^ n / (b - 1) := by
    apply (le_div_iff₀ hδ).mpr
    linarith
  have h1 : (1 : ℝ) ≤ b ^ n := one_le_pow₀ hb.le
  calc
    (n : ℝ) + 1 ≤ b ^ n / (b - 1) + b ^ n := add_le_add hn' h1
    _ = _ := by ring

/-- The usual small-power bound for the number of ideal divisors over any number field. -/
theorem ideal_divisor_count_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal (𝓞 F), I ≠ ⊥ →
      (Set.ncard {J : Ideal (𝓞 F) | J ∣ I} : ℝ) ≤ C * (Ideal.absNorm I : ℝ) ^ ε := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (ht.eventually (eventually_ge_atTop (2 : ℝ)))
  let small : Finset (Ideal (𝓞 F)) :=
    (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) N).toFinset
  let b : ℝ := (2 : ℝ) ^ ε
  have hb : 1 < b := by
    dsimp [b]
    exact Real.one_lt_rpow (by norm_num) hε
  let c : ℝ := 1 + (b - 1)⁻¹
  have hc : 1 ≤ c := by
    dsimp [c]
    have hi : 0 ≤ (b - 1)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hb.le)
    linarith
  refine ⟨c ^ small.card, by positivity, ?_⟩
  intro I hI
  let S := divisorSupport I
  let e := fun P : Ideal (𝓞 F) => (normalizedFactors I).count P
  have hfac (P : Ideal (𝓞 F)) (hP : P ∈ S) :
      ((e P + 1 : ℕ) : ℝ) ≤
        (if P ∈ small then c else 1) * ((Ideal.absNorm P : ℝ) ^ ε) ^ e P := by
    have hnorm : (2 : ℝ) ≤ Ideal.absNorm P := by exact_mod_cast support_norm_two_le hP
    have hbase : b ≤ (Ideal.absNorm P : ℝ) ^ ε :=
      Real.rpow_le_rpow (by norm_num) hnorm hε.le
    by_cases hp : P ∈ small
    · rw [ite_eq_left hp]
      have hlin := linear_le_geometric b hb (e P)
      have hl : ((e P + 1 : ℕ) : ℝ) ≤ c * b ^ e P := by
        simpa only [Nat.cast_add, Nat.cast_one, c] using hlin
      apply hl.trans
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hbase _) (by positivity)
    · rw [ite_eq_right hp, one_mul]
      have hn : N ≤ Ideal.absNorm P := by
        have : ¬ Ideal.absNorm P ≤ N := fun h => hp (by simpa [small] using h)
        omega
      have hp2 := hN _ hn
      calc
        _ ≤ (2 : ℝ) ^ e P := by
          have hh := one_add_mul_sub_le_pow (by norm_num : (-1 : ℝ) ≤ 2) (e P)
          norm_num at hh ⊢
          linarith
        _ ≤ _ := pow_le_pow_left₀ (by norm_num) hp2 _
  have hprod := Finset.prod_le_prod₀
    (fun P (_ : P ∈ S) => (by positivity : 0 ≤ ((e P + 1 : ℕ) : ℝ))) hfac
  have hconst : (∏ P ∈ S, if P ∈ small then c else 1) ≤ c ^ small.card := by
    have he : (∏ P ∈ S, if P ∈ small then c else 1) = c ^ (S ∩ small).card := by simp []
    rw [he]
    exact pow_le_pow_right₀ hc (Finset.card_le_card Finset.inter_subset_right)
  have hpow : (∏ P ∈ S, ((Ideal.absNorm P : ℝ) ^ ε) ^ e P) =
      (Ideal.absNorm I : ℝ) ^ ε := by
    calc
      _ = ∏ P ∈ S, ((Ideal.absNorm P : ℝ) ^ e P) ^ ε := by
        apply Finset.prod_congr rfl
        intro P hP
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
          ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        rw [mul_comm]
      _ = (∏ P ∈ S, (Ideal.absNorm P : ℝ) ^ e P) ^ ε :=
        Real.finsetProd_rpow S _ (fun _ _ => by positivity) ε
      _ = _ := by rw [norm_factor_product I hI]
  have hcard : ((divisorFinset I).card : ℝ) ≤
      ∏ P ∈ S, ((e P + 1 : ℕ) : ℝ) := by
    exact_mod_cast divisor_card_le_factor_product I hI
  have hcount : (divisorCount I : ℝ) ≤
      ∏ P ∈ S, ((e P + 1 : ℕ) : ℝ) := by
    rw [divisors_finset_card I hI]
    exact hcard
  have hfinal : (divisorCount I : ℝ) ≤
      c ^ small.card * (Ideal.absNorm I : ℝ) ^ ε := by
    apply hcount.trans
    rw [Finset.prod_mul_distrib, hpow] at hprod
    exact hprod.trans (mul_le_mul_of_nonneg_right hconst (by positivity))
  simpa [divisorCount] using hfinal

/-- The ideal Möbius function defined in FSide has norm at most one. -/
theorem ideal_moebius_norm_le_one (I : Ideal (𝓞 F)) :
    ‖(ArtinPrimitiveRoots.A2.idealMoebius I : ℂ)‖ ≤ 1 := by
  unfold ArtinPrimitiveRoots.A2.idealMoebius
  split_ifs <;> simp
end Proofs.A2Z1

/-- **ext:divisor-bound** (06-zero-free.tex:145): `τ_F(𝔫) ≪_{F,ε} N𝔫^ε`; the ideal Möbius
function is bounded by one. -/
theorem ext_divisor_bound :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ I : Ideal (𝓞 F), I ≠ ⊥ →
        (idealDivisorCount I : ℝ) ≤ C * Real.rpow (Ideal.absNorm I : ℝ) ε ∧
        ‖(idealMoebius I : ℂ)‖ ≤ 1 := by
  intro ε hε
  obtain ⟨C, hC, hdiv⟩ :=
    ArtinPrimitiveRoots.A2.Proofs.A2Z1.ideal_divisor_count_small_power (F := F) ε hε
  refine ⟨C, hC, ?_⟩
  intro I hI
  constructor
  · simpa [idealDivisorCount] using hdiv I hI
  · exact ArtinPrimitiveRoots.A2.Proofs.A2Z1.ideal_moebius_norm_le_one (F := F) I

/-- **ext:phragmen-lindelof** (Mathlib, `Analysis/Complex/PhragmenLindelof.lean:275`):
vertical-strip Phragmén–Lindelöf principle. -/
theorem ext_phragmen_lindelof {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {a b C : ℝ}
    (hfd : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hB : ∃ A B c : ℝ, c < Real.pi / (b - a) ∧
      ∀ z : ℂ, a < z.re → z.re < b →
        ‖f z‖ ≤ A * Real.exp (B * Real.exp (c * |z.im|)))
    (hle_a : ∀ z : ℂ, z.re = a → ‖f z‖ ≤ C)
    (hle_b : ∀ z : ℂ, z.re = b → ‖f z‖ ≤ C) :
    ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ C := by
  intro z hza hzb
  rcases hB with ⟨A, B, c, hc, hbound⟩
  apply PhragmenLindelof.vertical_strip hfd ?_ hle_a hle_b hza hzb
  refine ⟨c, hc, B, ?_⟩
  rw [Asymptotics.isBigO_iff]
  refine ⟨max A 0, ?_⟩
  have hS : ∀ᶠ w : ℂ in
      Filter.comap (fun z : ℂ => |z.im|) Filter.atTop ⊓
      Filter.principal (Complex.re ⁻¹' Set.Ioo a b),
      w ∈ Complex.re ⁻¹' Set.Ioo a b := by
    rw [Filter.eventually_inf_principal]
    exact Filter.Eventually.of_forall fun _ hw => hw
  filter_upwards [hS] with w hw
  have hz := hbound w (Set.mem_preimage.mp hw).1 (Set.mem_preimage.mp hw).2
  calc
    ‖f w‖ ≤ A * Real.exp (B * Real.exp (c * |w.im|)) := hz
    _ ≤ max A 0 * ‖Real.exp (B * Real.exp (c * |w.im|))‖ := by
      rw [Real.norm_eq_abs, Real.abs_exp]
      gcongr
      exact le_max_left _ _

/-- **zf:detector-shift** (06-zero-free.tex:226-264): a zero at `β+iγ` yields the smoothed
detector identity and the shifted-line bound with exponent `-3.46 + A_F ρ + ε`. -/
def detectorSmoothedSum (U β γ : ℝ) (ω : ArtinPrimitiveRoots.A1.HeckeChar F) : ℂ :=
  ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
    (detectorCoeff U I.1 : ℂ) * ω.idealValue I.1 *
      ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-(β + γ * Complex.I)) *
      Complex.exp (-((Ideal.absNorm I.1 : ℕ) : ℂ) / (U : ℂ) ^ 10)

/-- Vertical Mellin integral with the factor `dv = i dt` absorbed. -/
def verticalMellinIntegral (f : ℂ → ℂ) (c : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, f (c + t * Complex.I)

private theorem frequency_heckeLSeries_eq_ray
    (ω : ArtinPrimitiveRoots.A1.HeckeChar F) (hfin : IsOfFinOrder ω)
    (𝔣 : Ideal (𝓞 F)) (h𝔣 : IsPrimitiveConductor ω 𝔣) :
    ∃ m : ClassFieldTheory.RayClassModulus F,
      ∃ ψ : ClassFieldTheory.RayClassGroup m →* ℂˣ,
        ∀ s : ℂ, 1 < s.re → heckeLSeries ω s =
          ArtinPrimitiveRoots.Hecke.LSeriesRay ψ s := by
  classical
  obtain ⟨m, ψ, hm, -, hval⟩ :=
    ArtinPrimitiveRoots.Dictionary.exists_rayClass_of_heckeChar ω hfin 𝔣 h𝔣.1 h𝔣.2.1
  have hunr : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F,
      v ∉ m.finitePart.support → ω.UnramifiedAt v := by
    intro v hv
    refine ArtinPrimitiveRoots.A2.qsa_unramifiedAt_of_conductorDvd ω 𝔣 h𝔣.2.1 v ?_
    rw [← hm, ArtinPrimitiveRoots.Dictionary.idealExp_modulusIdeal]
    exact Finsupp.notMem_support_iff.mp hv
  have hseries : ∀ s : ℂ, 1 < s.re → heckeLSeries ω s =
      ArtinPrimitiveRoots.Hecke.LSeriesRay ψ s := by
    intro s hs
    refine ArtinPrimitiveRoots.A2.qsa_heckeLSeries_eq_LSeriesRay ω ψ ?_ hs
    intro I hI
    by_cases hcop : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m I
    · exact ArtinPrimitiveRoots.Dictionary.idealValue_eq_charValue ψ ω
        (fun v hv => ⟨hunr v hv, (hval v hv).symm⟩) I hcop
    · rw [ArtinPrimitiveRoots.Hecke.charValue, dif_neg hcop]
      have hex : ∃ v ∈ m.finitePart.support, v.asIdeal ∣ I := by
        by_contra hnot
        push_neg at hnot
        apply hcop
        refine ⟨hI, ?_⟩
        intro v hv
        simp only [ArtinPrimitiveRoots.Hecke.idealUnit, Units.val_mk0]
        rw [FractionalIdeal.count_coe F v hI]
        have hcount :=
          (Associates.count_ne_zero_iff_dvd hI v.irreducible).not.mpr (hnot v hv)
        push_neg at hcount
        exact_mod_cast hcount
      obtain ⟨v, hv, hvI⟩ := hex
      have hv𝔣 : v.asIdeal ∣ 𝔣 := by
        rw [← hm]
        unfold ArtinPrimitiveRoots.Dictionary.modulusIdeal
        have hpos : m.finitePart v ≠ 0 := Finsupp.mem_support_iff.mp hv
        exact (dvd_pow_self v.asIdeal hpos).trans
          (Finset.dvd_prod_of_mem (fun w => w.asIdeal ^ m.finitePart w) hv)
      exact ArtinPrimitiveRoots.A2.qs_idealValue_eq_zero_of_conductor_M0
        ω 𝔣 h𝔣 v.asIdeal I v.isPrime v.ne_bot hv𝔣 hI hvI
  exact ⟨m, ψ, hseries⟩

private theorem detector_zero_real_le_one
    (ω : ArtinPrimitiveRoots.A1.HeckeChar F) (hfin : IsOfFinOrder ω)
    (𝔣 : Ideal (𝓞 F)) (h𝔣 : IsPrimitiveConductor ω 𝔣)
    (L : HeckeLContinuation ω) {s : ℂ} (hz : L.value s = 0) : s.re ≤ 1 := by
  by_contra hnot
  have hs : 1 < s.re := lt_of_not_ge hnot
  obtain ⟨m, ψ, hseries⟩ := frequency_heckeLSeries_eq_ray ω hfin 𝔣 h𝔣
  have hnonzero := (ArtinPrimitiveRoots.Hecke.norm_LSeriesRay_le ψ hs).2.1
  apply hnonzero
  calc
    ArtinPrimitiveRoots.Hecke.LSeriesRay ψ s = heckeLSeries ω s := (hseries s hs).symm
    _ = L.value s := (L.agrees s hs).symm
    _ = 0 := hz

private def detectorZeroExtend (ω : ArtinPrimitiveRoots.A1.HeckeChar F)
    (I : Ideal (𝓞 F)) : ℂ := if I = ⊥ then 0 else ω.idealValue I

private theorem detector_idealValue_mul (ω : ArtinPrimitiveRoots.A1.HeckeChar F)
    (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    ω.idealValue (I * J) = ω.idealValue I * ω.idealValue J := by
  classical
  simp only [ArtinPrimitiveRoots.A1.HeckeChar.idealValue,
    UniqueFactorizationMonoid.normalizedFactors_mul hI hJ,
    Multiset.map_add, Multiset.prod_add]

private theorem detectorZeroExtend_mul (ω : ArtinPrimitiveRoots.A1.HeckeChar F)
    (I J : Ideal (𝓞 F)) :
    detectorZeroExtend ω (I * J) = detectorZeroExtend ω I * detectorZeroExtend ω J := by
  by_cases hI : I = ⊥
  · subst I
    simp [detectorZeroExtend]
  by_cases hJ : J = ⊥
  · subst J
    simp [detectorZeroExtend]
  have hIJ : I * J ≠ ⊥ := mul_ne_zero hI hJ
  simp [detectorZeroExtend, hI, hJ, hIJ, detector_idealValue_mul]

private abbrev detectorRayZeroModulus : ClassFieldTheory.RayClassModulus F := ⟨0, ∅⟩

private abbrev detectorRayZeroChar :
    ClassFieldTheory.RayClassGroup (detectorRayZeroModulus (F := F)) →* ℂˣ := 1

private abbrev detectorRayNormFiber (n : ℕ) :=
  {I : Ideal (𝓞 F) // Ideal.absNorm I = n}

private theorem detectorRayZeroCharValue (I : Ideal (𝓞 F)) :
    ArtinPrimitiveRoots.Hecke.charValue (detectorRayZeroChar (F := F)) I =
      if I = ⊥ then 0 else 1 := by
  classical
  by_cases hI : I = ⊥
  · simp [ArtinPrimitiveRoots.Hecke.charValue, ArtinPrimitiveRoots.Hecke.IsCoprimeTo, hI]
  · have hcop : ArtinPrimitiveRoots.Hecke.IsCoprimeTo
        (detectorRayZeroModulus (F := F)) I := by
      change ∃ h' : I ≠ ⊥,
        ArtinPrimitiveRoots.Hecke.idealUnit I h' ∈
          ClassFieldTheory.rayClassPrimeToIdeals (detectorRayZeroModulus (F := F))
      refine ⟨hI, ?_⟩
      change ∀ v, v ∈ (0 : IsDedekindDomain.HeightOneSpectrum (𝓞 F) →₀ ℕ).support → _
      intro v hv
      simp at hv
    simp [ArtinPrimitiveRoots.Hecke.charValue, hI, hcop]

private theorem detectorRayZeroCoeff_eq_card {n : ℕ} (hn : n ≠ 0) :
    ArtinPrimitiveRoots.Hecke.coeff (detectorRayZeroChar (F := F)) n =
      (Nat.card (detectorRayNormFiber (F := F) n) : ℂ) := by
  classical
  unfold ArtinPrimitiveRoots.Hecke.coeff
  let N := Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 F) n
  calc
    _ = ∑ I ∈ N.toFinset, (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [detectorRayZeroCharValue]
      have hIn : Ideal.absNorm I = n := N.mem_toFinset.mp hI
      have hI0 : I ≠ ⊥ := by
        intro h
        subst I
        simp at hIn
        exact hn hIn.symm
      simp [hI0]
    _ = (N.toFinset.card : ℂ) := by simp
    _ = (Nat.card (detectorRayNormFiber (F := F) n) : ℂ) := by
      exact_mod_cast (Nat.card_eq_card_finite_toFinset N).symm

private theorem detector_series_summable (f : Ideal (𝓞 F) → ℂ)
    (hb : ∀ I, ‖f I‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      f I.1 * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) := by
  classical
  let c : ℕ → ℂ := ArtinPrimitiveRoots.Hecke.coeff (detectorRayZeroChar (F := F))
  have hc : LSeriesSummable c (s.re : ℂ) := by
    simpa [c, LSeriesSummable] using
      ArtinPrimitiveRoots.Hecke.LSeriesSummable_coeff (detectorRayZeroChar (F := F))
        (by simpa using hs)
  have hcnorm : Summable (fun n => ‖LSeries.term c (s.re : ℂ) n‖) := hc.norm
  let N (n : ℕ) := detectorRayNormFiber (F := F) n
  let g : (Σ n, N n) → ℝ := fun p =>
    ‖if p.2.1 = ⊥ then 0 else f p.2.1 * ((Ideal.absNorm p.2.1 : ℕ) : ℂ) ^ (-s)‖
  have hfib (n : ℕ) : Summable (fun I : N n => g ⟨n, I⟩) := by
    letI : Fintype (N n) := @Fintype.ofFinite _
      (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 F) n)
    exact Summable.of_finite
  have hbound (n : ℕ) : (∑' I : N n, g ⟨n, I⟩) ≤
      ‖LSeries.term c (s.re : ℂ) n‖ := by
    by_cases hn : n = 0
    · subst n
      letI : Fintype (N 0) := @Fintype.ofFinite _
        (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 F) 0)
      have hbot : ∀ I : N 0, I.1 = ⊥ := by
        intro I
        apply Ideal.absNorm_eq_zero_iff.mp
        simpa using I.2
      simp [g, hbot]
    · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      letI : Fintype (N n) := @Fintype.ofFinite _
        (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 F) n)
      have hterm (I : N n) : g ⟨n, I⟩ ≤ Real.rpow (n : ℝ) (-s.re) := by
        have hIbot : I.1 ≠ ⊥ := by
          intro h
          have hzero : Ideal.absNorm I.1 = 0 := by rw [h]; simp
          have h0n : (0 : ℕ) = n := hzero.symm.trans I.2
          exact hn h0n.symm
        have hnormIpos : 0 < (Ideal.absNorm I.1 : ℝ) := by
          rw [I.2]
          exact hnpos
        have hpow : ‖((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)‖ =
            Real.rpow (n : ℝ) (-s.re) := by
          rw [← Complex.ofReal_natCast,
            Complex.norm_cpow_eq_rpow_re_of_pos hnormIpos, I.2]
          congr 1
        change ‖if I.1 = ⊥ then 0 else
          f I.1 * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)‖ ≤ _
        rw [if_neg hIbot, norm_mul, hpow]
        simpa using mul_le_mul_of_nonneg_right (hb I.1)
          (Real.rpow_nonneg hnpos.le (-s.re))
      calc
        (∑' I : N n, g ⟨n, I⟩) = ∑ I : N n, g ⟨n, I⟩ := by rw [tsum_fintype]
        _ ≤ ∑ _I : N n, Real.rpow (n : ℝ) (-s.re) :=
          Finset.sum_le_sum fun I _ => hterm I
        _ = (Nat.card (N n) : ℝ) * Real.rpow (n : ℝ) (-s.re) := by simp
        _ = ‖LSeries.term c (s.re : ℂ) n‖ := by
          rw [LSeries.norm_term_eq, if_neg hn]
          have hcval : c n = (Nat.card (N n) : ℂ) := by
            exact detectorRayZeroCoeff_eq_card hn
          rw [hcval, Complex.norm_natCast]
          simp only [Complex.ofReal_re]
          change (Nat.card (N n) : ℝ) * Real.rpow (n : ℝ) (-s.re) =
            (Nat.card (N n) : ℝ) / Real.rpow (n : ℝ) s.re
          have hpowNeg : Real.rpow (n : ℝ) (-s.re) =
              (Real.rpow (n : ℝ) s.re)⁻¹ := Real.rpow_neg hnpos.le s.re
          rw [hpowNeg, div_eq_mul_inv]
  have houter : Summable (fun n => ∑' I : N n, g ⟨n, I⟩) :=
    Summable.of_nonneg_of_le (fun n => tsum_nonneg fun I => norm_nonneg _)
      hbound hcnorm
  have hsigma : Summable g :=
    (summable_sigma_of_nonneg (fun p => norm_nonneg _)).mpr ⟨hfib, houter⟩
  let e : (Σ n, N n) ≃ Ideal (𝓞 F) := Equiv.sigmaFiberEquiv Ideal.absNorm
  let φ : Ideal (𝓞 F) → ℝ := fun I =>
    ‖if I = ⊥ then 0 else f I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)‖
  have hcomp : g = φ ∘ e := by funext p; rfl
  have hfullNorm : Summable (fun I : Ideal (𝓞 F) =>
      ‖if I = ⊥ then 0 else f I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)‖) :=
    e.summable_iff.mp (hcomp ▸ hsigma)
  have hfull : Summable (fun I : Ideal (𝓞 F) =>
      if I = ⊥ then 0 else f I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)) :=
    Summable.of_norm hfullNorm
  exact (hfull.comp_injective Subtype.val_injective).congr fun I => by simp [I.property]

private theorem detector_euler_uniform_bound :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ (ω : ArtinPrimitiveRoots.A1.HeckeChar F), IsOfFinOrder ω →
        ∀ (L : HeckeLContinuation ω) (s : ℂ), 4 ≤ s.re → ‖L.value s‖ ≤ M := by
  classical
  let bterm (J : {I : Ideal (𝓞 F) // I ≠ ⊥}) : ℂ :=
    ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-(2 : ℂ))
  have hbbase : Summable bterm := by
    simpa [bterm] using detector_series_summable (fun _ : Ideal (𝓞 F) => 1)
      (by intro I; simp) (s := (2 : ℂ)) (by norm_num)
  let M : ℝ := ∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥}, ‖bterm J‖
  have hM : 0 ≤ M := by dsimp [M]; exact tsum_nonneg fun _ => norm_nonneg _
  refine ⟨M, hM, ?_⟩
  intro ω hω L s hs
  have hωbound : ∀ I, ‖ω.idealValue I‖ ≤ 1 := by
    intro I
    exact ArtinPrimitiveRoots.A2.Proofs.A2ZeroDetect.idealValue_norm_le_one_of_finOrder
      ω hω I
  have hseries := detector_series_summable ω.idealValue hωbound (by linarith : 1 < s.re)
  have hterm (J : {I : Ideal (𝓞 F) // I ≠ ⊥}) :
      ‖ω.idealValue J.1 * ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s)‖ ≤ ‖bterm J‖ := by
    have hNnat : 0 < Ideal.absNorm J.1 := by
      exact Ideal.absNorm_pos_of_nonZeroDivisors
        ⟨J.1, mem_nonZeroDivisors_iff_ne_zero.mpr J.2⟩
    have hN : (1 : ℝ) ≤ (Ideal.absNorm J.1 : ℝ) := by exact_mod_cast hNnat
    have hsNorm : ‖((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s)‖ =
        Real.rpow (Ideal.absNorm J.1 : ℝ) (-s.re) := by
      rw [← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hNnat)]
      simp
    have hbNorm : ‖bterm J‖ = Real.rpow (Ideal.absNorm J.1 : ℝ) (-2) := by
      dsimp [bterm]
      rw [← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hNnat)]
      simp
    have hpow : Real.rpow (Ideal.absNorm J.1 : ℝ) (-s.re) ≤
        Real.rpow (Ideal.absNorm J.1 : ℝ) (-2) := by
      apply Real.rpow_le_rpow_of_exponent_le hN
      linarith
    calc
      _ = ‖ω.idealValue J.1‖ *
            ‖((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s)‖ := by simp [norm_mul]
      _ ≤ 1 * Real.rpow (Ideal.absNorm J.1 : ℝ) (-s.re) := by
        rw [hsNorm]
        exact mul_le_mul_of_nonneg_right (hωbound J.1)
          (Real.rpow_nonneg (by positivity) _)
      _ ≤ _ := by rw [hbNorm]; simpa using hpow
  calc
    ‖L.value s‖ = ‖heckeLSeries ω s‖ := by rw [L.agrees s (by linarith)]
    _ ≤ ∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥},
          ‖ω.idealValue J.1 * ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s)‖ :=
      norm_tsum_le_tsum_norm hseries.norm
    _ ≤ M := by
      dsimp [M]
      exact hseries.norm.tsum_le_tsum hterm hbbase.norm

private theorem detector_L_strip_growth
    (A_F ρ δ C₀ U β γ : ℝ) (hAF : 0 < A_F) (hδ : 0 < δ)
    (hρ : 0 < ρ) (hC₀ : 0 < C₀) (hU : 2 ≤ U)
    (hβ : 996 / 1000 ≤ β) (hβone : β ≤ 1)
    (hγ : |γ| ≤ 4 * Real.rpow U ρ)
    (ω : ArtinPrimitiveRoots.A1.HeckeChar F) (𝔣 : Ideal (𝓞 F))
    (hprim : IsPrimitiveConductor ω 𝔣) (hω : IsOfFinOrder ω) (hnon : ω ≠ 1)
    (L : HeckeLContinuation ω) (hNf : (Ideal.absNorm 𝔣 : ℝ) ≤ C₀ * U)
    (Cg Meuler : ℝ) (hCg : 0 < Cg) (hMeuler : 0 ≤ Meuler)
    (hGrowthAt : ∀ (ω : ArtinPrimitiveRoots.A1.HeckeChar F), IsOfFinOrder ω → ω ≠ 1 →
      ∀ (f : Ideal (𝓞 F)), IsPrimitiveConductor ω f →
        ∀ (L : HeckeLContinuation ω) (s : ℂ),
          3 / 1000 ≤ s.re → s.re ≤ 4 →
            ‖L.value s‖ ≤ Cg * Real.rpow (Ideal.absNorm f : ℝ) (1 / 2 + δ) *
              Real.rpow (2 + |s.im|) A_F)
    (hEuler : ∀ (ω : ArtinPrimitiveRoots.A1.HeckeChar F), IsOfFinOrder ω →
      ∀ (L : HeckeLContinuation ω) (s : ℂ), 4 ≤ s.re → ‖L.value s‖ ≤ Meuler)
    {c : ℝ} (hc : 1 < c) :
    ∀ z : ℂ, 1 / 2 - β ≤ z.re → z.re ≤ c →
      ‖L.value (β + γ * Complex.I + z)‖ ≤
        (Cg * Real.rpow (C₀ * U) (1 / 2 + δ) * Real.rpow 6 A_F *
          Real.rpow U (A_F * ρ) + Meuler + 1) *
            (1 + |z.im|) ^ Nat.ceil A_F := by
  classical
  let n : ℕ := Nat.ceil A_F
  let α : ℝ := 1 / 2 + δ
  let Q : ℝ := C₀ * U
  let H : ℝ := Cg * Real.rpow Q α * Real.rpow 6 A_F * Real.rpow U (A_F * ρ)
  let A : ℝ := H + Meuler + 1
  have hUone : 1 ≤ U := by linarith
  have hUpos : 0 < U := by linarith
  have hAFn : A_F ≤ (n : ℝ) := by dsimp [n]; exact Nat.le_ceil A_F
  have hαnonneg : 0 ≤ α := by dsimp [α]; linarith
  have hqfpos : 0 < (Ideal.absNorm 𝔣 : ℝ) := by
    have hqnat := Ideal.absNorm_pos_of_nonZeroDivisors
      ⟨𝔣, mem_nonZeroDivisors_iff_ne_zero.mpr hprim.1⟩
    exact_mod_cast hqnat
  have hQpos : 0 < Q := by dsimp [Q]; positivity
  have hQnorm : (Ideal.absNorm 𝔣 : ℝ) ≤ Q := by simpa [Q] using hNf
  have hUrho : 1 ≤ Real.rpow U ρ := Real.one_le_rpow hUone hρ.le
  have hgammaBound : 2 + |γ| ≤ 6 * Real.rpow U ρ := by
    have hγ' : 2 + |γ| ≤ 2 + 4 * Real.rpow U ρ := by linarith
    have hscale : 2 + 4 * Real.rpow U ρ ≤ 6 * Real.rpow U ρ := by
      nlinarith [hUrho]
    exact hγ'.trans hscale
  have hheightBound (z : ℂ) :
      Real.rpow (2 + |γ + z.im|) A_F ≤
        Real.rpow 6 A_F * Real.rpow U (A_F * ρ) * (1 + |z.im|) ^ n := by
    have habs : 2 + |γ + z.im| ≤ (2 + |γ|) * (1 + |z.im|) := by
      have habsAdd := abs_add_le γ z.im
      nlinarith [abs_nonneg γ, abs_nonneg z.im]
    have hbase : 1 ≤ 1 + |z.im| := by linarith [abs_nonneg z.im]
    have htime : Real.rpow (1 + |z.im|) A_F ≤ (1 + |z.im|) ^ n := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hbase hAFn
    have hgamma : Real.rpow (2 + |γ|) A_F ≤
        Real.rpow (6 * Real.rpow U ρ) A_F :=
      Real.rpow_le_rpow (by positivity) hgammaBound (by positivity)
    have hmul : Real.rpow (6 * Real.rpow U ρ) A_F =
        Real.rpow 6 A_F * Real.rpow (Real.rpow U ρ) A_F :=
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6) (by positivity)
    have hmulPower : Real.rpow (Real.rpow U ρ) A_F =
        Real.rpow U (ρ * A_F) :=
      (Real.rpow_mul (by positivity : 0 ≤ U) ρ A_F).symm
    calc
      _ ≤ Real.rpow ((2 + |γ|) * (1 + |z.im|)) A_F :=
        Real.rpow_le_rpow (by positivity) habs (by positivity)
      _ = Real.rpow (2 + |γ|) A_F * Real.rpow (1 + |z.im|) A_F :=
        Real.mul_rpow (by positivity) (by positivity)
      _ ≤ Real.rpow (6 * Real.rpow U ρ) A_F *
            Real.rpow (1 + |z.im|) A_F := by
        exact mul_le_mul_of_nonneg_right hgamma
          (Real.rpow_nonneg (by positivity) _)
      _ = Real.rpow 6 A_F * Real.rpow (Real.rpow U ρ) A_F *
            Real.rpow (1 + |z.im|) A_F := by
        exact congrArg (fun x => x * Real.rpow (1 + |z.im|) A_F) hmul
      _ = Real.rpow 6 A_F * Real.rpow U (ρ * A_F) *
            Real.rpow (1 + |z.im|) A_F := by
        exact congrArg (fun x => Real.rpow 6 A_F * x * Real.rpow (1 + |z.im|) A_F)
          hmulPower
      _ = Real.rpow 6 A_F * Real.rpow U (A_F * ρ) *
            Real.rpow (1 + |z.im|) A_F := by rw [mul_comm ρ A_F]
      _ ≤ Real.rpow 6 A_F * Real.rpow U (A_F * ρ) *
            (1 + |z.im|) ^ n := by
        have hcoef : 0 ≤ Real.rpow 6 A_F * Real.rpow U (A_F * ρ) :=
          mul_nonneg (Real.rpow_nonneg (by norm_num) _)
            (Real.rpow_nonneg (by linarith) _)
        exact mul_le_mul_of_nonneg_left htime hcoef
  have hHnonneg : 0 ≤ H := by dsimp [H, Q, α]; positivity
  have hAeq : A = Cg * Real.rpow (C₀ * U) (1 / 2 + δ) *
      Real.rpow 6 A_F * Real.rpow U (A_F * ρ) + Meuler + 1 := by
    dsimp [A, H, Q, α]
  intro z hzlo hzhi
  let w : ℂ := (β : ℂ) + γ * Complex.I + z
  have hwre : w.re = β + z.re := by simp [w]
  have hwim : w.im = γ + z.im := by simp [w]
  have hwlo : 1 / 2 ≤ w.re := by rw [hwre]; linarith
  by_cases hwhi : w.re ≤ 4
  · have hconv := hGrowthAt ω hω hnon 𝔣 hprim L w
      (by linarith : 3 / 1000 ≤ w.re) hwhi
    have hcondpow :
        Real.rpow (Ideal.absNorm 𝔣 : ℝ) α ≤ Real.rpow Q α :=
      Real.rpow_le_rpow (le_of_lt hqfpos) hQnorm hαnonneg
    have hbound :
        ‖L.value w‖ ≤ Cg * Real.rpow Q α *
          Real.rpow 6 A_F * Real.rpow U (A_F * ρ) *
            (1 + |z.im|) ^ n := by
      calc
        _ ≤ Cg * Real.rpow (Ideal.absNorm 𝔣 : ℝ) α *
              Real.rpow (2 + |w.im|) A_F := hconv
        _ ≤ Cg * Real.rpow Q α * Real.rpow (2 + |w.im|) A_F := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcondpow hCg.le)
            (Real.rpow_nonneg (by positivity) _)
        _ ≤ Cg * Real.rpow Q α *
              (Real.rpow 6 A_F * Real.rpow U (A_F * ρ) *
                (1 + |z.im|) ^ n) := by
          have hcoef : 0 ≤ Cg * Real.rpow Q α :=
            mul_nonneg hCg.le (Real.rpow_nonneg (by positivity) _)
          have h := mul_le_mul_of_nonneg_left (hheightBound z) hcoef
          simpa [hwim] using h
        _ = H * (1 + |z.im|) ^ n := by dsimp [H]; ring
    calc
      ‖L.value (β + γ * Complex.I + z)‖ = ‖L.value w‖ := by simp [w]
      _ ≤ H * (1 + |z.im|) ^ n := hbound
      _ ≤ A * (1 + |z.im|) ^ n := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [A]
        linarith
      _ = (Cg * Real.rpow (C₀ * U) (1 / 2 + δ) * Real.rpow 6 A_F *
            Real.rpow U (A_F * ρ) + Meuler + 1) * (1 + |z.im|) ^ n := by
        rw [hAeq]
  · have hw4 : 4 ≤ w.re := le_of_not_ge hwhi
    have hEulerBound := hEuler ω hω L w hw4
    have hbase1 : 1 ≤ 1 + |z.im| := by linarith [abs_nonneg z.im]
    have hpoly : 1 ≤ (1 + |z.im|) ^ n := one_le_pow₀ hbase1
    calc
      ‖L.value (β + γ * Complex.I + z)‖ = ‖L.value w‖ := by simp [w]
      _ ≤ Meuler := hEulerBound
      _ ≤ A := by dsimp [A]; linarith
      _ ≤ A * (1 + |z.im|) ^ n :=
        le_mul_of_one_le_right (by positivity) hpoly
      _ = (Cg * Real.rpow (C₀ * U) (1 / 2 + δ) * Real.rpow 6 A_F *
            Real.rpow U (A_F * ρ) + Meuler + 1) * (1 + |z.im|) ^ n := by
        rw [hAeq]

private theorem detector_gamma_left_bound (n : ℕ) :
    ∃ G : ℝ, 0 < G ∧ ∀ β : ℝ, 996 / 1000 ≤ β → β ≤ 1 →
      ∀ t : ℝ,
        ‖Complex.Gamma (((1 / 2 - β : ℝ) : ℂ) + t * Complex.I)‖ ≤
          G / (1 + |t|) ^ (n + 2) := by
  obtain ⟨G₀, hG₀, hrapid⟩ :=
    OAI.SevenEighths.GammaZeroDetector.gamma_rapid_bound
      (1 / 2 : ℝ) (504 / 1000) (by norm_num) (n + 2)
  let G : ℝ := G₀ / (496 / 1000)
  refine ⟨G, by dsimp [G]; positivity, ?_⟩
  intro β hβ hβone
  let d : ℝ := 1 / 2 - β
  have hdlo : -(1 / 2 : ℝ) ≤ d := by dsimp [d]; linarith
  have hdhi : d ≤ -(496 / 1000 : ℝ) := by dsimp [d]; linarith
  intro t
  let z : ℂ := (d : ℂ) + t * Complex.I
  have hzre : z.re = d := by simp [z]
  have hzim : z.im = t := by simp [z]
  have hzplusre : (z + 1).re = d + 1 := by simp [hzre]
  have hz : z ≠ 0 := by
    intro hz
    have h := congrArg Complex.re hz
    simp [hzre] at h
    linarith [hdhi]
  have hzpluslo : (1 / 2 : ℝ) ≤ (z + 1).re := by rw [hzplusre]; dsimp [d]; linarith
  have hzplushi : (z + 1).re ≤ 504 / 1000 := by rw [hzplusre]; dsimp [d]; linarith
  have hrapidLine : (1 + |t|) ^ (n + 2) * ‖Complex.Gamma (z + 1)‖ ≤ G₀ := by
    have h := hrapid (z + 1) hzpluslo hzplushi
    simpa [hzim] using h
  have hGammaPlus : ‖Complex.Gamma (z + 1)‖ ≤ G₀ / (1 + |t|) ^ (n + 2) := by
    apply (le_div_iff₀ (by positivity : 0 < (1 + |t|) ^ (n + 2))).2
    simpa [mul_comm] using hrapidLine
  have hnormZ : (496 / 1000 : ℝ) ≤ ‖z‖ := by
    have habs : (496 / 1000 : ℝ) ≤ |d| := by
      rw [abs_of_nonpos (hdhi.trans (by norm_num : -(496 / 1000 : ℝ) ≤ 0))]
      linarith
    have habsz : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    rw [hzre] at habsz
    exact habs.trans habsz
  have hnormGamma : ‖Complex.Gamma z‖ =
      ‖Complex.Gamma (z + 1)‖ * ‖z‖⁻¹ := by
    have hrec := Complex.Gamma_add_one z hz
    have hrec' : Complex.Gamma z = Complex.Gamma (z + 1) / z := by
      rw [hrec]
      field_simp [hz]
    calc
      ‖Complex.Gamma z‖ = ‖Complex.Gamma (z + 1) / z‖ := by rw [hrec']
      _ = ‖Complex.Gamma (z + 1)‖ / ‖z‖ := norm_div _ _
      _ = _ := by rw [div_eq_mul_inv]
  calc
    ‖Complex.Gamma (((1 / 2 - β : ℝ) : ℂ) + t * Complex.I)‖ =
        ‖Complex.Gamma z‖ := by simp [z, d]
    _ = ‖Complex.Gamma (z + 1)‖ * ‖z‖⁻¹ := hnormGamma
    _ ≤ (G₀ / (1 + |t|) ^ (n + 2)) * (496 / 1000)⁻¹ := by
      have hinv : ‖z‖⁻¹ ≤ (496 / 1000 : ℝ)⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) hnormZ
      exact mul_le_mul hGammaPlus hinv
        (by positivity) (by positivity)
    _ = G / (1 + |t|) ^ (n + 2) := by dsimp [G]; field_simp

private theorem detector_mollifier_differentiable
    (U : ℝ) (ω : ArtinPrimitiveRoots.A1.HeckeChar F) :
    Differentiable ℂ (mollifier U ω.idealValue) := by
  classical
  unfold mollifier
  apply Differentiable.fun_sum
  intro I hI
  by_cases hbot : I = ⊥
  · have hμ : (idealMoebius I : ℂ) = 0 := by
      simp [ArtinPrimitiveRoots.A2.idealMoebius, hbot]
    simp [hμ]
  · have hNnat : Ideal.absNorm I ≠ 0 := by
      intro hN
      exact hbot (Ideal.absNorm_eq_zero_iff.mp hN)
    have hN : ((Ideal.absNorm I : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hNnat
    have hpow : Differentiable ℂ
        (fun s : ℂ => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)) := by
      apply Differentiable.const_cpow
      · exact Differentiable.neg differentiable_id
      · exact Or.inl hN
    exact (differentiable_const
      ((idealMoebius I : ℂ) * ω.idealValue I)).mul hpow

private theorem detector_kernel_scale (U : ℝ) (hU : 0 < U) (z : ℂ) :
    ((U ^ 10 : ℝ) : ℂ) ^ z = (U : ℂ) ^ (10 * z) := by
  have hU10 : 0 < U ^ 10 := pow_pos hU _
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hU10.ne'),
    ← Complex.ofReal_log hU10.le,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hU.ne'),
    ← Complex.ofReal_log hU.le]
  congr 1
  push_cast
  rw [Real.log_pow U 10]
  push_cast
  ring

private theorem gamma_line_norm_integrable (c : ℝ) (hc : 0 < c) :
    Integrable (fun t : ℝ => ‖Complex.Gamma ((c : ℂ) + t * Complex.I)‖) := by
  obtain ⟨K, hK, hγ⟩ := OAI.SevenEighths.GammaZeroDetector.gamma_rapid_bound c c hc 2
  have hdom (t : ℝ) :
      ‖Complex.Gamma ((c : ℂ) + t * Complex.I)‖ ≤ K / (1 + t ^ 2) := by
    have h := hγ ((c : ℂ) + t * Complex.I) (by simp) (by simp)
    have hsq : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by
      nlinarith [sq_abs t, abs_nonneg t]
    have h' : (1 + |t|) ^ 2 *
        ‖Complex.Gamma ((c : ℂ) + t * Complex.I)‖ ≤ K := by simpa using h
    apply (le_div_iff₀ (by positivity : 0 < 1 + t ^ 2)).2
    have hmul := mul_le_mul_of_nonneg_right hsq
      (norm_nonneg (Complex.Gamma ((c : ℂ) + t * Complex.I)))
    simpa [mul_comm] using hmul.trans h'
  apply (integrable_inv_one_add_sq.const_mul K).mono'
  · have hline : Continuous (fun t : ℝ => (c : ℂ) + t * Complex.I) := by fun_prop
    have hΓ : Continuous (fun t : ℝ => Complex.Gamma ((c : ℂ) + t * Complex.I)) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact (OAI.SevenEighths.GammaZeroDetector.gamma_differentiableAt_right
        (by simp [hc])).continuousAt.comp hline.continuousAt
    exact hΓ.norm.aestronglyMeasurable
  · filter_upwards [] with t
    simpa [div_eq_mul_inv] using hdom t

private theorem detectorCoeff_complex_divisor_sum (U : ℝ) (hU : 1 ≤ U)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (z : ℂ) :
    (detectorCoeff U I : ℂ) * z =
      ∑ D ∈ (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊U ^ 2⌋₊).toFinset,
        (if D ∣ I then (idealMoebius D : ℂ) else 0) * z := by
  have hα := ArtinPrimitiveRoots.Proofs.A2FreqP.detectorCoeff_divisor_sum U hU I hI
  have hαc : (detectorCoeff U I : ℂ) =
      ∑ D ∈ (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊U ^ 2⌋₊).toFinset,
        (if D ∣ I then (idealMoebius D : ℂ) else 0) := by
    exact_mod_cast hα
  rw [hαc, Finset.sum_mul]

private theorem detector_line_convolution_expansion
    (U : ℝ) (hU : 1 ≤ U) (ω : ArtinPrimitiveRoots.A1.HeckeChar F)
    (hω : IsOfFinOrder ω) (L : ℂ → ℂ)
    (hL : ∀ s : ℂ, 1 < s.re → L s = heckeLSeries ω s)
    (β γ c : ℝ) (hσ : 1 < β + c) :
    ∀ t : ℝ,
      L (β + γ * Complex.I + ((c : ℂ) + t * Complex.I)) *
          ArtinPrimitiveRoots.A2.mollifier U ω.idealValue
            (β + γ * Complex.I + ((c : ℂ) + t * Complex.I)) =
        ∑ D ∈ (Ideal.finite_setOfPred_absNorm_le
            (S := 𝓞 F) ⌊U ^ 2⌋₊).toFinset,
          ∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥},
            if D ∣ J.1 then (idealMoebius D : ℂ) * detectorZeroExtend ω J.1 *
              ((Ideal.absNorm J.1 : ℕ) : ℂ) ^
                (-(β + γ * Complex.I + ((c : ℂ) + t * Complex.I))) else 0 := by
  classical
  let f : Ideal (𝓞 F) → ℂ := detectorZeroExtend ω
  let S : Finset (Ideal (𝓞 F)) :=
    (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊U ^ 2⌋₊).toFinset
  let sfun (t : ℝ) : ℂ := β + γ * Complex.I + ((c : ℂ) + t * Complex.I)
  have hmul : ∀ I J, f (I * J) = f I * f J := by
    intro I J
    exact detectorZeroExtend_mul ω I J
  have hbound : ∀ I, ‖f I‖ ≤ 1 := by
    intro I
    by_cases hI : I = ⊥
    · simp [f, detectorZeroExtend, hI]
    · simp only [f, detectorZeroExtend, if_neg hI]
      exact ArtinPrimitiveRoots.A2.Proofs.A2ZeroDetect.idealValue_norm_le_one_of_finOrder
        ω hω I
  have hseries (t : ℝ) : L (sfun t) =
      ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
        f I.1 * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-sfun t) := by
    have hs : 1 < (sfun t).re := by simpa [sfun] using hσ
    rw [hL (sfun t) hs]
    unfold heckeLSeries
    apply tsum_congr
    intro I
    simp [f, detectorZeroExtend, I.2]
  have hMoll (t : ℝ) :
      ArtinPrimitiveRoots.A2.mollifier U f (sfun t) =
        ArtinPrimitiveRoots.A2.mollifier U ω.idealValue (sfun t) := by
    unfold ArtinPrimitiveRoots.A2.mollifier
    apply Finset.sum_congr rfl
    intro I hI
    by_cases hbot : I = ⊥
    · simp [f, detectorZeroExtend, hbot, idealMoebius]
    · simp [f, detectorZeroExtend, hbot]
  have hdet (t : ℝ) : L (sfun t) *
      ArtinPrimitiveRoots.A2.mollifier U ω.idealValue (sfun t) =
        ∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥},
          (detectorCoeff U J.1 : ℂ) * f J.1 *
            ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-sfun t) := by
    have h := ArtinPrimitiveRoots.A2.detector_identity U hU f hmul hbound
      (s := sfun t) (by simpa [sfun] using hσ)
    rw [← hseries t, hMoll t] at h
    exact h.1
  have hswap : ∀ t : ℝ,
      (∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥},
          (detectorCoeff U J.1 : ℂ) * f J.1 *
            ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-sfun t)) =
        ∑ D ∈ S, ∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥},
          if D ∣ J.1 then (idealMoebius D : ℂ) * f J.1 *
            ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-sfun t) else 0 := by
    intro t
    let w (D : Ideal (𝓞 F)) (J : {I : Ideal (𝓞 F) // I ≠ ⊥}) :=
      if D ∣ J.1 then (idealMoebius D : ℂ) * f J.1 *
        ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-sfun t) else 0
    have hweight (D : Ideal (𝓞 F)) : Summable (w D) := by
      exact ArtinPrimitiveRoots.Proofs.A2FreqP.detector_divisor_weight_summable
        f hbound (by simpa [sfun] using hσ) D
    have hcoef (J : {I : Ideal (𝓞 F) // I ≠ ⊥}) :
        (detectorCoeff U J.1 : ℂ) * f J.1 *
            ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-sfun t) =
          ∑ D ∈ S, w D J := by
      have hcoeff := detectorCoeff_complex_divisor_sum U hU J.1 J.2
        (f J.1 * ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-sfun t))
      calc
        _ = (detectorCoeff U J.1 : ℂ) *
              (f J.1 * ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-sfun t)) := by ring
        _ = _ := hcoeff
        _ = ∑ D ∈ S, w D J := by
          apply Finset.sum_congr rfl
          intro D hD
          by_cases hdiv : D ∣ J.1 <;> simp [w, hdiv] <;> ring
    calc
      _ = ∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥}, ∑ D ∈ S, w D J := by
        apply tsum_congr
        exact hcoef
      _ = _ := Summable.tsum_finsetSum (s := S)
        (fun D hD => hweight D)
  intro t
  calc
    _ = L (sfun t) * ArtinPrimitiveRoots.A2.mollifier U ω.idealValue (sfun t) := by
      rfl
    _ = ∑ D ∈ S, ∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥},
          if D ∣ J.1 then (idealMoebius D : ℂ) * f J.1 *
            ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-sfun t) else 0 := by
      rw [hdet t, hswap t]

private theorem detector_mellin_fourier_inversion (x c : ℝ)
    (hx : 0 < x) (hc : 0 < c) :
    verticalMellinIntegral
      (fun v => Complex.Gamma v * (x : ℂ) ^ (-v)) c = Complex.exp (-(x : ℂ)) := by
  let f : ℝ → ℂ := fun t => (Real.exp (-t) : ℂ)
  have hm (s : ℂ) (hs : 0 < s.re) : mellin f s = Complex.Gamma s := by
    rw [Complex.Gamma_eq_integral hs, ← Complex.GammaIntegral_eq_mellin]
  have hf : MellinConvergent f (c : ℂ) := by
    simpa only [MellinConvergent, f, smul_eq_mul, mul_comm] using
      (Complex.GammaIntegral_convergent (by exact_mod_cast hc))
  have hline : ∀ t : ℝ, mellin f ((c : ℂ) + t * Complex.I) =
      Complex.Gamma ((c : ℂ) + t * Complex.I) := by
    intro t
    apply hm
    simp [hc]
  have hΓint : Integrable (fun t : ℝ => Complex.Gamma ((c : ℂ) + t * Complex.I)) := by
    obtain ⟨K, hK, hγ⟩ := OAI.SevenEighths.GammaZeroDetector.gamma_rapid_bound c c hc 2
    have hdom : ∀ t : ℝ,
        ‖Complex.Gamma ((c : ℂ) + t * Complex.I)‖ ≤ K / (1 + t ^ 2) := by
      intro t
      have h := hγ ((c : ℂ) + t * Complex.I) (by simp) (by simp)
      have hsq : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by
        nlinarith [sq_abs t, abs_nonneg t]
      apply (le_div_iff₀ (by positivity : 0 < 1 + t ^ 2)).2
      have h' : (1 + |t|) ^ 2 *
          ‖Complex.Gamma ((c : ℂ) + t * Complex.I)‖ ≤ K := by simpa using h
      have hmul := mul_le_mul_of_nonneg_right hsq
        (norm_nonneg (Complex.Gamma ((c : ℂ) + t * Complex.I)))
      simpa [mul_comm] using hmul.trans h'
    apply (integrable_inv_one_add_sq.const_mul K).mono'
    · apply Continuous.aestronglyMeasurable
      have hlinecont : Continuous (fun t : ℝ => (c : ℂ) + t * Complex.I) := by fun_prop
      apply continuous_iff_continuousAt.mpr
      intro t
      exact (OAI.SevenEighths.GammaZeroDetector.gamma_differentiableAt_right
        (by simp [hc])).continuousAt.comp hlinecont.continuousAt
    · filter_upwards [] with t
      simpa [div_eq_mul_inv] using hdom t
  have hv : Complex.VerticalIntegrable (mellin f) c := by
    change Integrable (fun t : ℝ => mellin f ((c : ℂ) + t * Complex.I))
    exact hΓint.congr (Filter.Eventually.of_forall fun t => (hline t).symm)
  have hi := mellinInv_mellin_eq c f hx hf hv (by
    dsimp [f]
    fun_prop)
  simp only [mellinInv, smul_eq_mul] at hi
  simp_rw [hline] at hi
  have hintegral :
      (∫ t : ℝ, Complex.Gamma ((c : ℂ) + t * Complex.I) *
        (x : ℂ) ^ (-((c : ℂ) + t * Complex.I))) =
      ∫ t : ℝ, (x : ℂ) ^ (-((c : ℂ) + t * Complex.I)) *
        Complex.Gamma ((c : ℂ) + t * Complex.I) := by
    apply integral_congr_ae
    filter_upwards [] with t
    ring
  unfold verticalMellinIntegral
  rw [hintegral]
  simpa [f, Complex.ofReal_exp, Complex.ofReal_neg, mul_comm] using hi

private theorem detector_scaled_mellin_term (N : ℕ) (hN : 0 < N)
    (U β γ c : ℝ) (hU : 0 < U) (hc : 0 < c) :
    verticalMellinIntegral
      (fun v => ((N : ℕ) : ℂ) ^ (-(β + γ * Complex.I + v)) *
        Complex.Gamma v * (U : ℂ) ^ (10 * v)) c =
      ((N : ℕ) : ℂ) ^ (-(β + γ * Complex.I)) *
        Complex.exp (-(((N : ℝ) / U ^ 10 : ℝ) : ℂ)) := by
  let s₀ : ℂ := (β : ℂ) + γ * Complex.I
  let x : ℝ := (N : ℝ) / U ^ 10
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hx : 0 < x := by dsimp [x]; exact div_pos hNreal (pow_pos hU 10)
  have hNcomplex : ((N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hbase : ∀ v : ℂ,
      ((N : ℕ) : ℂ) ^ (-(s₀ + v)) * (U : ℂ) ^ (10 * v) =
        ((N : ℕ) : ℂ) ^ (-s₀) * (x : ℂ) ^ (-v) := by
    intro v
    have hNpower : ((N : ℕ) : ℂ) ^ (-v) * (U : ℂ) ^ (10 * v) =
        (x : ℂ) ^ (-v) := by
      have hlogx : Real.log x = Real.log (N : ℝ) - 10 * Real.log U := by
        dsimp [x]
        rw [Real.log_div hNreal.ne' (pow_ne_zero _ hU.ne'), Real.log_pow U 10]
        norm_num
      rw [← Complex.ofReal_natCast]
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
        ← Complex.ofReal_log hx.le,
        Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hNreal.ne'),
        ← Complex.ofReal_log hNreal.le,
        Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hU.ne'),
        ← Complex.ofReal_log hU.le, hlogx]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hNsum : ((N : ℕ) : ℂ) ^ (-(s₀ + v)) =
        ((N : ℕ) : ℂ) ^ (-s₀) * ((N : ℕ) : ℂ) ^ (-v) := by
      rw [show -(s₀ + v) = -s₀ + -v by ring, Complex.cpow_add _ _ hNcomplex]
    calc
      _ = (((N : ℕ) : ℂ) ^ (-s₀) * ((N : ℕ) : ℂ) ^ (-v)) *
            (U : ℂ) ^ (10 * v) := by rw [hNsum]
      _ = ((N : ℕ) : ℂ) ^ (-s₀) *
            (((N : ℕ) : ℂ) ^ (-v) * (U : ℂ) ^ (10 * v)) := by ring
      _ = _ := by rw [hNpower]
  have hfun (t : ℝ) :
      ((N : ℕ) : ℂ) ^ (-(s₀ + ((c : ℂ) + t * Complex.I))) *
          Complex.Gamma ((c : ℂ) + t * Complex.I) *
            (U : ℂ) ^ (10 * ((c : ℂ) + t * Complex.I)) =
        ((N : ℕ) : ℂ) ^ (-s₀) *
            (Complex.Gamma ((c : ℂ) + t * Complex.I) *
            (x : ℂ) ^ (-((c : ℂ) + t * Complex.I))) := by
    calc
      _ = (((N : ℕ) : ℂ) ^ (-(s₀ + ((c : ℂ) + t * Complex.I))) *
            (U : ℂ) ^ (10 * ((c : ℂ) + t * Complex.I))) *
          Complex.Gamma ((c : ℂ) + t * Complex.I) := by ring
      _ = (((N : ℕ) : ℂ) ^ (-s₀) *
            (x : ℂ) ^ (-((c : ℂ) + t * Complex.I))) *
          Complex.Gamma ((c : ℂ) + t * Complex.I) := by
        rw [hbase]
      _ = _ := by ring
  have hInt :
      (∫ t : ℝ, ((N : ℕ) : ℂ) ^
          (-(s₀ + ((c : ℂ) + t * Complex.I))) *
            Complex.Gamma ((c : ℂ) + t * Complex.I) *
              (U : ℂ) ^ (10 * ((c : ℂ) + t * Complex.I))) =
        ∫ t : ℝ, ((N : ℕ) : ℂ) ^ (-s₀) *
          (Complex.Gamma ((c : ℂ) + t * Complex.I) *
            (x : ℂ) ^ (-((c : ℂ) + t * Complex.I))) := by
    apply integral_congr_ae
    filter_upwards [] with t
    exact hfun t
  have hfactor :
      (∫ t : ℝ, ((N : ℕ) : ℂ) ^
          (-(s₀ + ((c : ℂ) + t * Complex.I))) *
            Complex.Gamma ((c : ℂ) + t * Complex.I) *
              (U : ℂ) ^ (10 * ((c : ℂ) + t * Complex.I))) =
        ((N : ℕ) : ℂ) ^ (-s₀) *
          (∫ t : ℝ, Complex.Gamma ((c : ℂ) + t * Complex.I) *
            (x : ℂ) ^ (-((c : ℂ) + t * Complex.I))) := by
    rw [hInt, integral_const_mul]
  have hMell := detector_mellin_fourier_inversion x c hx hc
  calc
    verticalMellinIntegral
        (fun v => ((N : ℕ) : ℂ) ^ (-(s₀ + v)) * Complex.Gamma v *
          (U : ℂ) ^ (10 * v)) c =
        ((N : ℕ) : ℂ) ^ (-s₀) *
          verticalMellinIntegral
            (fun v => Complex.Gamma v * (x : ℂ) ^ (-v)) c := by
      unfold verticalMellinIntegral
      rw [hfactor]
      ring
    _ = _ := by rw [hMell]

private def detectorLineParameter (β γ c t : ℝ) : ℂ :=
  (β : ℂ) + γ * Complex.I + ((c : ℂ) + t * Complex.I)

private def detectorLineDivisorWeight (f : Ideal (𝓞 F) → ℂ)
    (D : Ideal (𝓞 F)) (s : ℂ) (J : {I : Ideal (𝓞 F) // I ≠ ⊥}) : ℂ :=
  if D ∣ J.1 then (idealMoebius D : ℂ) * f J.1 *
    ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s) else 0

private theorem detector_countableIdeals : Countable (Ideal (𝓞 F)) := by
  classical
  let N (n : ℕ) := {I : Ideal (𝓞 F) // Ideal.absNorm I = n}
  have hfinite (n : ℕ) : Finite (N n) := by
    letI : Fintype (N n) := @Fintype.ofFinite _
      (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 F) n)
    infer_instance
  letI (n : ℕ) : Fintype (N n) := @Fintype.ofFinite _
    (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 F) n)
  letI : Countable (Σ n, N n) := inferInstance
  exact Countable.of_equiv (Σ n, N n) (Equiv.sigmaFiberEquiv Ideal.absNorm)

private theorem detector_integrable_tsum_of_summable_integral_norm
    {ι : Type*} [Countable ι] {G : ι → ℝ → ℂ}
    (hGint : ∀ i, Integrable (G i) (volume : Measure ℝ))
    (hGsum : Summable (fun i => ∫ t : ℝ, ‖G i t‖)) :
    Integrable (fun t : ℝ => ∑' i, G i t) (volume : Measure ℝ) := by
  refine ⟨AEStronglyMeasurable.tsum (fun i => (hGint i).1), ?_⟩
  show ∫⁻ t, ‖∑' i, G i t‖ₑ ∂(volume : Measure ℝ) < ⊤
  have h0 (i : ι) :
      ∫⁻ t, ‖G i t‖ₑ ∂(volume : Measure ℝ) = ‖∫ t : ℝ, ‖G i t‖‖ₑ := by
    rw [← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm (hGint i),
      Real.enorm_eq_ofReal (integral_nonneg (fun t => norm_nonneg (G i t)))]
  calc
    ∫⁻ t, ‖∑' i, G i t‖ₑ ∂(volume : Measure ℝ)
        ≤ ∫⁻ t, ∑' i, ‖G i t‖ₑ ∂(volume : Measure ℝ) :=
          lintegral_mono (fun t => enorm_tsum_le_tsum_enorm)
    _ = ∑' i, ∫⁻ t, ‖G i t‖ₑ ∂(volume : Measure ℝ) :=
          lintegral_tsum (fun i => (hGint i).1.enorm)
    _ = ∑' i, ‖∫ t : ℝ, ‖G i t‖‖ₑ := tsum_congr h0
    _ < ⊤ := by
      have h1 (i : ι) : ‖∫ t : ℝ, ‖G i t‖‖ₑ =
          ENNReal.ofReal (∫ t : ℝ, ‖G i t‖) :=
        Real.enorm_eq_ofReal (integral_nonneg (fun t => norm_nonneg (G i t)))
      rw [tsum_congr h1]
      rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun i => integral_nonneg (fun t => norm_nonneg (G i t))) hGsum]
      exact ENNReal.ofReal_lt_top

private theorem detector_divisor_line_integral_tsum
    (U β γ c : ℝ) (hU : 0 < U) (hc : 0 < c) (hσ : 1 < β + c)
    (f : Ideal (𝓞 F) → ℂ) (hb : ∀ I, ‖f I‖ ≤ 1) (D : Ideal (𝓞 F)) :
    (Summable (fun J : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
        ∫ t : ℝ, detectorLineDivisorWeight f D (detectorLineParameter β γ c t) J *
          Complex.Gamma ((c : ℂ) + t * Complex.I) *
            (U : ℂ) ^ (10 * ((c : ℂ) + t * Complex.I))) ∧
    ((∫ t : ℝ,
        (∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥},
          detectorLineDivisorWeight f D (detectorLineParameter β γ c t) J) *
          Complex.Gamma ((c : ℂ) + t * Complex.I) *
            (U : ℂ) ^ (10 * ((c : ℂ) + t * Complex.I))) =
      ∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥},
        ∫ t : ℝ, detectorLineDivisorWeight f D (detectorLineParameter β γ c t) J *
          Complex.Gamma ((c : ℂ) + t * Complex.I) *
            (U : ℂ) ^ (10 * ((c : ℂ) + t * Complex.I)))) ∧
    Integrable (fun t : ℝ =>
      (∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥},
        detectorLineDivisorWeight f D (detectorLineParameter β γ c t) J) *
        Complex.Gamma ((c : ℂ) + t * Complex.I) *
          (U : ℂ) ^ (10 * ((c : ℂ) + t * Complex.I))) := by
  classical
  let line (t : ℝ) : ℂ := detectorLineParameter β γ c t
  let vline (t : ℝ) : ℂ := (c : ℂ) + t * Complex.I
  let σ : ℝ := β + c
  have hσpos : 0 < σ := by dsimp [σ]; linarith
  have hwreal : Summable (fun J : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      detectorLineDivisorWeight f D (σ : ℂ) J) :=
    ArtinPrimitiveRoots.Proofs.A2FreqP.detector_divisor_weight_summable
      f hb (by simpa [σ] using hσ) D
  have hGammaInt := gamma_line_norm_integrable c hc
  let Gγ : ℝ := ∫ t : ℝ, ‖Complex.Gamma (vline t)‖
  have hGγnonneg : 0 ≤ Gγ := by dsimp [Gγ]; positivity
  have hGγeq : Gγ = ∫ t : ℝ, ‖Complex.Gamma (vline t)‖ := rfl
  have hNpos (J : {I : Ideal (𝓞 F) // I ≠ ⊥}) :
      0 < (Ideal.absNorm J.1 : ℝ) := by
    exact_mod_cast (Ideal.absNorm_pos_of_nonZeroDivisors
      ⟨J.1, mem_nonZeroDivisors_iff_ne_zero.mpr J.2⟩)
  have hReLine (t : ℝ) : (line t).re = σ := by
    simp [line, detectorLineParameter, σ]
  have hNormPow (J : {I : Ideal (𝓞 F) // I ≠ ⊥}) (t : ℝ) :
      ‖((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-(line t))‖ =
        ‖((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-(σ : ℂ))‖ := by
    have hN : 0 < (Ideal.absNorm J.1 : ℝ) := hNpos J
    have hleft : ‖((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-(line t))‖ =
      Real.rpow (Ideal.absNorm J.1 : ℝ) (-σ) := by
      rw [← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos hN]
      simp [hReLine]
    have hright : ‖((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-(σ : ℂ))‖ =
        Real.rpow (Ideal.absNorm J.1 : ℝ) (-σ) := by
      rw [← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos hN]
      simp
    rw [hleft, hright]
  have hNormUpow (t : ℝ) :
      ‖(U : ℂ) ^ (10 * vline t)‖ = Real.rpow U (10 * c) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hU]
    simp [vline]
  let Cpow : ℝ := Real.rpow U (10 * c)
  have hCpow : 0 ≤ Cpow := by dsimp [Cpow]; positivity
  let Term (J : {I : Ideal (𝓞 F) // I ≠ ⊥}) (t : ℝ) : ℂ :=
    detectorLineDivisorWeight f D (line t) J * Complex.Gamma (vline t) *
      (U : ℂ) ^ (10 * vline t)
  have hTermNorm (J : {I : Ideal (𝓞 F) // I ≠ ⊥}) (t : ℝ) :
      ‖Term J t‖ =
        ‖detectorLineDivisorWeight f D (σ : ℂ) J‖ * Cpow *
          ‖Complex.Gamma (vline t)‖ := by
    by_cases hdiv : D ∣ J.1
    · simp [Term, detectorLineDivisorWeight, hdiv, norm_mul, hNormPow, hNormUpow, Cpow]
      ring
    · simp [Term, detectorLineDivisorWeight, hdiv, Cpow]
  have hTermContinuous (J : {I : Ideal (𝓞 F) // I ≠ ⊥}) :
      Continuous (Term J) := by
    have hvline : Continuous vline := by dsimp [vline]; fun_prop
    have hline : Continuous line := by dsimp [line, detectorLineParameter]; fun_prop
    have hGamma : Continuous (fun t : ℝ => Complex.Gamma (vline t)) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact (OAI.SevenEighths.GammaZeroDetector.gamma_differentiableAt_right
        (by simpa [vline] using hc)).continuousAt.comp hvline.continuousAt
    have hpowN : Continuous (fun t : ℝ =>
        ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-line t)) := by
      have hNnat : Ideal.absNorm J.1 ≠ 0 := Nat.ne_of_gt (Nat.cast_pos.mp (hNpos J))
      letI : NeZero ((Ideal.absNorm J.1 : ℕ) : ℂ) :=
        ⟨by exact_mod_cast hNnat⟩
      exact (continuous_const_cpow ((Ideal.absNorm J.1 : ℕ) : ℂ)).comp (by fun_prop)
    have hpowU : Continuous (fun t : ℝ => (U : ℂ) ^ (10 * vline t)) := by
      letI : NeZero (U : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hU.ne'⟩
      exact (continuous_const_cpow (U : ℂ)).comp (by fun_prop)
    dsimp [Term, detectorLineDivisorWeight]
    split_ifs <;> fun_prop
  have hTermIntegrable (J : {I : Ideal (𝓞 F) // I ≠ ⊥}) : Integrable (Term J) := by
    let Cj : ℝ := ‖detectorLineDivisorWeight f D (σ : ℂ) J‖ * Cpow
    have hCj : 0 ≤ Cj := by dsimp [Cj]; positivity
    have hdom : ∀ᵐ t : ℝ, ‖Term J t‖ ≤ Cj * ‖Complex.Gamma (vline t)‖ := by
      filter_upwards [] with t
      exact le_of_eq (by simpa [Cj] using hTermNorm J t)
    have hstrong : AEStronglyMeasurable (Term J) :=
      (hTermContinuous J).aestronglyMeasurable
    exact (hGammaInt.const_mul Cj).mono' hstrong hdom
  have hTermInt (J : {I : Ideal (𝓞 F) // I ≠ ⊥}) :
      (∫ t : ℝ, ‖Term J t‖) =
        ‖detectorLineDivisorWeight f D (σ : ℂ) J‖ * Cpow * Gγ := by
    simp_rw [hTermNorm]
    rw [integral_const_mul]
  have hTermSummable : Summable (fun J : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      ∫ t : ℝ, ‖Term J t‖) := by
    have hs := hwreal.norm.mul_right (Cpow * Gγ)
    apply hs.congr
    intro J
    rw [hTermInt]
    ring
  letI : Countable (Ideal (𝓞 F)) := detector_countableIdeals
  letI : Countable {I : Ideal (𝓞 F) // I ≠ ⊥} := Subtype.val_injective.countable
  have hint := integral_tsum_of_summable_integral_norm hTermIntegrable hTermSummable
  have hsumTerm : Summable (fun J : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      ∫ t : ℝ, Term J t) :=
    Summable.of_norm_bounded hTermSummable fun J =>
      norm_integral_le_integral_norm (fun t : ℝ => Term J t)
  have hmul (t : ℝ) :
      (∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥},
        detectorLineDivisorWeight f D (line t) J) *
          (Complex.Gamma (vline t) * (U : ℂ) ^ (10 * vline t)) =
        ∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥}, Term J t := by
    have hwt := ArtinPrimitiveRoots.Proofs.A2FreqP.detector_divisor_weight_summable
      f hb (by rw [hReLine t]; exact hσ) D
    have h := (Summable.tsum_mul_right
      (Complex.Gamma (vline t) * (U : ℂ) ^ (10 * vline t)) hwt).symm
    simpa [detectorLineDivisorWeight, Term, mul_assoc] using h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa [line, vline, Term] using hsumTerm
  · calc
      _ = ∫ t : ℝ, ∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥}, Term J t := by
        apply integral_congr_ae
        filter_upwards [] with t
        calc
          _ = (∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥},
              detectorLineDivisorWeight f D (line t) J) *
                (Complex.Gamma (vline t) * (U : ℂ) ^ (10 * vline t)) := by ring
          _ = _ := hmul t
      _ = _ := hint.symm
  · have hsumTermIntegrable :=
      detector_integrable_tsum_of_summable_integral_norm hTermIntegrable hTermSummable
    have hfactor : Integrable (fun t : ℝ =>
        (∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥},
          detectorLineDivisorWeight f D (line t) J) *
          (Complex.Gamma (vline t) * (U : ℂ) ^ (10 * vline t))) := by
      exact hsumTermIntegrable.congr
        (Filter.Eventually.of_forall fun t => (hmul t).symm)
    simpa [line, vline, mul_assoc] using hfactor

private theorem detector_divisor_line_verticalMellin
    (U β γ c : ℝ) (hU : 0 < U) (hc : 0 < c) (hσ : 1 < β + c)
    (f : Ideal (𝓞 F) → ℂ) (hb : ∀ I, ‖f I‖ ≤ 1) (D : Ideal (𝓞 F)) :
    (Summable (fun J : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      verticalMellinIntegral
        (fun v => detectorLineDivisorWeight f D
          ((β : ℂ) + γ * Complex.I + v) J * Complex.Gamma v *
          (U : ℂ) ^ (10 * v)) c) ∧
      verticalMellinIntegral
        (fun v => (∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥},
          detectorLineDivisorWeight f D ((β : ℂ) + γ * Complex.I + v) J) *
            Complex.Gamma v * (U : ℂ) ^ (10 * v)) c =
      ∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥},
        verticalMellinIntegral
          (fun v => detectorLineDivisorWeight f D
            ((β : ℂ) + γ * Complex.I + v) J * Complex.Gamma v *
            (U : ℂ) ^ (10 * v)) c) ∧
      Integrable (fun t : ℝ =>
        (∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥},
          detectorLineDivisorWeight f D
            ((β : ℂ) + γ * Complex.I + ((c : ℂ) + t * Complex.I)) J) *
          Complex.Gamma ((c : ℂ) + t * Complex.I) *
            (U : ℂ) ^ (10 * ((c : ℂ) + t * Complex.I))) := by
  classical
  obtain ⟨⟨hsum, hEq⟩, hint⟩ :=
    detector_divisor_line_integral_tsum U β γ c hU hc hσ f hb D
  have hsum' : Summable (fun J : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      verticalMellinIntegral
        (fun v => detectorLineDivisorWeight f D
          ((β : ℂ) + γ * Complex.I + v) J * Complex.Gamma v *
          (U : ℂ) ^ (10 * v)) c) := by
    change Summable (fun J : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      (1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ, detectorLineDivisorWeight f D
          ((β : ℂ) + γ * Complex.I + ((c : ℂ) + t * Complex.I)) J *
          Complex.Gamma ((c : ℂ) + t * Complex.I) *
          (U : ℂ) ^ (10 * ((c : ℂ) + t * Complex.I)))
    exact hsum.mul_left _
  refine ⟨⟨hsum', ?_⟩, ?_⟩
  unfold verticalMellinIntegral
  calc
    _ = (1 / (2 * Real.pi) : ℂ) *
          ∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥},
            ∫ t : ℝ, detectorLineDivisorWeight f D
                ((β : ℂ) + γ * Complex.I + ((c : ℂ) + t * Complex.I)) J *
                  Complex.Gamma ((c : ℂ) + t * Complex.I) *
                  (U : ℂ) ^ (10 * ((c : ℂ) + t * Complex.I)) := by
        simpa [detectorLineParameter] using
          congrArg (fun z : ℂ => (1 / (2 * Real.pi) : ℂ) * z) hEq
    _ = ∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥},
          (1 / (2 * Real.pi) : ℂ) *
            ∫ t : ℝ, detectorLineDivisorWeight f D
                ((β : ℂ) + γ * Complex.I + ((c : ℂ) + t * Complex.I)) J *
                  Complex.Gamma ((c : ℂ) + t * Complex.I) *
                  (U : ℂ) ^ (10 * ((c : ℂ) + t * Complex.I)) :=
        (hsum.tsum_mul_left (1 / (2 * Real.pi) : ℂ)).symm
    _ = _ := by
      apply tsum_congr
      intro J
      rfl
  · simpa [detectorLineParameter] using hint

private theorem detector_divisor_scaled_mellin
    (U β γ c : ℝ) (hU : 0 < U) (hc : 0 < c)
    (f : Ideal (𝓞 F) → ℂ) (D : Ideal (𝓞 F))
    (J : {I : Ideal (𝓞 F) // I ≠ ⊥}) :
    verticalMellinIntegral
      (fun v => detectorLineDivisorWeight f D
        ((β : ℂ) + γ * Complex.I + v) J * Complex.Gamma v *
        (U : ℂ) ^ (10 * v)) c =
      if D ∣ J.1 then
        (idealMoebius D : ℂ) * f J.1 *
          ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-((β : ℂ) + γ * Complex.I)) *
            Complex.exp (-(((Ideal.absNorm J.1 : ℝ) / U ^ 10 : ℝ) : ℂ))
      else 0 := by
  classical
  by_cases hdiv : D ∣ J.1
  · rw [if_pos hdiv]
    let N : ℕ := Ideal.absNorm J.1
    let a : ℂ := (idealMoebius D : ℂ) * f J.1
    have hN : 0 < N := by
      dsimp [N]
      exact Ideal.absNorm_pos_of_nonZeroDivisors
        ⟨J.1, mem_nonZeroDivisors_iff_ne_zero.mpr J.2⟩
    have hpoint (t : ℝ) :
        detectorLineDivisorWeight f D
            ((β : ℂ) + γ * Complex.I + ((c : ℂ) + t * Complex.I)) J *
          Complex.Gamma ((c : ℂ) + t * Complex.I) *
            (U : ℂ) ^ (10 * ((c : ℂ) + t * Complex.I)) =
          a * (((N : ℕ) : ℂ) ^
              (-((β : ℂ) + γ * Complex.I + ((c : ℂ) + t * Complex.I))) *
            Complex.Gamma ((c : ℂ) + t * Complex.I) *
              (U : ℂ) ^ (10 * ((c : ℂ) + t * Complex.I))) := by
      simp [detectorLineDivisorWeight, hdiv, a, N]
      ring
    have hint :
        (∫ t : ℝ, detectorLineDivisorWeight f D
            ((β : ℂ) + γ * Complex.I + ((c : ℂ) + t * Complex.I)) J *
          Complex.Gamma ((c : ℂ) + t * Complex.I) *
            (U : ℂ) ^ (10 * ((c : ℂ) + t * Complex.I))) =
        a * (∫ t : ℝ, ((N : ℕ) : ℂ) ^
              (-((β : ℂ) + γ * Complex.I + ((c : ℂ) + t * Complex.I))) *
            Complex.Gamma ((c : ℂ) + t * Complex.I) *
              (U : ℂ) ^ (10 * ((c : ℂ) + t * Complex.I))) := by
      calc
        _ = ∫ t : ℝ, a * (((N : ℕ) : ℂ) ^
              (-((β : ℂ) + γ * Complex.I + ((c : ℂ) + t * Complex.I))) *
            Complex.Gamma ((c : ℂ) + t * Complex.I) *
              (U : ℂ) ^ (10 * ((c : ℂ) + t * Complex.I))) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hpoint
        _ = _ := by rw [integral_const_mul]
    unfold verticalMellinIntegral
    calc
      _ = a * verticalMellinIntegral
          (fun v => ((N : ℕ) : ℂ) ^
            (-((β : ℂ) + γ * Complex.I + v)) * Complex.Gamma v *
              (U : ℂ) ^ (10 * v)) c := by
        simp only [verticalMellinIntegral]
        rw [hint]
        ring
      _ = a * (((N : ℕ) : ℂ) ^ (-((β : ℂ) + γ * Complex.I)) *
            Complex.exp (-(((N : ℝ) / U ^ 10 : ℝ) : ℂ))) := by
        rw [detector_scaled_mellin_term N hN U β γ c hU hc]
      _ = (idealMoebius D : ℂ) * f J.1 *
            ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-((β : ℂ) + γ * Complex.I)) *
              Complex.exp (-(((Ideal.absNorm J.1 : ℝ) / U ^ 10 : ℝ) : ℂ)) := by
        simp [a, N]
        ring
  · rw [if_neg hdiv]
    unfold verticalMellinIntegral
    simp [detectorLineDivisorWeight, hdiv]

private theorem detector_original_line_identity
    (U β γ c : ℝ) (hU : 1 ≤ U) (hUpos : 0 < U) (hc : 0 < c)
    (hσ : 1 < β + c) (ω : ArtinPrimitiveRoots.A1.HeckeChar F)
    (hω : IsOfFinOrder ω) (L : HeckeLContinuation ω) :
    detectorSmoothedSum U β γ ω =
      verticalMellinIntegral
        (fun v => L.value (β + γ * Complex.I + v) *
          mollifier U ω.idealValue (β + γ * Complex.I + v) *
          Complex.Gamma v * (U : ℂ) ^ (10 * v)) c := by
  classical
  let f : Ideal (𝓞 F) → ℂ := detectorZeroExtend ω
  let S : Finset (Ideal (𝓞 F)) :=
    (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊U ^ 2⌋₊).toFinset
  let s (t : ℝ) : ℂ := β + γ * Complex.I + ((c : ℂ) + t * Complex.I)
  let v (t : ℝ) : ℂ := (c : ℂ) + t * Complex.I
  have hfbound : ∀ I, ‖f I‖ ≤ 1 := by
    intro I
    by_cases hI : I = ⊥
    · simp [f, detectorZeroExtend, hI]
    · simp only [f, detectorZeroExtend, if_neg hI]
      exact ArtinPrimitiveRoots.A2.Proofs.A2ZeroDetect.idealValue_norm_le_one_of_finOrder
        ω hω I
  have hexp (t : ℝ) :
      L.value (s t) * mollifier U ω.idealValue (s t) =
        ∑ D ∈ S, ∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥},
          detectorLineDivisorWeight f D (s t) J := by
    have h := detector_line_convolution_expansion U hU ω hω L.value L.agrees
      β γ c hσ t
    calc
      _ = ∑ D ∈ S, ∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥},
            if D ∣ J.1 then (idealMoebius D : ℂ) *
              detectorZeroExtend ω J.1 *
                ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-(s t)) else 0 := by
        simpa [S, s] using h
      _ = _ := by
        apply Finset.sum_congr rfl
        intro D hD
        apply tsum_congr
        intro J
        by_cases hdiv : D ∣ J.1 <;>
          simp [detectorLineDivisorWeight, f, detectorZeroExtend, s, hdiv, J.2]
  have hexpGamma (t : ℝ) :
      L.value (s t) * mollifier U ω.idealValue (s t) *
          Complex.Gamma (v t) * (U : ℂ) ^ (10 * v t) =
        ∑ D ∈ S, (∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥},
          detectorLineDivisorWeight f D (s t) J) *
            Complex.Gamma (v t) * (U : ℂ) ^ (10 * v t) := by
    calc
      _ = (L.value (s t) * mollifier U ω.idealValue (s t)) *
            (Complex.Gamma (v t) * (U : ℂ) ^ (10 * v t)) := by ring
      _ = (∑ D ∈ S, ∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥},
            detectorLineDivisorWeight f D (s t) J) *
            (Complex.Gamma (v t) * (U : ℂ) ^ (10 * v t)) := by rw [hexp t]
      _ = ∑ D ∈ S, (∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥},
            detectorLineDivisorWeight f D (s t) J) *
            (Complex.Gamma (v t) * (U : ℂ) ^ (10 * v t)) := Finset.sum_mul ..
      _ = _ := by apply Finset.sum_congr rfl; intro D hD; ring
  have hlineD (D : Ideal (𝓞 F)) :=
    detector_divisor_line_verticalMellin U β γ c hUpos hc hσ f hfbound D
  have hlineDint (D : Ideal (𝓞 F)) :
      Integrable (fun t : ℝ =>
        (∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥},
          detectorLineDivisorWeight f D
            ((β : ℂ) + γ * Complex.I + ((c : ℂ) + t * Complex.I)) J) *
          Complex.Gamma ((c : ℂ) + t * Complex.I) *
            (U : ℂ) ^ (10 * ((c : ℂ) + t * Complex.I))) := (hlineD D).2
  have hline :
      verticalMellinIntegral
          (fun v => L.value (β + γ * Complex.I + v) *
            mollifier U ω.idealValue (β + γ * Complex.I + v) *
            Complex.Gamma v * (U : ℂ) ^ (10 * v)) c =
        ∑ D ∈ S, ∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥},
          verticalMellinIntegral
            (fun v => detectorLineDivisorWeight f D
              (β + γ * Complex.I + v) J * Complex.Gamma v *
                (U : ℂ) ^ (10 * v)) c := by
    unfold verticalMellinIntegral
    calc
      _ = (1 / (2 * Real.pi) : ℂ) *
            ∫ t : ℝ, ∑ D ∈ S,
              (∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥},
                detectorLineDivisorWeight f D
                  ((β : ℂ) + γ * Complex.I + ((c : ℂ) + t * Complex.I)) J) *
                Complex.Gamma ((c : ℂ) + t * Complex.I) *
                  (U : ℂ) ^ (10 * ((c : ℂ) + t * Complex.I)) := by
          congr 1
          apply integral_congr_ae
          filter_upwards [] with t
          simpa [s, v, mul_assoc] using hexpGamma t
      _ = (1 / (2 * Real.pi) : ℂ) *
            ∑ D ∈ S, ∫ t : ℝ,
              (∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥},
                detectorLineDivisorWeight f D
                  ((β : ℂ) + γ * Complex.I + ((c : ℂ) + t * Complex.I)) J) *
                Complex.Gamma ((c : ℂ) + t * Complex.I) *
                  (U : ℂ) ^ (10 * ((c : ℂ) + t * Complex.I)) := by
          congr 1
          rw [integral_finsetSum S (fun D hD => hlineDint D)]
      _ = ∑ D ∈ S, verticalMellinIntegral
            (fun v => (∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥},
              detectorLineDivisorWeight f D (β + γ * Complex.I + v) J) *
              Complex.Gamma v * (U : ℂ) ^ (10 * v)) c := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro D hD
          rfl
      _ = _ := by
          apply Finset.sum_congr rfl
          intro D hD
          exact (hlineD D).1.2
  have hcomm :
      (∑ D ∈ S, ∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥},
        verticalMellinIntegral
          (fun v => detectorLineDivisorWeight f D
            (β + γ * Complex.I + v) J * Complex.Gamma v *
              (U : ℂ) ^ (10 * v)) c) =
      ∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥},
        ∑ D ∈ S, verticalMellinIntegral
          (fun v => detectorLineDivisorWeight f D
            (β + γ * Complex.I + v) J * Complex.Gamma v *
              (U : ℂ) ^ (10 * v)) c := by
    exact (Summable.tsum_finsetSum (s := S) fun D hD => (hlineD D).1.1).symm
  have hcoeff (J : {I : Ideal (𝓞 F) // I ≠ ⊥}) :
      (∑ D ∈ S, verticalMellinIntegral
        (fun v => detectorLineDivisorWeight f D
          (β + γ * Complex.I + v) J * Complex.Gamma v *
            (U : ℂ) ^ (10 * v)) c) =
        (detectorCoeff U J.1 : ℂ) * f J.1 *
          ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-(β + γ * Complex.I)) *
            Complex.exp (-(((Ideal.absNorm J.1 : ℝ) / U ^ 10 : ℝ) : ℂ)) := by
    let z : ℂ := f J.1 * ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-(β + γ * Complex.I)) *
      Complex.exp (-(((Ideal.absNorm J.1 : ℝ) / U ^ 10 : ℝ) : ℂ))
    calc
      _ = ∑ D ∈ S, (if D ∣ J.1 then (idealMoebius D : ℂ) * z else 0) := by
        apply Finset.sum_congr rfl
        intro D hD
        rw [detector_divisor_scaled_mellin U β γ c hUpos hc f D J]
        by_cases hdiv : D ∣ J.1 <;> simp [z, hdiv, mul_assoc]
      _ = _ := by
        simpa [S, z, mul_assoc] using
          (detectorCoeff_complex_divisor_sum U hU J.1 J.2 z).symm
  have hsumcoeff : detectorSmoothedSum U β γ ω =
      ∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥},
        ∑ D ∈ S, verticalMellinIntegral
          (fun v => detectorLineDivisorWeight f D
            (β + γ * Complex.I + v) J * Complex.Gamma v *
              (U : ℂ) ^ (10 * v)) c := by
    unfold detectorSmoothedSum
    apply tsum_congr
    intro J
    have hExp : Complex.exp
        (-(((Ideal.absNorm J.1 : ℝ) / U ^ 10 : ℝ) : ℂ)) =
        Complex.exp (-((Ideal.absNorm J.1 : ℕ) : ℂ) / (U : ℂ) ^ 10) := by
      apply congrArg Complex.exp
      rw [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast]
      ring
    calc
      _ = (detectorCoeff U J.1 : ℂ) * f J.1 *
            ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-(β + γ * Complex.I)) *
              Complex.exp (-((Ideal.absNorm J.1 : ℕ) : ℂ) / (U : ℂ) ^ 10) := by
        simp only [f, detectorZeroExtend, if_neg J.2]
      _ = (detectorCoeff U J.1 : ℂ) * f J.1 *
            ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-(β + γ * Complex.I)) *
              Complex.exp (-(((Ideal.absNorm J.1 : ℝ) / U ^ 10 : ℝ) : ℂ)) := by
        rw [← hExp]
      _ = _ := (hcoeff J).symm
  calc
    detectorSmoothedSum U β γ ω =
        ∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥},
          ∑ D ∈ S, verticalMellinIntegral
            (fun v => detectorLineDivisorWeight f D
              (β + γ * Complex.I + v) J * Complex.Gamma v *
                (U : ℂ) ^ (10 * v)) c := hsumcoeff
    _ = _ := by rw [← hcomm, ← hline]

private theorem detector_shift_identity_claims
    (ω : ArtinPrimitiveRoots.A1.HeckeChar F) (𝔣 : Ideal (𝓞 F))
    (hprim : IsPrimitiveConductor ω 𝔣) (hω : IsOfFinOrder ω)
    (L : HeckeLContinuation ω) (U β γ : ℝ) (hU : 2 ≤ U)
    (hz : L.value (β + γ * Complex.I) = 0) (hβ : 996 / 1000 ≤ β)
    {c : ℝ} (hc : 1 < c) :
    β ≤ 1 ∧ detectorSmoothedSum U β γ ω =
      verticalMellinIntegral
        (fun v => L.value (β + γ * Complex.I + v) *
          mollifier U ω.idealValue (β + γ * Complex.I + v) *
          Complex.Gamma v * (U : ℂ) ^ (10 * v)) c := by
  have hUone : 1 ≤ U := by linarith
  have hUpos : 0 < U := by linarith
  have hcpos : 0 < c := by linarith
  have hσ : 1 < β + c := by linarith
  refine ⟨?_, ?_⟩
  · simpa using detector_zero_real_le_one ω hω 𝔣 hprim L hz
  · exact
      detector_original_line_identity U β γ c hUone hUpos hcpos hσ ω hω L

/-- **zf:detector-shift** (06-zero-free.tex:226-264): exact zero-detector statement. Corrected per
rev-a2 to include positive `ε` and continuation values; corrected per sol-gate-a2 to carry the
field-dependent convexity growth bound used by the shift. -/
theorem zf_detector_shift
    (A_F ρ ε C₀ : ℝ) (hAF : 0 < A_F) (hε : 0 < ε) (hC₀ : 0 < C₀)
    (hρ : 0 < ρ ∧ ρ < min (1 / 10) (1 / (A_F + 1)))
    (hGrowth : ConductorHeightBound (F := F) A_F) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ω : ArtinPrimitiveRoots.A1.HeckeChar F) (𝔣 : Ideal (𝓞 F)),
        IsPrimitiveConductor ω 𝔣 → IsOfFinOrder ω → ω ≠ 1 →
        ∀ (L : HeckeLContinuation ω) (U β γ : ℝ), 2 ≤ U →
          (Ideal.absNorm 𝔣 : ℝ) ≤ C₀ * U →
          L.value (β + γ * Complex.I) = 0 →
          996 / 1000 ≤ β → |γ| ≤ 4 * Real.rpow U ρ →
          ∀ {c : ℝ}, 1 < c →
            β ≤ 1 ∧
            detectorSmoothedSum U β γ ω =
              verticalMellinIntegral
                (fun v => L.value (β + γ * Complex.I + v) *
                  mollifier U ω.idealValue (β + γ * Complex.I + v) *
                  Complex.Gamma v * (U : ℂ) ^ (10 * v)) c ∧
            ‖detectorSmoothedSum U β γ ω‖ ≤
              C * Real.rpow U (-(346 / 100 : ℝ) + A_F * ρ + ε) := by
  classical
  obtain ⟨Cmol, hCmol, hmoll⟩ := detector_mollifier_norm_bound (F := F)
  obtain ⟨Cg, hCg, hGrowthAt⟩ := hGrowth ε hε
  obtain ⟨Meuler, hMeuler, hEuler⟩ := detector_euler_uniform_bound (F := F)
  obtain ⟨Gleft, hGleft, hGammaLeft⟩ := detector_gamma_left_bound (Nat.ceil A_F)
  let α : ℝ := 1 / 2 + ε
  let p : ℝ := α + A_F * ρ
  let Cstrip : ℝ := Cg * Real.rpow C₀ α * Real.rpow 6 A_F + Meuler + 1
  let C : ℝ := Gleft * Cmol * Cstrip / 2
  have hC : 0 < C := by dsimp [C, Cstrip]; positivity
  refine ⟨C, hC, ?_⟩
  intro ω 𝔣 hprim hω hnon L U β γ hU hNf hz hβ hγ c hc
  have hUone : 1 ≤ U := by linarith
  have hUpos : 0 < U := by linarith
  have hβone : β ≤ 1 := by
    exact (detector_shift_identity_claims ω 𝔣 hprim hω L U β γ hU hz hβ hc).1
  have hclaims := detector_shift_identity_claims ω 𝔣 hprim hω L U β γ hU hz hβ hc
  let Astrip : ℝ :=
    Cg * Real.rpow (C₀ * U) α * Real.rpow 6 A_F * Real.rpow U (A_F * ρ) + Meuler + 1
  have hstrip : ∀ z : ℂ, 1 / 2 - β ≤ z.re → z.re ≤ c →
      ‖L.value (β + γ * Complex.I + z)‖ ≤ Astrip * (1 + |z.im|) ^ Nat.ceil A_F := by
    intro z hzlo hzhi
    simpa [Astrip, α] using
      detector_L_strip_growth A_F ρ ε C₀ U β γ hAF hε hρ.1 hC₀ hU hβ hβone hγ
        ω 𝔣 hprim hω hnon L hNf Cg Meuler hCg hMeuler hGrowthAt hEuler (c := c) hc z hzlo hzhi
  have hAstrip : 0 ≤ Astrip := by dsimp [Astrip]; positivity
  have hAstripUniform : Astrip ≤ Cstrip * Real.rpow U p := by
    have hCpow : Real.rpow (C₀ * U) α = Real.rpow C₀ α * Real.rpow U α :=
      Real.mul_rpow (le_of_lt hC₀) hUpos.le
    have hUpow : Real.rpow U α * Real.rpow U (A_F * ρ) = Real.rpow U p := by
      dsimp [p]
      rw [← Real.rpow_add hUpos]
    have hpnonneg : 0 ≤ p :=
      add_nonneg (by dsimp [α]; linarith) (mul_nonneg hAF.le hρ.1.le)
    have hUoneP : 1 ≤ Real.rpow U p := Real.one_le_rpow hUone hpnonneg
    have hmain :
        Cg * Real.rpow (C₀ * U) α * Real.rpow 6 A_F * Real.rpow U (A_F * ρ) =
          (Cg * Real.rpow C₀ α * Real.rpow 6 A_F) * Real.rpow U p := by
      rw [hCpow, ← hUpow]
      ring
    calc
      Astrip = Cg * Real.rpow (C₀ * U) α * Real.rpow 6 A_F *
          Real.rpow U (A_F * ρ) + Meuler + 1 := rfl
      _ = (Cg * Real.rpow C₀ α * Real.rpow 6 A_F) * Real.rpow U p + Meuler + 1 := by
        rw [hmain]
      _ ≤ Cstrip * Real.rpow U p := by
        dsimp [Cstrip]
        let coeff : ℝ := Cg * Real.rpow C₀ α * Real.rpow 6 A_F
        have hrest : 0 ≤ Meuler + 1 := by linarith
        have hrestmul : Meuler + 1 ≤ (Meuler + 1) * Real.rpow U p := by
          calc
            Meuler + 1 = (Meuler + 1) * 1 := by ring
            _ ≤ (Meuler + 1) * Real.rpow U p :=
              mul_le_mul_of_nonneg_left hUoneP hrest
        have hsumle : coeff * Real.rpow U p + (Meuler + 1) ≤
            coeff * Real.rpow U p + (Meuler + 1) * Real.rpow U p := by
          simpa [add_comm] using
            add_le_add_left hrestmul (coeff * Real.rpow U p)
        have hgap : coeff * Real.rpow U p + (Meuler + 1) ≤
            (coeff + (Meuler + 1)) * Real.rpow U p := by
          calc
            _ ≤ coeff * Real.rpow U p + (Meuler + 1) * Real.rpow U p := hsumle
            _ = _ := by rw [← add_mul]
        calc
          _ = coeff * Real.rpow U p + (Meuler + 1) := by dsimp [coeff]; ring
          _ ≤ (coeff + (Meuler + 1)) * Real.rpow U p := hgap
          _ = _ := by dsimp [coeff]; ring_nf
  have hidentity := hclaims.2
  let s₀ : ℂ := (β : ℂ) + γ * Complex.I
  let f : ℂ → ℂ := fun z => L.value (s₀ + z)
  let g : ℂ → ℂ := fun z => mollifier U ω.idealValue (s₀ + z)
  let Y : ℝ := U ^ 10
  let d : ℝ := 1 / 2 - β
  have hAffine : Differentiable ℂ (fun z : ℂ => s₀ + z) :=
    (differentiable_const s₀).add differentiable_id
  have hf : Differentiable ℂ f := by
    dsimp [f]
    exact L.differentiable.comp hAffine
  have hg : Differentiable ℂ g := by
    dsimp [g]
    exact (detector_mollifier_differentiable U ω).comp hAffine
  have hf0 : f 0 = 0 := by
    simp [f, s₀, hz]
  have hYone : 1 ≤ Y := by
    dsimp [Y]
    exact one_le_pow₀ hUone
  have hYpos : 0 < Y := by dsimp [Y]; positivity
  have hda : -1 < d := by dsimp [d]; linarith
  have hdc : d ≤ c := by dsimp [d]; linarith
  have hstripF : ∀ z : ℂ, d ≤ z.re → z.re ≤ c →
      ‖f z‖ ≤ Astrip * (1 + |z.im|) ^ Nat.ceil A_F := by
    intro z hzlo hzhi
    simpa [f, s₀, d] using hstrip z hzlo hzhi
  have hstripG : ∀ z : ℂ, d ≤ z.re → z.re ≤ c → ‖g z‖ ≤ Cmol * U := by
    intro z hzlo hzhi
    have hs : 1 / 2 ≤ (s₀ + z).re := by
      simp [s₀]
      dsimp [d] at hzlo
      linarith
    simpa [g] using hmoll U hU ω hω (s₀ + z) hs
  have hAstripNat : 0 ≤ Astrip := hAstrip
  have hB : 0 ≤ Cmol * U := mul_nonneg hCmol.le hUpos.le
  have hcontour := OAI.SevenEighths.GammaZeroDetector.cancelledKernel_contour_shift
    hf hg hf0 hYone hda hdc (Nat.ceil A_F) hAstripNat hB hstripF hstripG
  have hzeroLine (x : ℝ) (hx : x ≠ 0) (t : ℝ) :
      (x : ℂ) + t * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    have hx0 : x = 0 := by simpa using hre
    exact hx hx0
  have hdne : d ≠ 0 := by
    dsimp [d]
    linarith
  have hLiteral (x t : ℝ) :
      OAI.SevenEighths.GammaZeroDetector.literalKernel f g Y
          ((x : ℂ) + t * Complex.I) =
        L.value (s₀ + ((x : ℂ) + t * Complex.I)) *
          mollifier U ω.idealValue (s₀ + ((x : ℂ) + t * Complex.I)) *
          Complex.Gamma ((x : ℂ) + t * Complex.I) *
          (U : ℂ) ^ (10 * ((x : ℂ) + t * Complex.I)) := by
    dsimp [OAI.SevenEighths.GammaZeroDetector.literalKernel, f, g, Y]
    rw [detector_kernel_scale U hUpos]
    ring
  have hCancelled (x : ℝ) (hx : x ≠ 0) (t : ℝ) :
      OAI.SevenEighths.GammaZeroDetector.cancelledKernel f g Y
          ((x : ℂ) + t * Complex.I) =
        OAI.SevenEighths.GammaZeroDetector.literalKernel f g Y
          ((x : ℂ) + t * Complex.I) :=
    OAI.SevenEighths.GammaZeroDetector.cancelledKernel_eq_literal hf0
      (hzeroLine x hx t)
  have hverticalShift :
      verticalMellinIntegral
          (fun v => L.value (s₀ + v) * mollifier U ω.idealValue (s₀ + v) *
            Complex.Gamma v * (U : ℂ) ^ (10 * v)) c =
      verticalMellinIntegral
          (fun v => L.value (s₀ + v) * mollifier U ω.idealValue (s₀ + v) *
            Complex.Gamma v * (U : ℂ) ^ (10 * v)) d := by
    unfold verticalMellinIntegral
    congr 1
    calc
      (∫ t : ℝ, L.value (s₀ + ((c : ℂ) + t * Complex.I)) *
          mollifier U ω.idealValue (s₀ + ((c : ℂ) + t * Complex.I)) *
          Complex.Gamma ((c : ℂ) + t * Complex.I) *
          (U : ℂ) ^ (10 * ((c : ℂ) + t * Complex.I))) =
        ∫ t : ℝ, OAI.SevenEighths.GammaZeroDetector.cancelledKernel f g Y
          ((c : ℂ) + t * Complex.I) := by
        apply integral_congr_ae
        filter_upwards [] with t
        exact ((hCancelled c (ne_of_gt (lt_trans (by norm_num) hc)) t).trans
          (hLiteral c t)).symm
      _ = ∫ t : ℝ, OAI.SevenEighths.GammaZeroDetector.cancelledKernel f g Y
            ((d : ℂ) + t * Complex.I) := hcontour.symm
      _ = ∫ t : ℝ, L.value (s₀ + ((d : ℂ) + t * Complex.I)) *
          mollifier U ω.idealValue (s₀ + ((d : ℂ) + t * Complex.I)) *
          Complex.Gamma ((d : ℂ) + t * Complex.I) *
          (U : ℂ) ^ (10 * ((d : ℂ) + t * Complex.I)) := by
        apply integral_congr_ae
        filter_upwards [] with t
        exact (hCancelled d hdne t).trans (hLiteral d t)
  have hleftKernelInt :
      Integrable (fun t : ℝ =>
        OAI.SevenEighths.GammaZeroDetector.cancelledKernel f g Y
          ((d : ℂ) + t * Complex.I)) := by
    obtain ⟨Kstrip, hKstrip, hKernelStrip⟩ :=
      OAI.SevenEighths.GammaZeroDetector.cancelledKernel_strip_bound
        hf hg hf0 hYone hda (Nat.ceil A_F) hAstripNat hB hstripF hstripG
    exact OAI.SevenEighths.GammaZeroDetector.cancelledKernel_vertical_integrable
      hf hg hYpos hda ⟨le_rfl, hdc⟩ hKernelStrip
  have hleftIntegrable :
      Integrable (fun t : ℝ => L.value (s₀ + ((d : ℂ) + t * Complex.I)) *
        mollifier U ω.idealValue (s₀ + ((d : ℂ) + t * Complex.I)) *
        Complex.Gamma ((d : ℂ) + t * Complex.I) *
        (U : ℂ) ^ (10 * ((d : ℂ) + t * Complex.I))) := by
    exact hleftKernelInt.congr (Filter.Eventually.of_forall fun t =>
      (hCancelled d hdne t).trans (hLiteral d t))
  let Kleft : ℝ := Real.rpow U (10 * d) * Gleft * Astrip * Cmol * U
  have hKleft : 0 ≤ Kleft := by dsimp [Kleft]; positivity
  have hleftPoint (t : ℝ) :
      ‖L.value (s₀ + ((d : ℂ) + t * Complex.I)) *
        mollifier U ω.idealValue (s₀ + ((d : ℂ) + t * Complex.I)) *
        Complex.Gamma ((d : ℂ) + t * Complex.I) *
        (U : ℂ) ^ (10 * ((d : ℂ) + t * Complex.I))‖ ≤ Kleft / (1 + t ^ 2) := by
    let z : ℂ := (d : ℂ) + t * Complex.I
    have hzlo : d ≤ z.re := by simp [z]
    have hzhi : z.re ≤ c := by simp [z]; exact hdc
    have hF := hstripF z hzlo hzhi
    have hG := hstripG z hzlo hzhi
    have hGamma := hGammaLeft β hβ hβone t
    have hFt : ‖L.value (s₀ + z)‖ ≤ Astrip * (1 + |t|) ^ Nat.ceil A_F := by
      simpa [z] using hF
    have hGt : ‖mollifier U ω.idealValue (s₀ + z)‖ ≤ Cmol * U := by
      simpa [z] using hG
    have hGammat : ‖Complex.Gamma z‖ ≤
        Gleft / (1 + |t|) ^ (Nat.ceil A_F + 2) := by
      simpa [z, d] using hGamma
    have hpowNorm : ‖(U : ℂ) ^ (10 * z)‖ = Real.rpow U (10 * d) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hUpos]
      simp [z]
    have hVpos : 0 < 1 + |t| := by positivity
    have hVbound : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by
      nlinarith [sq_abs t, abs_nonneg t]
    have hratio : (1 + |t|) ^ (Nat.ceil A_F) /
        (1 + |t|) ^ (Nat.ceil A_F + 2) = 1 / (1 + |t|) ^ 2 := by
      rw [pow_add]
      field_simp [ne_of_gt hVpos]
    have hproduct :
        (Astrip * (1 + |t|) ^ Nat.ceil A_F) * (Cmol * U) *
          (Gleft / (1 + |t|) ^ (Nat.ceil A_F + 2)) *
          Real.rpow U (10 * d) = Kleft / (1 + |t|) ^ 2 := by
      calc
        _ = (Astrip * Cmol * U * Gleft * Real.rpow U (10 * d)) *
              ((1 + |t|) ^ Nat.ceil A_F /
                (1 + |t|) ^ (Nat.ceil A_F + 2)) := by ring
        _ = (Astrip * Cmol * U * Gleft * Real.rpow U (10 * d)) *
              (1 / (1 + |t|) ^ 2) := by rw [hratio]
        _ = Kleft / (1 + |t|) ^ 2 := by dsimp [Kleft]; ring
    calc
      _ = ‖L.value (s₀ + z)‖ * ‖mollifier U ω.idealValue (s₀ + z)‖ *
            ‖Complex.Gamma z‖ * ‖(U : ℂ) ^ (10 * z)‖ := by
          simp [norm_mul, mul_assoc, z]
      _ ≤ ((Astrip * (1 + |t|) ^ Nat.ceil A_F) * (Cmol * U)) *
            ((Gleft / (1 + |t|) ^ (Nat.ceil A_F + 2)) *
              Real.rpow U (10 * d)) := by
          have hFG : ‖L.value (s₀ + z)‖ * ‖mollifier U ω.idealValue (s₀ + z)‖ ≤
              (Astrip * (1 + |t|) ^ Nat.ceil A_F) * (Cmol * U) :=
            mul_le_mul hFt hGt (norm_nonneg _) (by positivity)
          have hGP : ‖Complex.Gamma z‖ * ‖(U : ℂ) ^ (10 * z)‖ ≤
              (Gleft / (1 + |t|) ^ (Nat.ceil A_F + 2)) *
                Real.rpow U (10 * d) := by
            rw [hpowNorm]
            exact mul_le_mul_of_nonneg_right hGammat (Real.rpow_nonneg hUpos.le _)
          have hprod := mul_le_mul hFG hGP (by positivity) (by positivity)
          simpa [mul_assoc] using hprod
      _ = Kleft / (1 + |t|) ^ 2 := by simpa [mul_assoc] using hproduct
      _ ≤ Kleft / (1 + t ^ 2) := by
        exact div_le_div_of_nonneg_left hKleft (by positivity) hVbound
  have hleftMajor : Integrable (fun t : ℝ => Kleft / (1 + t ^ 2)) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (integrable_inv_one_add_sq.const_mul Kleft)
  have hleftIntegralNorm :
      (∫ t : ℝ, ‖L.value (s₀ + ((d : ℂ) + t * Complex.I)) *
        mollifier U ω.idealValue (s₀ + ((d : ℂ) + t * Complex.I)) *
        Complex.Gamma ((d : ℂ) + t * Complex.I) *
        (U : ℂ) ^ (10 * ((d : ℂ) + t * Complex.I))‖) ≤ Kleft * Real.pi := by
    calc
      _ ≤ ∫ t : ℝ, Kleft / (1 + t ^ 2) :=
        integral_mono_ae hleftIntegrable.norm hleftMajor (Filter.Eventually.of_forall hleftPoint)
      _ = Kleft * Real.pi := by
        rw [show (fun t : ℝ => Kleft / (1 + t ^ 2)) =
          fun t => Kleft * (1 + t ^ 2)⁻¹ by funext t; ring,
          integral_const_mul, integral_univ_inv_one_add_sq]
  have hverticalLeftNorm :
      ‖verticalMellinIntegral
        (fun v => L.value (s₀ + v) * mollifier U ω.idealValue (s₀ + v) *
          Complex.Gamma v * (U : ℂ) ^ (10 * v)) d‖ ≤ Kleft / 2 := by
    unfold verticalMellinIntegral
    have hscalar : ‖(1 / (2 * Real.pi) : ℂ)‖ = (1 / (2 * Real.pi) : ℝ) := by
      have hpos : 0 < (1 / (2 * Real.pi) : ℝ) := by positivity
      have hcast : (1 / (2 * Real.pi) : ℂ) =
          ((1 / (2 * Real.pi) : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, Complex.norm_real, Real.norm_of_nonneg hpos.le]
    have hnormIntegral :
        ‖∫ t : ℝ, L.value (s₀ + ((d : ℂ) + t * Complex.I)) *
          mollifier U ω.idealValue (s₀ + ((d : ℂ) + t * Complex.I)) *
          Complex.Gamma ((d : ℂ) + t * Complex.I) *
          (U : ℂ) ^ (10 * ((d : ℂ) + t * Complex.I))‖ ≤ Kleft * Real.pi :=
      (norm_integral_le_integral_norm (fun t : ℝ =>
        L.value (s₀ + ((d : ℂ) + t * Complex.I)) *
          mollifier U ω.idealValue (s₀ + ((d : ℂ) + t * Complex.I)) *
          Complex.Gamma ((d : ℂ) + t * Complex.I) *
          (U : ℂ) ^ (10 * ((d : ℂ) + t * Complex.I)))).trans hleftIntegralNorm
    change ‖(1 / (2 * Real.pi) : ℂ) *
      (∫ t : ℝ, L.value (s₀ + ((d : ℂ) + t * Complex.I)) *
        mollifier U ω.idealValue (s₀ + ((d : ℂ) + t * Complex.I)) *
        Complex.Gamma ((d : ℂ) + t * Complex.I) *
        (U : ℂ) ^ (10 * ((d : ℂ) + t * Complex.I)))‖ ≤ Kleft / 2
    rw [norm_mul, hscalar]
    calc
      _ ≤ (1 / (2 * Real.pi) : ℝ) * (Kleft * Real.pi) :=
        mul_le_mul_of_nonneg_left hnormIntegral (by positivity)
      _ = Kleft / 2 := by field_simp
  have hdetNorm : ‖detectorSmoothedSum U β γ ω‖ ≤ Kleft / 2 := by
    calc
      _ = ‖verticalMellinIntegral
          (fun v => L.value (β + γ * Complex.I + v) *
            mollifier U ω.idealValue (β + γ * Complex.I + v) *
            Complex.Gamma v * (U : ℂ) ^ (10 * v)) c‖ := by rw [hidentity]
      _ = ‖verticalMellinIntegral
          (fun v => L.value (s₀ + v) * mollifier U ω.idealValue (s₀ + v) *
            Complex.Gamma v * (U : ℂ) ^ (10 * v)) d‖ := by
        apply congrArg norm
        simpa [s₀] using hverticalShift
      _ ≤ Kleft / 2 := hverticalLeftNorm
  have hstripExp :
      10 * d + p + 1 ≤ -(346 / 100 : ℝ) + A_F * ρ + ε := by
    dsimp [d, p, α]
    nlinarith [hβ]
  have hUexp : Real.rpow U (10 * d + p + 1) ≤
      Real.rpow U (-(346 / 100 : ℝ) + A_F * ρ + ε) :=
    Real.rpow_le_rpow_of_exponent_le hUone hstripExp
  have hUproduct : Real.rpow U (10 * d) * U * Real.rpow U p =
      Real.rpow U (10 * d + p + 1) := by
    have hpowAdd : Real.rpow U (10 * d) * Real.rpow U p = Real.rpow U (10 * d + p) :=
      (Real.rpow_add hUpos (10 * d) p).symm
    calc
      _ = Real.rpow U (10 * d) * Real.rpow U p * U := by ring
      _ = Real.rpow U (10 * d + p) * U :=
        congrArg (fun x => x * U) hpowAdd
      _ = Real.rpow U (10 * d + p) * Real.rpow U 1 := by
        simpa using congrArg (fun x : ℝ => Real.rpow U (10 * d + p) * x)
          (Real.rpow_one U).symm
      _ = Real.rpow U ((10 * d + p) + 1) :=
        (Real.rpow_add hUpos (10 * d + p) 1).symm
      _ = _ := by congr 1 <;> ring
  have hKleftBound : Kleft / 2 ≤
      (Gleft * Cmol * Cstrip / 2) * Real.rpow U (10 * d + p + 1) := by
    calc
      _ = (Gleft * Cmol / 2) * (Real.rpow U (10 * d) * Astrip * U) := by
        dsimp [Kleft]
        ring
      _ ≤ (Gleft * Cmol / 2) *
            (Real.rpow U (10 * d) * (Cstrip * Real.rpow U p) * U) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc
          Real.rpow U (10 * d) * Astrip * U =
              (Real.rpow U (10 * d) * U) * Astrip := by ring
          _ ≤ (Real.rpow U (10 * d) * U) * (Cstrip * Real.rpow U p) :=
            mul_le_mul_of_nonneg_left hAstripUniform
              (mul_nonneg (Real.rpow_nonneg hUpos.le _) hUpos.le)
          _ = Real.rpow U (10 * d) * (Cstrip * Real.rpow U p) * U := by ring
      _ = (Gleft * Cmol * Cstrip / 2) *
            (Real.rpow U (10 * d) * U * Real.rpow U p) := by ring
      _ = _ := by rw [hUproduct]
  have hKbound : Kleft / 2 ≤ C * Real.rpow U (-(346 / 100 : ℝ) + A_F * ρ + ε) := by
    calc
      _ ≤ (Gleft * Cmol * Cstrip / 2) * Real.rpow U (10 * d + p + 1) := hKleftBound
      _ = C * Real.rpow U (10 * d + p + 1) := by rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left hUexp (by positivity)
  exact ⟨hβone, hidentity, hdetNorm.trans hKbound⟩

/-- **zf:detector-count** (06-zero-free.tex:266-333): in a dyadic family, the number of
characters with a zero at `Re s ≥ .996`, `|Im s| ≤ 4 U^ρ`, is `O(U^{.088+ρ+ε})`. Corrected per
rev-a2 to count nonprincipal continuation zeros and per sol-gate-a2 to require the convexity
growth bound for the supplied field exponent. -/
theorem zf_detector_count
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (η : ArtinPrimitiveRoots.A1.HeckeChar F) (hη : IsOfFinOrder η)
    (fd : FrequencyData S D η)
    (L : ∀ u : fd.U, fd.omega u ≠ 1 → HeckeLContinuation (fd.omega u))
    (A_F ρ ε : ℝ) (hAF : 0 < A_F)
    (hρ : 0 < ρ ∧ ρ < min (1 / 10) (1 / (A_F + 1)))
    (hε : 0 < ε)
    (hGrowth : ConductorHeightBound (F := F) A_F) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 2 ≤ U →
      ∀ E : Finset fd.U,
        (∀ u ∈ E, U ≤ fd.q u ∧ fd.q u < 2 * U ∧
          ∃ hnon : fd.omega u ≠ 1, ∃ s : ℂ,
            996 / 1000 ≤ s.re ∧ |s.im| ≤ 4 * Real.rpow U ρ ∧ (L u hnon).value s = 0) →
        (E.card : ℝ) ≤ C * Real.rpow U (88 / 1000 + ρ + ε) := by
  obtain ⟨Cf, hCf, hcond⟩ := fd.conductor_bound
  have hAρ : A_F * ρ < 1 := by
    have h1 : ρ < 1 / (A_F + 1) := lt_of_lt_of_le hρ.2 (min_le_right _ _)
    have h2 : ρ * (A_F + 1) < 1 := by
      rwa [lt_div_iff₀ (by linarith)] at h1
    nlinarith [hρ.1]
  refine Proofs.A2ZeroDetect.detector_count_core S D η fd L A_F ρ ε hρ.1 hAρ hε
    ext_ideal_count ?_ ?_
  · intro δ hδ
    obtain ⟨C, hC, h⟩ := ext_divisor_bound (F := F) δ hδ
    exact ⟨C, hC, fun I hI => (h I hI).1⟩
  · intro δ hδ
    obtain ⟨C, hC, hsh⟩ := zf_detector_shift (F := F) A_F ρ δ (2 * Cf) hAF hδ (by positivity)
      hρ hGrowth
    refine ⟨C, hC, ?_⟩
    intro u hnon U β γ hU hq1 hq2 hz hβ hγ
    obtain ⟨𝔣, hprim, hnorm⟩ := hcond u
    have hN : (Ideal.absNorm 𝔣 : ℝ) ≤ 2 * Cf * U := by nlinarith
    have h := hsh (fd.omega u) 𝔣 hprim (fd.omega_finiteOrder u) hnon (L u hnon) U β γ hU hN hz
      hβ hγ (c := 2) (by norm_num)
    exact ⟨h.1, h.2.2⟩

/-- The exponent in the three-circles interpolation used for reciprocal bounds. -/
def reciprocalExponent : ℝ :=
  Real.log ((1002 / 1000 : ℝ) / (999 / 1000)) /
    Real.log ((1003 / 1000 : ℝ) / (999 / 1000))

open scoped ComplexOrder

private theorem reciprocal_dedekindZeta_re_eq_tsum (σ : ℝ) (hσ : 1 < σ) :
    (NumberField.dedekindZeta F (σ : ℂ)).re =
      ∑' n : ℕ, ‖LSeries.term
        (fun n => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ))
        (σ : ℂ) n‖ := by
  let count : ℕ → ℕ := fun n => Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n}
  have hs : LSeriesSummable (fun n => (count n : ℂ)) (σ : ℂ) := by
    exact_mod_cast DedekindResidue.count_LSeriesSummable F (by simpa using hσ)
  have hnonneg (n : ℕ) :
      0 ≤ LSeries.term (fun n => (count n : ℂ)) (σ : ℂ) n := by
    simpa using LSeries.term_nonneg (by positivity) σ
  calc
    (NumberField.dedekindZeta F (σ : ℂ)).re =
        (∑' n, LSeries.term (fun n => (count n : ℂ)) (σ : ℂ) n).re := rfl
    _ = ∑' n, (LSeries.term (fun n => (count n : ℂ)) (σ : ℂ) n).re :=
      Complex.re_tsum hs
    _ = ∑' n, ‖LSeries.term (fun n => (count n : ℂ)) (σ : ℂ) n‖ := by
      apply tsum_congr
      intro n
      exact congrArg Complex.re (Complex.eq_coe_norm_of_nonneg (hnonneg n))

private theorem reciprocal_dedekindZeta_re_antitone {σ₀ σ : ℝ}
    (hσ₀ : 1 < σ₀) (hle : σ₀ ≤ σ) :
    (NumberField.dedekindZeta F (σ : ℂ)).re ≤
      (NumberField.dedekindZeta F (σ₀ : ℂ)).re := by
  have hσ : 1 < σ := lt_of_lt_of_le hσ₀ hle
  rw [reciprocal_dedekindZeta_re_eq_tsum σ hσ,
    reciprocal_dedekindZeta_re_eq_tsum σ₀ hσ₀]
  have hσsum : LSeriesSummable
      (fun n => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)) (σ : ℂ) := by
    exact_mod_cast DedekindResidue.count_LSeriesSummable F (by simpa using hσ)
  have hterm (n : ℕ) :
      ‖LSeries.term
          (fun n => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ))
          (σ : ℂ) n‖ ≤
        ‖LSeries.term
          (fun n => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ))
          (σ₀ : ℂ) n‖ := by
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    split_ifs with hn
    · rfl
    · have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
      have hpow : (n : ℝ) ^ σ₀ ≤ (n : ℝ) ^ σ :=
        Real.rpow_le_rpow_of_exponent_le hnreal hle
      have hnum : 0 ≤ ‖(Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)‖ :=
        norm_nonneg _
      exact div_le_div_of_nonneg_left hnum (by positivity) hpow
  have hσ₀sum : LSeriesSummable
      (fun n => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)) (σ₀ : ℂ) := by
    exact_mod_cast DedekindResidue.count_LSeriesSummable F (by simpa using hσ₀)
  exact (hσsum.norm.tsum_le_tsum hterm
    hσ₀sum.norm)

private theorem reciprocal_complex_log_norm_bound {z : ℂ} {B : ℝ}
    (hB : 1 ≤ B) (hz : z ≠ 0) (hup : ‖z‖ ≤ B) (hinv : ‖z⁻¹‖ ≤ B) :
    ‖Complex.log z‖ ≤ Real.log B + Real.pi := by
  have hzp : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hBp : 0 < B := by linarith
  have hinvp : 0 < ‖z‖⁻¹ := inv_pos.mpr hzp
  have hlogUpper : Real.log ‖z‖ ≤ Real.log B := Real.log_le_log hzp hup
  have hinvNorm : ‖z‖⁻¹ ≤ B := by simpa [norm_inv] using hinv
  have hlogInv : Real.log (‖z‖⁻¹) ≤ Real.log B :=
    Real.log_le_log hinvp hinvNorm
  have hlogLower : -Real.log B ≤ Real.log ‖z‖ := by
    rw [Real.log_inv] at hlogInv
    linarith
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hre : |(Complex.log z).re| ≤ Real.log B := by
    rw [Complex.log_re]
    exact abs_le.mpr ⟨hlogLower, hlogUpper⟩
  have him : |(Complex.log z).im| ≤ Real.pi := by
    rw [Complex.log_im]
    exact Complex.abs_arg_le_pi z
  have hdecomp : Complex.log z = (Complex.log z).re + (Complex.log z).im * Complex.I := by
    apply Complex.ext
    · simp
    · simp
  calc
    ‖Complex.log z‖ = ‖(Complex.log z).re + (Complex.log z).im * Complex.I‖ :=
      congrArg norm hdecomp
    _ ≤ ‖((Complex.log z).re : ℂ)‖ + ‖((Complex.log z).im : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |(Complex.log z).re| + |(Complex.log z).im| := by simp
    _ ≤ Real.log B + Real.pi := add_le_add hre him

private theorem reciprocal_omitted_factor_bound
    (χ : ArtinPrimitiveRoots.A1.HeckeChar F) (hχ : IsOfFinOrder χ)
    (ξ : ℂ) (hξ : 998 / 1000 ≤ ξ.re) (v : ArtinPrimitiveRoots.A1.FinPlace F) :
    (1 - χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-ξ)) ≠ 0 ∧
      ‖(1 - χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-ξ))⁻¹‖ ≤
        (1 - (Ideal.absNorm v.asIdeal : ℝ) ^ (-(998 / 1000 : ℝ)))⁻¹ := by
  have hN : 1 < Ideal.absNorm v.asIdeal :=
    NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hNr : 1 < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast hN
  have hNpos : 0 < Ideal.absNorm v.asIdeal := by omega
  have hpowNorm : ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-ξ)‖ =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-ξ.re) := by
    rw [Complex.norm_natCast_cpow_of_pos hNpos]
    rfl
  have hpow : (Ideal.absNorm v.asIdeal : ℝ) ^ (-ξ.re) ≤
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-(998 / 1000 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith [hξ])
  have hr : (Ideal.absNorm v.asIdeal : ℝ) ^ (-(998 / 1000 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hNr (by norm_num)
  have hz : ‖χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-ξ)‖ ≤
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-(998 / 1000 : ℝ)) := by
    rw [norm_mul, hpowNorm]
    calc
      _ ≤ 1 * (Ideal.absNorm v.asIdeal : ℝ) ^ (-ξ.re) :=
        mul_le_mul_of_nonneg_right
          (ArtinPrimitiveRoots.Proofs.A2FreqP.reciprocal_primeValue_norm_le_one χ hχ v)
          (by positivity)
      _ ≤ 1 * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(998 / 1000 : ℝ)) := by gcongr
      _ = _ := by ring
  have hden : 0 < ‖1 - χ.primeValue v *
      (Ideal.absNorm v.asIdeal : ℂ) ^ (-ξ)‖ := by
    have htriangle := norm_sub_norm_le (1 : ℂ)
      (χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-ξ))
    have hlow : 0 < 1 - (Ideal.absNorm v.asIdeal : ℝ) ^ (-(998 / 1000 : ℝ)) :=
      sub_pos.mpr hr
    rw [norm_one] at htriangle
    nlinarith
  constructor
  · exact norm_pos_iff.mp hden
  · rw [norm_inv]
    have hlowpos : 0 < 1 - (Ideal.absNorm v.asIdeal : ℝ) ^ (-(998 / 1000 : ℝ)) :=
      sub_pos.mpr hr
    have htriangle := norm_sub_norm_le (1 : ℂ)
      (χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-ξ))
    rw [norm_one] at htriangle
    have hlow : 1 - (Ideal.absNorm v.asIdeal : ℝ) ^ (-(998 / 1000 : ℝ)) ≤
        ‖1 - χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-ξ)‖ := by
      nlinarith
    exact (inv_le_inv₀ hden hlowpos).2 hlow

private def reciprocalOmissionBound (S : ArtinPrimitiveRoots.A1.SData F CE condη) : ℝ :=
  ∏ v ∈ S.Sf, (1 - (Ideal.absNorm v.asIdeal : ℝ) ^ (-(998 / 1000 : ℝ)))⁻¹

private theorem reciprocal_omitted_product_inverse_bound
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (χ : ArtinPrimitiveRoots.A1.HeckeChar F) (hχ : IsOfFinOrder χ)
    (ξ : ℂ) (hξ : 998 / 1000 ≤ ξ.re) :
    let P := ∏ v ∈ S.Sf,
      (1 - χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-ξ))
    P ≠ 0 ∧ ‖P⁻¹‖ ≤ reciprocalOmissionBound S := by
  classical
  dsimp only
  let P := ∏ v ∈ S.Sf,
    (1 - χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-ξ))
  let Q := ∏ v ∈ S.Sf,
    (1 - χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-ξ))⁻¹
  have hcancel : P * Q = 1 := by
    dsimp [P, Q]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro v hv
    exact mul_inv_cancel₀
      (reciprocal_omitted_factor_bound χ hχ ξ hξ v).1
  have hP : P ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hcancel
    norm_num at hcancel
  have hPinv : P⁻¹ = Q := by
    calc
      P⁻¹ = P⁻¹ * 1 := by simp
      _ = P⁻¹ * (P * Q) := by rw [hcancel]
      _ = Q := by rw [← mul_assoc, inv_mul_cancel₀ hP, one_mul]
  have hQnorm : ‖Q‖ ≤ reciprocalOmissionBound S := by
    dsimp [Q, reciprocalOmissionBound]
    calc
      _ ≤ ∏ v ∈ S.Sf,
          ‖(1 - χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-ξ))⁻¹‖ :=
        Finset.norm_prod_le _ _
      _ ≤ ∏ v ∈ S.Sf,
          (1 - (Ideal.absNorm v.asIdeal : ℝ) ^ (-(998 / 1000 : ℝ)))⁻¹ := by
        apply Finset.prod_le_prod₀
        · intro v hv
          positivity
        · intro v hv
          exact (reciprocal_omitted_factor_bound χ hχ ξ hξ v).2
  exact ⟨hP, by rw [hPinv]; exact hQnorm⟩

open Metric Set Complex
open scoped Topology
set_option maxHeartbeats 1000000

/-- **zf:reciprocal-bound** (06-zero-free.tex:335-366): zero-free control for the primitive twist
implies a `U^ε` bound for the reciprocal incomplete L-function on the smaller rectangle. Corrected
per rev-a2 to use incomplete analytic continuations and a constant uniform in dyadic `U`. -/
theorem zf_reciprocal_bound
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (η : ArtinPrimitiveRoots.A1.HeckeChar F) (hη : IsOfFinOrder η)
    (fd : FrequencyData S D η)
    (Lomega : ∀ u : fd.U, fd.omega u ≠ 1 → HeckeLContinuation (fd.omega u))
    (Linc : ∀ u : fd.U, fd.omega u ≠ 1 →
      IncompleteHeckeLContinuation S (η * (fd.kummer u)⁻¹))
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ ε : ℝ, 0 < ε →
      ∃ Cε : ℝ, 0 < Cε ∧ ∀ U : ℝ, U₀ ≤ U →
        ∀ u, U ≤ fd.q u → fd.q u < 2 * U →
          ∀ hnon : fd.omega u ≠ 1,
          (∀ s : ℂ, 996 / 1000 ≤ s.re →
            |s.im| ≤ 4 * Real.rpow U ρ → (Lomega u hnon).value s ≠ 0) →
          ∀ ξ : ℂ, 998 / 1000 ≤ ξ.re →
            |ξ.im| ≤ 2 * Real.rpow U ρ →
            ‖((Linc u hnon).value ξ)⁻¹‖ ≤ Cε * Real.rpow U ε := by
  classical
  let a : ℝ := 996 / 1000
  let e : ℝ := 1 / 4000
  let R : ℝ := 2 - a - 2 * e
  let Rinc : ℝ := 2 - 997 / 1000
  let Rpoly : ℝ := 2 - a - 3 * e
  let Rinner : ℝ := 2 - a - 6 * e
  have hRpos : 0 < R := by norm_num [R, a, e]
  have hRbig : R < 2 := by norm_num [R, a, e]
  have hRincpos : 0 < Rinc := by norm_num [Rinc]
  have hRinc_le_R : Rinc < R := by norm_num [Rinc, R, a, e]
  have hRpoly_le_R : Rpoly < R := by norm_num [Rpoly, R, a, e]
  have hRinner_target : (2 - 998 / 1000 : ℝ) < Rinner := by
    norm_num [Rinner, a, e]
  let U₀ : ℝ := max (Real.exp 1) (Real.rpow R (ρ⁻¹))
  have hU₀two : 2 ≤ U₀ := by
    dsimp [U₀]
    exact (Real.exp_one_gt_two.le.trans (le_max_left _ _))
  have hrootpow : Real.rpow (Real.rpow R (ρ⁻¹)) ρ = R :=
    Real.rpow_inv_rpow hRpos.le hρ.ne'
  have hTge (U : ℝ) (hU₀ : U₀ ≤ U) : R ≤ Real.rpow U ρ := by
    have hroot : Real.rpow R (ρ⁻¹) ≤ U := (le_max_right _ _).trans hU₀
    have hrootpos : 0 < Real.rpow R (ρ⁻¹) := Real.rpow_pos_of_pos hRpos _
    have hmono := Real.rpow_le_rpow hrootpos.le hroot hρ.le
    rw [← hrootpow]
    exact hmono
  obtain ⟨A_F, hA_F, hconvAll⟩ := zf_convexity (F := F)
  obtain ⟨Ccv, hCcv, hconv⟩ := hconvAll 1 (by norm_num)
  obtain ⟨Cfd, hCfd, hconductor⟩ := fd.conductor_bound
  let H : ℝ := max 1 (2 * Cfd)
  let p : ℝ := 3 / 2 + A_F * ρ
  let K₀ : ℝ := Ccv * Real.rpow H (3 / 2) * Real.rpow 6 A_F
  let K : ℝ := max (Real.exp 1) K₀
  let B : ℝ := |(NumberField.dedekindZeta F ((3 / 2 : ℝ) : ℂ)).re| + 1
  let A : ℝ := 100 + 197 * Real.log B + 99 * Real.pi
  have hH : 1 ≤ H := le_max_left _ _
  have hH₂ : 2 * Cfd ≤ H := le_max_right _ _
  have hK : Real.exp 1 ≤ K := le_max_left _ _
  have hK₀ : K₀ ≤ K := le_max_right _ _
  have hKpos : 0 < K := (Real.exp_pos 1).trans_le hK
  have hB : 1 ≤ B := by
    have h := abs_nonneg (NumberField.dedekindZeta F ((3 / 2 : ℝ) : ℂ)).re
    dsimp [B]
    linarith
  have hBz : (NumberField.dedekindZeta F ((3 / 2 : ℝ) : ℂ)).re ≤ B := by
    dsimp [B]
    linarith [le_abs_self (NumberField.dedekindZeta F ((3 / 2 : ℝ) : ℂ)).re]
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hA : 1 ≤ A := by
    have hterm₁ : 0 ≤ 197 * Real.log B := mul_nonneg (by norm_num) hlogB
    have hterm₂ : 0 ≤ 99 * Real.pi := by positivity
    dsimp [A]
    linarith
  have hp : 1 ≤ p := by
    dsimp [p]
    nlinarith [mul_pos hA_F hρ]
  have hZbound (σ : ℝ) (hσ : 3 / 2 ≤ σ) :
      (NumberField.dedekindZeta F (σ : ℂ)).re ≤ B := by
    calc
      _ ≤ (NumberField.dedekindZeta F ((3 / 2 : ℝ) : ℂ)).re :=
        reciprocal_dedekindZeta_re_antitone (by norm_num) hσ
      _ ≤ B := hBz
  have hCcvnonneg : 0 ≤ Ccv := hCcv.le
  have hK₀nonneg : 0 ≤ K₀ := by
    dsimp [K₀]
    positivity
  refine ⟨U₀, hU₀two, ?_⟩
  intro ε hε
  obtain ⟨Drec, hDrec, hlogControl⟩ :=
    OAI.SevenEighths.LogarithmicControl.logarithmic_control
      (e := e) (A := A) (M := p) (ε := ε)
      (by norm_num [e]) (by norm_num [e]) hA hp hε
  have hOmissionPos : 0 < reciprocalOmissionBound S := by
    unfold reciprocalOmissionBound
    apply Finset.prod_pos
    intro v hv
    have hvN : 1 < (Ideal.absNorm v.asIdeal : ℝ) := by
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
    have hpow : (Ideal.absNorm v.asIdeal : ℝ) ^ (-(998 / 1000 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hvN (by norm_num)
    exact inv_pos.mpr (sub_pos.mpr hpow)
  let Cε : ℝ := reciprocalOmissionBound S * (Drec * Real.rpow K ε + B)
  have hCε : 0 < Cε := by
    dsimp [Cε]
    positivity
  refine ⟨Cε, hCε, ?_⟩
  intro U hU₀ u hqlo hqhi hnon hzero ξ hξ hξim
  have hUpos : 0 < U := by linarith [hU₀two.trans hU₀]
  have hUone : 1 ≤ U := by linarith
  let T : ℝ := Real.rpow U ρ
  have hTpos : 0 < T := Real.rpow_pos_of_pos hUpos _
  have hTR : R ≤ T := by simpa [T] using hTge U hU₀
  obtain ⟨f, hprim, hnormf⟩ := hconductor u
  have hnormf' : (Ideal.absNorm f : ℝ) ≤ H * U := by
    calc
      (Ideal.absNorm f : ℝ) ≤ Cfd * fd.q u := hnormf
      _ ≤ Cfd * (2 * U) := mul_le_mul_of_nonneg_left (le_of_lt hqhi) hCfd.le
      _ = (2 * Cfd) * U := by ring
      _ ≤ H * U := mul_le_mul_of_nonneg_right hH₂ hUpos.le
  have hfNormPos : 0 < (Ideal.absNorm f : ℝ) := by
    have hf0 : f ≠ ⊥ := hprim.1
    have hfN : 0 < Ideal.absNorm f :=
      Ideal.absNorm_pos_of_nonZeroDivisors
        ⟨f, mem_nonZeroDivisors_of_ne_zero hf0⟩
    exact_mod_cast hfN
  let ω : ArtinPrimitiveRoots.A1.HeckeChar F := fd.omega u
  let L : HeckeLContinuation ω := Lomega u hnon
  let χ : ArtinPrimitiveRoots.A1.HeckeChar F := η * (fd.kummer u)⁻¹
  let inc : IncompleteHeckeLContinuation S χ := Linc u hnon
  have hωfinite : IsOfFinOrder ω := fd.omega_finiteOrder u
  obtain ⟨m, ψ, hseries⟩ := frequency_heckeLSeries_eq_ray ω hωfinite f hprim
  have hLray (s : ℂ) (hs : 1 < s.re) :
      L.value s = ArtinPrimitiveRoots.Hecke.LSeriesRay ψ s := by
    calc
      L.value s = heckeLSeries ω s := L.agrees s hs
      _ = ArtinPrimitiveRoots.Hecke.LSeriesRay ψ s := hseries s hs
  have hRayBounds (s : ℂ) (hs : 3 / 2 ≤ s.re) :
      ‖L.value s‖ ≤ B ∧ L.value s ≠ 0 ∧ ‖(L.value s)⁻¹‖ ≤ B := by
    have hs' : 1 < s.re := by linarith
    have hRay := ArtinPrimitiveRoots.Hecke.norm_LSeriesRay_le ψ hs'
    have hZ := hZbound s.re hs
    have heq := hLray s hs'
    refine ⟨?_, ?_, ?_⟩
    · calc
        ‖L.value s‖ = ‖ArtinPrimitiveRoots.Hecke.LSeriesRay ψ s‖ := by rw [heq]
        _ ≤ (NumberField.dedekindZeta F s.re).re := hRay.1
        _ ≤ B := hZ
    · intro hzero
      apply hRay.2.1
      rw [← heq]
      exact hzero
    · calc
        ‖(L.value s)⁻¹‖ = ‖(ArtinPrimitiveRoots.Hecke.LSeriesRay ψ s)⁻¹‖ := by rw [heq]
        _ ≤ (NumberField.dedekindZeta F s.re).re := hRay.2.2
        _ ≤ B := hZ
  have hGrowthData := hconv ω hωfinite hnon f hprim L.value
    ⟨L.differentiable, L.agrees⟩
  let Cline : ℝ := K * U
  have hCline : Real.exp 1 ≤ Cline := by
    dsimp [Cline]
    calc
      Real.exp 1 ≤ K := hK
      _ ≤ K * U := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hUone hKpos.le
  have hzeroBall {s : ℂ} (c : ℂ) (t : ℝ) (hc : c = 2 + (t : ℂ) * Complex.I)
      (ht : |t| ≤ 2 * T) (hs : s ∈ Metric.ball c R) :
      996 / 1000 ≤ s.re ∧ |s.im| ≤ 4 * T := by
    have hdist : ‖s - c‖ < R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hs
    have hcRe : c.re = 2 := by rw [hc]; simp
    have hcIm : c.im = t := by rw [hc]; simp
    have hReNorm : |s.re - 2| ≤ ‖s - c‖ := by
      calc
        |s.re - 2| = |(s - c).re| := by simp [Complex.sub_re, hcRe]
        _ ≤ ‖s - c‖ := Complex.abs_re_le_norm _
    have himNorm : |s.im - t| ≤ ‖s - c‖ := by
      calc
        |s.im - t| = |(s - c).im| := by simp [Complex.sub_im, hcIm]
        _ ≤ ‖s - c‖ := Complex.abs_im_le_norm _
    have hReLo : 996 / 1000 ≤ s.re := by
      have h := (abs_lt.mp (hReNorm.trans_lt hdist)).1
      dsimp [R, a, e] at h
      linarith
    have hIm : |s.im| ≤ |t| + |s.im - t| := by
      have hsum : s.im = t + (s.im - t) := by ring
      calc
        |s.im| = |t + (s.im - t)| := congrArg abs hsum
        _ ≤ |t| + |s.im - t| := abs_add_le _ _
    have hTbig : R ≤ 2 * T := by linarith [hTR]
    refine ⟨hReLo, ?_⟩
    calc
      |s.im| ≤ |t| + |s.im - t| := hIm
      _ ≤ 2 * T + R := by linarith [ht, himNorm.trans hdist.le]
      _ ≤ 4 * T := by linarith
  let c : ℂ := 2 + (ξ.im : ℂ) * Complex.I
  have hcRe : c.re = 2 := by simp [c]
  have hcIm : c.im = ξ.im := by simp [c]
  let P : ℂ → ℂ := fun s => ∏ v ∈ S.Sf,
    (1 - ω.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))
  have hPdiff : Differentiable ℂ P := by
    dsimp [P]
    exact ArtinPrimitiveRoots.Proofs.A2FreqP.reciprocal_omittedEulerFactors_differentiable S ω
  have hPInv := reciprocal_omitted_product_inverse_bound S ω hωfinite ξ hξ
  have hincFactor (s : ℂ) (hs : 1 < s.re) :
      inc.value s = L.value s * P s := by
    have hfactor := ArtinPrimitiveRoots.Proofs.A2FreqP.reciprocal_incompleteHeckeLSeries_eq_complete_factors
      (S := S) ω hωfinite s hs
    calc
      inc.value s = incompleteHeckeLSeries S χ s := inc.agrees s hs
      _ = incompleteHeckeLSeries S ω s := by
        dsimp [χ, ω]
        rw [fd.omega_induces_twist u]
      _ = heckeLSeries ω s * P s := by simpa [P] using hfactor
      _ = L.value s * P s := by rw [← L.agrees s hs]
  have hRincBall (s : ℂ) (hs : s ∈ Metric.ball c Rinc) :
      997 / 1000 < s.re := by
    have hdist : ‖s - c‖ < Rinc := by simpa [Metric.mem_ball, dist_eq_norm] using hs
    have hReNorm : |s.re - 2| ≤ ‖s - c‖ := by
      have hh := Complex.abs_re_le_norm (s - c)
      have hReEq : (s - c).re = s.re - 2 := by rw [Complex.sub_re, hcRe]
      rw [hReEq] at hh
      exact hh
    have h := (abs_lt.mp (hReNorm.trans_lt hdist)).1
    dsimp [Rinc] at h
    linarith
  have hincDiff : DifferentiableOn ℂ inc.value (Metric.ball c Rinc) :=
    inc.differentiableOn.mono (by
      intro s hs
      exact hRincBall s hs)
  have hprodDiff : DifferentiableOn ℂ (fun s => L.value s * P s)
      (Metric.ball c Rinc) :=
    (L.differentiable.differentiableOn.mul hPdiff.differentiableOn)
  have hincAnalytic : AnalyticOnNhd ℂ inc.value (Metric.ball c Rinc) :=
    hincDiff.analyticOnNhd isOpen_ball
  have hprodAnalytic : AnalyticOnNhd ℂ (fun s => L.value s * P s)
      (Metric.ball c Rinc) := hprodDiff.analyticOnNhd isOpen_ball
  have hcRePos : 1 < c.re := by simp [c]
  have hEqEvent : inc.value =ᶠ[𝓝 c] (fun s => L.value s * P s) := by
    have hopen : {s : ℂ | 1 < s.re} ∈ 𝓝 c :=
      (isOpen_lt continuous_const continuous_re).mem_nhds hcRePos
    filter_upwards [hopen] with s hs
    exact hincFactor s hs
  have hEqOn : EqOn inc.value (fun s => L.value s * P s) (Metric.ball c Rinc) :=
    hincAnalytic.eqOn_of_preconnected_of_eventuallyEq hprodAnalytic
      (convex_ball c Rinc).isPreconnected (Metric.mem_ball_self hRincpos) hEqEvent
  by_cases hξle2 : ξ.re ≤ 2
  · have hdistEq : ξ - c = ((ξ.re - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [c]
    have hdist : dist ξ c ≤ Rinner := by
      rw [dist_eq_norm, hdistEq, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith : ξ.re - 2 ≤ 0)]
      dsimp [Rinner, a, e]
      linarith [hξ]
    have hξBall : ξ ∈ Metric.closedBall c Rinner := by
      simpa [Metric.mem_closedBall] using hdist
    have hξBallInc : ξ ∈ Metric.ball c Rinc := by
      rw [Metric.mem_ball]
      exact hdist.trans_lt (by norm_num [Rinner, Rinc, a, e])
    have hLzero : L.value ξ ≠ 0 := hzero ξ (by linarith [hξ]) (by linarith [hξim])
    have hLdiffOuter : DifferentiableOn ℂ L.value (Metric.ball c R) :=
      L.differentiable.differentiableOn
    have hLzeroOuter : ∀ s ∈ Metric.ball c R, L.value s ≠ 0 := by
      intro s hs
      obtain ⟨hre, him⟩ := hzeroBall c ξ.im rfl hξim hs
      exact hzero s hre him
    have hLcBounds := hRayBounds c (by simp [c]; norm_num)
    obtain ⟨g, hg, hge, hgc⟩ :=
      OAI.SevenEighths.LogarithmicControl.exists_holomorphic_log_normalized
        hRpos hLdiffOuter hLzeroOuter (Complex.exp_log hLcBounds.2.1)
    have hReBound : ∀ w ∈ Metric.closedBall c (1 / 2),
        (g w).re ≤ Real.log B := by
      intro w hw
      have hwOuter : w ∈ Metric.ball c R :=
        Metric.closedBall_subset_ball (by norm_num [R, a, e]) hw
      have hExpw := hge hwOuter
      have hRew : 3 / 2 ≤ w.re := by
        have hdist : ‖w - c‖ ≤ 1 / 2 := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hw
        have habs : |w.re - 2| ≤ ‖w - c‖ := by
          have hh := Complex.abs_re_le_norm (w - c)
          have hReEq : (w - c).re = w.re - 2 := by rw [Complex.sub_re, hcRe]
          rw [hReEq] at hh
          exact hh
        have hlow := (abs_le.mp (habs.trans hdist)).1
        linarith
      have hLw := hRayBounds w hRew
      have hExpw : Complex.exp (g w) = L.value w := by
        simpa only [Function.comp_apply] using hge hwOuter
      have hnormEq : Real.exp (g w).re = ‖L.value w‖ := by
        calc
          Real.exp (g w).re = ‖Complex.exp (g w)‖ := by rw [Complex.norm_exp]
          _ = ‖L.value w‖ := by rw [hExpw]
      have hlogEq : (g w).re = Real.log ‖L.value w‖ := by
        calc
          (g w).re = Real.log (Real.exp (g w).re) := by rw [Real.log_exp]
          _ = Real.log ‖L.value w‖ := by rw [hnormEq]
      rw [hlogEq]
      exact Real.log_le_log (norm_pos_iff.mpr hLw.2.1) hLw.1
    have hlogCenter := reciprocal_complex_log_norm_bound hB hLcBounds.2.1
      hLcBounds.1 hLcBounds.2.2
    have hgcNorm : ‖g c‖ ≤ Real.log B + Real.pi := by
      rw [hgc]
      exact hlogCenter
    have hReBoundBall : ∀ w ∈ Metric.ball c (1 / 2),
        (g w).re ≤ Real.log B + 1 := by
      intro w hw
      exact (hReBound w (Metric.ball_subset_closedBall hw)).trans (by linarith)
    have hgBall : DifferentiableOn ℂ g (Metric.ball c (1 / 2)) :=
      hg.mono (Metric.ball_subset_ball (by norm_num [R, a, e]))
    have hbc (s : ℂ) (hs : s ∈ Metric.closedBall c (49 / 100)) :
        ‖g s‖ ≤ 2 * (Real.log B + 1) * (49 / 100) / (1 / 2 - 49 / 100) +
          (Real.log B + Real.pi) * (1 / 2 + 49 / 100) / (1 / 2 - 49 / 100) :=
      OAI.SevenEighths.LogarithmicControl.borel_caratheodory_closedBall
        (by norm_num) (by norm_num) (by linarith [hlogB]) (by positivity)
        hgBall hReBoundBall hgcNorm hs
    have hEbound : ∀ s ∈ Metric.closedBall c (49 / 100), ‖g s‖ ≤ A := by
      intro s hs
      have hbc' := hbc s hs
      have hbound : ‖g s‖ ≤ 197 * Real.log B + 98 + 99 * Real.pi := by
        calc
          ‖g s‖ ≤ 2 * (Real.log B + 1) * (49 / 100) / (1 / 2 - 49 / 100) +
              (Real.log B + Real.pi) * (1 / 2 + 49 / 100) / (1 / 2 - 49 / 100) := hbc'
          _ = 197 * Real.log B + 98 + 99 * Real.pi := by norm_num <;> ring
      dsimp [A]
      linarith
    have hEdiff : DifferentiableOn ℂ g (Metric.ball c (1 / 2)) :=
      hg.mono (Metric.ball_subset_ball (by norm_num [R, a, e]))
    have hEeq : Set.EqOn (Complex.exp ∘ g) L.value (Metric.ball c (1 / 2)) := by
      intro s hs
      exact hge (Metric.ball_subset_ball (by norm_num [R, a, e]) hs)
    have hpoly : ∀ s ∈ Metric.ball c Rpoly, ‖L.value s‖ ≤ Real.rpow Cline p := by
      intro s hs
      have hsOuter : s ∈ Metric.ball c R :=
        Metric.ball_subset_ball (by norm_num [Rpoly, R, a, e]) hs
      obtain ⟨hre, him⟩ := hzeroBall c ξ.im rfl hξim hsOuter
      have hre' : 3 / 1000 ≤ s.re := by linarith
      have hre4 : s.re ≤ 4 := by
        have hdist : ‖s - c‖ < R := by
          simpa [Metric.mem_ball, dist_eq_norm] using hsOuter
        have hReNorm : |s.re - 2| ≤ ‖s - c‖ := by
          have hh := Complex.abs_re_le_norm (s - c)
          have hReEq : (s - c).re = s.re - 2 := by rw [Complex.sub_re, hcRe]
          rw [hReEq] at hh
          exact hh
        have habs : |s.re - 2| < R := hReNorm.trans_lt hdist
        have hupper := (abs_lt.mp habs).2
        dsimp [R, a, e] at hupper
        linarith
      have hGrowth := hGrowthData.1 s hre' hre4
      have hcf' : Real.rpow (Ideal.absNorm f : ℝ) (3 / 2) ≤
          Real.rpow (H * U) (3 / 2) :=
        Real.rpow_le_rpow hfNormPos.le hnormf' (by norm_num)
      have hcf : Real.rpow (Ideal.absNorm f : ℝ) (1 / 2 + 1) ≤
          Real.rpow (H * U) (3 / 2) := by
        have hexp : (1 / 2 + 1 : ℝ) = 3 / 2 := by norm_num
        rw [hexp]
        exact hcf'
      have hheight : 2 + |s.im| ≤ 6 * T := by
        have hdist : ‖s - c‖ < R := by
          simpa [Metric.mem_ball, dist_eq_norm] using hsOuter
        have hImNorm : |s.im - ξ.im| ≤ ‖s - c‖ := by
          have hh := Complex.abs_im_le_norm (s - c)
          have hImEq : (s - c).im = s.im - ξ.im := by rw [Complex.sub_im, hcIm]
          rw [hImEq] at hh
          exact hh
        have hsum : s.im = ξ.im + (s.im - ξ.im) := by ring
        have hxiL := neg_abs_le ξ.im
        have hxiU := le_abs_self ξ.im
        have hdiffL := neg_abs_le (s.im - ξ.im)
        have hdiffU := le_abs_self (s.im - ξ.im)
        have him4 : |s.im| ≤ 4 * T := by
          apply abs_le.mpr
          constructor
          · rw [hsum]
            nlinarith [hxiL, hdiffL, hξim, hImNorm.trans hdist.le, hTR]
          · rw [hsum]
            nlinarith [hxiU, hdiffU, hξim, hImNorm.trans hdist.le, hTR]
        have hTone : 1 ≤ T := by
          have hRone : 1 ≤ R := by norm_num [R, a, e]
          linarith [hTR]
        nlinarith [him4, hTone]
      have hht : Real.rpow (2 + |s.im|) A_F ≤ Real.rpow (6 * T) A_F :=
        Real.rpow_le_rpow (by positivity) hheight hA_F.le
      have hmul : Ccv * Real.rpow (Ideal.absNorm f : ℝ) (1 / 2 + 1) *
          Real.rpow (2 + |s.im|) A_F ≤
          Ccv * Real.rpow (H * U) (3 / 2) * Real.rpow (6 * T) A_F := by
        calc
          _ = (Ccv * Real.rpow (Ideal.absNorm f : ℝ) (1 / 2 + 1)) *
                Real.rpow (2 + |s.im|) A_F := by ring
          _ ≤ (Ccv * Real.rpow (H * U) (3 / 2)) *
                Real.rpow (2 + |s.im|) A_F :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hcf hCcv.le)
              (Real.rpow_nonneg (by positivity) _)
          _ ≤ (Ccv * Real.rpow (H * U) (3 / 2)) *
                Real.rpow (6 * T) A_F :=
            mul_le_mul_of_nonneg_left hht
              (mul_nonneg hCcv.le (Real.rpow_nonneg (by positivity) _))
      have hsplitH : Real.rpow (H * U) (3 / 2) =
          Real.rpow H (3 / 2) * Real.rpow U (3 / 2) :=
        Real.mul_rpow (by positivity) hUpos.le
      have hsplit6 : Real.rpow (6 * T) A_F =
          Real.rpow 6 A_F * Real.rpow T A_F :=
        Real.mul_rpow (by norm_num) hTpos.le
      have hTpow : Real.rpow T A_F = Real.rpow U (ρ * A_F) := by
        dsimp [T]
        exact (Real.rpow_mul hUpos.le ρ A_F).symm
      have hcombine : Real.rpow U (3 / 2) * Real.rpow U (ρ * A_F) =
          Real.rpow U p := by
        calc
          _ = Real.rpow U ((3 / 2) + (ρ * A_F)) :=
            (Real.rpow_add hUpos _ _).symm
          _ = Real.rpow U p := by congr 1; dsimp [p]; ring
      have hgrowth' : ‖L.value s‖ ≤ K₀ * Real.rpow U p := by
        calc
          ‖L.value s‖ ≤ Ccv * Real.rpow (Ideal.absNorm f : ℝ) (1 / 2 + 1) *
              Real.rpow (2 + |s.im|) A_F := hGrowth
          _ ≤ Ccv * Real.rpow (H * U) (3 / 2) * Real.rpow (6 * T) A_F := hmul
          _ = K₀ * Real.rpow U p := by
            calc
              _ = Ccv * (Real.rpow H (3 / 2) * Real.rpow U (3 / 2)) *
                    (Real.rpow 6 A_F * Real.rpow T A_F) := by
                rw [hsplitH, hsplit6]
              _ = Ccv * (Real.rpow H (3 / 2) * Real.rpow 6 A_F) *
                    (Real.rpow U (3 / 2) * Real.rpow U (ρ * A_F)) := by
                rw [hTpow]
                ring
              _ = K₀ * Real.rpow U p := by
                calc
                  _ = Ccv * (Real.rpow H (3 / 2) * Real.rpow 6 A_F) *
                        Real.rpow U p :=
                    congrArg (fun x : ℝ =>
                      Ccv * (Real.rpow H (3 / 2) * Real.rpow 6 A_F) * x) hcombine
                  _ = K₀ * Real.rpow U p := by dsimp [K₀]; ring
      have hKone : 1 ≤ K := by
        exact (Real.one_le_exp (by norm_num : 0 ≤ (1 : ℝ))).trans hK
      have hKpower : K ≤ Real.rpow K p := by
        calc
          K = Real.rpow K 1 := (Real.rpow_one K).symm
          _ ≤ Real.rpow K p := Real.rpow_le_rpow_of_exponent_le hKone hp
      calc
        ‖L.value s‖ ≤ K₀ * Real.rpow U p := hgrowth'
        _ ≤ K * Real.rpow U p :=
          mul_le_mul_of_nonneg_right hK₀ (Real.rpow_nonneg hUpos.le _)
        _ ≤ Real.rpow (K * U) p := by
          have hmulKU : Real.rpow (K * U) p = Real.rpow K p * Real.rpow U p :=
            Real.mul_rpow hKpos.le hUpos.le
          calc
            K * Real.rpow U p ≤ Real.rpow K p * Real.rpow U p :=
              mul_le_mul_of_nonneg_right hKpower (Real.rpow_nonneg hUpos.le _)
            _ = Real.rpow (K * U) p := hmulKU.symm
    have hcontrol := hlogControl a Cline L.value g c
      (by norm_num [a]) (by norm_num [a]) hCline
      hLdiffOuter hLzeroOuter hpoly hEdiff hEeq hEbound
    have hctrl' : ‖(L.value ξ)⁻¹‖ ≤ Drec * Real.rpow Cline ε := by
      have hsum := hcontrol.1 ξ hξBall
      exact (le_add_of_nonneg_left (norm_nonneg (L.value ξ))).trans hsum
    have hLincEq := hEqOn hξBallInc
    have hprodne : P ξ ≠ 0 := hPInv.1
    have hlinvProduct : ‖(inc.value ξ)⁻¹‖ =
        ‖(L.value ξ)⁻¹‖ * ‖(P ξ)⁻¹‖ := by
      rw [hLincEq, mul_inv, norm_mul]
    have hCpow : Real.rpow Cline ε = Real.rpow K ε * Real.rpow U ε := by
      dsimp [Cline]
      exact Real.mul_rpow hKpos.le hUpos.le
    have hDline : 0 ≤ Drec * Real.rpow Cline ε :=
      mul_nonneg hDrec.le (Real.rpow_nonneg (by positivity) _)
    have hbase : ‖(inc.value ξ)⁻¹‖ ≤
        Drec * Real.rpow K ε * Real.rpow U ε * reciprocalOmissionBound S := by
      calc
        ‖(inc.value ξ)⁻¹‖ = ‖(L.value ξ)⁻¹‖ * ‖(P ξ)⁻¹‖ := hlinvProduct
        _ ≤ (Drec * Real.rpow Cline ε) * ‖(P ξ)⁻¹‖ :=
          mul_le_mul_of_nonneg_right hctrl' (norm_nonneg _)
        _ ≤ (Drec * Real.rpow Cline ε) * reciprocalOmissionBound S :=
          mul_le_mul_of_nonneg_left hPInv.2 hDline
        _ = Drec * Real.rpow K ε * Real.rpow U ε * reciprocalOmissionBound S := by
          rw [hCpow]
          ring
    have hfinal : ‖(inc.value ξ)⁻¹‖ ≤ Cε * Real.rpow U ε := by
      dsimp [Cε]
      have hcoefBase : Drec * Real.rpow K ε ≤ Drec * Real.rpow K ε + B :=
        le_add_of_nonneg_right (by linarith [hB])
      have hcoeff : Drec * Real.rpow K ε * reciprocalOmissionBound S ≤
          (Drec * Real.rpow K ε + B) * reciprocalOmissionBound S :=
        mul_le_mul_of_nonneg_right hcoefBase hOmissionPos.le
      calc
        _ ≤ (Drec * Real.rpow K ε * reciprocalOmissionBound S) *
              Real.rpow U ε := by nlinarith [hbase]
        _ ≤ ((Drec * Real.rpow K ε + B) * reciprocalOmissionBound S) *
              Real.rpow U ε :=
          mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hUpos.le _)
        _ = Cε * Real.rpow U ε := by dsimp [Cε]; ring
    exact hfinal
  · have hξgt2 : 2 < ξ.re := lt_of_not_ge hξle2
    have hLinv : ‖(L.value ξ)⁻¹‖ ≤ B :=
      (hRayBounds ξ (by linarith)).2.2
    have hEqAt : inc.value ξ = L.value ξ * P ξ := hincFactor ξ (by linarith)
    have hbound : ‖(inc.value ξ)⁻¹‖ ≤ B * reciprocalOmissionBound S := by
      calc
        ‖(inc.value ξ)⁻¹‖ = ‖(L.value ξ)⁻¹‖ * ‖(P ξ)⁻¹‖ := by
          rw [hEqAt, mul_inv, norm_mul]
        _ ≤ B * ‖(P ξ)⁻¹‖ := mul_le_mul_of_nonneg_right hLinv (norm_nonneg _)
        _ ≤ B * reciprocalOmissionBound S :=
          mul_le_mul_of_nonneg_left hPInv.2 (by linarith [hB])
    have hUε : 1 ≤ Real.rpow U ε := Real.one_le_rpow hUone hε.le
    have hfinal : ‖(inc.value ξ)⁻¹‖ ≤ Cε * Real.rpow U ε := by
      dsimp [Cε]
      have hDK : 0 ≤ Drec * Real.rpow K ε :=
        mul_nonneg hDrec.le (Real.rpow_nonneg hKpos.le _)
      have hcoefBase : B ≤ Drec * Real.rpow K ε + B :=
        le_add_of_nonneg_left hDK
      have hcoeff : B * reciprocalOmissionBound S ≤
          (Drec * Real.rpow K ε + B) * reciprocalOmissionBound S :=
        mul_le_mul_of_nonneg_right hcoefBase hOmissionPos.le
      calc
        _ ≤ B * reciprocalOmissionBound S := hbound
        _ ≤ (Drec * Real.rpow K ε + B) * reciprocalOmissionBound S := hcoeff
        _ ≤ ((Drec * Real.rpow K ε + B) * reciprocalOmissionBound S) *
              Real.rpow U ε :=
          (by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hUε
              (by positivity : 0 ≤ (Drec * Real.rpow K ε + B) * reciprocalOmissionBound S))
        _ = Cε * Real.rpow U ε := by dsimp [Cε]; ring
    exact hfinal

namespace Proofs.A2Z1
open Metric Set Complex
open scoped Topology

/-- A centered closed-disk form of Borel--Carathéodory, including the zero-margin case. -/
theorem borel_caratheodory_centered {f : ℂ → ℂ} {c : ℂ} {R r M : ℝ}
    (hR : 0 < R) (hr : 0 ≤ r) (hsmall : r < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hRe : ∀ z ∈ Metric.closedBall c R, (f z).re ≤ M) :
    ∀ z ∈ Metric.closedBall c r,
      ‖f z - f c‖ ≤ (2 * r / (R - r)) * (M - (f c).re) := by
  have hfc : (f c).re ≤ M := hRe c (by simp [Metric.mem_closedBall, hR.le])
  let d : ℝ := M - (f c).re
  let q : ℝ := 2 * r / (R - r)
  have hd : 0 ≤ d := sub_nonneg.mpr hfc
  let g : ℂ → ℂ := fun w => f w - f c
  have hfd : DifferentiableOn ℂ f (Metric.ball c R) :=
    hf.differentiableOn.mono Metric.ball_subset_closedBall
  have hgd : DifferentiableOn ℂ g (Metric.ball c R) := hfd.sub_const (f c)
  intro z hz
  by_cases hr0 : r = 0
  · have hdist : dist z c = 0 := by
      apply le_antisymm
      · simpa [hr0] using hz
      · exact dist_nonneg
    have hzc : z = c := dist_eq_zero.mp hdist
    simp [hzc, hr0]
  · have hrpos : 0 < r := lt_of_le_of_ne hr (by
      intro h
      exact hr0 h.symm)
    have hqpos : 0 < q := by
      dsimp [q]
      exact div_pos (mul_pos (by norm_num) hrpos) (sub_pos.mpr hsmall)
    change ‖g z‖ ≤ q * d
    by_contra hnot
    have hbadTarget : q * d < ‖g z‖ := lt_of_not_ge hnot
    let δ : ℝ := (‖g z‖ - q * d) / (2 * q)
    have hδ : 0 < δ := by
      dsimp [δ]
      exact div_pos (sub_pos.mpr hbadTarget) (mul_pos (by norm_num) hqpos)
    have hReG : ∀ w ∈ Metric.ball c R, (g w).re ≤ d + δ := by
      intro w hw
      have hw' := Metric.ball_subset_closedBall hw
      have h := hRe w hw'
      dsimp [d]
      change (f w).re - (f c).re ≤ M - (f c).re + δ
      linarith
    have hbc := OAI.SevenEighths.LogarithmicControl.borel_caratheodory_closedBall
      (g := g) (c := c) (r := r) (R := R) (M := d + δ) (A := 0)
      hr hsmall (by linarith [hd, hδ]) (by norm_num) hgd hReG (by simp [g]) hz
    have hbc' : ‖g z‖ ≤ 2 * (d + δ) * r / (R - r) := by simpa using hbc
    have hline : ‖g z‖ ≤ q * d + (‖g z‖ - q * d) / 2 := by
      calc
        ‖g z‖ ≤ 2 * (d + δ) * r / (R - r) := hbc'
        _ = q * (d + δ) := by dsimp [q]; ring
        _ = q * d + (‖g z‖ - q * d) / 2 := by
          dsimp [δ]
          field_simp [hqpos.ne']
    nlinarith [hline, hbadTarget]

/-- Three-circles interpolation from the vertical-strip Hadamard theorem. -/
theorem three_circles_from_three_lines {f : ℂ → ℂ} {c : ℂ}
    {r₁ r r₂ M₁ M₂ : ℝ}
    (hr₁ : 0 < r₁) (hr : r₁ ≤ r) (hr₂ : r ≤ r₂) (houter : r < r₂)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c r₂))
    (h₁ : ∀ z, ‖z - c‖ = r₁ → ‖f z‖ ≤ M₁)
    (h₂ : ∀ z, ‖z - c‖ = r₂ → ‖f z‖ ≤ M₂) :
    ∀ z, ‖z - c‖ = r →
      ‖f z‖ ≤ Real.rpow M₁
          (Real.log (r₂ / r) / Real.log (r₂ / r₁)) *
        Real.rpow M₂ (1 - Real.log (r₂ / r) / Real.log (r₂ / r₁)) := by
  intro z hz
  have hr₁₂ : r₁ < r₂ := lt_of_le_of_lt hr houter
  have hrpos : 0 < r := hr₁.trans_le hr
  have hr₂pos : 0 < r₂ := hrpos.trans_le hr₂
  by_cases heq : r₁ = r
  · have hlogpos : 0 < Real.log (r₂ / r₁) :=
      Real.log_pos ((lt_div_iff₀ hr₁).2 (by nlinarith [hr₁₂]))
    have hratio : Real.log (r₂ / r) / Real.log (r₂ / r₁) = 1 := by
      rw [← heq]
      exact div_self (ne_of_gt hlogpos)
    have hz1 : ‖z - c‖ = r₁ := by simpa [heq] using hz
    simpa [hratio] using h₁ z hz1
  · have hr₁r : r₁ < r := lt_of_le_of_ne hr (by
      intro h
      exact heq h)
    let l : ℝ := Real.log r₁
    let u : ℝ := Real.log r₂
    let S : Set ℂ := Complex.HadamardThreeLines.verticalStrip l u
    let Sc : Set ℂ := Complex.HadamardThreeLines.verticalClosedStrip l u
    let g : ℂ → ℂ := fun w => f (c + Complex.exp w)
    have hl : l < u := by
      dsimp [l, u]
      exact Real.log_lt_log hr₁ hr₁₂
    have hclosure : closure S ⊆ Sc := by
      apply closure_minimal
      · intro w hw
        change w.re ∈ Set.Ioo l u at hw
        exact ⟨hw.1.le, hw.2.le⟩
      · exact isClosed_Icc.preimage Complex.continuous_re
    have hmapClosed : ∀ w ∈ Sc, c + Complex.exp w ∈ Metric.closedBall c r₂ := by
      intro w hw
      change w.re ∈ Set.Icc l u at hw
      rw [Metric.mem_closedBall, dist_eq_norm]
      simp only [add_sub_cancel_left, Complex.norm_exp]
      calc
        Real.exp w.re ≤ Real.exp (Real.log r₂) := Real.exp_le_exp.mpr (by simpa [u] using hw.2)
        _ = r₂ := Real.exp_log hr₂pos
    have hmap : ∀ w ∈ closure S, c + Complex.exp w ∈ Metric.closedBall c r₂ :=
      fun w hw => hmapClosed w (hclosure hw)
    have hg : DifferentiableOn ℂ g (closure S) := by
      dsimp [g]
      apply hf.differentiableOn.fun_comp
        (((differentiable_const c).add Complex.differentiable_exp).differentiableOn)
        hmap
    have hd : DiffContOnCl ℂ g S := hg.diffContOnCl
    have hB : BddAbove ((norm ∘ g) '' Sc) := by
      obtain ⟨B, hB⟩ := (isCompact_closedBall c r₂).bddAbove_image hf.continuousOn.norm
      refine ⟨B, ?_⟩
      rintro _ ⟨w, hw, rfl⟩
      apply hB
      exact ⟨c + Complex.exp w, hmapClosed w hw, by simp [g]⟩
    have h1edge : ∀ w, w ∈ Complex.re ⁻¹' {l} → ‖g w‖ ≤ M₁ := by
      intro w hw
      have hwre : w.re = l := by simpa [l] using hw
      apply h₁ (c + Complex.exp w)
      simpa [Complex.norm_exp, hwre, l, Real.exp_log hr₁] using
        (show ‖Complex.exp w‖ = r₁ by simp [Complex.norm_exp, hwre, l, Real.exp_log hr₁])
    have h2edge : ∀ w, w ∈ Complex.re ⁻¹' {u} → ‖g w‖ ≤ M₂ := by
      intro w hw
      have hwre : w.re = u := by simpa [u] using hw
      apply h₂ (c + Complex.exp w)
      simpa [Complex.norm_exp, hwre, u, Real.exp_log hr₂pos] using
        (show ‖Complex.exp w‖ = r₂ by simp [Complex.norm_exp, hwre, u, Real.exp_log hr₂pos])
    have hzpos : 0 < ‖z - c‖ := by rw [hz]; exact hrpos
    have hzne : z - c ≠ 0 := norm_pos_iff.mp hzpos
    let w := Complex.log (z - c)
    have hwre : w.re = Real.log r := by
      dsimp [w]
      rw [Complex.log_re, hz]
    have hwmem : w ∈ Sc := by
      change l ≤ w.re ∧ w.re ≤ u
      rw [hwre]
      constructor
      · dsimp [l]
        exact Real.log_le_log hr₁ hr
      · dsimp [u]
        exact Real.log_le_log hrpos hr₂
    have hα :
        (Real.log r - Real.log r₁) / (Real.log r₂ - Real.log r₁) =
          1 - Real.log (r₂ / r) / Real.log (r₂ / r₁) := by
      have h2 := Real.log_div hr₂pos.ne' hrpos.ne'
      have h1 := Real.log_div hr₂pos.ne' hr₁.ne'
      have hunit :
          Real.log r₂ / (Real.log r₂ - Real.log r₁) -
              Real.log r₁ / (Real.log r₂ - Real.log r₁) = 1 := by
        rw [← sub_div]
        exact div_self (ne_of_gt (sub_pos.mpr hl))
      rw [h2, h1]
      simp only [sub_div]
      linarith [hunit]
    have hβ :
        1 - (Real.log r - Real.log r₁) / (Real.log r₂ - Real.log r₁) =
          Real.log (r₂ / r) / Real.log (r₂ / r₁) := by rw [hα]; ring_nf
    have hlines := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
      hl hwmem hd hB h1edge h2edge
    rw [hwre, hβ, hα] at hlines
    simpa [g, w, Complex.exp_log hzne] using hlines
end Proofs.A2Z1

/-- **ext:borel-caratheodory** (Mathlib, `Analysis/Complex/BorelCaratheodory.lean:109`):
Borel--Carathéodory on concentric disks. -/
theorem ext_borel_caratheodory {f : ℂ → ℂ} {c : ℂ} {R r M : ℝ}
    (hR : 0 < R) (hr : 0 ≤ r) (hsmall : r < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hRe : ∀ z ∈ Metric.closedBall c R, (f z).re ≤ M) :
    ∀ z ∈ Metric.closedBall c r,
      ‖f z - f c‖ ≤ (2 * r / (R - r)) * (M - (f c).re) := by
  exact ArtinPrimitiveRoots.A2.Proofs.A2Z1.borel_caratheodory_centered
    hR hr hsmall hf hRe

/-- **ext:three-circles** (Mathlib, `Analysis/Complex/Hadamard.lean:610`): the maximum modulus
on an intermediate circle is bounded by logarithmic interpolation of the two outer maxima. -/
theorem ext_three_circles {f : ℂ → ℂ} {c : ℂ} {r₁ r r₂ M₁ M₂ : ℝ}
    (hr₁ : 0 < r₁) (hr : r₁ ≤ r) (hr₂ : r ≤ r₂) (houter : r < r₂)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c r₂))
    (h₁ : ∀ z, ‖z - c‖ = r₁ → ‖f z‖ ≤ M₁)
    (h₂ : ∀ z, ‖z - c‖ = r₂ → ‖f z‖ ≤ M₂) :
    ∀ z, ‖z - c‖ = r →
      ‖f z‖ ≤ Real.rpow M₁
          (Real.log (r₂ / r) / Real.log (r₂ / r₁)) *
        Real.rpow M₂ (1 - Real.log (r₂ / r) / Real.log (r₂ / r₁)) := by
  exact ArtinPrimitiveRoots.A2.Proofs.A2Z1.three_circles_from_three_lines
    hr₁ hr hr₂ houter hf h₁ h₂

/-- **ext:mellin-fourier-inversion** (06-zero-free.tex:226-264): Mellin inversion for the
exponential kernel, written as a vertical-line integral. -/
theorem ext_mellin_fourier_inversion (x c : ℝ) (hx : 0 < x) (hc : 0 < c) :
    verticalMellinIntegral
      (fun v => Complex.Gamma v * (x : ℂ) ^ (-v)) c = Complex.exp (-(x : ℂ)) := by
  let f : ℝ → ℂ := fun t => (Real.exp (-t) : ℂ)
  have hm (s : ℂ) (hs : 0 < s.re) : mellin f s = Complex.Gamma s := by
    rw [Complex.Gamma_eq_integral hs, ← Complex.GammaIntegral_eq_mellin]
  have hf : MellinConvergent f (c : ℂ) := by
    simpa only [MellinConvergent, f, smul_eq_mul, mul_comm] using
      (Complex.GammaIntegral_convergent (by exact_mod_cast hc))
  have hline : ∀ t : ℝ, mellin f ((c : ℂ) + t * Complex.I) =
      Complex.Gamma ((c : ℂ) + t * Complex.I) := by
    intro t
    apply hm
    simp [hc]
  have hΓint : Integrable (fun t : ℝ => Complex.Gamma ((c : ℂ) + t * Complex.I)) := by
    obtain ⟨K, hK, hγ⟩ := OAI.SevenEighths.GammaZeroDetector.gamma_rapid_bound c c hc 2
    have hdom : ∀ t : ℝ,
        ‖Complex.Gamma ((c : ℂ) + t * Complex.I)‖ ≤ K / (1 + t ^ 2) := by
      intro t
      have h := hγ ((c : ℂ) + t * Complex.I) (by simp) (by simp)
      have hsq : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by
        nlinarith [sq_abs t, abs_nonneg t]
      apply (le_div_iff₀ (by positivity : 0 < 1 + t ^ 2)).2
      have h' : (1 + |t|) ^ 2 *
          ‖Complex.Gamma ((c : ℂ) + t * Complex.I)‖ ≤ K := by simpa using h
      have hmul := mul_le_mul_of_nonneg_right hsq
        (norm_nonneg (Complex.Gamma ((c : ℂ) + t * Complex.I)))
      simpa [mul_comm] using hmul.trans h'
    apply (integrable_inv_one_add_sq.const_mul K).mono'
    · apply Continuous.aestronglyMeasurable
      have hlinecont : Continuous (fun t : ℝ => (c : ℂ) + t * Complex.I) := by fun_prop
      apply continuous_iff_continuousAt.mpr
      intro t
      exact (OAI.SevenEighths.GammaZeroDetector.gamma_differentiableAt_right (by simp [hc])).continuousAt
        |>.comp hlinecont.continuousAt
    · filter_upwards [] with t
      simpa [div_eq_mul_inv] using hdom t
  have hv : Complex.VerticalIntegrable (mellin f) c := by
    change Integrable (fun t : ℝ => mellin f ((c : ℂ) + t * Complex.I))
    exact hΓint.congr (Filter.Eventually.of_forall fun t => (hline t).symm)
  have hi := mellinInv_mellin_eq c f hx hf hv (by
    dsimp [f]
    fun_prop)
  simp only [mellinInv, smul_eq_mul] at hi
  simp_rw [hline] at hi
  have hintegral :
      (∫ t : ℝ, Complex.Gamma ((c : ℂ) + t * Complex.I) *
        (x : ℂ) ^ (-((c : ℂ) + t * Complex.I))) =
      ∫ t : ℝ, (x : ℂ) ^ (-((c : ℂ) + t * Complex.I)) *
        Complex.Gamma ((c : ℂ) + t * Complex.I) := by
    apply integral_congr_ae
    filter_upwards [] with t
    ring
  unfold verticalMellinIntegral
  rw [hintegral]
  simpa [f, Complex.ofReal_exp, Complex.ofReal_neg, mul_comm] using hi

/-- Completed Hecke L-function with the Deligne-normalized complex gamma factor. -/
def completedHeckeValue (L : ℂ → ℂ) (𝔣 : Ideal (𝓞 F)) (s : ℂ) : ℂ :=
  (Complex.ofReal (|discr F| * (Ideal.absNorm 𝔣 : ℝ))) ^ (s / 2) *
    Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F * L s

private theorem hk_ray_line_growth [IsTotallyComplex F]
    {m : ClassFieldTheory.RayClassModulus F}
    (ψ : ClassFieldTheory.RayClassGroup m →* ℂˣ) (hψ : ψ ≠ 1)
    (L Ldual : ℂ → ℂ)
    (hLd : Differentiable ℂ L) (hLdualD : Differentiable ℂ Ldual)
    (hAgree : ∀ s : ℂ, 1 < s.re → L s = ArtinPrimitiveRoots.Hecke.LSeriesRay ψ s)
    (hAgreeInv : ∀ s : ℂ, 1 < s.re →
      Ldual s = ArtinPrimitiveRoots.Hecke.LSeriesRay (ψ⁻¹) s)
    (hCeq : ∀ s : ℂ, (∀ n : ℕ, s ≠ -(n : ℂ)) →
      ArtinPrimitiveRoots.Hecke.hkCompleted ψ s =
        ArtinPrimitiveRoots.Hecke.hkCompletedValue L m s)
    (hCdualEq : ∀ s : ℂ, (∀ n : ℕ, s ≠ -(n : ℂ)) →
      ArtinPrimitiveRoots.Hecke.hkCompleted (ψ⁻¹) s =
        ArtinPrimitiveRoots.Hecke.hkCompletedValue Ldual m s)
    (W : ℂ) (hW : ‖W‖ = 1)
    (hFE : ∀ s : ℂ, ArtinPrimitiveRoots.Hecke.hkCompleted ψ s =
      W * ArtinPrimitiveRoots.Hecke.hkCompleted (ψ⁻¹) (1 - s))
    (x : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ e : ℕ, ∀ t : ℝ,
      ‖L ((x : ℂ) + t * Complex.I)‖ ≤ C * (2 + |t|) ^ e := by
  obtain ⟨A, hA, hconv⟩ := ArtinPrimitiveRoots.Hecke.LSeriesRay_convexity (K := F)
  obtain ⟨C₀, hC₀, hconv₀⟩ := hconv 1 (by norm_num) (3 / 1000) (by norm_num)
  let Cbase := C₀ * Real.rpow (ArtinPrimitiveRoots.Hecke.conductorNorm ψ : ℝ)
      (1 / 2 + 1) * Real.rpow (ArtinPrimitiveRoots.Hecke.modulusNorm m : ℝ) 1
  have hCbase : 0 ≤ Cbase := by
    dsimp [Cbase]
    apply mul_nonneg
    · exact mul_nonneg (le_of_lt hC₀)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  by_cases hxsmall : x < 3 / 1000
  · obtain ⟨CΓ, hCΓ, NΓ, hGammaRatio⟩ :=
      ArtinPrimitiveRoots.Proofs.A2FreqP.gammaC_ratio_polynomial (1 - x)
    have hψInv : ψ⁻¹ ≠ 1 := by
      intro hInv
      apply hψ
      calc
        ψ = (ψ⁻¹)⁻¹ := (inv_inv ψ).symm
        _ = (1 : ClassFieldTheory.RayClassGroup m →* ℂˣ)⁻¹ :=
          congrArg Inv.inv hInv
        _ = 1 := by ext C; simp
    let CbaseInv := C₀ * Real.rpow
      (ArtinPrimitiveRoots.Hecke.conductorNorm (ψ⁻¹) : ℝ) (1 / 2 + 1) *
      Real.rpow (ArtinPrimitiveRoots.Hecke.modulusNorm m : ℝ) 1
    have hCbaseInv : 0 ≤ CbaseInv := by
      dsimp [CbaseInv]
      apply mul_nonneg
      · exact mul_nonneg (le_of_lt hC₀)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hdualExist : ∃ Cdual : ℝ, 0 < Cdual ∧ ∃ eDual : ℕ,
        ∀ t : ℝ,
          ‖Ldual (((1 - x : ℝ) : ℂ) - t * Complex.I)‖ ≤
            Cdual * (2 + |t|) ^ eDual := by
      by_cases hdual4 : 1 - x ≤ 4
      · obtain ⟨eDual, heDual⟩ := exists_nat_gt A
        refine ⟨CbaseInv + 1, by positivity, eDual, ?_⟩
        intro t
        let sInv : ℂ := 1 - ((x : ℂ) + t * Complex.I)
        have hleft : 3 / 1000 ≤ sInv.re := by
          simp [sInv]
          linarith [hxsmall]
        have hright : sInv.re ≤ 4 := by simpa [sInv] using hdual4
        have hbound := hconv₀ m (ψ⁻¹) hψInv Ldual hLdualD hAgreeInv
          sInv hleft hright
        have hbaseBound : ‖Ldual sInv‖ ≤
            CbaseInv * Real.rpow (2 + |t|) A := by
          simpa [sInv, CbaseInv, add_comm (1 / 2 : ℝ)] using hbound
        have hbaseDual : 1 ≤ 2 + |t| := by nlinarith [abs_nonneg t]
        have hpow : Real.rpow (2 + |t|) A ≤ (2 + |t|) ^ eDual := by
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le
            hbaseDual (le_of_lt heDual)
        have hfinal :
            ‖Ldual sInv‖ ≤ (CbaseInv + 1) * (2 + |t|) ^ eDual := calc
          ‖Ldual sInv‖ ≤ CbaseInv * Real.rpow (2 + |t|) A := hbaseBound
          _ ≤ (CbaseInv + 1) * (2 + |t|) ^ eDual := by
            exact (mul_le_mul_of_nonneg_right (by linarith [hCbaseInv])
              (Real.rpow_nonneg (by positivity) _)).trans
              (mul_le_mul_of_nonneg_left hpow (by positivity))
        have hsInv : sInv = ((1 - x : ℝ) : ℂ) - t * Complex.I := by
          simp [sInv]
          ring
        have hlineArg : ((1 - x : ℝ) : ℂ) - t * Complex.I = sInv := by
          simp [sInv]
          ring
        rw [hlineArg]
        exact hfinal
      · have hdualgt : 4 < 1 - x := lt_of_not_ge hdual4
        let zetaDual := (NumberField.dedekindZeta F ((1 - x : ℝ) : ℂ)).re
        refine ⟨|zetaDual| + 1, by positivity, 0, ?_⟩
        intro t
        let sInv : ℂ := 1 - ((x : ℂ) + t * Complex.I)
        have hRe : 1 < sInv.re := by
          simpa [sInv] using (show 1 < 1 - x by linarith [hdualgt])
        have hAgree' := hAgreeInv sInv hRe
        have hEuler := (ArtinPrimitiveRoots.Hecke.norm_LSeriesRay_le
          (η := ψ⁻¹) hRe).1
        have hEuler' :
            ‖ArtinPrimitiveRoots.Hecke.LSeriesRay (ψ⁻¹) sInv‖ ≤ zetaDual := by
          simpa [sInv, zetaDual] using hEuler
        have hbound : ‖Ldual sInv‖ ≤ zetaDual := by rw [hAgree']; exact hEuler'
        have hbound' : ‖Ldual sInv‖ ≤ |zetaDual| + 1 := by
          exact hbound.trans (by linarith [le_abs_self zetaDual])
        have hsInv : sInv = ((1 - x : ℝ) : ℂ) - t * Complex.I := by
          simp [sInv]
          ring
        rw [hsInv.symm]
        simpa [zetaDual] using hbound'
    obtain ⟨Cdual, hCdual, eDual, hdualLine⟩ := hdualExist
    let e : ℕ := NΓ * NumberField.InfinitePlace.nrComplexPlaces F + eDual
    have hDpos : 0 <
        ((NumberField.discr F).natAbs : ℝ) *
          (ArtinPrimitiveRoots.Hecke.modulusNorm m : ℝ) := by
      apply mul_pos
      · exact_mod_cast Int.natAbs_pos.mpr (NumberField.discr_ne_zero F)
      · exact_mod_cast ArtinPrimitiveRoots.Dictionary.modulusNorm_pos m
    have hGammaNe {z : ℂ} (hz : z.im ≠ 0) : Complex.Gamma z ≠ 0 := by
      apply Complex.Gamma_ne_zero
      intro n hn
      have h := congrArg Complex.im hn
      apply hz
      simpa using h
    have hGammaCNe {z : ℂ} (hz : z.im ≠ 0) : Complex.Gammaℂ z ≠ 0 := by
      rw [Complex.Gammaℂ_def]
      apply mul_ne_zero
      · apply mul_ne_zero
        · norm_num
        · apply (Complex.cpow_ne_zero_iff).mpr
          exact Or.inl (show (2 : ℂ) * (Real.pi : ℂ) ≠ 0 by
            apply mul_ne_zero
            · norm_num
            · exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      · exact hGammaNe hz
    have hHigh : ∀ t : ℝ, 1 ≤ |t| →
        ‖L ((x : ℂ) + t * Complex.I)‖ ≤
            (Real.rpow
              (((NumberField.discr F).natAbs : ℝ) *
                (ArtinPrimitiveRoots.Hecke.modulusNorm m : ℝ))
              ((1 - 2 * x) / 2) *
            CΓ ^ NumberField.InfinitePlace.nrComplexPlaces F * Cdual) *
            (2 + |t|) ^ e := by
      intro t ht
      let s : ℂ := (x : ℂ) + t * Complex.I
      let sInv : ℂ := 1 - s
      have htne : t ≠ 0 := by
        intro ht0
        rw [ht0, abs_zero] at ht
        norm_num at ht
      have hspoles : ∀ n : ℕ, s ≠ -(n : ℂ) := by
        intro n hs
        have hi := congrArg Complex.im hs
        apply htne
        simpa [s] using hi
      have hsinvpoles : ∀ n : ℕ, sInv ≠ -(n : ℂ) := by
        intro n hs
        have hi := congrArg Complex.im hs
        apply htne
        have : -t = 0 := by simpa [sInv, s] using hi
        exact neg_eq_zero.mp this
      have hcompleted :
          ArtinPrimitiveRoots.Hecke.hkCompletedValue L m s =
            W * ArtinPrimitiveRoots.Hecke.hkCompletedValue Ldual m sInv := by
        calc
          _ = ArtinPrimitiveRoots.Hecke.hkCompleted ψ s := (hCeq s hspoles).symm
          _ = W * ArtinPrimitiveRoots.Hecke.hkCompleted (ψ⁻¹) sInv := by
            simpa [sInv] using hFE s
          _ = _ := by rw [hCdualEq sInv hsinvpoles]
      let d : ℝ := ((NumberField.discr F).natAbs : ℝ) *
        (ArtinPrimitiveRoots.Hecke.modulusNorm m : ℝ)
      let p : ℂ := (d : ℂ) ^ (s / 2)
      let pInv : ℂ := (d : ℂ) ^ (sInv / 2)
      let g : ℂ := Complex.Gammaℂ s
      let gInv : ℂ := Complex.Gammaℂ sInv
      let r : ℕ := NumberField.InfinitePlace.nrComplexPlaces F
      have hpNe : p ≠ 0 := by
        dsimp [p]
        exact (Complex.cpow_ne_zero_iff).mpr
          (Or.inl (Complex.ofReal_ne_zero.mpr (by dsimp [d]; linarith [hDpos])))
      have hgNe : g ≠ 0 := hGammaCNe (by simpa [s] using htne)
      have hden : p * g ^ r ≠ 0 := mul_ne_zero hpNe (pow_ne_zero _ hgNe)
      have hcompleted' : p * g ^ r * L s =
          W * (pInv * gInv ^ r * Ldual sInv) := by
        simpa [ArtinPrimitiveRoots.Hecke.hkCompletedValue, p, pInv, g, gInv, r, d,
          sInv] using hcompleted
      have hInvDen : (p * g ^ r)⁻¹ = p⁻¹ * (g⁻¹) ^ r := by
        rw [mul_inv_rev, inv_pow]
        ring
      have hformula : L s =
          W * (pInv / p) * (gInv / g) ^ r * Ldual sInv := by
        calc
          L s = (p * g ^ r)⁻¹ * (p * g ^ r) * L s := by
            rw [inv_mul_cancel₀ hden, one_mul]
          _ = (p * g ^ r)⁻¹ * (p * g ^ r * L s) := by ring
          _ = (p * g ^ r)⁻¹ *
                (W * (pInv * gInv ^ r * Ldual sInv)) := by rw [hcompleted']
          _ = W * (pInv / p) * (gInv / g) ^ r * Ldual sInv := by
            rw [hInvDen]
            simp_rw [div_eq_mul_inv]
            rw [mul_pow]
            ring
      have hbaseRatio :
          ‖pInv‖ / ‖p‖ =
            Real.rpow d ((1 - 2 * x) / 2) := by
        dsimp [pInv, p, d]
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hDpos,
          Complex.norm_cpow_eq_rpow_re_of_pos hDpos]
        have hsRe : s.re = x := by simp [s]
        have hInvRe : sInv.re = 1 - x := by simp [sInv, s]
        have hsHalf : (s / 2).re = x / 2 := by simp [hsRe]
        have hInvHalf : (sInv / 2).re = (1 - x) / 2 := by simp [hInvRe]
        rw [hsHalf, hInvHalf]
        rw [Real.rpow_def_of_pos hDpos, Real.rpow_def_of_pos hDpos,
          Real.rpow_def_of_pos hDpos]
        rw [← Real.exp_sub]
        congr 1
        ring
      have hGbound :
          ‖gInv / g‖ ≤ CΓ * (2 + |t|) ^ NΓ := by
        have h := hGammaRatio (-t) (by simpa [abs_neg] using ht)
        have h₁ : ((1 - x : ℝ) : ℂ) + (-t) * Complex.I = sInv := by
          dsimp [sInv, s]
          push_cast
          ring
        have h₂ : 1 - (((1 - x : ℝ) : ℂ) + (-t) * Complex.I) = s := by
          dsimp [s]
          push_cast
          ring
        calc
          ‖gInv / g‖ = ‖Complex.Gammaℂ sInv / Complex.Gammaℂ s‖ := rfl
          _ = ‖Complex.Gammaℂ
              (((1 - x : ℝ) : ℂ) + (-t) * Complex.I) /
                Complex.Gammaℂ
                  (1 - (((1 - x : ℝ) : ℂ) + (-t) * Complex.I))‖ := by
            rw [← h₁, ← h₂]
          _ ≤ CΓ * (2 + |t|) ^ NΓ := by simpa [abs_neg] using h
      have hGPow :
          ‖(gInv / g) ^ r‖ ≤ CΓ ^ r * (2 + |t|) ^ (NΓ * r) := by
        rw [norm_pow]
        calc
          ‖gInv / g‖ ^ r ≤ (CΓ * (2 + |t|) ^ NΓ) ^ r :=
            pow_le_pow_left₀ (norm_nonneg _) hGbound _
          _ = CΓ ^ r * (2 + |t|) ^ (NΓ * r) := by
            rw [mul_pow, ← pow_mul]
      have hLdual : ‖Ldual sInv‖ ≤ Cdual * (2 + |t|) ^ eDual := by
        have h := hdualLine t
        have hsInv : ((1 - x : ℝ) : ℂ) - t * Complex.I = sInv := by
          dsimp [sInv, s]
          push_cast
          ring
        rw [hsInv] at h
        exact h
      have hNormFormula :
          ‖L s‖ = ‖W‖ * (‖pInv‖ / ‖p‖) *
            ‖(gInv / g) ^ r‖ * ‖Ldual sInv‖ := by
        rw [hformula, norm_mul, norm_mul, norm_mul, norm_div, norm_pow]
      have hdnonneg : 0 ≤ d := le_of_lt (by simpa [d] using hDpos)
      calc
        ‖L s‖ = ‖W‖ * (‖pInv‖ / ‖p‖) *
            ‖(gInv / g) ^ r‖ * ‖Ldual sInv‖ := hNormFormula
        _ = (‖pInv‖ / ‖p‖) * ‖(gInv / g) ^ r‖ * ‖Ldual sInv‖ := by
          rw [hW]
          ring
        _ ≤ Real.rpow d ((1 - 2 * x) / 2) *
              ‖(gInv / g) ^ r‖ * ‖Ldual sInv‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_of_eq hbaseRatio) (norm_nonneg _))
            (norm_nonneg _)
        _ = Real.rpow d ((1 - 2 * x) / 2) * ‖Ldual sInv‖ *
              ‖(gInv / g) ^ r‖ := by ring
        _ ≤ Real.rpow d ((1 - 2 * x) / 2) * ‖Ldual sInv‖ *
              (CΓ ^ r * (2 + |t|) ^ (NΓ * r)) :=
          mul_le_mul_of_nonneg_left hGPow
            (mul_nonneg (Real.rpow_nonneg hdnonneg _) (norm_nonneg _))
        _ = Real.rpow d ((1 - 2 * x) / 2) *
              (CΓ ^ r * (2 + |t|) ^ (NΓ * r)) * ‖Ldual sInv‖ := by ring
        _ ≤ Real.rpow d ((1 - 2 * x) / 2) *
              (CΓ ^ r * (2 + |t|) ^ (NΓ * r)) *
                (Cdual * (2 + |t|) ^ eDual) :=
          mul_le_mul_of_nonneg_left hLdual
            (mul_nonneg (Real.rpow_nonneg hdnonneg _)
              (mul_nonneg (pow_nonneg (le_of_lt hCΓ) _)
                (pow_nonneg (by positivity) _)))
        _ = (Real.rpow d ((1 - 2 * x) / 2) * CΓ ^ r * Cdual) *
              (2 + |t|) ^ e := by
          calc
            _ = (Real.rpow d ((1 - 2 * x) / 2) * CΓ ^ r * Cdual) *
                ((2 + |t|) ^ (NΓ * r) * (2 + |t|) ^ eDual) := by ring
            _ = _ := by rw [← pow_add]
    let lineFun : ℝ → ℝ := fun t => ‖L ((x : ℂ) + t * Complex.I)‖
    have hlineCont : Continuous lineFun := by
      dsimp [lineFun]
      have hparam : Continuous (fun t : ℝ => (x : ℂ) + t * Complex.I) := by
        fun_prop
      exact continuous_norm.comp (hLd.continuous.comp hparam)
    obtain ⟨K, hK⟩ := (isCompact_Icc :
      IsCompact (Set.Icc (-1 : ℝ) 1)).bddAbove_image hlineCont.continuousOn
    let Cline := Real.rpow
          (((NumberField.discr F).natAbs : ℝ) *
            (ArtinPrimitiveRoots.Hecke.modulusNorm m : ℝ))
          ((1 - 2 * x) / 2) *
        CΓ ^ NumberField.InfinitePlace.nrComplexPlaces F * Cdual
    have hCline : 0 < Cline := by
      dsimp [Cline]
      positivity
    refine ⟨Cline + |K| + 1, by positivity, e, ?_⟩
    intro t
    by_cases ht : 1 ≤ |t|
    · have hHigh' : ‖L ((x : ℂ) + t * Complex.I)‖ ≤
          Cline * (2 + |t|) ^ e := by simpa [Cline] using hHigh t ht
      exact hHigh'.trans (mul_le_mul_of_nonneg_right
        (by linarith [abs_nonneg K]) (by positivity))
    · have ht' : |t| ≤ 1 := le_of_not_ge ht
      have hsmall := hK (Set.mem_image_of_mem lineFun (abs_le.mp ht'))
      have hnorm : ‖L ((x : ℂ) + t * Complex.I)‖ ≤ |K| := by
        exact le_trans hsmall (le_abs_self K)
      have hbase : 1 ≤ 2 + |t| := by nlinarith [abs_nonneg t]
      have hpow : 1 ≤ (2 + |t|) ^ e := one_le_pow₀ hbase
      calc
        _ ≤ |K| := hnorm
        _ ≤ (Cline + |K| + 1) * (2 + |t|) ^ e := by
          nlinarith [mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ Cline + |K| + 1)]
  · by_cases hxlarge : x ≤ 4
    · obtain ⟨e, he⟩ := exists_nat_gt A
      refine ⟨Cbase + 1, by positivity, e, ?_⟩
      intro t
      let s : ℂ := (x : ℂ) + t * Complex.I
      have hleft : 3 / 1000 ≤ s.re := by simpa [s] using le_of_not_gt hxsmall
      have hright : s.re ≤ 4 := by simpa [s] using hxlarge
      have hbound := hconv₀ m ψ hψ L hLd hAgree s hleft hright
      have hbaseBound : ‖L s‖ ≤ Cbase * Real.rpow (2 + |t|) A := by
        simpa [s, Cbase, add_comm (1 / 2 : ℝ)] using hbound
      have hpow : Real.rpow (2 + |t|) A ≤ (2 + |t|) ^ e := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le
          (by nlinarith [abs_nonneg t]) (le_of_lt he)
      calc
        ‖L s‖ ≤ Cbase * Real.rpow (2 + |t|) A := hbaseBound
        _ ≤ (Cbase + 1) * (2 + |t|) ^ e := by
          have hfac : Cbase * Real.rpow (2 + |t|) A ≤
              (Cbase + 1) * Real.rpow (2 + |t|) A :=
            mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by positivity) _)
          exact hfac.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
    · have hxgt : 1 < x := by linarith
      let zetaX := (NumberField.dedekindZeta F (x : ℂ)).re
      refine ⟨|zetaX| + 1, by positivity, 0, ?_⟩
      intro t
      let s : ℂ := (x : ℂ) + t * Complex.I
      have hs : 1 < s.re := by
        have hsre : s.re = x := by simp [s]
        rw [hsre]
        exact hxgt
      have hagree := hAgree s hs
      have hnorm := (ArtinPrimitiveRoots.Hecke.norm_LSeriesRay_le ψ hs).1
      have hnorm' : ‖ArtinPrimitiveRoots.Hecke.LSeriesRay ψ s‖ ≤ zetaX := by
        simpa [s, zetaX] using hnorm
      have hle : zetaX ≤ |zetaX| := le_abs_self zetaX
      calc
        ‖L ((x : ℂ) + t * Complex.I)‖ = ‖L s‖ := by simpa [s]
        _ = ‖ArtinPrimitiveRoots.Hecke.LSeriesRay ψ s‖ := congrArg norm hagree
        _ ≤ zetaX := hnorm'
        _ ≤ |zetaX| + 1 := by linarith
        _ = (|zetaX| + 1) * (2 + |t|) ^ 0 := by simp

private theorem hk_ray_strip_growth [IsTotallyComplex F]
    {m : ClassFieldTheory.RayClassModulus F}
    (ψ : ClassFieldTheory.RayClassGroup m →* ℂˣ) (hψ : ψ ≠ 1)
    (hp : ArtinPrimitiveRoots.Hecke.HKPrimitive ψ)
    (L Ldual : ℂ → ℂ)
    (hLdef : L = ArtinPrimitiveRoots.Hecke.hkEntireL ψ)
    (hLdualDef : Ldual = ArtinPrimitiveRoots.Hecke.hkEntireL (ψ⁻¹))
    (hLd : Differentiable ℂ L) (hLdualD : Differentiable ℂ Ldual)
    (hAgree : ∀ s : ℂ, 1 < s.re → L s = ArtinPrimitiveRoots.Hecke.LSeriesRay ψ s)
    (hAgreeInv : ∀ s : ℂ, 1 < s.re →
      Ldual s = ArtinPrimitiveRoots.Hecke.LSeriesRay (ψ⁻¹) s)
    (hCeq : ∀ s : ℂ, (∀ n : ℕ, s ≠ -(n : ℂ)) →
      ArtinPrimitiveRoots.Hecke.hkCompleted ψ s =
        ArtinPrimitiveRoots.Hecke.hkCompletedValue L m s)
    (hCdualEq : ∀ s : ℂ, (∀ n : ℕ, s ≠ -(n : ℂ)) →
      ArtinPrimitiveRoots.Hecke.hkCompleted (ψ⁻¹) s =
        ArtinPrimitiveRoots.Hecke.hkCompletedValue Ldual m s)
    (W : ℂ) (hW : ‖W‖ = 1)
    (hFE : ∀ s : ℂ, ArtinPrimitiveRoots.Hecke.hkCompleted ψ s =
      W * ArtinPrimitiveRoots.Hecke.hkCompleted (ψ⁻¹) (1 - s)) :
    ∀ a b : ℝ, a ≤ b → ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧
      ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
        ‖L s‖ ≤ C * Real.rpow (2 + |s.im|) A := by
  intro a b hab
  by_cases hdeg : a = b
  · subst b
    obtain ⟨C, hC, e, hline⟩ :=
      hk_ray_line_growth ψ hψ L Ldual hLd hLdualD hAgree hAgreeInv
        hCeq hCdualEq W hW hFE a
    refine ⟨C, (e : ℝ), hC, Nat.cast_nonneg _, ?_⟩
    intro s hsa hsb
    have hre : s.re = a := le_antisymm hsb hsa
    have hs : s = (a : ℂ) + s.im * Complex.I := by
      simpa [hre] using (Complex.re_add_im s).symm
    have hLval : L s = L ((a : ℂ) + s.im * Complex.I) := congrArg L hs
    have hline' : ‖L s‖ ≤ C * (2 + |s.im|) ^ e := by
      calc
        ‖L s‖ = ‖L ((a : ℂ) + s.im * Complex.I)‖ := congrArg norm hLval
        _ ≤ C * (2 + |s.im|) ^ e := hline s.im
    simpa [Real.rpow_natCast] using hline'
  · have hab' : a < b := lt_of_le_of_ne hab hdeg
    obtain ⟨Ca, hCa, ea, hla⟩ :=
      hk_ray_line_growth ψ hψ L Ldual hLd hLdualD hAgree hAgreeInv
        hCeq hCdualEq W hW hFE a
    obtain ⟨Cb, hCb, eb, hlb⟩ :=
      hk_ray_line_growth ψ hψ L Ldual hLd hLdualD hAgree hAgreeInv
        hCeq hCdualEq W hW hFE b
    let E : ℕ := max ea eb
    let B : ℝ := 2 + |a| + |b|
    let strip : Set ℂ := Complex.re ⁻¹' Set.Ioo a b
    let closedStrip : Set ℂ := Complex.re ⁻¹' Set.Icc a b
    let den : ℂ → ℂ := fun z => (B : ℂ) + z
    let G : ℂ → ℂ := fun z => L z / den z ^ E
    have hclosure : closure strip ⊆ closedStrip := by
      apply closure_minimal
      · intro z hz
        change z.re ∈ Set.Ioo a b at hz
        exact ⟨hz.1.le, hz.2.le⟩
      · exact isClosed_Icc.preimage Complex.continuous_re
    have hBleft : 2 ≤ B + a := by
      dsimp [B]
      have ha : -|a| ≤ a := neg_abs_le a
      linarith [ha, abs_nonneg b]
    have hdenRe : ∀ z ∈ closedStrip, 2 ≤ (den z).re := by
      intro z hz
      have hBa : B + a ≤ B + z.re := by linarith [hz.1]
      have hre : (den z).re = B + z.re := by simp [den]
      rw [hre]
      exact hBleft.trans hBa
    have hdenNe : ∀ z ∈ closedStrip, den z ^ E ≠ 0 := by
      intro z hz
      apply pow_ne_zero
      have h := hdenRe z hz
      intro hz0
      have hreal := congrArg Complex.re hz0
      have hzero : (den z).re = 0 := by simpa [den] using hreal
      linarith
    have hdenDiff : Differentiable ℂ (fun z : ℂ => den z ^ E) := by
      fun_prop
    have hGdiff : DifferentiableOn ℂ G (closure strip) := by
      dsimp [G]
      apply hLd.differentiableOn.div hdenDiff.differentiableOn
      intro z hz
      exact hdenNe z (hclosure hz)
    have hGdc : DiffContOnCl ℂ G strip := hGdiff.diffContOnCl
    obtain ⟨Cexp, Bexp, hCexp, hBexp, hprelim⟩ :=
      ArtinPrimitiveRoots.Hecke.hk_entire_L_preliminary_growth ψ hψ hp a b hab
    let c : ℝ := min (Real.pi / (2 * (b - a))) (1 / 2)
    have hcpos : 0 < c := by
      dsimp [c]
      exact lt_min (div_pos Real.pi_pos (by linarith)) (by norm_num)
    have hcsmall : c ≤ 1 := by
      dsimp [c]
      exact le_trans (min_le_right _ _) (by norm_num)
    have hcmargin : c < Real.pi / (b - a) := by
      dsimp [c]
      have hwidth : 0 < b - a := sub_pos.mpr hab'
      have hhalf : Real.pi / (2 * (b - a)) < Real.pi / (b - a) := by
        apply div_lt_div_of_pos_left Real.pi_pos hwidth
        nlinarith
      exact lt_of_le_of_lt (min_le_left _ _) hhalf
    have hdouble : ∃ A₀ B₀ : ℝ, c < Real.pi / (b - a) ∧
        ∀ z : ℂ, a < z.re → z.re < b →
          ‖G z‖ ≤ A₀ * Real.exp (B₀ * Real.exp (c * |z.im|)) := by
      refine ⟨Cexp, Bexp / c, hcmargin, ?_⟩
      intro z hza hzb
      have hzcl : z ∈ closedStrip := ⟨hza.le, hzb.le⟩
      have hDen : 1 ≤ ‖den z ^ E‖ := by
        rw [norm_pow]
        have hnormDen : 1 ≤ ‖den z‖ := by
          have hreal := hdenRe z hzcl
          have hnonneg : 0 ≤ (den z).re := by linarith
          calc
            1 ≤ (den z).re := by linarith
            _ = |(den z).re| := (abs_of_nonneg hnonneg).symm
            _ ≤ ‖den z‖ := Complex.abs_re_le_norm (den z)
        exact one_le_pow₀ hnormDen
      have hGle : ‖G z‖ ≤ ‖L z‖ := by
        dsimp [G]
        rw [norm_div]
        exact div_le_self (norm_nonneg _) hDen
      have hL := hprelim z hza.le hzb.le
      have hL' : ‖L z‖ ≤ Cexp * Real.exp (Bexp * (1 + |z.im|)) := by
        rw [hLdef]
        exact hL
      have hu : 1 + |z.im| ≤ c⁻¹ * Real.exp (c * |z.im|) := by
        have h1 : 1 + c * |z.im| ≤ Real.exp (c * |z.im|) := by
          simpa [add_comm] using Real.add_one_le_exp (c * |z.im|)
        have hmul : c * (1 + |z.im|) ≤ Real.exp (c * |z.im|) := by
          calc
            _ ≤ 1 + c * |z.im| := by nlinarith [hcsmall, abs_nonneg z.im]
            _ ≤ _ := h1
        calc
          1 + |z.im| = c⁻¹ * (c * (1 + |z.im|)) := by field_simp
          _ ≤ c⁻¹ * Real.exp (c * |z.im|) :=
            mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr hcpos.le)
      have hexp : Bexp * (1 + |z.im|) ≤
          (Bexp / c) * Real.exp (c * |z.im|) := by
        have h := mul_le_mul_of_nonneg_left hu hBexp.le
        simpa [div_eq_mul_inv, mul_assoc] using h
      exact (hGle.trans hL').trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr hexp) (le_of_lt hCexp))
    have hEdgeLine (x : ℝ) (Cx : ℝ) (hCx : 0 < Cx) (ex : ℕ)
        (hline : ∀ t : ℝ, ‖L ((x : ℂ) + t * Complex.I)‖ ≤
          Cx * (2 + |t|) ^ ex) (hexp : ex ≤ E) (hx : x = a ∨ x = b) :
        ∀ z : ℂ, z.re = x → ‖G z‖ ≤ Cx * 2 ^ E := by
      intro z hz
      have hzcl : z ∈ closedStrip := by
        rcases hx with hxa | hxb
        · have hzA : z.re = a := hz.trans hxa
          exact ⟨by rw [hzA], by rw [hzA]; exact hab⟩
        · have hzB : z.re = b := hz.trans hxb
          exact ⟨by rw [hzB]; exact hab, by rw [hzB]⟩
      have hlineZ : ‖L z‖ ≤ Cx * (2 + |z.im|) ^ ex := by
        have hzrepr : (x : ℂ) + z.im * Complex.I = z := by
          calc
            _ = (z.re : ℂ) + z.im * Complex.I := by rw [hz]
            _ = z := Complex.re_add_im z
        calc
          ‖L z‖ = ‖L ((x : ℂ) + z.im * Complex.I)‖ :=
            congrArg (fun w : ℂ => ‖L w‖) hzrepr.symm
          _ ≤ Cx * (2 + |z.im|) ^ ex := hline z.im
      have hdenLower : 2 ≤ ‖den z‖ := by
        have hreal := hdenRe z hzcl
        have hnonneg : 0 ≤ (den z).re := by linarith
        calc
          2 ≤ (den z).re := hreal
          _ = |(den z).re| := (abs_of_nonneg hnonneg).symm
          _ ≤ ‖den z‖ := Complex.abs_re_le_norm (den z)
      have htime : 2 + |z.im| ≤ 2 * ‖den z‖ := by
        have him := Complex.abs_im_le_norm (den z)
        have hIm : |(den z).im| = |z.im| := by simp [den]
        rw [hIm] at him
        nlinarith [hdenLower, him]
      have hpow : (2 + |z.im|) ^ ex ≤ (2 * ‖den z‖) ^ E := by
        calc
          _ ≤ (2 * ‖den z‖) ^ ex :=
            pow_le_pow_left₀ (by positivity : 0 ≤ (2 + |z.im| : ℝ)) htime ex
          _ ≤ (2 * ‖den z‖) ^ E :=
            pow_le_pow_right₀ (by linarith [hdenLower]) hexp
      have hdennorm : ‖den z ^ E‖ = ‖den z‖ ^ E := norm_pow _ _
      have hGnorm : ‖G z‖ = ‖L z‖ / ‖den z‖ ^ E := by
        simp [G, hdennorm, norm_div]
      rw [hGnorm]
      calc
        ‖L z‖ / ‖den z‖ ^ E ≤
            (Cx * (2 * ‖den z‖) ^ E) / ‖den z‖ ^ E :=
          div_le_div_of_nonneg_right
            (hlineZ.trans (mul_le_mul_of_nonneg_left hpow (le_of_lt hCx)))
            (by positivity)
        _ = Cx * 2 ^ E := by
          rw [mul_pow]
          field_simp [ne_of_gt
            (lt_of_lt_of_le (show 0 < (2 : ℝ) from by norm_num) hdenLower)] <;> ring
    let Cedge := max (Ca * 2 ^ E) (Cb * 2 ^ E) + 1
    have hEdgeA : ∀ z : ℂ, z.re = a → ‖G z‖ ≤ Cedge := by
      intro z hz
      have h := hEdgeLine a Ca hCa ea hla (Nat.le_max_left ea eb) (Or.inl rfl) z hz
      dsimp [Cedge]
      exact (le_trans h (le_max_left _ _)).trans (by linarith)
    have hEdgeB : ∀ z : ℂ, z.re = b → ‖G z‖ ≤ Cedge := by
      intro z hz
      have h := hEdgeLine b Cb hCb eb hlb (Nat.le_max_right ea eb) (Or.inr rfl) z hz
      dsimp [Cedge]
      exact (le_trans h (le_max_right _ _)).trans (by linarith)
    rcases hdouble with ⟨A₀, B₀, hc₀, hdouble₀⟩
    have hdoublePL : ∃ A₀ B₀ c₀ : ℝ, c₀ < Real.pi / (b - a) ∧
        ∀ z : ℂ, a < z.re → z.re < b →
          ‖G z‖ ≤ A₀ * Real.exp (B₀ * Real.exp (c₀ * |z.im|)) :=
      ⟨A₀, B₀, c, hc₀, hdouble₀⟩
    have hPL := ext_phragmen_lindelof (f := G) (a := a) (b := b)
      (C := Cedge) hGdc hdoublePL hEdgeA hEdgeB
    let M := max |a| |b|
    let K : ℝ := B + M + 1
    have hKpos : 0 < K := by dsimp [K, B, M]; positivity
    refine ⟨Cedge * K ^ E, (E : ℝ), by positivity, Nat.cast_nonneg _, ?_⟩
    intro s hsa hsb
    have hGbound := hPL s hsa hsb
    have hscl : s ∈ closedStrip := ⟨hsa, hsb⟩
    have habs : |s.re| ≤ M := by
      have hM₁ : |a| ≤ M := le_max_left _ _
      have hM₂ : |b| ≤ M := le_max_right _ _
      apply abs_le.mpr
      constructor
      · calc
          -M ≤ -|a| := by linarith
          _ ≤ s.re := by linarith [hscl.1, neg_abs_le a]
      · calc
          s.re ≤ b := hscl.2
          _ ≤ |b| := le_abs_self b
          _ ≤ M := hM₂
    have hnorm : ‖den s‖ ≤ K * (2 + |s.im|) := by
      have htriangle := Complex.norm_le_abs_re_add_abs_im (den s)
      have hreal : |(den s).re| ≤ B + M := by
        change |B + s.re| ≤ B + M
        calc
          |B + s.re| ≤ |B| + |s.re| := abs_add_le _ _
          _ = B + |s.re| := by rw [abs_of_nonneg (by dsimp [B]; positivity)]
          _ ≤ B + M := by nlinarith [habs]
      have hIm : |(den s).im| = |s.im| := by simp [den]
      rw [hIm] at htriangle
      calc
        ‖den s‖ ≤ B + M + |s.im| := htriangle.trans (add_le_add hreal le_rfl)
        _ ≤ K * (2 + |s.im|) := by
          dsimp [K]
          have hBM : 0 ≤ B + M := by dsimp [B, M]; positivity
          have hKM : 1 ≤ B + M + 1 := by linarith
          nlinarith [mul_nonneg (sub_nonneg.mpr hKM) (abs_nonneg s.im)]
    have hrec : L s = G s * den s ^ E := by
      dsimp [G]
      field_simp [hdenNe s hscl]
    have hpow : ‖den s‖ ^ E ≤ K ^ E * (2 + |s.im|) ^ E := by
      calc
        _ ≤ (K * (2 + |s.im|)) ^ E :=
          pow_le_pow_left₀ (norm_nonneg _) hnorm E
        _ = _ := by rw [mul_pow]
    have hpowEq : (2 + |s.im|) ^ E = Real.rpow (2 + |s.im|) (E : ℝ) :=
      (Real.rpow_natCast _ E).symm
    calc
      ‖L s‖ = ‖G s‖ * ‖den s‖ ^ E := by rw [hrec]; simp [norm_pow]
      _ ≤ Cedge * K ^ E * (2 + |s.im|) ^ E :=
        calc
          _ ≤ Cedge * ‖den s‖ ^ E :=
            mul_le_mul_of_nonneg_right hGbound (by positivity)
          _ ≤ Cedge * (K ^ E * (2 + |s.im|) ^ E) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
          _ = _ := by ring
      _ = Cedge * K ^ E * Real.rpow (2 + |s.im|) (E : ℝ) := by rw [hpowEq]

/-- **ext:hecke-continuation** (Tate, Main Theorem 4.4.1 and §4.5; blueprint:140).
For a primitive nonprincipal finite-order character of a totally complex number field, the Hecke
series has an entire continuation, polynomial growth on vertical strips, and the completed
functional equation with a root number of modulus one. Corrected per sol-gate-a2 to restrict the
pointwise Gamma product to arguments where both Gamma factors are regular. -/
theorem ext_hecke_continuation (hTC : IsTotallyComplex F)
    (ω : ArtinPrimitiveRoots.A1.HeckeChar F) (hfin : IsOfFinOrder ω) (hnon : ω ≠ 1)
    (𝔣 : Ideal (𝓞 F)) (h𝔣 : IsPrimitiveConductor ω 𝔣) :
    ∃ L Ldual : ℂ → ℂ,
      Differentiable ℂ L ∧ Differentiable ℂ Ldual ∧
      (∀ s : ℂ, 1 < s.re → L s = heckeLSeries ω s) ∧
      (∀ s : ℂ, 1 < s.re → Ldual s = heckeLSeries (ω⁻¹) s) ∧
      (∀ a b : ℝ, a ≤ b → ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧
        ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
          ‖L s‖ ≤ C * Real.rpow (2 + |s.im|) A) ∧
      (∀ a b : ℝ, a ≤ b → ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧
        ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
          ‖Ldual s‖ ≤ C * Real.rpow (2 + |s.im|) A) ∧
      ∃ W : ℂ, ‖W‖ = 1 ∧ ∀ s : ℂ,
      (∀ n : ℕ, s ≠ -(n : ℂ)) →
      (∀ n : ℕ, 1 - s ≠ -(n : ℂ)) →
          completedHeckeValue L 𝔣 s =
            W * completedHeckeValue Ldual 𝔣 (1 - s) := by
  letI : IsTotallyComplex F := hTC
  obtain ⟨m, ψ, hmNorm, hψ, hp, hseries, hseriesInv⟩ :=
    ArtinPrimitiveRoots.Proofs.A2FreqP.exists_primitive_ray_bridge
      (F := F) ω hfin hnon 𝔣 h𝔣
  let L : ℂ → ℂ := ArtinPrimitiveRoots.Hecke.hkEntireL ψ
  let Ldual : ℂ → ℂ := ArtinPrimitiveRoots.Hecke.hkEntireL (ψ⁻¹)
  obtain ⟨hLd, hLdualD, hLray, hLdualRay, hCd, hCdualD,
      hCeq, hCdualEq, hW⟩ :=
    ArtinPrimitiveRoots.Hecke.hk_fe_export_to_ext_hecke_continuation ψ hψ hp
  have hAgree : ∀ s : ℂ, 1 < s.re → L s = heckeLSeries ω s := by
    intro s hs
    exact (hLray s hs).trans (hseries s hs).symm
  have hAgreeDual : ∀ s : ℂ, 1 < s.re → Ldual s = heckeLSeries (ω⁻¹) s := by
    intro s hs
    exact (hLdualRay s hs).trans (hseriesInv s hs).symm
  have hAgreeRay : ∀ s : ℂ, 1 < s.re →
      L s = ArtinPrimitiveRoots.Hecke.LSeriesRay ψ s := by
    intro s hs
    simpa [L] using hLray s hs
  have hAgreeInvRay : ∀ s : ℂ, 1 < s.re →
      Ldual s = ArtinPrimitiveRoots.Hecke.LSeriesRay (ψ⁻¹) s := by
    intro s hs
    simpa [Ldual] using hLdualRay s hs
  have hCompletedEq (G : ℂ → ℂ) (s : ℂ) :
      ArtinPrimitiveRoots.Hecke.hkCompletedValue G m s = completedHeckeValue G 𝔣 s := by
    unfold ArtinPrimitiveRoots.Hecke.hkCompletedValue completedHeckeValue
    have hdisc : ((NumberField.discr F).natAbs : ℝ) = |NumberField.discr F| := by
      simp
    have hbase :
        ((NumberField.discr F).natAbs : ℝ) *
            (ArtinPrimitiveRoots.Hecke.modulusNorm m : ℝ) =
          |NumberField.discr F| * (Ideal.absNorm 𝔣 : ℝ) := by
      rw [hdisc, hmNorm]
    rw [hbase]
  have hfe := hW
  rcases hfe with ⟨W, hWnorm, hWfe⟩
  have hψInv : ψ⁻¹ ≠ 1 := by
    intro hInv
    apply hψ
    calc
      ψ = (ψ⁻¹)⁻¹ := (inv_inv ψ).symm
      _ = (1 : ClassFieldTheory.RayClassGroup m →* ℂˣ)⁻¹ :=
        congrArg Inv.inv hInv
      _ = 1 := by ext C; simp
  have hpInv : ArtinPrimitiveRoots.Hecke.HKPrimitive (ψ⁻¹) := by
    simpa [ArtinPrimitiveRoots.Hecke.HKPrimitive] using
      ArtinPrimitiveRoots.Dictionary.HKDICTRay.primitive_inv ψ hp
  have hWne : W ≠ 0 := by
    intro hzero
    rw [hzero] at hWnorm
    norm_num at hWnorm
  have hWInv : ‖W⁻¹‖ = 1 := by rw [norm_inv, hWnorm]; norm_num
  have hWfeInv : ∀ s : ℂ,
      ArtinPrimitiveRoots.Hecke.hkCompleted (ψ⁻¹) s =
        W⁻¹ * ArtinPrimitiveRoots.Hecke.hkCompleted ψ (1 - s) := by
    intro s
    have h := hWfe (1 - s)
    have hEq : ArtinPrimitiveRoots.Hecke.hkCompleted ψ (1 - s) =
        W * ArtinPrimitiveRoots.Hecke.hkCompleted (ψ⁻¹) s := by simpa using h
    calc
      ArtinPrimitiveRoots.Hecke.hkCompleted (ψ⁻¹) s =
          W⁻¹ * (W * ArtinPrimitiveRoots.Hecke.hkCompleted (ψ⁻¹) s) := by
            simp [hWne]
      _ = W⁻¹ * ArtinPrimitiveRoots.Hecke.hkCompleted ψ (1 - s) := by rw [← hEq]
  refine ⟨L, Ldual, ?_, ?_, hAgree, hAgreeDual, ?_, ?_, ⟨W, hWnorm, ?_⟩⟩
  · simpa [L] using hLd
  · simpa [Ldual] using hLdualD
  · exact hk_ray_strip_growth ψ hψ hp L Ldual (by rfl) (by rfl)
      hLd hLdualD hAgreeRay hAgreeInvRay
      hCeq hCdualEq W hWnorm hWfe
  · exact hk_ray_strip_growth (ψ⁻¹) hψInv hpInv Ldual L (by rfl) (by rfl)
      hLdualD hLd
      hAgreeInvRay hAgreeRay hCdualEq hCeq W⁻¹ hWInv hWfeInv
  · intro s hs h1s
    calc
      completedHeckeValue L 𝔣 s =
          ArtinPrimitiveRoots.Hecke.hkCompletedValue L m s := (hCompletedEq L s).symm
      _ = ArtinPrimitiveRoots.Hecke.hkCompleted ψ s := (hCeq s hs).symm
      _ = W * ArtinPrimitiveRoots.Hecke.hkCompleted (ψ⁻¹) (1 - s) := hWfe s
      _ = W * ArtinPrimitiveRoots.Hecke.hkCompletedValue Ldual m (1 - s) := by
        rw [hCdualEq (1 - s) h1s]
      _ = W * completedHeckeValue Ldual 𝔣 (1 - s) := by
        rw [hCompletedEq Ldual (1 - s)]

end ArtinPrimitiveRoots.A2
