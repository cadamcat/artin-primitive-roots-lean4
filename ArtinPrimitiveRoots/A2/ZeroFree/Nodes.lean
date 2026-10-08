import ArtinPrimitiveRoots.A2.ZeroFree.Results
import ArtinPrimitiveRoots.A2.FSide
import ArtinPrimitiveRoots.A2.Proofs.A2_ZERO_DETECT.Detect
import ArtinPrimitiveRoots.A2.Proofs.«A2-FE-GLUE».CharacterBridge
import ArtinPrimitiveRoots.A2.Proofs.«A2-FE-GLUE».GammaRatio
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
  sorry

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
  sorry

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
  sorry

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
