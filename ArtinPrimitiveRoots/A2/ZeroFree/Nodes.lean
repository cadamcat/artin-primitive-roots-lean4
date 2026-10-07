import ArtinPrimitiveRoots.A2.ZeroFree.Results
import ArtinPrimitiveRoots.A2.FSide
import ArtinPrimitiveRoots.Hecke.Dedekind
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
  sorry

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
  sorry

end ArtinPrimitiveRoots.A2
