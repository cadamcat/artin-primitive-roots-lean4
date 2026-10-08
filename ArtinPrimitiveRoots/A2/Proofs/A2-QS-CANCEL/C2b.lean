import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».C2
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».C1
import ArtinPrimitiveRoots.Proofs.qs_c_p.C2bHelpers

/-!
# A2-QS-CANCEL, part C2b: the paired main-term (boundary) bound

Guide: `runs/lanes/sol-thin-found/PROOFS.md:473-498` (`paired_main_bound`), lead's form: after
C1 only the boundary `κ/N t < N h ≤ κ` remains; `1/√N h ≤ √(N t/κ)` and the factor
`ψ(t)/√N t` give `1/√κ`.  `ψ(h) = χ_c(h) χ_d(h)` (`qs_gcd_pair_identity_S0` with `g = ⊤`), the
`e, t ∣ 𝔮` factors and `φ(c d)/N(c d) = (φ(c)/N c)(φ(d)/N d)` are column twists of modulus
`≤ 1` (at primes of `qsBadRad` use the local components, which are multiplicative in `c, d`);
apply `qs_divisor_pair_cauchy_C2` with `D₁ = D₂ = 1`-type trivial divisors (Dirac `μ`) and rows
`h` of norm `≤ κ`.  Divisor counts of `𝔮` cost `τ(𝔮)² ≤ (N 𝔮)²`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

/-- C2b (IMPL over C2): the boundary pair sum is
`≪ (N𝔮)² (nκ)^η √(M/κ) B1(κ, 2n) ‖z‖²`. -/
theorem qs_paired_main_bound_C2b [IsTotallyComplex K] (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M κ n : ℝ) (𝔮 : Ideal (𝓞 K)) (cols : Finset (Ideal (𝓞 K)))
      (z : Ideal (𝓞 K) → ℂ),
      0 < M → 1 ≤ κ → 1 ≤ n → QSBlockCols m qS 𝔮 n cols →
      ‖qsPairSum cols z (qsBoundaryKernel F W M κ 𝔮)‖ ≤
          C * qsN 𝔮 ^ 2 * (n * κ) ^ η * Real.sqrt (M / κ) * qsNorm F κ (2 * n) *
          ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  classical
  let ε : ℝ := η / 3
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨C₂, hC₂, hC₂bound⟩ := qs_divisor_pair_cauchy_C2u F hrf ε hε
  obtain ⟨Cφ, hCφ, hdivφ⟩ := qs_divisor_bound_M1 (K := K) ε hε
  obtain ⟨Cq, hCq, hdivq⟩ := qs_divisor_bound_M1 (K := K) 1 (by norm_num)
  let Iw : ℂ := mellin (fun y : ℝ => (W (y ^ 2) : ℂ)) 1
  let C₃ : ℝ := max C₂ 1
  have hC₃₂ : C₂ ≤ C₃ := le_max_left _ _
  have hC₃₁ : 1 ≤ C₃ := le_max_right _ _
  let Kbase : ℝ := ‖(qsResidueOne K : ℂ)‖ * ‖Iw‖ * Cq ^ 2 * C₃ * Cφ ^ 2
  let Ctarget : ℝ := 1 + Kbase * 2 ^ (2 * ε)
  refine ⟨Ctarget, by dsimp [Ctarget]; positivity, ?_⟩
  intro M κ n 𝔮 cols z hM hκ hn hblock
  rcases hblock with ⟨h𝔮, h𝔮bad, hcol, hclass⟩
  have h𝔮0 : 𝔮 ≠ ⊥ := h𝔮.ne_zero
  have h𝔮Npos : 0 < qsN 𝔮 := QSC2.qsN_pos h𝔮0
  have h𝔮N1 : 1 ≤ qsN 𝔮 := by
    have hnat : 1 ≤ Ideal.absNorm 𝔮 := Nat.one_le_iff_ne_zero.mpr (by
      intro hz
      exact h𝔮0 (Ideal.absNorm_eq_zero_iff.mp hz))
    exact_mod_cast hnat
  have hcount𝔮 : ((qsDivisors 𝔮).card : ℝ) ≤ Cq * qsN 𝔮 := by
    simpa [qsN, Real.rpow_one] using hdivq 𝔮 h𝔮0
  have hcols : ∀ c ∈ cols, QSAdm m qS c ∧ qsN c ≤ 2 * n := by
    intro c hc
    exact ⟨(hcol c hc).1, (hcol c hc).2.2.2⟩
  have hcolNonzero : ∀ c ∈ cols, c ≠ ⊥ := by
    intro c hc
    exact QSC2.ne_bot_of_QSAdm (hcol c hc).1
  have hphi : ∀ c ∈ cols, ‖(qsPhiRatio c : ℂ)‖ ≤ Cφ * (2 * n) ^ ε := by
    intro c hc
    have hc0 := hcolNonzero c hc
    have hsmall := qs_c2b_phiRatio_norm_le_card hc0
    have hdiv := hdivφ c hc0
    have hpow : qsN c ^ ε ≤ (2 * n) ^ ε :=
      Real.rpow_le_rpow (by positivity) (hcols c hc).2 hε.le
    exact hsmall.trans (hdiv.trans (mul_le_mul_of_nonneg_left hpow hCφ.le))
  let rows (t : Ideal (𝓞 K)) : Finset (Ideal (𝓞 K)) :=
    (qsSqfUpTo κ 𝔮).filter (fun a => κ / qsN t < qsN a)
  have hrows (t : Ideal (𝓞 K)) (ht : t ≠ ⊥) :
      ∀ a ∈ rows t, QSAdm m qS a ∧ qsN a ≤ κ := by
    intro a ha
    rcases Finset.mem_filter.mp ha with ⟨ha₀, _⟩
    have ha' := ha₀
    simp only [qsSqfUpTo, Finset.mem_filter, Set.Finite.mem_toFinset,
      Set.mem_ofPred_eq] at ha'
    rcases ha' with ⟨_, ⟨ha0, hasqf, hacop, hNa⟩⟩
    exact ⟨qs_c2b_row_admissible hqS h𝔮bad ha0 hasqf hacop, hNa⟩
  let ρ (t a : Ideal (𝓞 K)) : ℂ :=
    if κ / qsN t < qsN a then
      (((Real.sqrt κ / (Real.sqrt (qsN t) * Real.sqrt (qsN a))) : ℝ) : ℂ)
    else 0
  have hρ (t : Ideal (𝓞 K)) (ht : t ≠ ⊥) : ∀ a, ‖ρ t a‖ ≤ 1 := by
    intro a
    by_cases hcut : κ / qsN t < qsN a
    · have htpos : 0 < qsN t := QSC2.qsN_pos ht
      have hapos : 0 < qsN a := lt_trans (div_pos (by linarith) htpos) hcut
      have hden : 0 < Real.sqrt (qsN t) * Real.sqrt (qsN a) :=
        mul_pos (Real.sqrt_pos.2 htpos) (Real.sqrt_pos.2 hapos)
      have hprod : κ < qsN t * qsN a := by
        simpa [mul_comm] using (div_lt_iff₀ htpos).mp hcut
      have hroot : Real.sqrt κ < Real.sqrt (qsN t * qsN a) :=
        Real.sqrt_lt_sqrt (by positivity) hprod
      have hrootmul : Real.sqrt (qsN t * qsN a) =
          Real.sqrt (qsN t) * Real.sqrt (qsN a) := Real.sqrt_mul (le_of_lt htpos) _
      have hratio : Real.sqrt κ / (Real.sqrt (qsN t) * Real.sqrt (qsN a)) ≤ 1 :=
        (div_le_iff₀ hden).2 (by rw [one_mul, ← hrootmul]; exact le_of_lt hroot)
      have hrhoNonneg :
          0 ≤ Real.sqrt κ / (Real.sqrt (qsN t) * Real.sqrt (qsN a)) :=
        div_nonneg (Real.sqrt_nonneg _) (le_of_lt hden)
      calc
        ‖ρ t a‖ = ‖((Real.sqrt κ / (Real.sqrt (qsN t) * Real.sqrt (qsN a)) : ℝ) : ℂ)‖ := by
          rw [show ρ t a =
            ((Real.sqrt κ / (Real.sqrt (qsN t) * Real.sqrt (qsN a)) : ℝ) : ℂ) by
              simp [ρ, hcut]]
        _ = |Real.sqrt κ / (Real.sqrt (qsN t) * Real.sqrt (qsN a))| := by
          rw [Complex.norm_real, Real.norm_eq_abs]
        _ = Real.sqrt κ / (Real.sqrt (qsN t) * Real.sqrt (qsN a)) :=
          abs_of_nonneg hrhoNonneg
        _ ≤ 1 := hratio
    · simp [ρ, hcut]
  let ztw (e t c : Ideal (𝓞 K)) : ℂ :=
    z c * (qsPhiRatio c : ℂ) * qsC2bLocalTwist (F.character c) e *
      qsC2bLocalTwist (F.character c) t
  have hztw (e t : Ideal (𝓞 K)) (c : Ideal (𝓞 K)) (hc : c ∈ cols) :
      ‖ztw e t c‖ ≤ (Cφ * (2 * n) ^ ε) * ‖z c‖ := by
    have hcAdm := (hcol c hc).1
    rw [show ztw e t c = z c * (qsPhiRatio c : ℂ) *
        qsC2bLocalTwist (F.character c) e * qsC2bLocalTwist (F.character c) t by rfl]
    rw [norm_mul, norm_mul, norm_mul,
      qs_c2b_localTwist_norm_eq_one F hcAdm e,
      qs_c2b_localTwist_norm_eq_one F hcAdm t, mul_one, mul_one]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (hphi c hc) (norm_nonneg (z c))
  have hztwEnergy (e t : Ideal (𝓞 K)) :
      ∑ c ∈ cols, ‖ztw e t c‖ ^ 2 ≤
        (Cφ * (2 * n) ^ ε) ^ 2 * ∑ c ∈ cols, ‖z c‖ ^ 2 := by
    calc
      _ ≤ ∑ c ∈ cols, ((Cφ * (2 * n) ^ ε) * ‖z c‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro c hc
        have hz := hztw e t c hc
        have hnonneg : 0 ≤ (Cφ * (2 * n) ^ ε) * ‖z c‖ := by positivity
        exact pow_le_pow_left₀ (norm_nonneg _) hz 2
      _ = (Cφ * (2 * n) ^ ε) ^ 2 * ∑ c ∈ cols, ‖z c‖ ^ 2 := by
        simp_rw [mul_pow]
        rw [Finset.mul_sum]
  have hlargeBlock (e t : Ideal (𝓞 K)) (ht : t ≠ ⊥) (hκ₂ : 2 ≤ κ) :
      ‖qsPairSum cols (ztw e t) (fun c d =>
        ∑ a ∈ rows t, ρ t a * (F.character c).idealValue a *
          (F.character d).idealValue a)‖ ≤
        C₂ * (n * κ) ^ ε * qsNorm F κ (2 * n) *
          (Cφ * (2 * n) ^ ε) ^ 2 * ∑ c ∈ cols, ‖z c‖ ^ 2 := by
    let B : ℝ := κ / 2
    have hB : 1 ≤ B := by dsimp [B]; linarith
    let p : Ideal (𝓞 K) → Prop := fun e => e = ⊤
    let μ : MeasureTheory.Measure ℝ := MeasureTheory.Measure.dirac (0 : ℝ)
    let φ : ℝ → ℝ → ℝ → ℂ := fun _ _ _ => 1
    let Φ : ℝ → ℝ → ℝ → ℂ := fun _ _ _ => 1
    let gmaj : ℝ → ℝ := fun _ => 1
    haveI : MeasureTheory.IsFiniteMeasure μ := by dsimp [μ]; infer_instance
    have hmeasure : ∀ y u x : ℝ,
        Φ y u x = ∫ t, ((x : ℂ) ^ ((t : ℂ) * Complex.I)) * φ y u t ∂μ := by
      intro y u x
      simpa [μ, Φ, φ] using qs_c2b_dirac_constant_mixture y u x
    have hint : MeasureTheory.Integrable gmaj μ := by simp [gmaj, μ]
    have hmaj : ∀ y u t, ‖φ y u t‖ ≤ gmaj t := by simp [φ, gmaj]
    have hmass : ∫ t, gmaj t ∂μ ≤ 1 := by simp [gmaj, μ]
    have hp : ∀ e, p e → 1 ≤ qsN e ∧ qsN e ≤ 2 := by
      intro e he
      subst e
      simp [qsN]
    have hpC2 : ∀ e, p e → 1 ≤ qsN e ∧ qsN e ≤ 2 * 1 := by
      intro e he
      simpa using hp e he
    have hcolC2 : ∀ c ∈ cols, QSAdm m qS c ∧ qsN c ≤ 2 * n := hcols
    have hrowC2 : ∀ a ∈ rows t, QSAdm m qS a ∧ qsN a ≤ 2 * B := by
      intro a ha
      have h := hrows t ht a ha
      exact ⟨h.1, by dsimp [B]; nlinarith [h.2]⟩
    have hρC2 : ∀ a, ‖ρ t a‖ ≤ 1 := hρ t ht
    have hbase := hC₂bound n B 1 1 1 p p cols (rows t) (ztw e t) (ρ t)
      μ φ Φ gmaj (by linarith) hB (by norm_num) (by norm_num) hpC2 hpC2
      hcolC2 hrowC2 hρC2 hmeasure hint hmaj hmass
    have hsel (c : Ideal (𝓞 K)) (hc : c ∈ cols) :
        (qsDivisors c).filter p = {⊤} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton, p]
      constructor
      · intro hx
        exact hx.2
      · intro hx
        subst x
        refine ⟨(QSC2.mem_qsDivisors (hcolNonzero c hc)).2 ?_, rfl⟩
        simp
    have hcollapsed (c d : Ideal (𝓞 K)) (hc : c ∈ cols) (hd : d ∈ cols) :
        (∑ e₁ ∈ (qsDivisors c).filter p, ∑ e₂ ∈ (qsDivisors d).filter p,
          (qsMu (e₁ * e₂) : ℂ) *
            ∑ a ∈ rows t, ρ t a * (F.character c).idealValue a *
              (F.character d).idealValue a * Φ (qsN a) (qsN (e₁ * e₂)) (qsN (c * d))) =
          ∑ a ∈ rows t, ρ t a * (F.character c).idealValue a *
            (F.character d).idealValue a := by
      rw [hsel c hc, hsel d hd]
      have hmuTop : qsMu (⊤ : Ideal (𝓞 K)) = 1 := by
        exact qs_c2b_mu_top
      simp only [Finset.sum_singleton]
      rw [show (⊤ * ⊤ : Ideal (𝓞 K)) = ⊤ by simp, hmuTop]
      simp [qsN, Φ]
    have hpairEq :
        qsPairSum cols (ztw e t) (fun c d =>
          ∑ e₁ ∈ (qsDivisors c).filter p, ∑ e₂ ∈ (qsDivisors d).filter p,
            (qsMu (e₁ * e₂) : ℂ) *
              ∑ a ∈ rows t, ρ t a * (F.character c).idealValue a *
                (F.character d).idealValue a * Φ (qsN a) (qsN (e₁ * e₂)) (qsN (c * d))) =
        qsPairSum cols (ztw e t) (fun c d =>
          ∑ a ∈ rows t, ρ t a * (F.character c).idealValue a *
            (F.character d).idealValue a) := by
      unfold qsPairSum
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hcd : IsCoprime c d
      · simp only [if_pos hcd]
        rw [hcollapsed c d hc hd]
      · simp [hcd]
    rw [hpairEq] at hbase
    have hnorm : 0 ≤ qsNorm F κ (2 * n) := sq_nonneg _
    have hsqrt : Real.sqrt (qsNorm F κ (2 * n) * qsNorm F κ (2 * n)) =
        qsNorm F κ (2 * n) := by
      rw [show qsNorm F κ (2 * n) * qsNorm F κ (2 * n) =
        (qsNorm F κ (2 * n)) ^ 2 by ring, Real.sqrt_sq hnorm]
    have h2B : 2 * B = κ := by dsimp [B]; ring
    have hbase' :
        ‖qsPairSum cols (ztw e t) (fun c d =>
          ∑ a ∈ rows t, ρ t a * (F.character c).idealValue a *
            (F.character d).idealValue a)‖ ≤
          C₂ * (n * B) ^ ε * qsNorm F κ (2 * n) *
            ∑ c ∈ cols, ‖ztw e t c‖ ^ 2 := by
      rw [h2B] at hbase
      simpa [hsqrt] using hbase
    have hpow : (n * B) ^ ε ≤ (n * κ) ^ ε := by
      apply Real.rpow_le_rpow (by positivity) _ hε.le
      dsimp [B]
      nlinarith [hn, hκ₂]
    calc
      _ ≤ C₂ * (n * B) ^ ε * qsNorm F κ (2 * n) *
            ∑ c ∈ cols, ‖ztw e t c‖ ^ 2 := hbase'
      _ ≤ C₂ * (n * B) ^ ε * qsNorm F κ (2 * n) *
            ((Cφ * (2 * n) ^ ε) ^ 2 * ∑ c ∈ cols, ‖z c‖ ^ 2) := by
          exact mul_le_mul_of_nonneg_left (hztwEnergy e t)
            (by positivity [C₂, qsNorm F κ (2 * n), (n * B) ^ ε])
      _ ≤ C₂ * (n * κ) ^ ε * qsNorm F κ (2 * n) *
            ((Cφ * (2 * n) ^ ε) ^ 2 * ∑ c ∈ cols, ‖z c‖ ^ 2) := by
          gcongr
      _ = C₂ * (n * κ) ^ ε * qsNorm F κ (2 * n) *
            (Cφ * (2 * n) ^ ε) ^ 2 * ∑ c ∈ cols, ‖z c‖ ^ 2 := by ring
  have hsmallBlock (e t : Ideal (𝓞 K)) (ht : t ≠ ⊥) (hκsmall : κ < 2) :
      ‖qsPairSum cols (ztw e t) (fun c d =>
        ∑ a ∈ rows t, ρ t a * (F.character c).idealValue a *
          (F.character d).idealValue a)‖ ≤
        qsNorm F κ (2 * n) * (Cφ * (2 * n) ^ ε) ^ 2 *
          ∑ c ∈ cols, ‖z c‖ ^ 2 := by
    have hrowsSub : rows t ⊆ {⊤} := by
      intro a ha
      have hrow := hrows t ht a ha
      have ha0 : a ≠ ⊥ := QSC2.ne_bot_of_QSAdm hrow.1
      have hNaPos : 0 < Ideal.absNorm a := Nat.pos_iff_ne_zero.mpr (by
        intro hz
        exact ha0 (Ideal.absNorm_eq_zero_iff.mp hz))
      have hNa1 : 1 ≤ Ideal.absNorm a := Nat.one_le_iff_ne_zero.mpr (by omega)
      have hNaLt : (Ideal.absNorm a : ℝ) < 2 := lt_of_le_of_lt hrow.2 hκsmall
      have hNaNatLt : Ideal.absNorm a < 2 := by exact_mod_cast hNaLt
      have hNaEq : Ideal.absNorm a = 1 := by omega
      have haTop : a = ⊤ := Ideal.absNorm_eq_one_iff.mp hNaEq
      exact Finset.mem_singleton.mpr haTop
    have hrowsEq : rows t = if (⊤ : Ideal (𝓞 K)) ∈ rows t then {⊤} else ∅ := by
      ext a
      constructor
      · intro ha
        have haTop := hrowsSub ha
        simp only [Finset.mem_singleton] at haTop
        subst a
        simp [ha]
      · intro ha
        split_ifs at ha with htop
        · have haTop : a = ⊤ := by simpa using ha
          exact haTop ▸ htop
        · simp at ha
    let r : ℂ := if (⊤ : Ideal (𝓞 K)) ∈ rows t then ρ t ⊤ else 0
    have hcore (c d : Ideal (𝓞 K)) :
        (∑ a ∈ rows t, ρ t a * (F.character c).idealValue a *
          (F.character d).idealValue a) = r := by
      rw [hrowsEq]
      by_cases htop : (⊤ : Ideal (𝓞 K)) ∈ rows t <;>
        simp [r, htop, qs_c2b_idealValue_top]
    have hrnorm : ‖r‖ ≤ 1 := by
      by_cases htop : (⊤ : Ideal (𝓞 K)) ∈ rows t
      · simp [r, htop]
        exact hρ t ht ⊤
      · simp [r, htop]
    have hconst :
        ‖qsPairSum cols (ztw e t) (fun _ _ => (1 : ℂ))‖ ≤
          (cols.card : ℝ) * ∑ c ∈ cols, ‖ztw e t c‖ ^ 2 := by
      unfold qsPairSum
      dsimp
      simp only [mul_one]
      calc
        _ ≤ ∑ c ∈ cols, ‖∑ d ∈ cols,
              if IsCoprime c d then ztw e t c * conj (ztw e t d) else 0‖ := norm_sum_le _ _
        _ ≤ ∑ c ∈ cols, ∑ d ∈ cols, ‖ztw e t c‖ * ‖ztw e t d‖ := by
          apply Finset.sum_le_sum
          intro c hc
          calc
            _ ≤ ∑ d ∈ cols,
                ‖if IsCoprime c d then ztw e t c * conj (ztw e t d) else 0‖ := norm_sum_le _ _
            _ ≤ ∑ d ∈ cols, ‖ztw e t c‖ * ‖ztw e t d‖ := by
              apply Finset.sum_le_sum
              intro d hd
              by_cases hcd : IsCoprime c d
              · simp [hcd, norm_mul, Complex.norm_conj]
              · simp [hcd]
                positivity
        _ = (∑ c ∈ cols, ‖ztw e t c‖) ^ 2 := by
          rw [← Finset.sum_mul_sum]
          ring
        _ ≤ (cols.card : ℝ) * ∑ c ∈ cols, ‖ztw e t c‖ ^ 2 := by
          have hcs := Finset.sum_mul_sq_le_sq_mul_sq cols
            (fun c => ‖ztw e t c‖) (fun _ => (1 : ℝ))
          simpa [mul_comm] using hcs
    have hcard := qs_c2b_cols_card_le_norm F κ n hκ hn cols hcols
    have hconst' :
        ‖qsPairSum cols (ztw e t) (fun _ _ => (1 : ℂ))‖ ≤
          qsNorm F κ (2 * n) * ∑ c ∈ cols, ‖ztw e t c‖ ^ 2 := by
      calc
        _ ≤ (cols.card : ℝ) * ∑ c ∈ cols, ‖ztw e t c‖ ^ 2 := hconst
        _ ≤ qsNorm F κ (2 * n) * ∑ c ∈ cols, ‖ztw e t c‖ ^ 2 := by
          gcongr
    have hpairEq :
        qsPairSum cols (ztw e t) (fun c d =>
          ∑ a ∈ rows t, ρ t a * (F.character c).idealValue a *
            (F.character d).idealValue a) =
          r * qsPairSum cols (ztw e t) (fun _ _ => (1 : ℂ)) := by
      calc
        _ = qsPairSum cols (ztw e t) (fun c d => r * (1 : ℂ)) := by
          apply congrArg (qsPairSum cols (ztw e t))
          funext c d
          simp [hcore]
        _ = _ := qs_c2b_pairSum_const_mul cols (ztw e t) r (fun _ _ => (1 : ℂ))
    calc
      _ = ‖r * qsPairSum cols (ztw e t) (fun _ _ => (1 : ℂ))‖ := by rw [hpairEq]
      _ = ‖r‖ * ‖qsPairSum cols (ztw e t) (fun _ _ => (1 : ℂ))‖ := norm_mul _ _
      _ ≤ 1 * (qsNorm F κ (2 * n) * ∑ c ∈ cols, ‖ztw e t c‖ ^ 2) :=
        mul_le_mul hrnorm hconst' (norm_nonneg _) zero_le_one
      _ ≤ qsNorm F κ (2 * n) *
          ((Cφ * (2 * n) ^ ε) ^ 2 * ∑ c ∈ cols, ‖z c‖ ^ 2) := by
        have hnormQ : 0 ≤ qsNorm F κ (2 * n) := sq_nonneg _
        have hmulEnergy := mul_le_mul_of_nonneg_left (hztwEnergy e t) hnormQ
        simpa [one_mul] using hmulEnergy
      _ = qsNorm F κ (2 * n) * (Cφ * (2 * n) ^ ε) ^ 2 *
          ∑ c ∈ cols, ‖z c‖ ^ 2 := by ring
  let qdiv := qsDivisors 𝔮
  have hqdiv (e : Ideal (𝓞 K)) (he : e ∈ qdiv) : e ≠ ⊥ ∧ e ∣ 𝔮 := by
    have hediv : e ∣ 𝔮 := (QSC2.mem_qsDivisors h𝔮0).mp he
    constructor
    · intro he0
      subst e
      have hle : 𝔮 ≤ ⊥ := Ideal.le_of_dvd hediv
      exact h𝔮0 (bot_unique hle)
    · exact hediv
  let ψ (c d : Ideal (𝓞 K)) := qsPairChar F c d
  let rowPsi (t c d : Ideal (𝓞 K)) :=
    ∑ a ∈ rows t, (ψ c d).idealValue a * ρ t a
  let rowCore (t c d : Ideal (𝓞 K)) :=
    ∑ a ∈ rows t, ρ t a * (F.character c).idealValue a * (F.character d).idealValue a
  let kernelET (e t c d : Ideal (𝓞 K)) :=
    (qsPhiRatio (c * d) : ℂ) * (ψ c d).idealValue e * (ψ c d).idealValue t *
      rowPsi t c d
  let outerWeight (e : Ideal (𝓞 K)) := (qsMu e : ℂ) / (Real.sqrt (qsN e) : ℂ)
  let rootInv : ℂ := (1 / (Real.sqrt κ : ℝ) : ℂ)
  have hrowPair (t c d a : Ideal (𝓞 K)) (ht : t ≠ ⊥)
      (hc : c ∈ cols) (hd : d ∈ cols) (hcd : IsCoprime c d) (ha : a ∈ rows t) :
      (ψ c d).idealValue a =
        (F.character c).idealValue a * (F.character d).idealValue a := by
    have haAdm := (hrows t ht a ha).1
    have hcAdm := (hcol c hc).1
    have hdAdm := (hcol d hd).1
    have hgc : IsCoprime (⊤ : Ideal (𝓞 K)) c := by
      apply Ideal.isCoprime_iff_sup_eq.mpr
      exact sup_eq_left.mpr le_top
    have hgd : IsCoprime (⊤ : Ideal (𝓞 K)) d := by
      apply Ideal.isCoprime_iff_sup_eq.mpr
      exact sup_eq_left.mpr le_top
    have hatop : IsCoprime a (⊤ : Ideal (𝓞 K)) := by
      apply Ideal.isCoprime_iff_sup_eq.mpr
      exact sup_eq_right.mpr le_top
    have hident := qs_gcd_pair_identity_S0 F hrf (⊤ : Ideal (𝓞 K)) c d
      qs_c2b_top_admissible hcAdm hdAdm hgc hgd hcd a
      haAdm.2.1 haAdm.2.2
    have hident' :
        (F.character c).idealValue a * conj ((F.character d).idealValue a) =
          (ψ c d).idealValue a := by
      rw [if_pos hatop] at hident
      simpa [ψ, qsPairChar] using hident
    rw [qs_c2b_char_conj_eq F hdAdm a] at hident'
    exact hident'.symm
  have hEtTerm (e t c d : Ideal (𝓞 K)) (he : e ∈ qdiv) (htq : t ∈ qdiv)
      (hc : c ∈ cols) (hd : d ∈ cols) (hcd : IsCoprime c d) :
      z c * conj (z d) * kernelET e t c d =
        ztw e t c * conj (ztw e t d) * rowCore t c d := by
    have hcAdm := (hcol c hc).1
    have hdAdm := (hcol d hd).1
    have hcq := (hcol c hc).2.1
    have hdq := (hcol d hd).2.1
    have hphi := qs_phiRatio_mul_C0 c d (hcolNonzero c hc) (hcolNonzero d hd) hcd
    have hedata := hqdiv e he
    have htdata := hqdiv t htq
    have htwE := qs_c2b_pairValue_localTwist F c d 𝔮 e hcAdm hdAdm hcd
      (hclass c hc d hd) hcq hdq hedata.2 hedata.1
    have htwT := qs_c2b_pairValue_localTwist F c d 𝔮 t hcAdm hdAdm hcd
      (hclass c hc d hd) hcq hdq htdata.2 htdata.1
    have hrow : rowPsi t c d = rowCore t c d := by
      dsimp [rowPsi, rowCore]
      apply Finset.sum_congr rfl
      intro a ha
      rw [hrowPair t c d a htdata.1 hc hd hcd ha]
      ring
    change z c * conj (z d) *
        ((qsPhiRatio (c * d) : ℂ) * (ψ c d).idealValue e *
          (ψ c d).idealValue t * rowPsi t c d) =
      ztw e t c * conj (ztw e t d) * rowCore t c d
    rw [hphi, htwE, htwT, hrow]
    have hconjD : conj (ztw e t d) =
        conj (z d) * (qsPhiRatio d : ℂ) *
          qsC2bLocalTwist (F.character d) e * qsC2bLocalTwist (F.character d) t := by
      simp [ztw, qs_c2b_localTwist_conj_eq F hdAdm e,
        qs_c2b_localTwist_conj_eq F hdAdm t]
    rw [show ztw e t c = z c * (qsPhiRatio c : ℂ) *
        qsC2bLocalTwist (F.character c) e * qsC2bLocalTwist (F.character c) t by rfl,
      hconjD]
    push_cast
    ring_nf
  have hEtPair (e t : Ideal (𝓞 K)) (he : e ∈ qdiv) (htq : t ∈ qdiv) :
      qsPairSum cols z (kernelET e t) =
        qsPairSum cols (ztw e t) (rowCore t) := by
    unfold qsPairSum
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hcd : IsCoprime c d
    · simp only [if_pos hcd]
      exact hEtTerm e t c d he htq hc hd hcd
    · simp [hcd]
  let rowOriginal (t c d : Ideal (𝓞 K)) :=
    ∑ a ∈ rows t, (ψ c d).idealValue a / (Real.sqrt (qsN a) : ℂ)
  have hscaleRow (t a : Ideal (𝓞 K)) (htq : t ∈ qdiv) (ha : a ∈ rows t) :
      rootInv * ρ t a =
        1 / (Real.sqrt (qsN t) : ℂ) * (1 / (Real.sqrt (qsN a) : ℂ)) := by
    have ht0 := (hqdiv t htq).1
    have haAdm := (hrows t ht0 a ha).1
    have ha0 := QSC2.ne_bot_of_QSAdm haAdm
    have htN := QSC2.qsN_pos ht0
    have haN := QSC2.qsN_pos ha0
    have hk := Real.sqrt_pos.2 (by linarith : 0 < κ)
    have htS := Real.sqrt_pos.2 htN
    have haS := Real.sqrt_pos.2 haN
    have hkC : (Real.sqrt κ : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    have htC : (Real.sqrt (qsN t) : ℂ) ≠ 0 := by exact_mod_cast htS.ne'
    have haC : (Real.sqrt (qsN a) : ℂ) ≠ 0 := by exact_mod_cast haS.ne'
    have hcut : κ / qsN t < qsN a := (Finset.mem_filter.mp ha).2
    have hscaleReal :
        (1 / Real.sqrt κ) *
            (Real.sqrt κ / (Real.sqrt (qsN t) * Real.sqrt (qsN a))) =
          1 / Real.sqrt (qsN t) * (1 / Real.sqrt (qsN a)) := by
      field_simp [hk.ne', htS.ne', haS.ne']
    rw [show ρ t a =
      ((Real.sqrt κ / (Real.sqrt (qsN t) * Real.sqrt (qsN a)) : ℝ) : ℂ) by
        simp [ρ, hcut]]
    dsimp [rootInv]
    exact_mod_cast hscaleReal
  have hTscale (t : Ideal (𝓞 K)) (htq : t ∈ qdiv) (c d : Ideal (𝓞 K)) :
      (ψ c d).idealValue t / (Real.sqrt (qsN t) : ℂ) * rowOriginal t c d =
        rootInv * (ψ c d).idealValue t * rowPsi t c d := by
    dsimp [rowOriginal, rowPsi]
    rw [Finset.mul_sum]
    calc
      _ = ∑ a ∈ rows t,
            (ψ c d).idealValue t * (ψ c d).idealValue a *
              (1 / (Real.sqrt (qsN t) : ℂ) * (1 / (Real.sqrt (qsN a) : ℂ))) := by
          apply Finset.sum_congr rfl
          intro a ha
          ring
      _ = ∑ a ∈ rows t,
            (ψ c d).idealValue t * (ψ c d).idealValue a * (rootInv * ρ t a) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [← hscaleRow t a htq ha]
      _ = rootInv * (ψ c d).idealValue t *
            ∑ a ∈ rows t, (ψ c d).idealValue a * ρ t a := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          ring
  have hOuter (c d : Ideal (𝓞 K)) :
      (∑ e ∈ qdiv, outerWeight e * (ψ c d).idealValue e) *
        ∑ t ∈ qdiv, (ψ c d).idealValue t / (Real.sqrt (qsN t) : ℂ) *
          rowOriginal t c d =
      ∑ e ∈ qdiv, ∑ t ∈ qdiv,
        outerWeight e * rootInv * (ψ c d).idealValue e * (ψ c d).idealValue t *
          rowPsi t c d := by
    calc
      _ = ∑ e ∈ qdiv, (outerWeight e * (ψ c d).idealValue e) *
            ∑ t ∈ qdiv, (ψ c d).idealValue t / (Real.sqrt (qsN t) : ℂ) *
              rowOriginal t c d := by rw [Finset.sum_mul]
      _ = ∑ e ∈ qdiv, (outerWeight e * (ψ c d).idealValue e) *
            ∑ t ∈ qdiv, rootInv * (ψ c d).idealValue t * rowPsi t c d := by
          apply Finset.sum_congr rfl
          intro e he
          apply congrArg (fun x : ℂ => (outerWeight e * (ψ c d).idealValue e) * x)
          apply Finset.sum_congr rfl
          intro t htq
          exact hTscale t htq c d
      _ = ∑ e ∈ qdiv, ∑ t ∈ qdiv,
            outerWeight e * rootInv * (ψ c d).idealValue e * (ψ c d).idealValue t *
              rowPsi t c d := by
          apply Finset.sum_congr rfl
          intro e he
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t htq
          ring
  have hTsum (c d : Ideal (𝓞 K)) :
      (∑ t ∈ qsDivisors 𝔮,
        (ψ c d).idealValue t / (Real.sqrt (qsN t) : ℂ) *
          ∑ h ∈ (qsSqfUpTo κ 𝔮).filter (fun h => κ / qsN t < qsN h),
            (ψ c d).idealValue h / (Real.sqrt (qsN h) : ℂ)) =
      ∑ t ∈ qdiv, (ψ c d).idealValue t / (Real.sqrt (qsN t) : ℂ) *
        rowOriginal t c d := by
    apply Finset.sum_congr rfl
    intro t ht
    rfl
  have houterWeight (c d e : Ideal (𝓞 K)) :
      ((qsMu e : ℂ) * (ψ c d).idealValue e / (Real.sqrt (qsN e) : ℂ)) =
        outerWeight e * (ψ c d).idealValue e := by
    dsimp [outerWeight]
    ring_nf
  let R0 : ℂ := -((qsResidueOne K : ℂ) * Iw * (Real.sqrt M : ℂ))
  have hKernel (c d : Ideal (𝓞 K)) :
      qsBoundaryKernel F W M κ 𝔮 c d =
        R0 * ∑ e ∈ qdiv, ∑ t ∈ qdiv,
          outerWeight e * rootInv * kernelET e t c d := by
    unfold qsBoundaryKernel
    have hS :
        (∑ e ∈ qdiv, (qsMu e : ℂ) * (ψ c d).idealValue e /
          (Real.sqrt (qsN e) : ℂ)) =
          ∑ e ∈ qdiv, outerWeight e * (ψ c d).idealValue e := by
      apply Finset.sum_congr rfl
      intro e he
      exact houterWeight c d e
    rw [hS, hTsum c d]
    calc
      _ = R0 * ((qsPhiRatio (c * d) : ℂ) *
          ((∑ e ∈ qdiv, outerWeight e * (ψ c d).idealValue e) *
            ∑ t ∈ qdiv, (ψ c d).idealValue t / (Real.sqrt (qsN t) : ℂ) *
              rowOriginal t c d)) := by
            dsimp [R0, Iw]
            ring
      _ = R0 * ((qsPhiRatio (c * d) : ℂ) *
          ∑ e ∈ qdiv, ∑ t ∈ qdiv,
            outerWeight e * rootInv * (ψ c d).idealValue e * (ψ c d).idealValue t *
              rowPsi t c d) := by rw [hOuter c d]
      _ = R0 * ∑ e ∈ qdiv, ∑ t ∈ qdiv,
            outerWeight e * rootInv *
              ((qsPhiRatio (c * d) : ℂ) * (ψ c d).idealValue e *
                (ψ c d).idealValue t * rowPsi t c d) := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e he
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t htq
          ring
      _ = R0 * ∑ e ∈ qdiv, ∑ t ∈ qdiv,
            outerWeight e * rootInv * kernelET e t c d := by
          rfl
  have hBoundaryPair :
      qsPairSum cols z (qsBoundaryKernel F W M κ 𝔮) =
        R0 * ∑ e ∈ qdiv, ∑ t ∈ qdiv,
          outerWeight e * rootInv * qsPairSum cols (ztw e t) (rowCore t) := by
    calc
      _ = qsPairSum cols z (fun c d =>
            R0 * ∑ e ∈ qdiv, ∑ t ∈ qdiv,
              outerWeight e * rootInv * kernelET e t c d) := by
          unfold qsPairSum
          apply Finset.sum_congr rfl
          intro c hc
          apply Finset.sum_congr rfl
          intro d hd
          by_cases hcd : IsCoprime c d
          · simp only [if_pos hcd]
            rw [hKernel c d]
          · simp [hcd]
      _ = R0 * qsPairSum cols z (fun c d =>
            ∑ e ∈ qdiv, ∑ t ∈ qdiv,
              outerWeight e * rootInv * kernelET e t c d) :=
          qs_c2b_pairSum_const_mul cols z R0 _
      _ = R0 * ∑ e ∈ qdiv, ∑ t ∈ qdiv,
            qsPairSum cols z (fun c d => outerWeight e * rootInv * kernelET e t c d) := by
          rw [qs_c2b_pairSum_double_sum]
      _ = R0 * ∑ e ∈ qdiv, ∑ t ∈ qdiv,
            outerWeight e * rootInv * qsPairSum cols (ztw e t) (rowCore t) := by
          congr 1
          apply Finset.sum_congr rfl
          intro e he
          apply Finset.sum_congr rfl
          intro t htq
          rw [qs_c2b_pairSum_const_mul, hEtPair e t he htq]
  let A : ℝ := Cφ * (2 * n) ^ ε
  let Sz : ℝ := ∑ c ∈ cols, ‖z c‖ ^ 2
  let C₃ : ℝ := max C₂ 1
  have hC₃₂ : C₂ ≤ C₃ := le_max_left _ _
  have hC₃₁ : 1 ≤ C₃ := le_max_right _ _
  have hnκ : 1 ≤ n * κ := by nlinarith [hn, hκ]
  have hrpow1 : 1 ≤ (n * κ) ^ ε := Real.one_le_rpow hnκ hε.le
  have hqsNormNonneg : 0 ≤ qsNorm F κ (2 * n) := by
    dsimp [qsNorm]
    positivity
  have hblock (e t : Ideal (𝓞 K)) (he : e ∈ qdiv) (ht : t ∈ qdiv) :
      ‖qsPairSum cols (ztw e t) (rowCore t)‖ ≤
        C₃ * (n * κ) ^ ε * qsNorm F κ (2 * n) * A ^ 2 * Sz := by
    by_cases hκ₂ : 2 ≤ κ
    · calc
        _ ≤ C₂ * (n * κ) ^ ε * qsNorm F κ (2 * n) *
              (Cφ * (2 * n) ^ ε) ^ 2 * ∑ c ∈ cols, ‖z c‖ ^ 2 :=
          hlargeBlock e t (hqdiv t ht).1 hκ₂
        _ ≤ C₃ * (n * κ) ^ ε * qsNorm F κ (2 * n) * A ^ 2 * Sz := by
          calc
            _ = C₂ * ((n * κ) ^ ε * qsNorm F κ (2 * n) * A ^ 2 * Sz) := by
              simp [A, Sz]
              ring
            _ ≤ C₃ * ((n * κ) ^ ε * qsNorm F κ (2 * n) * A ^ 2 * Sz) := by
              apply mul_le_mul_of_nonneg_right hC₃₂
              exact mul_nonneg (mul_nonneg (mul_nonneg
                (Real.rpow_nonneg (by positivity) ε) hqsNormNonneg) (sq_nonneg A))
                (by positivity)
            _ = _ := by ring
    · have hκsmall : κ < 2 := lt_of_not_ge hκ₂
      have hfactor : 1 ≤ C₃ * (n * κ) ^ ε := by
        calc
          1 = 1 * 1 := by ring
          _ ≤ C₃ * (n * κ) ^ ε :=
            mul_le_mul hC₃₁ hrpow1 (by norm_num) (by positivity)
      calc
        _ ≤ qsNorm F κ (2 * n) *
              (Cφ * (2 * n) ^ ε) ^ 2 * ∑ c ∈ cols, ‖z c‖ ^ 2 :=
          hsmallBlock e t (hqdiv t ht).1 hκsmall
        _ = 1 * (qsNorm F κ (2 * n) * A ^ 2 * Sz) := by
          simp [A, Sz]
        _ ≤ C₃ * (n * κ) ^ ε * (qsNorm F κ (2 * n) * A ^ 2 * Sz) :=
          mul_le_mul_of_nonneg_right hfactor
            (mul_nonneg (mul_nonneg hqsNormNonneg (sq_nonneg A)) (by positivity))
        _ = C₃ * (n * κ) ^ ε * qsNorm F κ (2 * n) * A ^ 2 * Sz := by ring
  have houterWeightBound (e : Ideal (𝓞 K)) (he : e ∈ qdiv) :
      ‖outerWeight e‖ ≤ 1 := by
    have he0 := (hqdiv e he).1
    have hNnat : 1 ≤ Ideal.absNorm e := Nat.one_le_iff_ne_zero.mpr (by
      intro hz
      exact he0 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hN1 : 1 ≤ qsN e := by exact_mod_cast hNnat
    have hroot1 : 1 ≤ Real.sqrt (qsN e) := Real.one_le_sqrt.mpr hN1
    have hrootpos : 0 < Real.sqrt (qsN e) := Real.sqrt_pos.2 (by positivity)
    have hdennorm : ‖(Real.sqrt (qsN e) : ℂ)‖ = Real.sqrt (qsN e) := by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    dsimp [outerWeight]
    rw [norm_div, hdennorm]
    apply (div_le_iff₀ hrootpos).2
    have hnum : ‖(qsMu e : ℂ)‖ ≤ 1 := QSC2.norm_qsMu_le e
    nlinarith [hnum, hroot1]
  have hrootInvNorm : ‖rootInv‖ = 1 / Real.sqrt κ := by
    dsimp [rootInv]
    rw [norm_div, norm_one, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hsqrtMNorm : ‖(Real.sqrt M : ℂ)‖ = Real.sqrt M := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hR0Norm : ‖R0‖ = ‖(qsResidueOne K : ℂ)‖ * ‖Iw‖ * Real.sqrt M := by
    dsimp [R0]
    rw [norm_neg, norm_mul, norm_mul, hsqrtMNorm]
  let U : ℝ := C₃ * (n * κ) ^ ε * qsNorm F κ (2 * n) * A ^ 2 * Sz
  have hU : 0 ≤ U := by dsimp [U]; positivity [hqsNormNonneg]
  have htermBound (e t : Ideal (𝓞 K)) (he : e ∈ qdiv) (ht : t ∈ qdiv) :
      ‖outerWeight e * rootInv * qsPairSum cols (ztw e t) (rowCore t)‖ ≤
        (1 / Real.sqrt κ) * U := by
    rw [norm_mul, norm_mul, hrootInvNorm]
    calc
      ‖outerWeight e‖ * (1 / Real.sqrt κ) *
          ‖qsPairSum cols (ztw e t) (rowCore t)‖ ≤
        1 * (1 / Real.sqrt κ) * U := by
          calc
            _ ≤ 1 * (1 / Real.sqrt κ) *
                  ‖qsPairSum cols (ztw e t) (rowCore t)‖ := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right (houterWeightBound e he) (by positivity))
                  (norm_nonneg _)
            _ ≤ 1 * (1 / Real.sqrt κ) * U := by
                exact mul_le_mul_of_nonneg_left (hblock e t he ht) (by positivity)
      _ = (1 / Real.sqrt κ) * U := by ring
  have hdoubleNorm :
      ∑ e ∈ qdiv, ∑ t ∈ qdiv,
        ‖outerWeight e * rootInv * qsPairSum cols (ztw e t) (rowCore t)‖ ≤
          (qdiv.card : ℝ) ^ 2 * ((1 / Real.sqrt κ) * U) := by
    calc
      _ ≤ ∑ e ∈ qdiv, ∑ t ∈ qdiv, (1 / Real.sqrt κ) * U := by
        apply Finset.sum_le_sum
        intro e he
        apply Finset.sum_le_sum
        intro t ht
        exact htermBound e t he ht
      _ = (qdiv.card : ℝ) ^ 2 * ((1 / Real.sqrt κ) * U) := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
  have hqcard : ((qdiv.card : ℝ) ^ 2) ≤ (Cq * qsN 𝔮) ^ 2 := by
    have hcount : (qdiv.card : ℝ) ≤ Cq * qsN 𝔮 := by simpa [qdiv] using hcount𝔮
    exact pow_le_pow_left₀ (by positivity) hcount 2
  have hdoubleNorm' :
      ∑ e ∈ qdiv, ∑ t ∈ qdiv,
        ‖outerWeight e * rootInv * qsPairSum cols (ztw e t) (rowCore t)‖ ≤
          (Cq * qsN 𝔮) ^ 2 * ((1 / Real.sqrt κ) * U) := by
    exact hdoubleNorm.trans (mul_le_mul_of_nonneg_right hqcard (by positivity))
  have hboundaryNorm :
      ‖qsPairSum cols z (qsBoundaryKernel F W M κ 𝔮)‖ ≤
        ‖R0‖ * ((Cq * qsN 𝔮) ^ 2 * ((1 / Real.sqrt κ) * U)) := by
    rw [hBoundaryPair]
    calc
      _ = ‖R0‖ * ‖∑ e ∈ qdiv, ∑ t ∈ qdiv,
            outerWeight e * rootInv * qsPairSum cols (ztw e t) (rowCore t)‖ := norm_mul _ _
      _ ≤ ‖R0‖ * ∑ e ∈ qdiv, ∑ t ∈ qdiv,
            ‖outerWeight e * rootInv * qsPairSum cols (ztw e t) (rowCore t)‖ := by
          apply mul_le_mul_of_nonneg_left
          · calc
              _ ≤ ∑ e ∈ qdiv, ‖∑ t ∈ qdiv,
                    outerWeight e * rootInv * qsPairSum cols (ztw e t) (rowCore t)‖ :=
                    norm_sum_le _ _
              _ ≤ ∑ e ∈ qdiv, ∑ t ∈ qdiv,
                    ‖outerWeight e * rootInv * qsPairSum cols (ztw e t) (rowCore t)‖ := by
                    apply Finset.sum_le_sum
                    intro e he
                    exact norm_sum_le _ _
          · exact norm_nonneg _
      _ ≤ ‖R0‖ * ((Cq * qsN 𝔮) ^ 2 * ((1 / Real.sqrt κ) * U)) :=
          mul_le_mul_of_nonneg_left hdoubleNorm' (norm_nonneg _)
  have hAsq : A ^ 2 = Cφ ^ 2 * (2 * n) ^ (2 * ε) := by
    dsimp [A]
    rw [mul_pow]
    rw [show ((2 * n) ^ ε) ^ 2 = (2 * n) ^ (2 * ε) by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1
      push_cast
      ring]
  have h2nLe : 2 * n ≤ 2 * (n * κ) := by nlinarith [hn, hκ]
  have hpow2n : (2 * n) ^ (2 * ε) ≤ (2 * (n * κ)) ^ (2 * ε) :=
    Real.rpow_le_rpow (by positivity) h2nLe (by positivity)
  have hmulRpow : (2 * (n * κ)) ^ (2 * ε) =
      2 ^ (2 * ε) * (n * κ) ^ (2 * ε) :=
    Real.mul_rpow (by norm_num) (by positivity)
  have hexp : ε + 2 * ε = η := by dsimp [ε]; ring
  have hpowCombine : (n * κ) ^ ε * (2 * n) ^ (2 * ε) ≤
      2 ^ (2 * ε) * (n * κ) ^ η := by
    calc
      _ ≤ (n * κ) ^ ε * (2 * (n * κ)) ^ (2 * ε) :=
        mul_le_mul_of_nonneg_left hpow2n (Real.rpow_nonneg (by positivity) _)
      _ = (n * κ) ^ ε * (2 ^ (2 * ε) * (n * κ) ^ (2 * ε)) := by rw [hmulRpow]
      _ = 2 ^ (2 * ε) * ((n * κ) ^ ε * (n * κ) ^ (2 * ε)) := by ring
      _ = 2 ^ (2 * ε) * (n * κ) ^ (ε + 2 * ε) := by
        rw [← Real.rpow_add (by positivity : 0 < n * κ)]
      _ = 2 ^ (2 * ε) * (n * κ) ^ η := by rw [hexp]
  have hsqrtRatio : Real.sqrt M / Real.sqrt κ = Real.sqrt (M / κ) :=
    (Real.sqrt_div (le_of_lt hM) κ).symm
  have hpre :
      ‖R0‖ * ((Cq * qsN 𝔮) ^ 2 * ((1 / Real.sqrt κ) * U)) =
        Kbase * qsN 𝔮 ^ 2 * (Real.sqrt M / Real.sqrt κ) *
          qsNorm F κ (2 * n) * Sz * ((n * κ) ^ ε * (2 * n) ^ (2 * ε)) := by
    rw [hR0Norm]
    rw [show U = C₃ * (n * κ) ^ ε * qsNorm F κ (2 * n) * A ^ 2 * Sz by rfl]
    rw [hAsq]
    dsimp [Kbase]
    ring
  have hpreBound :
      ‖qsPairSum cols z (qsBoundaryKernel F W M κ 𝔮)‖ ≤
        Kbase * qsN 𝔮 ^ 2 * (Real.sqrt M / Real.sqrt κ) *
          qsNorm F κ (2 * n) * Sz * ((n * κ) ^ ε * (2 * n) ^ (2 * ε)) := by
    calc
      _ ≤ ‖R0‖ * ((Cq * qsN 𝔮) ^ 2 * ((1 / Real.sqrt κ) * U)) := hboundaryNorm
      _ = _ := hpre
  have hbaseNonneg :
      0 ≤ Kbase * qsN 𝔮 ^ 2 * (Real.sqrt M / Real.sqrt κ) *
        qsNorm F κ (2 * n) * Sz := by
    dsimp [Kbase]
    positivity [hqsNormNonneg]
  have hafter :
      ‖qsPairSum cols z (qsBoundaryKernel F W M κ 𝔮)‖ ≤
        Kbase * qsN 𝔮 ^ 2 * Real.sqrt (M / κ) * qsNorm F κ (2 * n) * Sz *
          (2 ^ (2 * ε) * (n * κ) ^ η) := by
    calc
      _ ≤ Kbase * qsN 𝔮 ^ 2 * (Real.sqrt M / Real.sqrt κ) *
            qsNorm F κ (2 * n) * Sz * ((n * κ) ^ ε * (2 * n) ^ (2 * ε)) := hpreBound
      _ ≤ Kbase * qsN 𝔮 ^ 2 * (Real.sqrt M / Real.sqrt κ) *
            qsNorm F κ (2 * n) * Sz * (2 ^ (2 * ε) * (n * κ) ^ η) :=
          mul_le_mul_of_nonneg_left hpowCombine hbaseNonneg
      _ = Kbase * qsN 𝔮 ^ 2 * Real.sqrt (M / κ) * qsNorm F κ (2 * n) * Sz *
            (2 ^ (2 * ε) * (n * κ) ^ η) := by rw [hsqrtRatio]
  have hconstant : Kbase * 2 ^ (2 * ε) ≤ Ctarget := by
    dsimp [Ctarget]
    calc
      Kbase * 2 ^ (2 * ε) ≤ Kbase * 2 ^ (2 * ε) + 1 :=
        le_add_of_nonneg_right (by norm_num : 0 ≤ (1 : ℝ))
      _ = 1 + Kbase * 2 ^ (2 * ε) := by ring
  calc
    _ ≤ Kbase * 2 ^ (2 * ε) * qsN 𝔮 ^ 2 * (n * κ) ^ η *
          Real.sqrt (M / κ) * qsNorm F κ (2 * n) * Sz := by
      rw [show Kbase * qsN 𝔮 ^ 2 * Real.sqrt (M / κ) * qsNorm F κ (2 * n) * Sz *
          (2 ^ (2 * ε) * (n * κ) ^ η) =
            Kbase * 2 ^ (2 * ε) * qsN 𝔮 ^ 2 * (n * κ) ^ η *
              Real.sqrt (M / κ) * qsNorm F κ (2 * n) * Sz by ring] at hafter
      exact hafter
    _ ≤ Ctarget * qsN 𝔮 ^ 2 * (n * κ) ^ η * Real.sqrt (M / κ) *
          qsNorm F κ (2 * n) * Sz := by
      have hrest : 0 ≤ qsN 𝔮 ^ 2 * (n * κ) ^ η * Real.sqrt (M / κ) *
          qsNorm F κ (2 * n) * Sz := by positivity [hqsNormNonneg]
      calc
        _ = (Kbase * 2 ^ (2 * ε)) *
              (qsN 𝔮 ^ 2 * (n * κ) ^ η * Real.sqrt (M / κ) *
                qsNorm F κ (2 * n) * Sz) := by ring
        _ ≤ Ctarget * (qsN 𝔮 ^ 2 * (n * κ) ^ η * Real.sqrt (M / κ) *
              qsNorm F κ (2 * n) * Sz) :=
          mul_le_mul_of_nonneg_right hconstant hrest
        _ = _ := by ring

end ArtinPrimitiveRoots.A2
