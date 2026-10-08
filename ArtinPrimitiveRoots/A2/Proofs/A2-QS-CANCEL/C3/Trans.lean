import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».C3.Decomp

/-!
# The dual transition kernel `E₃` as a sum of two-vector pair blocks

For a coprime equal-class pair `(c, d)` of block columns the kernel
`qsDualKernel (qsInnerTrans K) …` regroups as a finite sum over `e ∣ 𝔮`, the bad part
`a₂ ∣ R` of the row, the row dyad `k`, and the divisor dyads `j₁, j₂` of
`(twists of c) · (twists of d) · Σ_{e₁ ∣ c} Σ_{e₂ ∣ d} μ(e₁ e₂) Σ_{a₁} ρ(a₁) χ_c(a₁) χ_d(a₁) Φ(…)`,
with `Φ` the transition weight cut to the block (`phiT`).
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2.QSC3

open QSC2 QSP2

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

/-- The square weight of the dual kernel. -/
abbrev F0 (K : Type) [Field K] [NumberField K] (W : ℝ → ℝ) : ℝ → ℂ :=
  fun y => qsTransform K (fun x => (W x : ℂ)) (y ^ 2)

/-- Transition weight `M/(E √x) · (Z/u) · Σ_b (T F₀)(Z N b/u)`, `Z = √(E x/(M A))`. -/
def wtT (K : Type) [Field K] [NumberField K] (W : ℝ → ℝ) (M E A u x : ℝ) : ℂ :=
  ((M / (E * Real.sqrt x) : ℝ) : ℂ) * ((Real.sqrt (E * x / (M * A)) / u : ℝ) : ℂ) *
    ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
      qsTransform K (F0 K W) (Real.sqrt (E * x / (M * A)) * nb b / u)

/-- Lower dual cutoff. -/
def ylo (M n Λ E A : ℝ) : ℝ := Real.sqrt (E * n ^ 2 / (M * A)) / (2 * Λ)

/-- Upper dual cutoff. -/
def zhi (M n Λ E A : ℝ) : ℝ := 2 * Λ * Real.sqrt (E * n ^ 2 / (M * A))

open Classical in
/-- The block weight for one `(e, a₂, k, D)`. -/
def phiT (K : Type) [Field K] [NumberField K] (W : ℝ → ℝ) (M n Λ E A₂ : ℝ) (k : ℕ) (D : ℝ)
    (y u x : ℝ) : ℂ :=
  if 0 < y ∧ 0 < u ∧ ylo M n Λ E (A₂ * y) < u ∧ u ≤ zhi M n Λ E (A₂ * y) ∧
      (2 : ℝ) ^ k ≤ y ∧ D ≤ u then
    wtT K W M E (A₂ * y) u x else 0

open Classical in
/-- The row weight of one block `(a₂, k)`. -/
def rhoT (S : Finset (Ideal (𝓞 K))) (R a₂ : Ideal (𝓞 K)) (k : ℕ) (a₁ : Ideal (𝓞 K)) : ℂ :=
  if (a₂ * a₁ ∈ S ∧ a₂ * a₁ ⊔ R = a₂) ∧ Nat.log 2 (Ideal.absNorm a₁) = k then 1 else 0

theorem one_le_qsN {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : 1 ≤ qsN I := by
  have : Ideal.absNorm I ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.mp h)
  simp only [qsN]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr this

theorem qsN_le_of_dvd {e c : Ideal (𝓞 K)} (hc : c ≠ ⊥) (h : e ∣ c) : qsN e ≤ qsN c := by
  simp only [qsN]
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero
    (fun h0 => hc (Ideal.absNorm_eq_zero_iff.mp h0)))
    (Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd h))

/-- The general term `μ(e) ψ(e) ψ(a) μ(e') · wtT`. -/
def Tterm (F : QSFamily m qS) (W : ℝ → ℝ) (M : ℝ) (c d e a e' : Ideal (𝓞 K)) : ℂ :=
  (qsMu e : ℂ) * (qsPairChar F c d).idealValue e * (qsPairChar F c d).idealValue a *
    (qsMu e' : ℂ) * wtT K W M (qsN e) (qsN a) (qsN e') (qsN (c * d))

/-- The dual cutoff condition. -/
def Qcond (M n Λ : ℝ) (e a e' : Ideal (𝓞 K)) : Prop :=
  ylo M n Λ (qsN e) (qsN a) < qsN e' ∧ qsN e' ≤ zhi M n Λ (qsN e) (qsN a)

open Classical in
/-- Step A: the kernel as a triple sum over `e ∣ 𝔮`, rows and dual divisors. -/
theorem dualTrans_unfold (F : QSFamily m qS) (W : ℝ → ℝ) (M κ Λ n : ℝ) (𝔮 c d : Ideal (𝓞 K)) :
    qsDualKernel (qsInnerTrans K) F W M κ Λ n 𝔮 c d =
      ∑ e ∈ qsDivisors 𝔮, ∑ a ∈ qsSqfUpTo κ ⊤,
        ∑ e' ∈ (qsDivisors (c * d)).filter (fun e' => Qcond M n Λ e a e'),
          Tterm F W M c d e a e' := by
  unfold qsDualKernel qsInnerTrans
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr (by ext x; rw [Finset.mem_filter, Finset.mem_filter]; rfl) fun e' _ => ?_
  unfold Tterm wtT
  ring

/-- `ψ` at an outer divisor `e ∣ 𝔮` and at a split row `a₂ a₁`. -/
theorem pairChar_block (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥)
    {𝔮 c d : Ideal (𝓞 K)} (h𝔮bad : qsBadRad m qS ∣ 𝔮) (hc : QSAdm m qS c) (hd : QSAdm m qS d)
    (hc𝔮 : IsCoprime c 𝔮) (hd𝔮 : IsCoprime d 𝔮) (hcd : IsCoprime c d)
    (hcl : ∃ (hc' : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m c)
      (hd' : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m d),
      ArtinPrimitiveRoots.Hecke.rayClass m c hc' = ArtinPrimitiveRoots.Hecke.rayClass m d hd') :
    (∀ e, e ∣ 𝔮 → (qsPairChar F c d).idealValue e = twist F c e * twistInv F d e) ∧
    (∀ a₂ a₁, a₂ ∣ badIdeal m qS → QSAdm m qS a₁ →
      (qsPairChar F c d).idealValue (a₂ * a₁) =
        twist F c a₂ * twistInv F d a₂ *
          ((F.character c).idealValue a₁ * (F.character d).idealValue a₁)) := by
  constructor
  · intro e he
    refine pairChar_eq_twist F hc hd hcd hcl e ?_
    exact IsCoprime.mul_right (isCoprime_of_le hc𝔮.symm (Ideal.le_of_dvd he))
      (isCoprime_of_le hd𝔮.symm (Ideal.le_of_dvd he))
  · intro a₂ a₁ ha₂ ha₁
    have ha₂0 : a₂ ≠ ⊥ := by
      intro h0; rw [h0] at ha₂
      exact badIdeal_ne_bot hqS (le_bot_iff.mp (Ideal.le_of_dvd ha₂))
    rw [qs_idealValue_mul_M0 _ _ _ ha₂0 (ne_bot_of_QSAdm ha₁),
      pairChar_eq_twist F hc hd hcd hcl a₂ (IsCoprime.mul_right
        (coprime_of_dvd_bad hqS h𝔮bad hc𝔮 ha₂) (coprime_of_dvd_bad hqS h𝔮bad hd𝔮 ha₂)),
      pairChar_eq_mul F hrf hc hd hcd ha₁]

open Classical in
/-- The block decomposition of the dual transition kernel of one pair. -/
theorem dualTrans_decomp (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1)
    (hqS : qS ≠ ⊥) (W : ℝ → ℝ) (M κ Λ n : ℝ) (𝔮 : Ideal (𝓞 K)) (cols : Finset (Ideal (𝓞 K)))
    (hblock : QSBlockCols m qS 𝔮 n cols) (KB J : ℕ) (hKB : κ < 2 ^ KB) (hJ : 2 * n < 2 ^ J)
    {c d : Ideal (𝓞 K)} (hc : c ∈ cols) (hd : d ∈ cols) (hcd : IsCoprime c d) :
    qsDualKernel (qsInnerTrans K) F W M κ Λ n 𝔮 c d =
      ∑ e ∈ qsDivisors 𝔮, ∑ a₂ ∈ qsDivisors (badIdeal m qS), ∑ k ∈ Finset.range KB,
        ∑ j₁ ∈ Finset.range J, ∑ j₂ ∈ Finset.range J,
          ((qsMu e : ℂ) * twist F c e * twist F c a₂) * (twistInv F d e * twistInv F d a₂) *
            ∑ e₁ ∈ (qsDivisors c).filter (fun e => Nat.log 2 (Ideal.absNorm e) = j₁),
              ∑ e₂ ∈ (qsDivisors d).filter (fun e => Nat.log 2 (Ideal.absNorm e) = j₂),
                (qsMu (e₁ * e₂) : ℂ) *
                  ∑ a₁ ∈ qsUpTo m qS (2 ^ (k + 1)),
                    rhoT (qsSqfUpTo κ ⊤) (badIdeal m qS) a₂ k a₁ *
                      (F.character c).idealValue a₁ * (F.character d).idealValue a₁ *
                        phiT K W M n Λ (qsN e) (qsN a₂) k (2 ^ j₁ * 2 ^ j₂) (qsN a₁)
                          (qsN (e₁ * e₂)) (qsN (c * d)) := by
  obtain ⟨h𝔮sq, h𝔮bad, hcols, hcl⟩ := hblock
  obtain ⟨hcA, hc𝔮, hcn, hc2n⟩ := hcols c hc
  obtain ⟨hdA, hd𝔮, hdn, hd2n⟩ := hcols d hd
  have hc0 := ne_bot_of_QSAdm hcA
  have hd0 := ne_bot_of_QSAdm hdA
  obtain ⟨hψe, hψa⟩ := pairChar_block F hrf hqS h𝔮bad hcA hdA hc𝔮 hd𝔮 hcd (hcl c hc d hd)
  set S := qsSqfUpTo (K := K) κ ⊤ with hSdef
  set R := badIdeal m qS with hRdef
  have hS : ∀ a ∈ S, a ≠ ⊥ ∧ Squarefree a ∧ qsN a ≤ κ := by
    intro a ha
    rw [hSdef, qsSqfUpTo, Finset.mem_filter] at ha
    exact ⟨ha.2.1, ha.2.2.1, ha.2.2.2.2⟩
  have hJc : ∀ e ∈ qsDivisors c, Nat.log 2 (Ideal.absNorm e) < J := fun e he =>
    log_lt_of_le (le_trans (qsN_le_of_dvd hc0 ((mem_qsDivisors hc0).mp he)) hc2n) hJ
      (fun h => hc0 (by
        have := (mem_qsDivisors hc0).mp he
        rw [Ideal.absNorm_eq_zero_iff] at h; rw [h] at this
        exact le_bot_iff.mp (Ideal.le_of_dvd this)))
  have hJd : ∀ e ∈ qsDivisors d, Nat.log 2 (Ideal.absNorm e) < J := fun e he =>
    log_lt_of_le (le_trans (qsN_le_of_dvd hd0 ((mem_qsDivisors hd0).mp he)) hd2n) hJ
      (fun h => hd0 (by
        have := (mem_qsDivisors hd0).mp he
        rw [Ideal.absNorm_eq_zero_iff] at h; rw [h] at this
        exact le_bot_iff.mp (Ideal.le_of_dvd this)))
  have h𝔮0 : 𝔮 ≠ ⊥ := by
    rintro rfl
    exact bot_ne_top (Ideal.isUnit_iff.mp (h𝔮sq ⊥ (Ideal.dvd_iff_le.mpr bot_le)))
  rw [dualTrans_unfold]
  refine Finset.sum_congr rfl fun e he => ?_
  have he𝔮 : e ∣ 𝔮 := (mem_qsDivisors h𝔮0).mp he
  have hC : ∀ a₂ ∈ qsDivisors R, ∀ a₁, (a₂ * a₁ ∈ S ∧ a₂ * a₁ ⊔ R = a₂) → qsN a₁ ≤ κ := by
    intro a₂ ha₂ a₁ h
    obtain ⟨h0, _, hN⟩ := hS _ h.1
    have ha₂0 : a₂ ≠ ⊥ := fun h' => h0 (by rw [h', Ideal.bot_mul])
    have ha₁0 : a₁ ≠ ⊥ := fun h' => h0 (by rw [h', Ideal.mul_bot])
    rw [qsN_mul] at hN
    nlinarith [one_le_qsN ha₂0, qsN_pos ha₁0]
  calc ∑ a ∈ S, ∑ e' ∈ (qsDivisors (c * d)).filter (fun e' => Qcond M n Λ e a e'),
        Tterm F W M c d e a e'
      = ∑ a ∈ S, ∑ e₁ ∈ qsDivisors c, ∑ e₂ ∈ qsDivisors d,
          if Qcond M n Λ e a (e₁ * e₂) then Tterm F W M c d e a (e₁ * e₂) else 0 :=
        Finset.sum_congr rfl fun a _ => sum_divisors_mul hc0 hd0 hcd _ _
    _ = ∑ a₂ ∈ qsDivisors R, ∑ a₁ ∈ qsUpTo m qS κ,
          if a₂ * a₁ ∈ S ∧ a₂ * a₁ ⊔ R = a₂ then
            ∑ e₁ ∈ qsDivisors c, ∑ e₂ ∈ qsDivisors d,
              (if Qcond M n Λ e (a₂ * a₁) (e₁ * e₂) then
                Tterm F W M c d e (a₂ * a₁) (e₁ * e₂) else 0) else 0 :=
        sum_rows_split hqS S κ hS _
    _ = ∑ a₂ ∈ qsDivisors R, ∑ k ∈ Finset.range KB, ∑ a₁ ∈ qsUpTo m qS (2 ^ (k + 1)),
          if (a₂ * a₁ ∈ S ∧ a₂ * a₁ ⊔ R = a₂) ∧ Nat.log 2 (Ideal.absNorm a₁) = k then
            ∑ e₁ ∈ qsDivisors c, ∑ e₂ ∈ qsDivisors d,
              (if Qcond M n Λ e (a₂ * a₁) (e₁ * e₂) then
                Tterm F W M c d e (a₂ * a₁) (e₁ * e₂) else 0) else 0 :=
        Finset.sum_congr rfl fun a₂ ha₂ => sum_rows_dyadic κ KB hKB _ (hC a₂ ha₂) _
    _ = _ := by
        refine Finset.sum_congr rfl fun a₂ ha₂ => Finset.sum_congr rfl fun k _ => ?_
        have ha₂R : a₂ ∣ R := (mem_qsDivisors (badIdeal_ne_bot hqS)).mp ha₂
        set P : Ideal (𝓞 K) → Prop := fun a₁ =>
          (a₂ * a₁ ∈ S ∧ a₂ * a₁ ⊔ R = a₂) ∧ Nat.log 2 (Ideal.absNorm a₁) = k with hPdef
        set X : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ := fun a₁ e₁ e₂ =>
          if P a₁ then (if Qcond M n Λ e (a₂ * a₁) (e₁ * e₂) then
            Tterm F W M c d e (a₂ * a₁) (e₁ * e₂) else 0) else 0 with hXdef
        calc ∑ a₁ ∈ qsUpTo m qS (2 ^ (k + 1)),
              (if P a₁ then ∑ e₁ ∈ qsDivisors c, ∑ e₂ ∈ qsDivisors d,
                (if Qcond M n Λ e (a₂ * a₁) (e₁ * e₂) then
                  Tterm F W M c d e (a₂ * a₁) (e₁ * e₂) else 0) else 0)
            = ∑ a₁ ∈ qsUpTo m qS (2 ^ (k + 1)), ∑ e₁ ∈ qsDivisors c, ∑ e₂ ∈ qsDivisors d,
                X a₁ e₁ e₂ := by
              refine Finset.sum_congr rfl fun a₁ _ => ?_
              rw [hXdef]
              by_cases hp : P a₁
              · simp only [if_pos hp]
              · simp only [if_neg hp, Finset.sum_const_zero]
          _ = ∑ e₁ ∈ qsDivisors c, ∑ e₂ ∈ qsDivisors d, ∑ a₁ ∈ qsUpTo m qS (2 ^ (k + 1)),
                X a₁ e₁ e₂ := by
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun e₁ _ => Finset.sum_comm
          _ = ∑ j₁ ∈ Finset.range J,
                ∑ e₁ ∈ (qsDivisors c).filter (fun e => Nat.log 2 (Ideal.absNorm e) = j₁),
                ∑ j₂ ∈ Finset.range J,
                ∑ e₂ ∈ (qsDivisors d).filter (fun e => Nat.log 2 (Ideal.absNorm e) = j₂),
                ∑ a₁ ∈ qsUpTo m qS (2 ^ (k + 1)), X a₁ e₁ e₂ := by
              rw [sum_dyadic _ J hJc]
              refine Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun e₁ _ => ?_
              rw [sum_dyadic _ J hJd]
          _ = ∑ j₁ ∈ Finset.range J, ∑ j₂ ∈ Finset.range J,
                ∑ e₁ ∈ (qsDivisors c).filter (fun e => Nat.log 2 (Ideal.absNorm e) = j₁),
                ∑ e₂ ∈ (qsDivisors d).filter (fun e => Nat.log 2 (Ideal.absNorm e) = j₂),
                ∑ a₁ ∈ qsUpTo m qS (2 ^ (k + 1)), X a₁ e₁ e₂ :=
              Finset.sum_congr rfl fun j₁ _ => Finset.sum_comm
          _ = _ := by
              refine Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₂ _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun e₁ he₁ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun e₂ he₂ => ?_
              rw [Finset.mul_sum, Finset.mul_sum]
              refine Finset.sum_congr rfl fun a₁ ha₁ => ?_
              rw [Finset.mem_filter, mem_qsDivisors hc0] at he₁
              rw [Finset.mem_filter, mem_qsDivisors hd0] at he₂
              have ha₁A := (mem_qsUpTo.mp ha₁).1
              have he₁0 : e₁ ≠ ⊥ := fun h => hc0 (by
                have := he₁.1; rw [h] at this; exact le_bot_iff.mp (Ideal.le_of_dvd this))
              have he₂0 : e₂ ≠ ⊥ := fun h => hd0 (by
                have := he₂.1; rw [h] at this; exact le_bot_iff.mp (Ideal.le_of_dvd this))
              have hd₁ := dyad_bounds he₁0 he₁.2
              have hd₂ := dyad_bounds he₂0 he₂.2
              have hu : qsN (e₁ * e₂) = qsN e₁ * qsN e₂ := qsN_mul _ _
              have hA : qsN (a₂ * a₁) = qsN a₂ * qsN a₁ := qsN_mul _ _
              rw [hXdef]
              by_cases hp : P a₁
              · have hk' : Nat.log 2 (Ideal.absNorm a₁) = k := hp.2
                have hdk := dyad_bounds (ne_bot_of_QSAdm ha₁A) hk'
                simp only [if_pos hp, rhoT]
                rw [if_pos hp]
                by_cases hq : Qcond M n Λ e (a₂ * a₁) (e₁ * e₂)
                · rw [if_pos hq]
                  have hcond : 0 < qsN a₁ ∧ 0 < qsN (e₁ * e₂) ∧
                      ylo M n Λ (qsN e) (qsN a₂ * qsN a₁) < qsN (e₁ * e₂) ∧
                      qsN (e₁ * e₂) ≤ zhi M n Λ (qsN e) (qsN a₂ * qsN a₁) ∧
                      (2 : ℝ) ^ k ≤ qsN a₁ ∧ (2 : ℝ) ^ j₁ * 2 ^ j₂ ≤ qsN (e₁ * e₂) := by
                    refine ⟨qsN_pos (ne_bot_of_QSAdm ha₁A), ?_, ?_, ?_, hdk.1, ?_⟩
                    · rw [hu]; exact mul_pos (qsN_pos he₁0) (qsN_pos he₂0)
                    · rw [← hA]; exact hq.1
                    · rw [← hA]; exact hq.2
                    · rw [hu]; exact mul_le_mul hd₁.1 hd₂.1 (by positivity) (by positivity)
                  rw [phiT, if_pos hcond, Tterm, hψe e he𝔮, hψa a₂ a₁ ha₂R ha₁A, hA]
                  ring
                · rw [if_neg hq]
                  have hcond : ¬ (0 < qsN a₁ ∧ 0 < qsN (e₁ * e₂) ∧
                      ylo M n Λ (qsN e) (qsN a₂ * qsN a₁) < qsN (e₁ * e₂) ∧
                      qsN (e₁ * e₂) ≤ zhi M n Λ (qsN e) (qsN a₂ * qsN a₁) ∧
                      (2 : ℝ) ^ k ≤ qsN a₁ ∧ (2 : ℝ) ^ j₁ * 2 ^ j₂ ≤ qsN (e₁ * e₂)) := by
                    rintro ⟨_, _, h1, h2, _, _⟩
                    exact hq ⟨by rw [hA]; exact h1, by rw [hA]; exact h2⟩
                  rw [phiT, if_neg hcond]
                  ring
              · simp only [if_neg hp, rhoT]
                rw [if_neg hp]
                ring

end ArtinPrimitiveRoots.A2.QSC3
