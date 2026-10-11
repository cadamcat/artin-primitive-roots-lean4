import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MATRIX».Defs

/-!
# A2-QS-MATRIX, part M0: finite matrix, energy, monotonicity, duality, adapters

Generic operator facts: `OAI.FiniteSieveOperator.energy_bound`,
`operator_conjTranspose_norm`, `diagonal_twist_norm_le` (`O/NumberTheory/DirichletL/
QuadraticSieve/FiniteOperator.lean:77-186`).
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

/-- M0 (IMPL): ideal values of a Hecke character are completely multiplicative on nonzero
ideals (`idealValue` is a product over `normalizedFactors`). -/
theorem qs_idealValue_mul_M0 (χ : ArtinPrimitiveRoots.A1.HeckeChar K) (I J : Ideal (𝓞 K))
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    χ.idealValue (I * J) = χ.idealValue I * χ.idealValue J := by
  classical
  simp only [ArtinPrimitiveRoots.A1.HeckeChar.idealValue,
    UniqueFactorizationMonoid.normalizedFactors_mul hI hJ,
    Multiset.map_add, Multiset.prod_add]

private theorem qs_idealExp_mul (v : HeightOneSpectrum (𝓞 K))
    (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    ArtinPrimitiveRoots.A1.idealExp v (I * J) =
      ArtinPrimitiveRoots.A1.idealExp v I + ArtinPrimitiveRoots.A1.idealExp v J := by
  unfold ArtinPrimitiveRoots.A1.idealExp
  rw [← Associates.mk_mul_mk,
    Associates.count_mul (Associates.mk_ne_zero.mpr (by simpa [Ideal.zero_eq_bot] using hI))
      (Associates.mk_ne_zero.mpr (by simpa [Ideal.zero_eq_bot] using hJ)) v.associates_irreducible]

/-- M0 (IMPL): a character is ramified at every prime of its primitive conductor, so its ideal
value vanishes on ideals sharing a prime with the conductor.  (If `χ` were unramified at
`P ∣ f`, `ConductorDvd` would hold for `f` with the `P`-part removed, of smaller norm.) -/
theorem qs_idealValue_eq_zero_of_conductor_M0 (χ : ArtinPrimitiveRoots.A1.HeckeChar K)
    (f : Ideal (𝓞 K)) (hf : IsPrimitiveConductor χ f) (P I : Ideal (𝓞 K)) (hP : P.IsPrime)
    (hP0 : P ≠ ⊥) (hPf : P ∣ f) (hI : I ≠ ⊥) (hPI : P ∣ I) :
    χ.idealValue I = 0 := by
  classical
  let v : HeightOneSpectrum (𝓞 K) := ⟨P, hP, hP0⟩
  have hmemI : P ∈ UniqueFactorizationMonoid.normalizedFactors I := by
    apply (Ideal.mem_normalizedFactors_iff hI).2
    exact ⟨hP, Ideal.dvd_iff_le.mp hPI⟩
  by_cases hUnr : χ.UnramifiedAt v
  · let g : Ideal (𝓞 K) := (UniqueFactorizationMonoid.normalizedFactors f).erase P |>.prod
    have hfactors : P ∈ UniqueFactorizationMonoid.normalizedFactors f := by
      apply (Ideal.mem_normalizedFactors_iff hf.1).2
      exact ⟨hP, Ideal.dvd_iff_le.mp hPf⟩
    have hdecomp : f = P * g := by
      calc
        f = (UniqueFactorizationMonoid.normalizedFactors f).prod :=
          (Ideal.prod_normalizedFactors_eq_self hf.1).symm
        _ = (P ::ₘ (UniqueFactorizationMonoid.normalizedFactors f).erase P).prod := by
          exact congrArg Multiset.prod (Multiset.cons_erase hfactors).symm
        _ = P * ((UniqueFactorizationMonoid.normalizedFactors f).erase P).prod :=
          Multiset.prod_cons P _
        _ = P * g := rfl
    have hg : g ≠ ⊥ := by
      intro hg0
      apply hf.1
      rw [hdecomp, hg0]
      simp
    have hcond : χ.ConductorDvd g := by
      intro w u hu huinv hval
      by_cases hw : w = v
      · subst w
        exact hUnr u hu huinv
      · have hPexp : ArtinPrimitiveRoots.A1.idealExp w P = 0 := by
          have hc : FractionalIdeal.count K w
              (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0 :=
            FractionalIdeal.count_maximal_coprime K w (Ne.symm hw)
          have hc' :
              ((Associates.mk w.asIdeal).count (Associates.mk P).factors : ℤ) = 0 := by
            rw [FractionalIdeal.count_coe K w hP0] at hc
            exact hc
          simpa [ArtinPrimitiveRoots.A1.idealExp, v] using (Int.natCast_eq_zero.mp hc')
        have hexp : ArtinPrimitiveRoots.A1.idealExp w f =
            ArtinPrimitiveRoots.A1.idealExp w g := by
          calc
            ArtinPrimitiveRoots.A1.idealExp w f =
                ArtinPrimitiveRoots.A1.idealExp w (P * g) := by rw [hdecomp]
            _ = ArtinPrimitiveRoots.A1.idealExp w P + ArtinPrimitiveRoots.A1.idealExp w g :=
              qs_idealExp_mul w P g hP0 hg
            _ = ArtinPrimitiveRoots.A1.idealExp w g := by rw [hPexp]; simp
        apply hf.2.1 w u hu huinv
        simpa [hexp] using hval
    have hlt : Ideal.absNorm g < Ideal.absNorm f := by
      have hnorm : Ideal.absNorm f = Ideal.absNorm P * Ideal.absNorm g := by
        rw [hdecomp, map_mul]
      have hPnorm : 1 < Ideal.absNorm P := by
        simpa [v] using NumberField.HeightOneSpectrum.one_lt_absNorm v
      have hgnorm : 0 < Ideal.absNorm g :=
        Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr (by
          simpa [Ideal.zero_eq_bot] using hg)
      rw [hnorm]
      simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right hPnorm hgnorm
    exact False.elim ((not_le_of_gt hlt) (hf.2.2 g hg hcond))
  · obtain ⟨s, hs⟩ := Multiset.exists_cons_of_mem hmemI
    have hzero : χ.idealValue I = 0 := by
      unfold ArtinPrimitiveRoots.A1.HeckeChar.idealValue
      rw [hs, Multiset.map_cons, Multiset.prod_cons]
      have hpv : χ.primeValue v = 0 := by
        simp [ArtinPrimitiveRoots.A1.HeckeChar.primeValue, hUnr]
      rw [dite_eq_left ⟨hP, hP0⟩, hpv]
      simp
    exact hzero

/-- M0 (IMPL): `IsCoprimeTo m I` is nonvanishing plus coprimality to the modulus radical. -/
theorem qs_isCoprimeTo_iff_M0 (I : Ideal (𝓞 K)) :
    ArtinPrimitiveRoots.Hecke.IsCoprimeTo m I ↔ I ≠ ⊥ ∧ IsCoprime I (qsModulusRad m) := by
  classical
  have hcount (v : HeightOneSpectrum (𝓞 K)) (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) :
      FractionalIdeal.count K v (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0 ↔
        J ⊔ v.asIdeal = ⊤ := by
    have hJ0 : J ≠ (0 : Ideal (𝓞 K)) := by simpa [Ideal.zero_eq_bot] using hJ
    rw [FractionalIdeal.count_coe K v hJ]
    change ((Associates.mk v.asIdeal).count (Associates.mk J).factors : ℤ) = 0 ↔ _
    rw [Int.natCast_eq_zero]
    have hc : (Associates.mk v.asIdeal).count (Associates.mk J).factors ≠ 0 ↔
        v.asIdeal ∣ J :=
      Associates.count_ne_zero_iff_dvd hJ0 v.prime.irreducible
    have hzero :
        (Associates.mk v.asIdeal).count (Associates.mk J).factors = 0 ↔
          ¬(Associates.mk v.asIdeal).count (Associates.mk J).factors ≠ 0 := by simp
    rw [hzero, not_congr hc]
    constructor
    · intro hnot
      by_contra htop
      have htop' : v.asIdeal ⊔ J ≠ ⊤ := by
        intro h
        exact htop (by simpa [sup_comm] using h)
      have heq : v.asIdeal = v.asIdeal ⊔ J := v.isMaximal.eq_of_le htop' le_sup_left
      apply hnot
      exact Ideal.dvd_iff_le.mpr (by rw [heq]; exact le_sup_right)
    · intro hsup hdvd
      have hle : J ≤ v.asIdeal := Ideal.dvd_iff_le.mp hdvd
      have htop : (⊤ : Ideal (𝓞 K)) ≤ v.asIdeal := by
        calc
          ⊤ = J ⊔ v.asIdeal := hsup.symm
          _ ≤ v.asIdeal := sup_le hle le_rfl
      exact v.isPrime.ne_top (le_antisymm le_top htop)
  constructor
  · rintro ⟨hI, hmem⟩
    refine ⟨hI, Ideal.isCoprime_iff_sup_eq.mpr ?_⟩
    change ∀ v, v ∈ m.finitePart.support →
      FractionalIdeal.count K v
        ((ArtinPrimitiveRoots.Hecke.idealUnit I hI :
          NumberFieldFractionalIdealGroup K) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0 at hmem
    apply Ideal.sup_prod_eq_top
    intro v hv
    apply (hcount v I hI).mp
    simpa [ArtinPrimitiveRoots.Hecke.idealUnit] using hmem v hv
  · rintro ⟨hI, hcop⟩
    refine ⟨hI, ?_⟩
    change ∀ v, v ∈ m.finitePart.support →
      FractionalIdeal.count K v
        ((ArtinPrimitiveRoots.Hecke.idealUnit I hI :
          NumberFieldFractionalIdealGroup K) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0
    intro v hv
    have hsup : I ⊔ v.asIdeal = ⊤ := by
      have hprod : I ⊔ (∏ w ∈ m.finitePart.support, w.asIdeal) = ⊤ :=
        Ideal.isCoprime_iff_sup_eq.mp hcop
      have hle : (∏ w ∈ m.finitePart.support, w.asIdeal) ≤ v.asIdeal := by
        exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hv)
      apply le_antisymm le_top
      calc
        ⊤ = I ⊔ (∏ w ∈ m.finitePart.support, w.asIdeal) := hprod.symm
        _ ≤ I ⊔ v.asIdeal := sup_le_sup_left hle I
    change FractionalIdeal.count K v (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0
    exact (hcount v I hI).2 hsup

/-- M0 (IMPL): the energy of a coefficient vector on the up-to matrix is at most `B1 ‖z‖²`
(from `OAI.FiniteSieveOperator.energy_bound`). -/
theorem qs_energy_le_norm_M0 (F : QSFamily m qS) (M N : ℝ) (z : Ideal (𝓞 K) → ℂ) :
    ∑ d ∈ qsUpTo m qS M, ‖∑ c ∈ qsUpTo m qS N, z c * (F.character c).idealValue d‖ ^ 2 ≤
      qsNorm F M N * ∑ c ∈ qsUpTo m qS N, ‖z c‖ ^ 2 := by
  classical
  let A := qsMatrix F M N
  let rows := qsUpTo m qS M
  let cols := qsUpTo m qS N
  have h := OAI.FiniteSieveOperator.energy_bound A (fun c => z c.1)
  have hleft :
      (∑ d ∈ rows, ‖∑ c ∈ cols, z c * (F.character c).idealValue d‖ ^ 2) =
        ∑ d : rows, ‖∑ c : cols, z c.1 * (F.character c.1).idealValue d.1‖ ^ 2 := by
    have sum_subtype {α β : Type} [AddCommMonoid β] (s : Finset α) (f : α → β) :
        (∑ x ∈ s, f x) = ∑ x : s, f x.1 := by
      simpa using (Finset.sum_attach s f).symm
    rw [sum_subtype]
    apply Finset.sum_congr rfl
    intro d hd
    rw [sum_subtype]
  have hmat :
      (∑ d : rows, ‖∑ c : cols, z c.1 * (F.character c.1).idealValue d.1‖ ^ 2) =
        ∑ d : rows, ‖∑ c : cols, A d c * z c.1‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro d hd
    congr 2
    apply Finset.sum_congr rfl
    intro c hc
    simp [A, qsMatrix]
    ring
  have hright :
      (∑ c ∈ cols, ‖z c‖ ^ 2) = ∑ c : cols, ‖z c.1‖ ^ 2 := by
    have sum_subtype {α β : Type} [AddCommMonoid β] (s : Finset α) (f : α → β) :
        (∑ x ∈ s, f x) = ∑ x : s, f x.1 := by
      simpa using (Finset.sum_attach s f).symm
    exact sum_subtype cols (fun c => ‖z c‖ ^ 2)
  rw [hleft]
  calc
    _ = ∑ d : rows, ‖∑ c : cols, A d c * z c.1‖ ^ 2 := hmat
    _ ≤ ‖OAI.FiniteSieveOperator.operator A‖ ^ 2 * ∑ c : cols, ‖z c.1‖ ^ 2 := h
    _ = qsNorm F M N * (∑ c ∈ cols, ‖z c‖ ^ 2) := by
      rw [qsNorm, ← hright]

/-- M0 (IMPL): `B1` is the least coefficient-energy bound. -/
theorem qs_norm_le_of_energy_M0 (F : QSFamily m qS) (M N B : ℝ) (hB : 0 ≤ B)
    (h : ∀ z : Ideal (𝓞 K) → ℂ,
      ∑ d ∈ qsUpTo m qS M, ‖∑ c ∈ qsUpTo m qS N, z c * (F.character c).idealValue d‖ ^ 2 ≤
        B * ∑ c ∈ qsUpTo m qS N, ‖z c‖ ^ 2) :
    qsNorm F M N ≤ B := by
  classical
  let rows := qsUpTo m qS M
  let cols := qsUpTo m qS N
  let A := qsMatrix F M N
  have sum_subtype {α β : Type} [AddCommMonoid β] (s : Finset α) (f : α → β) :
      (∑ x ∈ s, f x) = ∑ x : s, f x.1 := by
    simpa using (Finset.sum_attach s f).symm
  have hbound : ∀ x : EuclideanSpace ℂ cols,
      ‖OAI.FiniteSieveOperator.operator A x‖ ≤ Real.sqrt B * ‖x‖ := by
    intro x
    let z' : Ideal (𝓞 K) → ℂ := fun c =>
      if hc : c ∈ cols then x ⟨c, hc⟩ else 0
    have hinner (d : rows) :
        (∑ c ∈ cols, z' c * (F.character c).idealValue d.1) =
          ∑ c : cols, A d c * x c := by
      rw [sum_subtype]
      apply Finset.sum_congr rfl
      intro c hc
      simp [A, qsMatrix, z']
      ring
    have hout :
        (∑ d ∈ rows, ‖∑ c ∈ cols, z' c * (F.character c).idealValue d‖ ^ 2) =
          ‖OAI.FiniteSieveOperator.operator A x‖ ^ 2 := by
      rw [sum_subtype, EuclideanSpace.norm_sq_eq]
      apply Finset.sum_congr rfl
      intro d hd
      rw [OAI.FiniteSieveOperator.operator_apply]
      exact congrArg (fun w : ℂ => ‖w‖ ^ 2) (hinner d)
    have hin :
        (∑ c ∈ cols, ‖z' c‖ ^ 2) = ‖x‖ ^ 2 := by
      rw [sum_subtype, EuclideanSpace.norm_sq_eq]
      apply Finset.sum_congr rfl
      intro c hc
      simp [z']
    have hE := h z'
    rw [hout, hin] at hE
    have hsq : ‖OAI.FiniteSieveOperator.operator A x‖ ^ 2 ≤
        (Real.sqrt B * ‖x‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hB]
      exact hE
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp hsq
  have hop : ‖OAI.FiniteSieveOperator.operator A‖ ≤ Real.sqrt B := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg B)
    exact hbound
  change ‖OAI.FiniteSieveOperator.operator (qsMatrix F M N)‖ ^ 2 ≤ B
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hop 2
  simpa [A, Real.sq_sqrt hB] using hsq

/-- M0 (IMPL): the up-to norm is monotone in both lengths (zero extension of coefficients,
nonnegative row sums). -/
private theorem qsUpTo_mono {K : Type} [Field K] [NumberField K]
    {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)} {X Y : ℝ}
    (hXY : X ≤ Y) : qsUpTo m qS X ⊆ qsUpTo m qS Y := by
  classical
  intro I hI
  unfold qsUpTo at hI ⊢
  rcases Finset.mem_filter.mp hI with ⟨hbase, hpred⟩
  have hnorm : Ideal.absNorm I ≤ ⌊X⌋₊ := by simpa using hbase
  have hfloor : ⌊X⌋₊ ≤ ⌊Y⌋₊ := Nat.floor_mono hXY
  have hbase' : I ∈ (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊Y⌋₊).toFinset := by
    simpa using hnorm.trans hfloor
  apply Finset.mem_filter.mpr
  exact ⟨hbase', ⟨hpred.1, hpred.2.trans hXY⟩⟩

private theorem qsUpTo_mem_of_adm_norm {K : Type} [Field K] [NumberField K]
    {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)} {X : ℝ}
    {I : Ideal (𝓞 K)} (hAdm : QSAdm m qS I)
    (hI : (Ideal.absNorm I : ℝ) ≤ X) : I ∈ qsUpTo m qS X := by
  classical
  unfold qsUpTo
  apply Finset.mem_filter.mpr
  refine ⟨?_, ⟨hAdm, hI⟩⟩
  have hf := Nat.floor_mono hI
  have hn : Ideal.absNorm I ≤ ⌊X⌋₊ := by simpa using hf
  simpa using hn

theorem qs_norm_mono_M0 (F : QSFamily m qS) {M M' N N' : ℝ} (hM : M ≤ M') (hN : N ≤ N') :
    qsNorm F M N ≤ qsNorm F M' N' := by
  classical
  let rows := qsUpTo m qS M
  let cols := qsUpTo m qS N
  let rows' := qsUpTo m qS M'
  let cols' := qsUpTo m qS N'
  have hRows : rows ⊆ rows' := qsUpTo_mono hM
  have hCols : cols ⊆ cols' := qsUpTo_mono hN
  apply qs_norm_le_of_energy_M0 F M N (qsNorm F M' N') (sq_nonneg _)
  intro z
  let z' : Ideal (𝓞 K) → ℂ := fun c => if c ∈ cols then z c else 0
  have hinner (d : Ideal (𝓞 K)) :
      (∑ c ∈ cols, z c * (F.character c).idealValue d) =
        ∑ c ∈ cols', z' c * (F.character c).idealValue d := by
    calc
      _ = ∑ c ∈ cols, z' c * (F.character c).idealValue d := by
        apply Finset.sum_congr rfl
        intro c hc
        simp [z', hc]
      _ = _ := by
        apply Finset.sum_subset hCols
        intro c hc hnot
        simp [z', hnot]
  have hcoef :
      (∑ c ∈ cols', ‖z' c‖ ^ 2) = ∑ c ∈ cols, ‖z c‖ ^ 2 := by
    calc
      _ = ∑ c ∈ cols', if c ∈ cols then ‖z c‖ ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro c hc
        by_cases hmem : c ∈ cols <;> simp [z', hmem]
      _ = _ := by
        symm
        calc
          _ = ∑ c ∈ cols, (if c ∈ cols then ‖z c‖ ^ 2 else 0) := by
            apply Finset.sum_congr rfl
            intro c hc
            simp [hc]
          _ = ∑ c ∈ cols', (if c ∈ cols then ‖z c‖ ^ 2 else 0) := by
            apply Finset.sum_subset hCols
            intro c hc hnot
            simp [hnot]
  have hsmall :
      (∑ d ∈ rows, ‖∑ c ∈ cols, z c * (F.character c).idealValue d‖ ^ 2) ≤
        qsNorm F M' N' * ∑ c ∈ cols, ‖z c‖ ^ 2 := by
    calc
      _ = ∑ d ∈ rows, ‖∑ c ∈ cols', z' c * (F.character c).idealValue d‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [hinner]
      _ ≤ ∑ d ∈ rows', ‖∑ c ∈ cols', z' c * (F.character c).idealValue d‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hRows (by
          intro d hd hnot
          exact sq_nonneg _)
      _ ≤ qsNorm F M' N' * ∑ c ∈ cols', ‖z' c‖ ^ 2 :=
        qs_energy_le_norm_M0 F M' N' z'
      _ = _ := by rw [hcoef]
  exact hsmall

/-- M0 (IMPL): reciprocity duality for trivial ray factor: the up-to matrix is symmetric
(`χ_c(d) = χ_d(c)` for coprime admissible `c, d`; both vanish when `c, d` share a prime, by
`qs_idealValue_eq_zero_of_conductor_M0`), so `B1(M,N) = B1(N,M)`. -/
theorem qs_norm_symm_M0 (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1) (M N : ℝ) :
    qsNorm F M N = qsNorm F N M := by
  classical
  have hstar (c : Ideal (𝓞 K)) (hc : QSAdm m qS c) (I : Ideal (𝓞 K)) :
      star ((F.character c).idealValue I) = (F.character c).idealValue I := by
    rcases F.quadraticValues c hc.1 hc.2.1 I with hz | hsq
    · simp [hz]
    · rcases sq_eq_one_iff.mp hsq with h | h <;> simp [h]
  have hentry (c d : Ideal (𝓞 K)) (hc : QSAdm m qS c) (hd : QSAdm m qS d) :
      (F.character c).idealValue d = star ((F.character d).idealValue c) := by
    by_cases hcop : IsCoprime c d
    · have hrec := F.reciprocity c d hc.1 hc.2.1 hd.1 hd.2.1 hcop
      calc
        (F.character c).idealValue d =
            ((F.rayFactor
              (ArtinPrimitiveRoots.Hecke.rayClass m c hc.2.1)
              (ArtinPrimitiveRoots.Hecke.rayClass m d hd.2.1) : ℂˣ) : ℂ) *
              (F.character d).idealValue c := hrec
        _ = (F.character d).idealValue c := by simp [hrf]
        _ = star ((F.character d).idealValue c) := (hstar d hd c).symm
    · have hsup : c ⊔ d ≠ ⊤ := by
        intro htop
        exact hcop (Ideal.isCoprime_iff_sup_eq.mpr htop)
      obtain ⟨Q, hQmax, hQle⟩ := Ideal.exists_le_maximal (c ⊔ d) hsup
      have hQ0 : Q ≠ ⊥ :=
        Ring.ne_bot_of_isMaximal_of_not_isField hQmax (NumberField.RingOfIntegers.not_isField K)
      let v : HeightOneSpectrum (𝓞 K) := ⟨Q, hQmax.isPrime, hQ0⟩
      have hcQ : c ≤ Q := le_trans le_sup_left hQle
      have hdQ : d ≤ Q := le_trans le_sup_right hQle
      have hQdivc : Q ∣ c := Ideal.dvd_iff_le.mpr hcQ
      have hQdivd : Q ∣ d := Ideal.dvd_iff_le.mpr hdQ
      rcases F.indexCondition c hc.1 hc.2.1 with ⟨_, hprimc, s, hconfc, _⟩
      rcases F.indexCondition d hd.1 hd.2.1 with ⟨_, hprimd, s', hconfd, _⟩
      have hQconfc : Q ∣ F.conductor c := Ideal.dvd_iff_le.mpr (by
        rw [hconfc]
        exact le_trans (Ideal.mul_le_inf.trans inf_le_left) hcQ)
      have hQconfd : Q ∣ F.conductor d := Ideal.dvd_iff_le.mpr (by
        rw [hconfd]
        exact le_trans (Ideal.mul_le_inf.trans inf_le_left) hdQ)
      have hcne : c ≠ ⊥ := (qs_isCoprimeTo_iff_M0 c).mp hc.2.1 |>.1
      have hdne : d ≠ ⊥ := (qs_isCoprimeTo_iff_M0 d).mp hd.2.1 |>.1
      have hzcd := qs_idealValue_eq_zero_of_conductor_M0 (F.character c)
        (F.conductor c) hprimc Q d hQmax.isPrime hQ0 hQconfc hdne hQdivd
      have hzdc := qs_idealValue_eq_zero_of_conductor_M0 (F.character d)
        (F.conductor d) hprimd Q c hQmax.isPrime hQ0 hQconfd hcne hQdivc
      simp [hzcd, hzdc]
  have htranspose : qsMatrix F N M = (qsMatrix F M N).conjTranspose := by
    have qAdm {X : ℝ} (c : qsUpTo m qS X) : QSAdm m qS c.1 := by
      have hc : c.1 ∈ qsUpTo m qS X := c.2
      unfold qsUpTo at hc
      exact (Finset.mem_filter.mp hc).2.1
    ext c d
    change (F.character d.1).idealValue c.1 =
      star ((F.character c.1).idealValue d.1)
    exact hentry d.1 c.1 (qAdm d) (qAdm c)
  rw [qsNorm, qsNorm, htranspose, OAI.FiniteSieveOperator.operator_conjTranspose_norm]

/-- M0 (IMPL; adapter G3 for the core): the sharp up-to bound gives the finite-subset energy
bound for arbitrary admissible row and column sets (extend `z` by zero, dominate row subsets). -/
theorem qs_finite_energy_of_core_M0 (F : QSFamily m qS) (hcore : QSCoreBound F) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ Cmax Dmax : ℝ, 1 ≤ Cmax → 1 ≤ Dmax →
        ∀ (rows cols : Finset (Ideal (𝓞 K))),
          (∀ I ∈ rows, QSAdm m qS I ∧ (Ideal.absNorm I : ℝ) ≤ Dmax) →
          (∀ I ∈ cols, QSAdm m qS I ∧ (Ideal.absNorm I : ℝ) ≤ Cmax) →
          ∀ z : Ideal (𝓞 K) → ℂ,
          ∑ d ∈ rows, ‖∑ c ∈ cols, z c * (F.character c).idealValue d‖ ^ 2 ≤
              C * (Cmax + Dmax) * Real.rpow (Cmax * Dmax) ε * ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  classical
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := hcore ε hε
  refine ⟨C, hC, ?_⟩
  intro Cmax Dmax hCmax hDmax rows cols hrows hcols z
  let rows' := qsUpTo m qS Dmax
  let cols' := qsUpTo m qS Cmax
  have hRows : rows ⊆ rows' := by
    intro I hI
    have h := hrows I hI
    exact qsUpTo_mem_of_adm_norm h.1 h.2
  have hCols : cols ⊆ cols' := by
    intro I hI
    have h := hcols I hI
    exact qsUpTo_mem_of_adm_norm h.1 h.2
  let z' : Ideal (𝓞 K) → ℂ := fun c => if c ∈ cols then z c else 0
  have hinner (d : Ideal (𝓞 K)) :
      (∑ c ∈ cols, z c * (F.character c).idealValue d) =
        ∑ c ∈ cols', z' c * (F.character c).idealValue d := by
    calc
      _ = ∑ c ∈ cols, z' c * (F.character c).idealValue d := by
        apply Finset.sum_congr rfl
        intro c hc
        simp [z', hc]
      _ = _ := by
        apply Finset.sum_subset hCols
        intro c hc hnot
        simp [z', hnot]
  have hcoef :
      (∑ c ∈ cols', ‖z' c‖ ^ 2) = ∑ c ∈ cols, ‖z c‖ ^ 2 := by
    calc
      _ = ∑ c ∈ cols', if c ∈ cols then ‖z c‖ ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro c hc
        by_cases hmem : c ∈ cols <;> simp [z', hmem]
      _ = _ := by
        symm
        calc
          _ = ∑ c ∈ cols, (if c ∈ cols then ‖z c‖ ^ 2 else 0) := by
            apply Finset.sum_congr rfl
            intro c hc
            simp [hc]
          _ = ∑ c ∈ cols', (if c ∈ cols then ‖z c‖ ^ 2 else 0) := by
            apply Finset.sum_subset hCols
            intro c hc hnot
            simp [hnot]
  have henergy := qs_energy_le_norm_M0 F Dmax Cmax z'
  have hsum : 0 ≤ ∑ c ∈ cols', ‖z' c‖ ^ 2 := Finset.sum_nonneg fun c hc => sq_nonneg _
  have hnorm := hbound Dmax Cmax hDmax hCmax
  calc
    (∑ d ∈ rows, ‖∑ c ∈ cols, z c * (F.character c).idealValue d‖ ^ 2) =
        ∑ d ∈ rows, ‖∑ c ∈ cols', z' c * (F.character c).idealValue d‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [hinner]
    _ ≤ ∑ d ∈ rows', ‖∑ c ∈ cols', z' c * (F.character c).idealValue d‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hRows (by
        intro d hd hnot
        exact sq_nonneg _)
    _ ≤ qsNorm F Dmax Cmax * ∑ c ∈ cols', ‖z' c‖ ^ 2 := henergy
    _ ≤ (C * (Dmax + Cmax) * Real.rpow (Dmax * Cmax) ε) *
          ∑ c ∈ cols', ‖z' c‖ ^ 2 := mul_le_mul_of_nonneg_right hnorm hsum
    _ = C * (Cmax + Dmax) * Real.rpow (Cmax * Dmax) ε *
          ∑ c ∈ cols, ‖z c‖ ^ 2 := by
      rw [hcoef]
      ring

end ArtinPrimitiveRoots.A2
