import ArtinPrimitiveRoots.Theta.Cover
import TauCeti.RingTheory.DedekindDomain.Factorization
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical nonZeroDivisors
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Every divisor supported outside `S_f` is the exterior divisor of a rational unit. -/
theorem th_classical_exterior_divisor_principal (D : FieldData F)
    (S : SData F CE condη) (H : HilbertData F)
    (e : FinPlace F →₀ ℤ) (he : ∀ v ∈ S.Sf, e v = 0) :
    ∃ a : Fˣ, ∀ v : FinPlace F, v ∉ S.Sf →
      v.valuation F (a : F) = WithZero.exp (-(e v)) := by
  classical
  have hprod (f : FinPlace F → ℕ) (hf : ∀ v ∉ e.support, f v = 0) :
      S.IsExterior (∏ v ∈ e.support, v.asIdeal ^ f v) ∧
        ∀ v : FinPlace F, FractionalIdeal.count F v
          ((∏ w ∈ e.support, w.asIdeal ^ f w : Ideal (𝓞 F)) :
            FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = (f v : ℤ) := by
    let I : Ideal (𝓞 F) := ∏ v ∈ e.support, v.asIdeal ^ f v
    have hI : I ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v hv => pow_ne_zero _ v.ne_bot
    refine ⟨⟨hI, ?_⟩, ?_⟩
    · intro v hv hIv
      obtain ⟨w, hw, hwv⟩ := v.isPrime.prod_le.mp hIv
      have hwv' : w.asIdeal ≤ v.asIdeal := Ideal.IsPrime.le_of_pow_le hwv
      have hwv'' : w = v :=
        HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top hwv')
      subst w
      exact (e.mem_support_iff.mp hw) (he v hv)
    · intro v
      have hcast : (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
          ∏ w ∈ e.support,
            (w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^ f w := by
        change (FractionalIdeal.coeIdealHom (nonZeroDivisors (𝓞 F)) F)
          (∏ w ∈ e.support, w.asIdeal ^ f w) = _
        simp only [map_prod, map_pow]
        rfl
      change FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = _
      rw [hcast, FractionalIdeal.count_prod F v _ _
        (fun w hw => pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot))]
      simp only [FractionalIdeal.count_pow, FractionalIdeal.count_maximal,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
      by_cases hv : v ∈ e.support
      · simp only [ite_eq_left hv]
      · simp only [ite_eq_right hv, hf v hv, Nat.cast_zero]
  let Ip : Ideal (𝓞 F) := ∏ v ∈ e.support, v.asIdeal ^ (e v).toNat
  let In : Ideal (𝓞 F) := ∏ v ∈ e.support, v.asIdeal ^ (-e v).toNat
  have hp := hprod (fun v => (e v).toNat) (by
    intro v hv
    simp only [Finsupp.notMem_support_iff.mp hv, Int.toNat_zero])
  have hn := hprod (fun v => (-e v).toNat) (by
    intro v hv
    simp only [Finsupp.notMem_support_iff.mp hv, neg_zero, Int.toNat_zero])
  obtain ⟨Bd⟩ := BData.nonempty D S H
  obtain ⟨ap, hap, _⟩ := Bd.exists_allowed Ip hp.1
  obtain ⟨an, han, _⟩ := Bd.exists_allowed In hn.1
  let a : Fˣ := ap / an
  refine ⟨a, ?_⟩
  intro v hv
  have hcount : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) = e v := by
    simp only [a, Units.val_div_eq_div_val]
    rw [FractionalIdeal.count_spanSingleton_div F v ap.ne_zero an.ne_zero,
      hap.2.2 v hv, han.2.2 v hv, hp.2 v, hn.2 v]
    omega
  have hlog : -WithZero.log (v.valuation F (a : F)) = e v := by
    rw [← FractionalIdeal.count_toPrincipalIdeal_eq_neg_log_valuation F v a,
      coe_toPrincipalIdeal]
    exact hcount
  have hlog' : WithZero.log (v.valuation F (a : F)) = -(e v) := by omega
  rw [← hlog', WithZero.exp_log (by simpa only [ne_eq, Valuation.zero_iff] using a.ne_zero)]

/-- Scalar squares and the chosen small torus level leave finitely many local determinant classes. -/
theorem th_classical_local_determinant_reps (D : FieldData F)
    (H : HilbertData F) (v : FinPlace F) (L : FinLocalCover D H v)
    (m : ℕ) (hm : L.m0 ≤ m) :
    ∃ R : Finset (v.adicCompletion F)ˣ,
      ∀ u : (v.adicCompletion F)ˣ, ∃ a ∈ R,
        ∃ c b : (v.adicCompletion F)ˣ,
          u = a * c ^ 2 * b ∧ L.a b ∈ L.Kc m := by
  classical
  let K := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  let _ : Finite (IsLocalRing.ResidueField O) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  have hproper : ProperSpace K :=
    (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F)),
        inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)))⟩
  have hcompact : IsCompact (O : Set K) := by
    have hset : (O : Set K) = Metric.closedBall (0 : K) 1 := by
      change (↑((Valued.v : Valuation K (WithZero (Multiplicative ℤ))).integer) : Set K) =
        Metric.closedBall (0 : K) 1
      exact Valued.toNormedField.setOfPred_mem_integer_eq_closedBall (L := K)
    rw [hset]
    exact hproper.isCompact_closedBall 0 1
  let _ : CompactSpace O := isCompact_iff_compactSpace.mp hcompact
  let ι : Oˣ →* Kˣ := Units.map (algebraMap O K).toMonoidHom
  have hιval (a : Oˣ) : Valued.v (ι a : K) = 1 := by
    change Valued.v (((a : O) : K)) = 1
    exact HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp a.isUnit
  let W (a : Oˣ) : Set Oˣ :=
    {b | Valued.v (((b : O) : K) - ((a : O) : K)) ≤ WithZero.exp (-(m : ℤ))}
  have hW (a : Oˣ) : IsOpen (W a) := by
    apply (v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero).preimage
    exact (continuous_subtype_val.comp Units.continuous_val).sub continuous_const
  obtain ⟨s, hs⟩ := (isCompact_univ : IsCompact (Set.univ : Set Oˣ)).elim_finite_subcover W hW
    (by
      intro a ha
      exact Set.mem_iUnion.mpr ⟨a, by simp [W]⟩)
  obtain ⟨p, hp⟩ := v.valuedAdicCompletion_surjective (K := F) (WithZero.exp (1 : ℤ))
  have hp0 : p ≠ 0 := by
    intro hp0
    exact WithZero.exp_ne_zero (by simpa only [hp0, map_zero] using hp.symm)
  let π : Kˣ := Units.mk0 p hp0
  have hπval : Valued.v (π : K) = WithZero.exp (1 : ℤ) := hp
  let R : Finset Kˣ := (s ×ˢ ({0, 1} : Finset ℤ)).image (fun ar => ι ar.1 * π ^ ar.2)
  refine ⟨R, ?_⟩
  intro u
  let n : ℤ := WithZero.log (Valued.v (u : K))
  let t : Kˣ := u / π ^ n
  have hu0 : Valued.v (u : K) ≠ 0 := by simpa only [ne_eq, Valuation.zero_iff] using u.ne_zero
  have htval : Valued.v (t : K) = 1 := by
    simp only [t, Units.val_div_eq_div_val, Units.val_zpow_eq_zpow_val, map_div₀,
      map_zpow₀, hπval, ← WithZero.exp_zsmul, smul_eq_mul, mul_one]
    change Valued.v (u : K) / WithZero.exp (WithZero.log (Valued.v (u : K))) = 1
    rw [WithZero.exp_log hu0, div_self hu0]
  let tO : O := ⟨(t : K), by
    change Valued.v (t : K) ≤ 1
    exact htval.le⟩
  have hto : IsUnit tO :=
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr htval
  let tu : Oˣ := hto.unit
  have htu : (ι tu : K) = (t : K) := by
    change (((hto.unit : O) : K)) = (t : K)
    rw [hto.unit_spec]
  obtain ⟨a, ha, hclose⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ tu))
  change Valued.v ((ι tu : K) - (ι a : K)) ≤ WithZero.exp (-(m : ℤ)) at hclose
  rw [htu] at hclose
  let b : Kˣ := t / ι a
  have hb : ((b : K) - 1) ∈ ball v m := by
    change Valued.v ((b : K) - 1) ≤ WithZero.exp (-(m : ℤ))
    have heq : ((b : K) - 1) = ((t : K) - (ι a : K)) / (ι a : K) := by
      simp only [b, Units.val_div_eq_div_val]
      exact div_sub_one (ι a).ne_zero
    rw [heq, map_div₀, hιval, div_one]
    exact hclose
  have hr : n % 2 ∈ ({0, 1} : Finset ℤ) := by
    have h0 := Int.emod_nonneg n (by norm_num : (2 : ℤ) ≠ 0)
    have h2 := Int.emod_lt_of_pos n (by norm_num : (0 : ℤ) < 2)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  refine ⟨ι a * π ^ (n % 2), Finset.mem_image.mpr ⟨(a, n % 2),
    Finset.mem_product.mpr ⟨ha, hr⟩, rfl⟩, π ^ (n / 2), b, ?_, L.a_Kc m hm b hb⟩
  have hn : n % 2 + (n / 2) * 2 = n := Int.emod_add_ediv_mul n 2
  calc
    u = π ^ n * t := by simp [t, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    _ = π ^ (n % 2) * (π ^ (n / 2)) ^ 2 * t := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_add]
      change π ^ n * t = π ^ (n % 2 + (n / 2) * 2) * t
      rw [hn]
    _ = (ι a * π ^ (n % 2)) * (π ^ (n / 2)) ^ 2 * b := by
      simp [b, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

end ArtinPrimitiveRoots.A1.Theta
