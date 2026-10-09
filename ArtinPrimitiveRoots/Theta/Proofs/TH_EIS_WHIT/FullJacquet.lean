import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.GaussBound

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory Filter
open scoped Classical Topology

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-- In the absolute-convergence range the stabilized Jacquet functional is the full integral. -/
theorem whit_local_jacquet_integral {D : FieldData F} {H : HilbertData F}
    {v : FinPlace F} (L : FinLocalCover D H v) (T : TorusRep D H v)
    (A : AddCharData F) (μ : LocHaar v) {s : ℂ} (hs : 0 < s.re)
    (f : L.L → T.V) (hf : IsSection L T s f) :
    Integrable (fun u => A.ψ v (-u) • f (L.w * L.n (Multiplicative.ofAdd u))) μ.μ ∧
      jacquet L A μ f =
        ∫ u, A.ψ v (-u) • f (L.w * L.n (Multiplicative.ofAdd u)) ∂μ.μ := by
  classical
  let K := v.adicCompletion F
  let kernel : K → T.V := fun u => A.ψ v (-u) • f (L.w * L.n (Multiplicative.ofAdd u))
  have hbase : Integrable (fun u : K => f (L.w * L.n (Multiplicative.ofAdd u))) μ.μ := by
    simpa only [mul_one] using (intertwine_isSection L T μ s hs f hf).1 (1 : L.L)
  have hopen : IsOpen (v.adicCompletionIntegers F : Set K) :=
    Valued.isOpen_valuationSubring K
  have hpsi : IsLocallyConstant (A.ψ v) := by
    apply (IsLocallyConstant.iff_exists_open _).2
    intro t
    refine ⟨{y : K | y - t ∈ v.adicCompletionIntegers F},
      hopen.preimage (continuous_id.sub continuous_const), ?_, ?_⟩
    · change t - t ∈ v.adicCompletionIntegers F
      rw [sub_self]
      exact (v.adicCompletionIntegers F).zero_mem
    · intro y hy
      have hi := A.integral v (y - t) hy
      simpa only [sub_add_cancel, hi, one_mul] using
        (A.ψ v).map_add_eq_mul (y - t) t
  have hphase : Continuous (fun u : K => A.ψ v (-u)) :=
    hpsi.continuous.comp continuous_neg
  have hnorm (u : K) : ‖kernel u‖ = ‖f (L.w * L.n (Multiplicative.ofAdd u))‖ := by
    simp only [kernel, norm_smul, whit_psi_norm, one_mul]
  have hint : Integrable kernel μ.μ :=
    hbase.mono (hphase.aestronglyMeasurable.smul hbase.aestronglyMeasurable)
      (ae_of_all _ fun u => (hnorm u).le)
  have hpoint (u : K) : ∃ N : ℕ, u ∈ ball v (-(N : ℤ)) := by
    by_cases hu : u = 0
    · refine ⟨0, ?_⟩
      change Valued.v u ≤ WithZero.exp (-(-(0 : ℤ)))
      rw [hu, map_zero]
      exact bot_le
    · have hval : Valued.v u ≠ 0 := by simpa [hu]
      lift Valued.v u to ℤ using hval with n hn
      refine ⟨n.natAbs, ?_⟩
      simp only [ball, Int.neg_neg]
      change Valued.v u ≤ WithZero.exp (n.natAbs : ℤ)
      rw [← hn]
      apply WithZero.exp_le_exp.mpr
      cases n with
      | ofNat k => simp
      | negSucc k => simp [Int.natAbs]; omega
  have hcover : (⋃ N : ℕ, ball v (-(N : ℤ))) = (Set.univ : Set K) := by
    ext u
    constructor
    · intro _
      simp
    · intro _
      obtain ⟨N, hN⟩ := hpoint u
      exact Set.mem_iUnion.mpr ⟨N, hN⟩
  have hmono : Monotone (fun N : ℕ => ball v (-(N : ℤ))) := by
    intro N M hNM u hu
    simp only [ball, Int.neg_neg] at hu ⊢
    exact hu.trans (WithZero.exp_le_exp.mpr (by exact_mod_cast hNM))
  have hmeas (N : ℕ) : MeasurableSet (ball v (-(N : ℤ))) :=
    (v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero).measurableSet
  have ht : Tendsto (fun N : ℕ => ∫ u in ball v (-(N : ℤ)), kernel u ∂μ.μ)
      atTop (𝓝 (∫ u, kernel u ∂μ.μ)) := by
    have h := tendsto_setIntegral_of_monotone hmeas hmono hint.integrableOn
    simpa only [hcover, setIntegral_univ] using h
  have hlim : Tendsto (fun N : ℕ => jacquetTrunc L A μ N f)
      atTop (𝓝 (∫ u, kernel u ∂μ.μ)) := by
    simpa only [jacquetTrunc, kernel] using ht
  refine ⟨hint, ?_⟩
  change limUnder atTop (fun N : ℕ => jacquetTrunc L A μ N f) = ∫ u, kernel u ∂μ.μ
  exact hlim.limUnder_eq

end ArtinPrimitiveRoots.A1.Theta
