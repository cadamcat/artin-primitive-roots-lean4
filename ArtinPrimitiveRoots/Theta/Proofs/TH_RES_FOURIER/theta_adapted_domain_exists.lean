import ArtinPrimitiveRoots.Proofs.th_res_fourier_a.BoundedIdealDomain

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- An adapted nonzero ideal and a bounded measurable domain exist at every g,
uniformly over the family parameter. Guide: sol-thin-thglobal/PROOFS.md:851–855.
Uses FourierFamilyHyp.level, restricted-product support, inverse different, and ideal lattices.
Feeds theta_fourierCoeff and thetaWhit_equiv through fourierFirstCoeff. -/
theorem theta_adapted_domain_exists {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} {sec : ∀ s : ℂ, GlobalSection P G s}
    {T0 : Finset (FinPlace F)} (hFam : FourierFamilyHyp μ sec T0) (g : P.tc.G) :
    ∃ (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
      (Pd : Set (InfinitePlace F → ℂ)),
      FourierAdaptedDomain sec g 𝔞 Pd 1 ∧ MeasurableSet Pd := by
  classical
  letI : IsTotallyComplex F := D.isTotallyComplex
  obtain ⟨x, hxg⟩ := P.q_surj g
  have hT0 : S.Sf ⊆ T0 := by
    intro v hv
    have hv' : v ∈ (sec 0).T0 := (sec 0).sub hv
    rwa [hFam.T0_eq 0] at hv'
  let Bad : Set (FinPlace F) :=
    {v | v ∉ T0 ∧ ∃ hv : v ∉ S.Sf, P.compF v x ∉ (P.tame v hv).Kmax}
  have hBad : Bad.Finite := (P.comp_restricted x).subset fun v hv => hv.2
  let V : Finset (FinPlace F) := T0 ∪ hBad.toFinset
  let level (v : FinPlace F) (hv : v ∈ T0) : ℕ := Classical.choose (hFam.level v hv)
  have level_spec (v : FinPlace F) (hv : v ∈ T0) :
      (P.loc v).m0 ≤ level v hv ∧
        ∀ s' z, ∀ k ∈ (P.loc v).Kc (level v hv),
          (sec s').f v (z * k) = (sec s').f v z :=
    Classical.choose_spec (hFam.level v hv)
  have hlocal (v : FinPlace F) (hvV : v ∈ V) :
      ∃ n : ℕ, ∀ ξ : v.adicCompletion F, ξ ∈ ball v n →
        ( (∀ hvT : v ∈ T0,
          (P.compF v x)⁻¹ * (P.loc v).n (Multiplicative.ofAdd ξ) * P.compF v x ∈
            (P.loc v).Kc (level v hvT)) ∧
        (∀ hvnotT : v ∉ T0, ∀ hvS : v ∉ S.Sf,
          (P.compF v x)⁻¹ * (P.loc v).n (Multiplicative.ofAdd ξ) * P.compF v x ∈
            (P.tame v hvS).Kmax)) := by
    by_cases hvT : v ∈ T0
    · let m := level v hvT
      let K := (P.loc v).Kc m
      let U : Set (P.loc v).L :=
        {z | (P.compF v x)⁻¹ * z * P.compF v x ∈ K}
      have hUopen : IsOpen U := by
        apply (P.loc v).Kc_open m (level_spec v hvT).1 |>.preimage
        fun_prop
      have hUone : (1 : (P.loc v).L) ∈ U := by simp [U, K]
      obtain ⟨n, hn, hsub⟩ := (P.loc v).Kc_nhds U (hUopen.mem_nhds hUone)
      refine ⟨n, ?_⟩
      intro ξ hξ
      constructor
      · intro hvT'
        have hnmem : (P.loc v).n (Multiplicative.ofAdd ξ) ∈ (P.loc v).Kc n :=
          (P.loc v).n_Kc n hn ξ hξ
        simpa [U, K, m] using hsub hnmem
      · intro hvnotT hvS'
        exact False.elim (hvnotT hvT)
    · have hvBadFin : v ∈ hBad.toFinset := by
        simpa [V, hvT] using hvV
      have hvBad : v ∈ Bad := hBad.mem_toFinset.mp hvBadFin
      obtain ⟨_, ⟨hvS, _⟩⟩ := hvBad
      let K := (P.tame v hvS).Kmax
      let U : Set (P.loc v).L :=
        {z | (P.compF v x)⁻¹ * z * P.compF v x ∈ K}
      have hUopen : IsOpen U := by
        apply (P.tame v hvS).open_.preimage
        fun_prop
      have hUone : (1 : (P.loc v).L) ∈ U := by simp [U, K]
      obtain ⟨n, hn, hsub⟩ := (P.loc v).Kc_nhds U (hUopen.mem_nhds hUone)
      refine ⟨n, ?_⟩
      intro ξ hξ
      constructor
      · intro hvT'
        exact False.elim (hvT hvT')
      · intro _hvnotT hvS'
        have hnmem : (P.loc v).n (Multiplicative.ofAdd ξ) ∈ (P.loc v).Kc n :=
          (P.loc v).n_Kc n hn ξ hξ
        simpa [U, K] using hsub hnmem
  let nBound (v : FinPlace F) : ℕ :=
    if hv : v ∈ V then (hlocal v hv).choose else 0
  have hlocal_spec (v : FinPlace F) (hv : v ∈ V) :
      ∀ ξ : v.adicCompletion F, ξ ∈ ball v (nBound v) →
        ( (∀ hvT : v ∈ T0,
            (P.compF v x)⁻¹ * (P.loc v).n (Multiplicative.ofAdd ξ) * P.compF v x ∈
              (P.loc v).Kc (level v hvT)) ∧
        (∀ hvnotT : v ∉ T0, ∀ hvS : v ∉ S.Sf,
          (P.compF v x)⁻¹ * (P.loc v).n (Multiplicative.ofAdd ξ) * P.compF v x ∈
            (P.tame v hvS).Kmax)) := by
    simpa [nBound, hv] using (hlocal v hv).choose_spec
  let J : Ideal (𝓞 F) := V.inf (fun v => v.asIdeal ^ nBound v)
  have hpow_ne (v : FinPlace F) : v.asIdeal ^ nBound v ≠ ⊥ := by
    by_cases hn : nBound v = 0
    · simp [hn]
    · intro h
      exact v.ne_bot ((Ideal.pow_eq_bot hn).mp h)
  have hJne : J ≠ ⊥ := by
    dsimp [J]
    induction V using Finset.induction_on with
    | empty => simp
    | @insert v V hv ih =>
      simp only [Finset.inf_insert, hv]
      exact Ideal.inf_ne_bot_of_ne_bot (hpow_ne v) ih
  have hJle (v : FinPlace F) (hv : v ∈ V) : J ≤ v.asIdeal ^ nBound v := by
    exact Finset.inf_le hv
  let 𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F :=
    Units.mk0 (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
      (FractionalIdeal.coeIdeal_ne_zero.mpr hJne)
  have h𝔞 : 𝔞 ≠ 0 := Units.ne_zero (Units.mk0 (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
      (FractionalIdeal.coeIdeal_ne_zero.mpr hJne))
  obtain ⟨Pd, hPd, hb, hm⟩ :=
    bounded_measurable_ideal_domain D
      (Units.mk0 (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
        (FractionalIdeal.coeIdeal_ne_zero.mpr hJne))
  have hξideal (ξ : F) (hξ : ξ ∈ (𝔞 : Submodule (𝓞 F) F)) :
      ∃ y : 𝓞 F, y ∈ J ∧ algebraMap (𝓞 F) F y = ξ := by
    have hmem : ξ ∈ (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
      simpa [𝔞] using hξ
    exact (FractionalIdeal.mem_coeIdeal _).mp hmem
  have hξball (ξ : F) (hξ : ξ ∈ (𝔞 : Submodule (𝓞 F) F))
      (v : FinPlace F) (hv : v ∈ V) :
      ((ξ : F) : v.adicCompletion F) ∈ ball v (nBound v) := by
    obtain ⟨y, hyJ, hξeq⟩ := hξideal ξ hξ
    have hyv : y ∈ v.asIdeal ^ nBound v := hJle v hv hyJ
    have hval : v.intValuation y ≤ WithZero.exp (-(nBound v : ℤ)) :=
      (HeightOneSpectrum.intValuation_le_pow_iff_mem v y (nBound v)).2 hyv
    change Valued.v ((ξ : F) : v.adicCompletion F) ≤
      WithZero.exp (-(nBound v : ℤ))
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← hξeq,
      HeightOneSpectrum.valuation_of_algebraMap]
    exact hval
  have hξint (ξ : F) (hξ : ξ ∈ (𝔞 : Submodule (𝓞 F) F))
      (v : FinPlace F) : ((ξ : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    obtain ⟨y, hyJ, hξeq⟩ := hξideal ξ hξ
    change Valued.v ((ξ : F) : v.adicCompletion F) ≤ 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← hξeq,
      HeightOneSpectrum.valuation_of_algebraMap]
    exact v.intValuation_le_one y
  have hfix : FourierIdealFix sec g 𝔞 := by
    intro s ξ hξ h
    obtain ⟨y, hyJ, hξeq⟩ := hξideal ξ hξ
    let u : S.FS := (0, -infEmbA ξ)
    obtain ⟨xA, hqA, hcompFA, hcompCA⟩ := P.nS_components u
    let xR := P.ratRP (upperGL ξ)
    let nRP := xR * xA
    have hnRP : P.q nRP = nFin P ξ := by
      change P.q (xR * xA) = P.tc.rat (upperGL ξ) *
        P.tc.nS (Multiplicative.ofAdd u)
      rw [P.q.map_mul, P.q_ratRP, hqA]
    have hmatF (v : FinPlace F) :
        Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) (upperGL ξ) =
          upperM (v.adicCompletion F) (algebraMap F (v.adicCompletion F) ξ) := by
      ext i j <;> fin_cases i <;> fin_cases j <;> simp [upperGL, upperM]
    have hcompR (v : FinPlace F) :
        P.compF v xR = (P.loc v).n
          (Multiplicative.ofAdd ((ξ : F) : v.adicCompletion F)) := by
      rw [P.compF_ratRP, hmatF, ← (P.loc v).sec_n]
      rfl
    have hcompA (v : FinPlace F) : P.compF v xA = 1 := by
      rw [hcompFA v]
      by_cases hv : v ∈ S.Sf <;> simp [u, hv]
    have hcompN (v : FinPlace F) :
        P.compF v nRP = (P.loc v).n
          (Multiplicative.ofAdd ((ξ : F) : v.adicCompletion F)) := by
      simp [nRP, (P.compF v).map_mul, hcompR, hcompA]
    have hmatC (w : InfinitePlace F) :
        Matrix.GeneralLinearGroup.map w.embedding (upperGL ξ) =
          upperM ℂ (w.embedding ξ) := by
      ext i j <;> fin_cases i <;> fin_cases j <;> simp [upperGL, upperM]
    have hupper (w : InfinitePlace F) :
        upperM ℂ (w.embedding ξ) * upperM ℂ (-(w.embedding ξ)) = 1 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> simp [upperM, Matrix.mul_apply]
    have hcompRN (w : InfinitePlace F) :
        P.compC w nRP = 1 := by
      dsimp [nRP]
      rw [(P.compC w).map_mul]
      rw [P.compC_ratRP, hmatC, hcompCA w]
      have hu2 : u.2 w = -(w.embedding ξ) := rfl
      rw [← QuotientGroup.mk_mul, hu2, hupper]
      simp
    let kRP := x⁻¹ * nRP * x
    have hqk : P.q kRP = g⁻¹ * nFin P ξ * g := by
      simp [kRP, nRP, hnRP, hxg]
    have hcompK (v : FinPlace F) :
        P.compF v kRP = (P.compF v x)⁻¹ *
          (P.loc v).n (Multiplicative.ofAdd ((ξ : F) : v.adicCompletion F)) *
          P.compF v x := by
      simp [kRP, (P.compF v).map_mul, (P.compF v).map_inv, hcompN]
    have hcompKC (w : InfinitePlace F) : P.compC w kRP = 1 := by
      simp [kRP, (P.compC w).map_mul, (P.compC w).map_inv, hcompRN]
    have hKmem (v : FinPlace F) (hvT : v ∈ T0) :
        P.compF v kRP ∈ (P.loc v).Kc (level v hvT) := by
      have hvV : v ∈ V := by simp [V, hvT]
      have hball := hξball ξ hξ v hvV
      have hloc := ((hlocal_spec v hvV ((ξ : F) : v.adicCompletion F) hball).1 hvT)
      simpa [hcompK v] using hloc
    have hKmax (v : FinPlace F) (hvT : v ∉ T0) (hvS : v ∉ S.Sf) :
        P.compF v kRP ∈ (P.tame v hvS).Kmax := by
      by_cases hvBad : v ∈ Bad
      · have hvV : v ∈ V := by
          simp only [V, Finset.mem_union]
          exact Or.inr (hBad.mem_toFinset.mpr hvBad)
        have hball := hξball ξ hξ v hvV
        simpa [hcompK v] using
          ((hlocal_spec v hvV ((ξ : F) : v.adicCompletion F) hball).2 hvT hvS)
      · have hxK : P.compF v x ∈ (P.tame v hvS).Kmax := by
          by_contra hnot
          exact hvBad ⟨hvT, ⟨hvS, hnot⟩⟩
        have hnK : (P.loc v).n (Multiplicative.ofAdd ((ξ : F) : v.adicCompletion F)) ∈
            (P.tame v hvS).Kmax := (P.tame v hvS).n_mem _ (hξint ξ hξ v)
        rw [hcompK v]
        have hinvn : (P.compF v x)⁻¹ *
            (P.loc v).n (Multiplicative.ofAdd ((ξ : F) : v.adicCompletion F)) ∈
              (P.tame v hvS).Kmax :=
          (P.tame v hvS).Kmax.mul_mem ((P.tame v hvS).Kmax.inv_mem hxK) hnK
        exact (P.tame v hvS).Kmax.mul_mem hinvn hxK
    have hlocalFix (v : FinPlace F) (y : (P.loc v).L) :
        (sec s).f v (y * P.compF v kRP) = (sec s).f v y := by
      by_cases hvT : v ∈ T0
      · exact (level_spec v hvT).2 s y _ (hKmem v hvT)
      · have hvS : v ∉ S.Sf := fun hS => hvT (hT0 hS)
        have hvSec : v ∉ (sec s).T0 := by rw [hFam.T0_eq s]; exact hvT
        exact ((sec s).f_sph v hvSec).2 y _ (hKmax v hvT hvS)
    have hscalar (h : P.tc.G) :
        scalarOf P G (sec s).f (sec s).fC (h * P.q kRP) =
          scalarOf P G (sec s).f (sec s).fC h := by
      obtain ⟨r, hr⟩ := P.q_surj h
      have hrk : P.q (r * kRP) = h * P.q kRP := by simp [hr]
      rw [← hrk, ← hr]
      rw [(scalarOf_q P G (sec s) (r * kRP)).2, (scalarOf_q P G (sec s) r).2]
      congr 1
      · apply finprod_congr
        intro v
        rw [(P.compF v).map_mul]
        exact congrArg (G.lam v) (hlocalFix v (P.compF v r))
      · apply Finset.prod_congr rfl
        intro w hw
        simp [(P.compC w).map_mul, hcompKC]
    have htarget :
        scalarOf P G (sec s).f (sec s).fC (h * (g⁻¹ * nFin P ξ * g)) =
          scalarOf P G (sec s).f (sec s).fC (h) := by
      rw [← hqk]
      exact hscalar h
    exact htarget
  have hdual : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf 1 (infEmbA ξ) = 1 := by
    intro ξ hξ
    obtain ⟨y, hyJ, hξeq⟩ := hξideal ξ hξ
    simpa [hξeq] using psiInf_one_integral D S A y
  refine ⟨𝔞, Pd, ?_, hm⟩
  exact ⟨h𝔞, hfix, hPd, hb, hdual⟩

end ArtinPrimitiveRoots.A1.Theta
