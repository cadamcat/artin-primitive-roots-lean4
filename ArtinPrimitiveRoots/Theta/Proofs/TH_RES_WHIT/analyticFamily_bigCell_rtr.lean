import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.Defs
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Topology.Baire.LocallyCompactRegular

set_option autoImplicit false

open NumberField IsDedekindDomain
open Filter
open scoped Classical Topology

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}
variable {P : CoverPackage D S H A} {G : GlobalDatum P}
  {μ : ∀ v : FinPlace F, LocHaar v}

private theorem bigCell_analytic {v : FinPlace F} (L : FinLocalCover D H v) (T : TorusRep D H v)
    (φ : v.adicCompletion F → T.V) (g : L.L) :
    AnalyticOnNhd ℂ (fun s => bigCell L T s φ g) {s | 0 < s.re} := by
  classical
  by_cases hd : ∃ (x : v.adicCompletion F) (ζ : rootsOfUnity 3 ℂ)
      (y : (v.adicCompletion F)ˣ) (t : v.adicCompletion F),
        g = L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w * L.n (Multiplicative.ofAdd t)
  · let x := hd.choose
    let ζ := hd.choose_spec.choose
    let y := hd.choose_spec.choose_spec.choose
    let t := hd.choose_spec.choose_spec.choose_spec.choose
    have hdecomp : g =
        L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w * L.n (Multiplicative.ofAdd t) :=
      hd.choose_spec.choose_spec.choose_spec.choose_spec
    have hpow : AnalyticOnNhd ℂ
        (fun s : ℂ => (absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s)) {s | 0 < s.re} := by
      apply AnalyticOnNhd.cpow analyticOnNhd_const (analyticOnNhd_const.add analyticOnNhd_id)
      intro s hs
      exact Complex.ofReal_mem_slitPlane.mpr (absFin_pos (Units.ne_zero y))
    have hformula : (fun s : ℂ => bigCell L T s φ g) =
        (fun s => ((ζ : ℂˣ) : ℂ) •
          ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s)) • T.σa y (φ t)) := by
      funext s
      rw [hdecomp]
      exact bigCell_apply L T s φ x ζ y t
    rw [hformula]
    fun_prop
  · dsimp [bigCell]
    split_ifs with h
    · exact (hd h).elim
    · exact analyticOnNhd_const

private theorem bigCell_scale {v : FinPlace F} (L : FinLocalCover D H v)
    (T : TorusRep D H v) (φ : v.adicCompletion F → T.V)
    (g : L.L) :
    ∃ r : ℝ, 0 < r ∧ ∀ s : ℂ,
      bigCell L T s φ g = ((r : ℂ) ^ s) • bigCell L T 0 φ g := by
  classical
  by_cases hd : ∃ (x : v.adicCompletion F) (ζ : rootsOfUnity 3 ℂ)
      (y : (v.adicCompletion F)ˣ) (t : v.adicCompletion F),
        g = L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w * L.n (Multiplicative.ofAdd t)
  · let x := hd.choose
    let ζ := hd.choose_spec.choose
    let y := hd.choose_spec.choose_spec.choose
    let t := hd.choose_spec.choose_spec.choose_spec.choose
    have hdecomp : g =
        L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w * L.n (Multiplicative.ofAdd t) :=
      hd.choose_spec.choose_spec.choose_spec.choose_spec
    have hpos : 0 < absFin v y := absFin_pos (Units.ne_zero y)
    have hval (s : ℂ) : bigCell L T s φ g =
        ((ζ : ℂˣ) : ℂ) • ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s)) • T.σa y (φ t) := by
      rw [hdecomp]
      exact bigCell_apply L T s φ x ζ y t
    refine ⟨absFin v y, hpos, ?_⟩
    intro s
    have hcpow : ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s)) =
        ((absFin v y : ℂ) ^ s) * ((absFin v y : ℂ) ^ ((1 : ℂ) / 2)) := by
      rw [show (1 : ℂ) / 2 + s = s + (1 : ℂ) / 2 by ring]
      exact Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hpos))
    rw [hval s, hval 0, hcpow]
    simp only [smul_smul]
    congr 1
    ring
  · refine ⟨1, one_pos, ?_⟩
    intro s
    dsimp [bigCell]
    split_ifs with h
    · exact (hd h).elim
    · simp

private theorem bigCell_uniform_level {v : FinPlace F} (L : FinLocalCover D H v)
    (T : TorusRep D H v) (φ : v.adicCompletion F → T.V)
    (hφ : IsLocallyConstant φ) (hc : HasCompactSupport φ) :
    ∃ m, L.m0 ≤ m ∧ ∀ s g k, k ∈ L.Kc m →
      bigCell L T s φ (g * k) = bigCell L T s φ g := by
  classical
  obtain ⟨m0, hm0, hlevel0⟩ := (bigCell_isSection L T 0 φ hφ hc).2.2
  obtain ⟨m1, hm1, hlevel1⟩ := (bigCell_isSection L T 1 φ hφ hc).2.2
  let m := max m0 m1
  have hm : L.m0 ≤ m := le_trans hm0 (Nat.le_max_left _ _)
  refine ⟨m, hm, ?_⟩
  intro s g k hk
  have hk0 : k ∈ L.Kc m0 := L.Kc_anti m0 m hm0 (Nat.le_max_left _ _) hk
  have hk1 : k ∈ L.Kc m1 := L.Kc_anti m1 m hm1 (Nat.le_max_right _ _) hk
  have hbase0 := hlevel0 g k hk0
  have hbase1 := hlevel1 g k hk1
  obtain ⟨r0, hr0, hscale0⟩ := bigCell_scale L T φ g
  obtain ⟨r1, hr1, hscale1⟩ := bigCell_scale L T φ (g * k)
  have hscale0one : bigCell L T 1 φ g = (r0 : ℂ) • bigCell L T 0 φ g := by
    simpa using hscale0 1
  have hscale1one : bigCell L T 1 φ (g * k) =
      (r1 : ℂ) • bigCell L T 0 φ (g * k) := by
    simpa using hscale1 1
  by_cases hz : bigCell L T 0 φ g = 0
  · calc
      bigCell L T s φ (g * k) = (r1 : ℂ) ^ s • bigCell L T 0 φ (g * k) := hscale1 s
      _ = 0 := by rw [hbase0, hz]; simp
      _ = (r0 : ℂ) ^ s • bigCell L T 0 φ g := by rw [hz]; simp
      _ = bigCell L T s φ g := (hscale0 s).symm
  · have hcoef : (r0 : ℂ) = (r1 : ℂ) := by
      apply (smul_left_injective ℂ hz)
      calc
        (r0 : ℂ) • bigCell L T 0 φ g = bigCell L T 1 φ g := hscale0one.symm
        _ = bigCell L T 1 φ (g * k) := hbase1.symm
        _ = (r1 : ℂ) • bigCell L T 0 φ (g * k) := hscale1one
        _ = (r1 : ℂ) • bigCell L T 0 φ g := by rw [hbase0]
    calc
      bigCell L T s φ (g * k) = (r1 : ℂ) ^ s • bigCell L T 0 φ (g * k) := hscale1 s
      _ = (r0 : ℂ) ^ s • bigCell L T 0 φ g := by rw [hcoef, hbase0]
      _ = bigCell L T s φ g := (hscale0 s).symm

private theorem bigCell_rtr_uniform_level {v : FinPlace F} (L : FinLocalCover D H v)
    (T : TorusRep D H v) (φ : v.adicCompletion F → T.V)
    (hφ : IsLocallyConstant φ) (hc : HasCompactSupport φ) (h : L.L) :
    ∃ m, L.m0 ≤ m ∧ ∀ s g k, k ∈ L.Kc m →
      rtr h (bigCell L T s φ) (g * k) = rtr h (bigCell L T s φ) g := by
  classical
  obtain ⟨m, hm, hlevel⟩ := bigCell_uniform_level L T φ hφ hc
  let U : Set L.L := {k | h⁻¹ * k * h ∈ L.Kc m}
  have hcont : Continuous (fun k : L.L => h⁻¹ * k * h) := by fun_prop
  have hUopen : IsOpen U := by
    change IsOpen ((fun k : L.L => h⁻¹ * k * h) ⁻¹' (L.Kc m : Set L.L))
    exact (L.Kc_open m hm).preimage hcont
  have hUone : (1 : L.L) ∈ U := by simp [U]
  obtain ⟨m', hm', hmsub⟩ := L.Kc_nhds U (hUopen.mem_nhds hUone)
  refine ⟨m', hm', ?_⟩
  intro s g k hk
  change bigCell L T s φ ((g * k) * h) = bigCell L T s φ (g * h)
  have harg : (g * k) * h = (g * h) * (h⁻¹ * k * h) := by group
  rw [harg]
  exact hlevel s (g * h) (h⁻¹ * k * h) (hmsub hk)

private theorem adicCompletion_ball_compact {v : FinPlace F} (N : ℕ) :
    IsCompact (ball v (-(N : ℤ))) := by
  let K := v.adicCompletion F
  letI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  have hproper : ProperSpace K :=
    (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F)),
        inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)))⟩
  let R : ℝ := (WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v)
    (WithZero.exp (N : ℤ)) : ℝ)
  have hball : ball v (-(N : ℤ)) = Metric.closedBall (0 : K) R := by
    ext x
    simp only [ball, Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
    rw [FinitePlace.norm_def]
    simp only [R, NNReal.coe_le_coe]
    simpa only [neg_neg] using
      ((WithZeroMulInt.toNNReal_strictMono
        (HeightOneSpectrum.one_lt_absNorm_nnreal v)).le_iff_le
          (a := Valued.v x) (b := WithZero.exp (N : ℤ))).symm
  rw [hball]
  exact hproper.isCompact_closedBall 0 R

private theorem jacquetTrunc_analytic {v : FinPlace F} (L : FinLocalCover D H v)
    (T : TorusRep D H v) (A : AddCharData F) (μ : LocHaar v)
    (φ : v.adicCompletion F → T.V) (hφ : IsLocallyConstant φ)
    (hc : HasCompactSupport φ) (q : L.L) (N : ℕ) :
    AnalyticOnNhd ℂ
      (fun s => jacquetTrunc L A μ N (rtr q (bigCell L T s φ))) {s | 0 < s.re} := by
  classical
  let K := v.adicCompletion F
  let J : ℂ → K → T.V := fun s x =>
    A.ψ v (-x) • rtr q (bigCell L T s φ) (L.w * L.n (Multiplicative.ofAdd x))
  have hpoint (x : K) : AnalyticOnNhd ℂ (fun s => J s x) {s | 0 < s.re} := by
    dsimp [J, rtr]
    have h := (bigCell_analytic L T φ ((L.w * L.n (Multiplicative.ofAdd x)) * q)).const_smul
      (c := A.ψ v (-x))
    have heq : (A.ψ v (-x) • fun s => bigCell L T s φ
        ((L.w * L.n (Multiplicative.ofAdd x)) * q)) =
        (fun s => A.ψ v (-x) • bigCell L T s φ
          ((L.w * L.n (Multiplicative.ofAdd x)) * q)) := by
      funext s
      rfl
    rw [← heq]
    exact h
  obtain ⟨m, hm, hlevel⟩ := bigCell_rtr_uniform_level L T φ hφ hc q
  let U : Set K := ball v (m : ℤ)
  have hUopen : IsOpen U := by
    change IsOpen {x : K | Valued.v x ≤ WithZero.exp (-(m : ℤ))}
    exact v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero
  have hshift : ∀ s x u, u ∈ U → J s (x + u) = J s x := by
    intro s x u hu
    have huO : u ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v u ≤ WithZero.exp 0
      change Valued.v u ≤ WithZero.exp (-(m : ℤ)) at hu
      exact hu.trans (WithZero.exp_le_exp.mpr (by omega))
    have hnegO : -u ∈ v.adicCompletionIntegers F :=
      (v.adicCompletionIntegers F).neg_mem u huO
    have hψ0 : A.ψ v (-u) = 1 := A.integral v (-u) hnegO
    have hψ : A.ψ v (-(x + u)) = A.ψ v (-x) := by
      rw [neg_add, AddChar.map_add_eq_mul, hψ0, mul_one]
    have hnu : L.n (Multiplicative.ofAdd u) ∈ L.Kc m := L.n_Kc m hm u hu
    have hadd : L.n (Multiplicative.ofAdd (x + u)) =
        L.n (Multiplicative.ofAdd x) * L.n (Multiplicative.ofAdd u) := by simp
    have harg : L.w * L.n (Multiplicative.ofAdd (x + u)) =
        (L.w * L.n (Multiplicative.ofAdd x)) * L.n (Multiplicative.ofAdd u) := by
      rw [hadd]
      group
    have hsec : rtr q (bigCell L T s φ) (L.w * L.n (Multiplicative.ofAdd (x + u))) =
        rtr q (bigCell L T s φ) (L.w * L.n (Multiplicative.ofAdd x)) := by
      rw [harg]
      exact hlevel s (L.w * L.n (Multiplicative.ofAdd x))
        (L.n (Multiplicative.ofAdd u)) hnu
    change A.ψ v (-(x + u)) • rtr q (bigCell L T s φ)
        (L.w * L.n (Multiplicative.ofAdd (x + u))) =
      A.ψ v (-x) • rtr q (bigCell L T s φ)
        (L.w * L.n (Multiplicative.ofAdd x))
    rw [hψ, hsec]
  let C : K → Set K := fun x => {y | y - x ∈ U}
  have hCopen (x : K) : IsOpen (C x) := by
    change IsOpen ((fun y : K => y - x) ⁻¹' U)
    exact hUopen.preimage (by fun_prop)
  let B : Set K := ball v (-(N : ℤ))
  have hBcompact : IsCompact B := adicCompletion_ball_compact N
  have hBmeas : MeasurableSet B := hBcompact.isClosed.measurableSet
  let I := {x : K // x ∈ B}
  let C' : I → Set K := fun x => C x.1
  have hC'open : ∀ x : I, IsOpen (C' x) := fun x => hCopen x.1
  have hC'cover : B ⊆ ⋃ x : I, C' x := by
    intro x hx
    refine Set.mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩
    change x - x ∈ U
    have hzero : (0 : K) ∈ U := by
      change Valued.v (0 : K) ≤ WithZero.exp (-(m : ℤ))
      simp
    simpa using hzero
  obtain ⟨t, htcov⟩ := hBcompact.elim_finite_subcover C' hC'open hC'cover
  let E : I → Set K := fun i => B ∩ C' i
  have hEm (i : I) : MeasurableSet (E i) :=
    hBmeas.inter (hC'open i).measurableSet
  have hEsub (i : I) : E i ⊆ B := Set.inter_subset_left
  have hEunion : (⋃ i ∈ t, E i) = B := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion₂.1 hx with ⟨i, hi, hxE⟩
      exact hxE.1
    · intro hx
      rcases Set.mem_iUnion₂.1 (htcov hx) with ⟨i, hi, hxi⟩
      exact Set.mem_iUnion₂.2 ⟨i, hi, ⟨hx, hxi⟩⟩
  have hconst (i : I) (s : ℂ) : Set.EqOn (J s) (fun _ => J s i.1) (E i) := by
    intro x hx
    have hu : x - i.1 ∈ U := hx.2
    have hdecomp : x = i.1 + (x - i.1) := by abel
    rw [hdecomp]
    exact hshift s i.1 (x - i.1) hu
  have hSIntegrable (s : ℂ) : ∀ i ∈ t, MeasureTheory.IntegrableOn (J s) (E i) μ.μ := by
    intro i hi
    have hfinite : μ.μ (E i) ≠ ⊤ := by
      apply ne_of_lt
      exact lt_of_le_of_lt (MeasureTheory.measure_mono (hEsub i)) hBcompact.measure_lt_top
    have hconstInt : MeasureTheory.IntegrableOn (fun _ : K => J s i.1) (E i) μ.μ :=
      MeasureTheory.integrableOn_const hfinite
    exact (MeasureTheory.integrableOn_congr_fun (hconst i s) (hEm i)).2 hconstInt
  have hsumAnalytic : AnalyticOnNhd ℂ
        (fun s => ∑ u ∈ t.powerset with u.Nonempty,
        (-1 : ℝ) ^ (u.card + 1) • ∫ x in (⋂ i ∈ u, E i), J s x ∂μ.μ)
      {s | 0 < s.re} := by
    apply Finset.analyticOnNhd_fun_sum (t.powerset.filter fun u => u.Nonempty)
    intro u hu
    have hu' := (Finset.mem_filter.mp hu).1
    have hunonempty := (Finset.mem_filter.mp hu).2
    obtain ⟨i, hi⟩ := Finset.Nonempty.exists_mem hunonempty
    have hiT : i ∈ t := Finset.mem_powerset.mp hu' hi
    let Vset : Set K := ⋂ j ∈ u, E j
    have hVmeas : MeasurableSet Vset := by
      refine u.measurableSet_biInter fun j hj => hEm j
    have hVi : Vset ⊆ E i := by
      intro x hx
      change x ∈ ⋂ j ∈ u, E j at hx
      simp only [Set.mem_iInter] at hx
      exact hx i hi
    have hIntEq (s : ℂ) :
        (∫ x in Vset, J s x ∂μ.μ) = μ.μ.real Vset • J s i.1 := by
      calc
        (∫ x in Vset, J s x ∂μ.μ) =
            ∫ x in Vset, (fun _ : K => J s i.1) x ∂μ.μ := by
              apply MeasureTheory.setIntegral_congr_fun hVmeas
              intro x hx
              exact hconst i s (hVi hx)
        _ = μ.μ.real Vset • J s i.1 := MeasureTheory.setIntegral_const _
    let c : ℂ := (((-1 : ℝ) ^ (u.card + 1) * μ.μ.real Vset : ℝ) : ℂ)
    have hterm : AnalyticOnNhd ℂ
        (fun s => (-1 : ℝ) ^ (u.card + 1) • ∫ x in Vset, J s x ∂μ.μ)
        {s | 0 < s.re} := by
      have hbase : AnalyticOnNhd ℂ (fun s => c • J s i.1) {s | 0 < s.re} := by
        have hbase' := (hpoint i.1).const_smul (c := c)
        have heq : (c • fun s => J s i.1) = (fun s => c • J s i.1) := by
          funext s
          rfl
        rw [← heq]
        exact hbase'
      apply hbase.congr (isOpen_lt continuous_const Complex.continuous_re)
      intro s hs
      change c • J s i.1 =
        (-1 : ℝ) ^ (u.card + 1) • ∫ x in Vset, J s x ∂μ.μ
      rw [hIntEq s]
      change (((-1 : ℝ) ^ (u.card + 1) * μ.μ.real Vset : ℝ) : ℂ) • J s i.1 =
        (-1 : ℝ) ^ (u.card + 1) • (μ.μ.real Vset • J s i.1)
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ),
        RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, Complex.ofReal_mul]
      simp only [J, rtr, smul_smul, mul_assoc]
      rfl
    simpa [Vset] using hterm
  have hform : (fun s => jacquetTrunc L A μ N (rtr q (bigCell L T s φ))) =
      (fun s => ∑ u ∈ t.powerset with u.Nonempty,
        (-1 : ℝ) ^ (u.card + 1) • ∫ x in (⋂ i ∈ u, E i), J s x ∂μ.μ) := by
    funext s
    change (∫ x in B, J s x ∂μ.μ) = _
    rw [← hEunion]
    exact MeasureTheory.integral_biUnion_eq_sum_powerset
      (fun i hi => hEm i) (hSIntegrable s)
  rw [hform]
  exact hsumAnalytic

private theorem jacquet_analytic_from_trunc {v : FinPlace F} (L : FinLocalCover D H v)
    (T : TorusRep D H v) (A : AddCharData F) (μ : LocHaar v)
    (φ : v.adicCompletion F → T.V) (hφ : IsLocallyConstant φ)
    (hc : HasCompactSupport φ) (q : L.L) :
    AnalyticOnNhd ℂ
      (fun s => jacquet L A μ (rtr q (bigCell L T s φ))) {s | 0 < s.re} := by
  classical
  let dom : Set ℂ := {s | 0 < s.re}
  have hDopen : IsOpen dom := by
    exact isOpen_lt continuous_const Complex.continuous_re
  have hDpre : IsPreconnected dom := by
    simpa [dom] using (convex_halfSpace_re_gt (0 : ℝ)).isPreconnected
  let X := {s : ℂ // s ∈ dom}
  haveI : LocallyCompactSpace X := hDopen.locallyCompactSpace
  haveI : BaireSpace X := BaireSpace.of_t2Space_locallyCompactSpace
  let trunc : ℕ → ℂ → T.V := fun n s =>
    jacquetTrunc L A μ n (rtr q (bigCell L T s φ))
  have htrunc (n : ℕ) : AnalyticOnNhd ℂ (trunc n) dom := by
    simpa [trunc] using jacquetTrunc_analytic L T A μ φ hφ hc q n
  let delta : ℕ → ℂ → T.V := fun n s => trunc (n + 1) s - trunc n s
  have hdelta (n : ℕ) : AnalyticOnNhd ℂ (delta n) dom := by
    dsimp [delta]
    exact (htrunc (n + 1)).sub (htrunc n)
  let d : ℕ → X → T.V := fun n s => delta n s.1
  have hdcont (n : ℕ) : Continuous (d n) := by
    change Continuous (fun s : X => delta n s.1)
    dsimp [X, dom]
    exact continuousOn_iff_continuous_domRestrict.mp (hdelta n).continuousOn
  let openSet : ℕ → Set X := fun n =>
    if h : ∃ x : X, d n x ≠ 0 then {x | d n x ≠ 0} else Set.univ
  have hopen (n : ℕ) : IsOpen (openSet n) := by
    by_cases hn : ∃ x : X, d n x ≠ 0
    · simp only [openSet, dif_pos hn]
      exact (isClosed_singleton (x := (0 : T.V))).isOpen_compl.preimage (hdcont n)
    · simp [openSet, hn]
  have hdense (n : ℕ) : Dense (openSet n) := by
    rw [dense_iff_inter_open]
    intro V hV hVne
    by_cases hn : ∃ x : X, d n x ≠ 0
    · have hmeet : (V ∩ {x : X | d n x ≠ 0}).Nonempty := by
        by_contra hmeet
        have hzero : ∀ x ∈ V, d n x = 0 := by
          intro x hxV
          by_contra hx
          exact hmeet ⟨x, hxV, hx⟩
        obtain ⟨x, hxV⟩ := hVne
        obtain ⟨W, hWopen, hWpre⟩ := isOpen_induced_iff.mp hV
        have hxW : (x : ℂ) ∈ W := by
          have : x ∈ (Subtype.val : X → ℂ) ⁻¹' W := by rw [hWpre]; exact hxV
          exact this
        have hEvent : delta n =ᶠ[𝓝 (x : ℂ)] 0 := by
          filter_upwards [hWopen.mem_nhds hxW, hDopen.mem_nhds x.property] with y hyW hyD
          have hyV : (⟨y, hyD⟩ : X) ∈ V := by
            rw [← hWpre]
            exact hyW
          simpa [d] using hzero ⟨y, hyD⟩ hyV
        have hzeroOn : Set.EqOn (delta n) 0 dom :=
          (hdelta n).eqOn_zero_of_preconnected_of_eventuallyEq_zero
            hDpre x.property hEvent
        obtain ⟨x', hx'⟩ := hn
        have hxzero : d n x' = 0 := by
          simpa [d] using hzeroOn x'.property
        exact hx' hxzero
      have hmeet' : (V ∩ openSet n).Nonempty := by
        simpa [openSet, hn] using hmeet
      exact hmeet'
    · simpa [openSet, hn] using hVne
  have hDense : Dense (⋂ n, openSet n) := dense_iInter_of_isOpen_nat hopen hdense
  have hXne : (Set.univ : Set X).Nonempty :=
    ⟨⟨1, by norm_num [dom]⟩, Set.mem_univ _⟩
  obtain ⟨x, hx⟩ := (dense_iff_inter_open.mp hDense) Set.univ isOpen_univ hXne
  have hxOpen (n : ℕ) : x ∈ openSet n := Set.mem_iInter.1 hx.2 n
  have hpointStable (y : X) : ∃ N₀, ∀ N, N₀ ≤ N →
      trunc N y.1 = jacquet L A μ (rtr q (bigCell L T y.1 φ)) := by
    have hsec : IsSection L T y.1 (rtr q (bigCell L T y.1 φ)) :=
      IsSection.rtr (bigCell_isSection L T y.1 φ hφ hc) q
    exact jacquet_stable L T A μ y.1 (rtr q (bigCell L T y.1 φ)) hsec
  obtain ⟨N₀, hstableAtX⟩ := hpointStable x
  have hdeltaAtX (n : ℕ) (hn : N₀ ≤ n) : d n x = 0 := by
    have h0 := hstableAtX n hn
    have h1 := hstableAtX (n + 1) (le_trans hn (Nat.le_succ n))
    change delta n x.1 = 0
    dsimp [delta]
    rw [h1, h0]
    simp
  have hdeltaUniform (n : ℕ) (hn : N₀ ≤ n) (s : ℂ) (hs : s ∈ dom) :
      delta n s = 0 := by
    by_contra hne
    have hnonzero : ∃ y : X, d n y ≠ 0 := ⟨⟨s, hs⟩, by simpa [d] using hne⟩
    have hxne : d n x ≠ 0 := by simpa [openSet, hnonzero] using hxOpen n
    exact hxne (hdeltaAtX n hn)
  have hstep (n : ℕ) (hn : N₀ ≤ n) (s : ℂ) (hs : s ∈ dom) :
      trunc (n + 1) s = trunc n s := by
    have h := hdeltaUniform n hn s hs
    exact sub_eq_zero.mp (by simpa [delta] using h)
  have htruncConst (s : ℂ) (hs : s ∈ dom) : ∀ N, N₀ ≤ N → trunc N s = trunc N₀ s := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => rfl
    | succ n hn ih => exact (hstep n hn s hs).trans ih
  have hJacEq (s : ℂ) (hs : s ∈ dom) :
      jacquet L A μ (rtr q (bigCell L T s φ)) = trunc N₀ s := by
    have hsec : IsSection L T s (rtr q (bigCell L T s φ)) :=
      IsSection.rtr (bigCell_isSection L T s φ hφ hc) q
    obtain ⟨Ns, hstable⟩ :=
      jacquet_stable L T A μ s (rtr q (bigCell L T s φ)) hsec
    let M := max N₀ Ns
    calc
      jacquet L A μ (rtr q (bigCell L T s φ)) = trunc M s := (hstable M (Nat.le_max_right _ _)).symm
      _ = trunc N₀ s := htruncConst s hs M (Nat.le_max_left _ _)
  have hEqOn : Set.EqOn (fun s => jacquet L A μ (rtr q (bigCell L T s φ))) (trunc N₀) dom := by
    intro s hs
    exact hJacEq s hs
  exact (htrunc N₀).congr hDopen hEqOn.symm

/-- Insert a place and replace its section by a translated compactly supported big-cell
family, preserving all other sections. This supplies the M/J analyticity and uniform level
needed by family spanning and residue coordinates.
Uses: bigCell_isSection, intertwine_bigCell_analytic, jacquet_stable, IsSection.rtr.
Feeds: sectionSpace_family_spanning and thetaWhit_section_multilinear. -/
theorem analyticFamily_bigCell_rtr (Fam : AnalyticFamily P G μ) (v0 : FinPlace F)
    (φ : v0.adicCompletion F → (G.T v0).V) (hφ : IsLocallyConstant φ)
    (hc : HasCompactSupport φ) (h : (P.loc v0).L) :
    ∃ Fam' : AnalyticFamily P G μ, ExteriorFamily Fam v0 Fam' ∧
      ∀ s, (Fam'.sec s).f v0 = rtr h (bigCell (P.loc v0) (G.T v0) s φ) := by
  classical
  let sec' : ∀ s : ℂ, GlobalSection P G s := fun s =>
    { T0 := insert v0 Fam.T0
      sub := fun x hx => Finset.mem_insert_of_mem (by
        simpa [Fam.T0_eq s] using (Fam.sec s).sub hx)
      f := fun v => if hv : v = v0 then
        hv.symm ▸ rtr h (bigCell (P.loc v0) (G.T v0) s φ) else (Fam.sec s).f v
      f_sec := by
        intro v
        by_cases hv : v = v0
        · subst v
          simp
          exact IsSection.rtr (bigCell_isSection (P.loc v0) (G.T v0) s φ hφ hc) h
        · simpa [hv] using (Fam.sec s).f_sec v
      f_sph := by
        intro v hv
        have hvne : v ≠ v0 := by
          intro he
          subst v
          exact hv (Finset.mem_insert_self v0 Fam.T0)
        have hvFam : v ∉ Fam.T0 := by
          intro hv'
          exact hv (Finset.mem_insert_of_mem hv')
        have hvold : v ∉ (Fam.sec s).T0 := by
          simpa [Fam.T0_eq s] using hvFam
        obtain ⟨hval, hlevel⟩ := (Fam.sec s).f_sph v hvold
        constructor
        · simpa [hvne] using hval
        · intro g k hk
          simpa [hvne] using hlevel g k hk
      fC := (Fam.sec s).fC
      fC_sec := (Fam.sec s).fC_sec
      fC_smooth := (Fam.sec s).fC_smooth
      fC_jointSmooth := (Fam.sec s).fC_jointSmooth }
  have hsec0 (s : ℂ) : (sec' s).f v0 =
      rtr h (bigCell (P.loc v0) (G.T v0) s φ) := by
    simp [sec']
  let Fam' : AnalyticFamily P G μ :=
    { sec := sec'
      T0 := insert v0 Fam.T0
      T0_eq := fun _ => rfl
      fC_sph := by
        intro s w
        exact Fam.fC_sph s w
      f_analytic := by
        intro v g
        by_cases hv : v = v0
        · subst v
          have hEq : (fun s => (sec' s).f v0 g) =
              (fun s => bigCell (P.loc v0) (G.T v0) s φ (g * h)) := by
            funext s
            rw [congrFun (hsec0 s) g]
            rfl
          rw [hEq]
          exact bigCell_analytic (P.loc v0) (G.T v0) φ (g * h)
        · have hEq : (fun s => (sec' s).f v g) =
              (fun s => (Fam.sec s).f v g) := by
            funext s
            simp [sec', hv]
          rw [hEq]
          exact Fam.f_analytic v g
      M_analytic := by
        intro v hv g
        by_cases hvne : v = v0
        · subst v
          have hEq : (fun s => intertwine (P.loc v0) (μ v0) ((sec' s).f v0) g) =
              (fun s => intertwine (P.loc v0) (μ v0)
                (bigCell (P.loc v0) (G.T v0) s φ) (g * h)) := by
            funext s
            rw [hsec0 s, intertwine_rtr]
            rfl
          rw [hEq]
          exact intertwine_bigCell_analytic (P.loc v0) (G.T v0) (μ v0) φ hφ hc (g * h)
        · have hvFam : v ∈ Fam.T0 := by
            rcases Finset.mem_insert.mp hv with hv' | hv'
            · exact (hvne hv').elim
            · exact hv'
          have hEq : (fun s => intertwine (P.loc v) (μ v) ((sec' s).f v) g) =
              (fun s => intertwine (P.loc v) (μ v) ((Fam.sec s).f v) g) := by
            funext s
            simp [sec', hvne]
          rw [hEq]
          exact Fam.M_analytic v hvFam g
      J_analytic := by
        intro v hv g
        by_cases hvne : v = v0
        · subst v
          have hEq : (fun s => jacquet (P.loc v0) A (μ v0)
                (rtr g ((sec' s).f v0))) =
              (fun s => jacquet (P.loc v0) A (μ v0)
                (rtr (g * h) (bigCell (P.loc v0) (G.T v0) s φ))) := by
            funext s
            rw [hsec0 s]
            have hcomp : rtr g (rtr h (bigCell (P.loc v0) (G.T v0) s φ)) =
                rtr (g * h) (bigCell (P.loc v0) (G.T v0) s φ) := by
              funext x
              simp [rtr, mul_assoc]
            rw [hcomp]
          rw [hEq]
          exact jacquet_analytic_from_trunc (P.loc v0) (G.T v0) A (μ v0)
            φ hφ hc (g * h)
        · have hvFam : v ∈ Fam.T0 := by
            rcases Finset.mem_insert.mp hv with hv' | hv'
            · exact (hvne hv').elim
            · exact hv'
          have hEq : (fun s => jacquet (P.loc v) A (μ v)
                (rtr g ((sec' s).f v))) =
              (fun s => jacquet (P.loc v) A (μ v)
                (rtr g ((Fam.sec s).f v))) := by
            funext s
            simp [sec', hvne]
          rw [hEq]
          exact Fam.J_analytic v hvFam g
      level := by
        intro v hv
        by_cases hvne : v = v0
        · subst v
          obtain ⟨m, hm, hlevel⟩ :=
            bigCell_rtr_uniform_level (P.loc v0) (G.T v0) φ hφ hc h
          refine ⟨m, hm, ?_⟩
          intro s g k hk
          rw [hsec0 s]
          exact hlevel s g k hk
        · have hvFam : v ∈ Fam.T0 := by
            rcases Finset.mem_insert.mp hv with hv' | hv'
            · exact (hvne hv').elim
            · exact hv'
          obtain ⟨m, hm, hlevel⟩ := Fam.level v hvFam
          refine ⟨m, hm, ?_⟩
          intro s g k hk
          dsimp [sec']
          simp [hvne]
          exact hlevel s g k hk }
  refine ⟨Fam', ?_, ?_⟩
  · constructor
    · rfl
    · intro s v hv
      dsimp [Fam', sec']
      simp [hv]
  · intro s
    exact hsec0 s

end ArtinPrimitiveRoots.A1.Theta
