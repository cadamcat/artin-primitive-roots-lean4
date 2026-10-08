import ArtinPrimitiveRoots.Theta.Proofs.TH_FACTOR.Defs

set_option autoImplicit false

open NumberField IsDedekindDomain Filter Topology Complex
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

theorem unitPart_factor (v : FinPlace F) (x : (v.adicCompletion F)ˣ) :
    unifLoc v ^ ordv v x * unitPart v x = x := by
  dsimp [unitPart]
  calc
    unifLoc v ^ ordv v x *
        (x * unifLoc v ^ (-ordv v x)) =
      x * (unifLoc v ^ ordv v x * (unifLoc v ^ ordv v x)⁻¹) := by
        rw [zpow_neg]
        ac_rfl
    _ = x := by simp

theorem thFactorB_unitPart_isLocUnit (v : FinPlace F) (x : (v.adicCompletion F)ˣ) :
    IsLocUnit v (unitPart v x) := by
  have hx0 : Valued.v (x : v.adicCompletion F) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr x.ne_zero
  have hxv : Valued.v (x : v.adicCompletion F) = WithZero.exp (-ordv v x) := by
    rw [← WithZero.exp_log hx0]
    simp [ordv, WithZero.toAdd_unzero_eq_log hx0]
  have hπ : Valued.v (unifLoc v : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    change Valued.v ((unif v : F) : v.adicCompletion F) = WithZero.exp (-1 : ℤ)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
  have hval : Valued.v (unitPart v x : v.adicCompletion F) = 1 := by
    simp only [unitPart, Units.val_mul, Units.val_zpow_eq_zpow_val]
    change Valued.v ((x : v.adicCompletion F) *
      (unifLoc v : v.adicCompletion F) ^ (-ordv v x)) = 1
    rw [map_mul, map_zpow₀, hxv, hπ]
    rw [← WithZero.exp_zsmul, ← WithZero.exp_add]
    congr 1
    simp
  constructor
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hval]
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have hval' : Valued.v (((unitPart v x)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
      simp [hval]
    rw [hval']

theorem sphWeyl_data {P : CoverPackage D S H A} {G : GlobalDatum P}
    (v : FinPlace F) (hv : v ∉ S.Sf) (s : ℂ) :
    IsSection (P.loc v) (G.T v).weyl (-s) (sphWeyl P G v hv s) ∧
      sphWeyl P G v hv s 1 = (G.B v hv).weyl.e 0 ∧
      ∀ g k, k ∈ (P.tame v hv).Kmax →
        sphWeyl P G v hv s (g * k) = sphWeyl P G v hv s g := by
  have hv6 : (6 : 𝓞 F) ∉ v.asIdeal := fun h => hv (S.over6 v h)
  let τ := P.tame v hv
  let B := G.B v hv
  refine ⟨?_, ?_, ?_⟩
  · change IsSection (P.loc v) (G.T v).weyl (-s)
      (spherical_section (P.loc v) τ (G.T v).weyl B.weyl hv6 (-s)).choose
    exact (spherical_section (P.loc v) τ (G.T v).weyl B.weyl hv6 (-s)).choose_spec.1
  · change (spherical_section (P.loc v) τ (G.T v).weyl B.weyl hv6 (-s)).choose 1 = _
    exact (spherical_section (P.loc v) τ (G.T v).weyl B.weyl hv6 (-s)).choose_spec.2.1
  · intro g k hk
    change (spherical_section (P.loc v) τ (G.T v).weyl B.weyl hv6 (-s)).choose (g * k) = _
    exact (spherical_section (P.loc v) τ (G.T v).weyl B.weyl hv6 (-s)).choose_spec.2.2.1 g k hk

theorem cv_analytic (v : FinPlace F) :
    AnalyticOnNhd ℂ (fun s => cv v s) {s | 0 < s.re} := by
  intro s hs
  change 0 < s.re at hs
  have hq1 : 1 < qv v := qv_gt_one v
  have hq : 0 < qv v := lt_trans zero_lt_one hq1
  have hden : 1 - (qv v : ℂ) ^ (-6 * s) ≠ 0 := by
    intro hz
    have hpow : (qv v : ℂ) ^ (-6 * s) = 1 := (sub_eq_zero.mp hz).symm
    have hnorm : ‖(qv v : ℂ) ^ (-6 * s)‖ < 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hq]
      apply Real.rpow_lt_one_of_one_lt_of_neg hq1
      rw [Complex.mul_re]
      norm_num
      nlinarith [hs]
    rw [hpow] at hnorm
    norm_num at hnorm
  dsimp [cv]
  fun_prop (disch := aesop)

theorem spherical_jacquet_analytic {P : CoverPackage D S H A} {G : GlobalDatum P}
    (μ : ∀ v : FinPlace F, LocHaar v) (v : FinPlace F) (hv : v ∉ S.Sf)
    (f : ℂ → (P.loc v).L → (G.T v).V)
    (hsec : ∀ s, IsSection (P.loc v) (G.T v) s (f s))
    (h1 : ∀ s, f s 1 = (G.B v hv).e 0)
    (hK : ∀ s g k, k ∈ (P.tame v hv).Kmax → f s (g * k) = f s g)
    (g : (P.loc v).L) :
    AnalyticOnNhd ℂ (fun s => jacquet (P.loc v) A (μ v)
      (rtr g (f s))) {s | 0 < s.re} := by
  intro s hs
  have hv6 : (6 : 𝓞 F) ∉ v.asIdeal := fun h => hv (S.over6 v h)
  have hd : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal := fun h => hv (S.different_mem v h)
  let τ := P.tame v hv
  let B := G.B v hv
  obtain ⟨x, y, ζ, k, hk, hg⟩ := iwasawa_tame (P.loc v) τ g
  have hdrop (z : ℂ) : rtr g (f z) =
      rtr ((P.loc v).n (Multiplicative.ofAdd x) * (P.loc v).z ζ * (P.loc v).a y) (f z) := by
    funext t
    simp only [rtr]
    rw [hg]
    simpa [mul_assoc] using hK z (t *
      ((P.loc v).n (Multiplicative.ofAdd x) * (P.loc v).z ζ * (P.loc v).a y)) k hk
  have hcomp (z : ℂ) :
      rtr ((P.loc v).n (Multiplicative.ofAdd x) * (P.loc v).z ζ * (P.loc v).a y) (f z) =
        rtr ((P.loc v).n (Multiplicative.ofAdd x))
          (rtr ((P.loc v).z ζ) (rtr ((P.loc v).a y) (f z))) := by
    funext t
    simp [rtr, mul_assoc]
  have hJred (z : ℂ) : jacquet (P.loc v) A (μ v) (rtr g (f z)) =
      A.ψ v x • (((ζ : ℂˣ) : ℂ) •
        jacquet (P.loc v) A (μ v) (rtr ((P.loc v).a y) (f z))) := by
    have ha : IsSection (P.loc v) (G.T v) z (rtr ((P.loc v).a y) (f z)) :=
      (hsec z).rtr ((P.loc v).a y)
    have hz : IsSection (P.loc v) (G.T v) z
        (rtr ((P.loc v).z ζ) (rtr ((P.loc v).a y) (f z))) :=
      ha.rtr ((P.loc v).z ζ)
    calc
      _ = jacquet (P.loc v) A (μ v)
          (rtr ((P.loc v).n (Multiplicative.ofAdd x) * (P.loc v).z ζ * (P.loc v).a y) (f z)) :=
            congrArg (jacquet (P.loc v) A (μ v)) (hdrop z)
      _ = jacquet (P.loc v) A (μ v)
          (rtr ((P.loc v).n (Multiplicative.ofAdd x))
            (rtr ((P.loc v).z ζ) (rtr ((P.loc v).a y) (f z)))) :=
            congrArg (jacquet (P.loc v) A (μ v)) (hcomp z)
      _ = A.ψ v x • jacquet (P.loc v) A (μ v)
          (rtr ((P.loc v).z ζ) (rtr ((P.loc v).a y) (f z))) :=
            (jacquet_equiv (P.loc v) (G.T v) A (μ v) z _ hz).1 x
      _ = A.ψ v x • (((ζ : ℂˣ) : ℂ) •
          jacquet (P.loc v) A (μ v) (rtr ((P.loc v).a y) (f z))) := by
            rw [(jacquet_equiv (P.loc v) (G.T v) A (μ v) z _ ha).2 ζ]
  let e := ordv v y
  let u := unitPart v y
  have hu : IsLocUnit v u := thFactorB_unitPart_isLocUnit v y
  have hy : unifLoc v ^ e * u = y := unitPart_factor v y
  by_cases he : e < 0
  · have hzero (z : ℂ) :
        jacquet (P.loc v) A (μ v) (rtr ((P.loc v).a y) (f z)) = 0 := by
      rw [← hy]
      rw [jacquet_spherical_unit (P.loc v) τ (G.T v) A (μ v) hv6 z
        (f z) (hsec z) (hK z) e u hu]
      rw [jacquet_spherical_neg (P.loc v) τ (G.T v) B A (μ v) hv6 hd z
        (f z) (hsec z) (hK z) e he]
      simp
    have hfun : (fun z => jacquet (P.loc v) A (μ v) (rtr g (f z))) = fun _ => 0 := by
      funext z
      rw [hJred z, hzero z]
      simp
    rw [hfun]
    fun_prop
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt he)
    have hyN : unifLoc v ^ (n : ℤ) * u = y := by
      simpa [e, hn] using hy
    let formula (z : ℂ) : (G.T v).V :=
      ((qv v : ℂ) ^ (-(n : ℂ) * (1 / 2 - z))) •
        (((1 + (1 - (qv v : ℂ)⁻¹) *
          ∑ j ∈ Finset.Icc 1 (n / 3), (qv v : ℂ) ^ (-6 * (j : ℂ) * z)) •
            B.e (-(n : ZMod 3))) +
          (((qv v : ℂ) ^ (-2 * ((n : ℂ) + 1) * z) * shellTerm D A v (n + 1)) •
            B.e ((n : ZMod 3) + 2)))
    have hunit (z : ℂ) :
        jacquet (P.loc v) A (μ v) (rtr ((P.loc v).a y) (f z)) =
          localChi D v u ^ (2 * (n : ℤ)) •
            jacquet (P.loc v) A (μ v)
              (rtr ((P.loc v).a (unifLoc v ^ (n : ℤ))) (f z)) := by
      rw [← hyN]
      exact jacquet_spherical_unit (P.loc v) τ (G.T v) A (μ v) hv6 z
        (f z) (hsec z) (hK z) (n : ℤ) u hu
    have hbase (z : ℂ) :
        jacquet (P.loc v) A (μ v)
          (rtr ((P.loc v).a (unifLoc v ^ (n : ℤ))) (f z)) = formula z := by
      exact jacquet_spherical (P.loc v) τ (G.T v) B A (μ v) hv6 hd z
        (f z) (hsec z) (h1 z) (hK z) n
    have hfun : (fun z => jacquet (P.loc v) A (μ v) (rtr g (f z))) =
        fun z => A.ψ v x • (((ζ : ℂˣ) : ℂ) •
          (localChi D v u ^ (2 * (n : ℤ)) • formula z)) := by
      funext z
      rw [hJred z, hunit z, hbase z]
    have hq1 : 1 < qv v := qv_gt_one v
    have hq : 0 < qv v := lt_trans zero_lt_one hq1
    have hqmem : (qv v : ℂ) ∈ Complex.slitPlane :=
      Complex.ofReal_mem_slitPlane.mpr hq
    let c : ℂ := A.ψ v x * ((ζ : ℂˣ) : ℂ) * localChi D v u ^ (2 * (n : ℤ))
    have hscaledEq : (fun z => A.ψ v x • (((ζ : ℂˣ) : ℂ) •
          (localChi D v u ^ (2 * (n : ℤ)) • formula z))) =
        fun z => c • formula z := by
      funext z
      simp [c, smul_smul, mul_assoc]
    have hformula : AnalyticAt ℂ formula s := by
      dsimp [formula]
      fun_prop (disch := aesop)
    have hscaled : AnalyticAt ℂ (fun z => c • formula z) s := by
      have hc : AnalyticAt ℂ (fun _ : ℂ => c) s := by fun_prop
      exact hc.smul hformula
    rw [hfun]
    rw [hscaledEq]
    exact hscaled

theorem sphWeyl_analytic {P : CoverPackage D S H A} {G : GlobalDatum P}
    (v : FinPlace F) (hv : v ∉ S.Sf) (g : (P.loc v).L) :
    AnalyticOnNhd ℂ (fun s => sphWeyl P G v hv s g) {s | 0 < s.re} := by
  intro s hs
  have hv6 : (6 : 𝓞 F) ∉ v.asIdeal := fun h => hv (S.over6 v h)
  let τ := P.tame v hv
  let B := G.B v hv
  obtain ⟨x, y, ζ, k, hk, hg⟩ := iwasawa_tame (P.loc v) τ g
  have hsec (z : ℂ) : IsSection (P.loc v) (G.T v).weyl (-z) (sphWeyl P G v hv z) := by
    simpa [sphWeyl, τ, B] using
      (spherical_section (P.loc v) τ (G.T v).weyl B.weyl hv6 (-z)).choose_spec.1
  have hnorm (z : ℂ) : sphWeyl P G v hv z 1 = B.weyl.e 0 := by
    change (spherical_section (P.loc v) τ (G.T v).weyl B.weyl hv6 (-z)).choose 1 = _
    exact (spherical_section (P.loc v) τ (G.T v).weyl B.weyl hv6 (-z)).choose_spec.2.1
  have hinv (z : ℂ) : ∀ g' k', k' ∈ τ.Kmax →
      sphWeyl P G v hv z (g' * k') = sphWeyl P G v hv z g' := by
    intro g' k' hk'
    change (spherical_section (P.loc v) τ (G.T v).weyl B.weyl hv6 (-z)).choose (g' * k') = _
    exact (spherical_section (P.loc v) τ (G.T v).weyl B.weyl hv6 (-z)).choose_spec.2.2.1 g' k' hk'
  have hrpos : 0 < absFin v (y : v.adicCompletion F) :=
    absFin_pos (Units.ne_zero y)
  have hval (z : ℂ) : sphWeyl P G v hv z g =
      ((ζ : ℂˣ) : ℂ) • ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 - z)) •
        (G.T v).weyl.σa y (B.weyl.e 0) := by
    rw [hg]
    have hz : (P.loc v).z ζ * (P.loc v).n (Multiplicative.ofAdd x) =
        (P.loc v).n (Multiplicative.ofAdd x) * (P.loc v).z ζ := by
      exact (P.loc v).z_central ζ _
    have hfactor :
        (P.loc v).n (Multiplicative.ofAdd x) * (P.loc v).z ζ * (P.loc v).a y * k =
          (P.loc v).z ζ * ((P.loc v).n (Multiplicative.ofAdd x) * (P.loc v).a y * k) := by
      calc
        _ = ((P.loc v).z ζ * (P.loc v).n (Multiplicative.ofAdd x)) *
            (P.loc v).a y * k := by rw [hz.symm]
        _ = _ := by simp only [mul_assoc]
    have hkval : sphWeyl P G v hv z k = B.weyl.e 0 := by
      change (spherical_section (P.loc v) τ (G.T v).weyl B.weyl hv6 (-z)).choose k = _
      calc
        _ = (spherical_section (P.loc v) τ (G.T v).weyl B.weyl hv6 (-z)).choose 1 := by
          simpa only [one_mul] using
            (spherical_section (P.loc v) τ (G.T v).weyl B.weyl hv6 (-z)).choose_spec.2.2.1 1 k hk
        _ = B.weyl.e 0 :=
          (spherical_section (P.loc v) τ (G.T v).weyl B.weyl hv6 (-z)).choose_spec.2.1
    rw [hfactor]
    rw [(hsec z).2.1 ζ _]
    rw [(hsec z).1 x y k]
    rw [hkval]
    rfl
  rw [show (fun z : ℂ => sphWeyl P G v hv z g) =
      fun z => ((ζ : ℂˣ) : ℂ) • ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 - z)) •
        (G.T v).weyl.σa y (B.weyl.e 0) from funext hval]
  fun_prop (disch := aesop)

theorem sphericalIntertwine_analytic {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ)
    (hT : Fam.T0 = S.Sf) (v : FinPlace F) (hv : v ∉ S.Sf)
    (g : (P.loc v).L) :
    AnalyticOnNhd ℂ
      (fun s => intertwine (P.loc v) (μ v) ((Fam.sec s).f v) g) {s | 0 < s.re} := by
  intro s hs
  change 0 < s.re at hs
  have hvFam : v ∉ Fam.T0 := by rw [hT]; exact hv
  have hv6 : (6 : 𝓞 F) ∉ v.asIdeal := fun h => hv (S.over6 v h)
  have hvsec (z : ℂ) : v ∉ (Fam.sec z).T0 := by
    rw [Fam.T0_eq z]
    exact hvFam
  have hsrc (z : ℂ) : IsSection (P.loc v) (G.T v) z ((Fam.sec z).f v) :=
    (Fam.sec z).f_sec v
  have hsrc1 (z : ℂ) : (Fam.sec z).f v 1 = (G.B v hv).e 0 :=
    ((Fam.sec z).f_sph v (hvsec z)).1
  have hsrcK (z : ℂ) : ∀ g' k', k' ∈ (P.tame v hv).Kmax →
      (Fam.sec z).f v (g' * k') = (Fam.sec z).f v g' := by
    intro g' k' hk
    exact (Fam.sec z).f_sph v (hvsec z) |>.2 g' k' hk
  have hpoint (z : ℂ) (hz : 0 < z.re) :
      intertwine (P.loc v) (μ v) ((Fam.sec z).f v) g =
        cv v z • sphWeyl P G v hv z g := by
    have hsph := sphWeyl_data (P := P) (G := G) v hv z
    have hM := intertwine_spherical (P.loc v) (P.tame v hv) (G.T v) (G.B v hv)
      (μ v) hv6 z hz ((Fam.sec z).f v) (hsrc z) (hsrc1 z) (hsrcK z)
      (sphWeyl P G v hv z) hsph.1 hsph.2.1 hsph.2.2
    exact congrFun hM g
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hdom : {z : ℂ | 0 < z.re} ∈ 𝓝 s := hopen.mem_nhds hs
  have hEq : (fun z => intertwine (P.loc v) (μ v) ((Fam.sec z).f v) g) =ᶠ[𝓝 s]
      fun z => cv v z • sphWeyl P G v hv z g := by
    filter_upwards [hdom] with z hz
    exact hpoint z hz
  exact ((cv_analytic v s hs).smul (sphWeyl_analytic (P := P) (G := G) v hv g s hs)).congr hEq.symm

def translateLocalAt {P : CoverPackage D S H A} {G : GlobalDatum P}
    (f : ∀ w : FinPlace F, (P.loc w).L → (G.T w).V)
    (v : FinPlace F) (k : (P.loc v).L) :
    ∀ w : FinPlace F, (P.loc w).L → (G.T w).V := by
  intro w
  exact if h : w = v then h.symm ▸ rtr k (f v) else f w

@[simp] theorem translateLocalAt_self {P : CoverPackage D S H A} {G : GlobalDatum P}
    (f : ∀ w : FinPlace F, (P.loc w).L → (G.T w).V)
    (v : FinPlace F) (k : (P.loc v).L) :
    translateLocalAt f v k v = rtr k (f v) := by
  simp [translateLocalAt]

theorem translateLocalAt_of_ne {P : CoverPackage D S H A} {G : GlobalDatum P}
    (f : ∀ w : FinPlace F, (P.loc w).L → (G.T w).V)
    (v w : FinPlace F) (k : (P.loc v).L) (h : w ≠ v) :
    translateLocalAt f v k w = f w := by
  simp [translateLocalAt, h]

noncomputable def translateExteriorFamily {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ)
    (hT : Fam.T0 = S.Sf) (v : FinPlace F) (hv : v ∉ S.Sf) (k : (P.loc v).L) :
    AnalyticFamily P G μ := by
  have hvFam : v ∉ Fam.T0 := by rw [hT]; exact hv
  have hvsec (s : ℂ) : v ∉ (Fam.sec s).T0 := by rw [Fam.T0_eq s]; exact hvFam
  let sec' : ∀ s, GlobalSection P G s := fun s =>
    { (Fam.sec s) with
      T0 := insert v (Fam.sec s).T0
      sub := by
        intro w hw
        exact Finset.mem_insert_of_mem ((Fam.sec s).sub hw)
      f := translateLocalAt (Fam.sec s).f v k
      f_sec := by
        intro w
        by_cases h : w = v
        · subst w
          simpa [translateLocalAt] using ((Fam.sec s).f_sec v).rtr k
        · simpa [translateLocalAt, h] using (Fam.sec s).f_sec w
      f_sph := by
        intro w hw
        have hOld : w ∉ (Fam.sec s).T0 := by
          intro hm
          exact hw (Finset.mem_insert_of_mem hm)
        have hne : w ≠ v := by
          intro hEq
          subst w
          exact hw (Finset.mem_insert_self _ _)
        simpa [translateLocalAt, hne] using (Fam.sec s).f_sph w hOld }
  refine
    { sec := sec'
      T0 := insert v Fam.T0
      T0_eq := fun s => congrArg (fun T => insert v T) (Fam.T0_eq s)
      fC_sph := Fam.fC_sph
      f_analytic := ?_
      M_analytic := ?_
      J_analytic := ?_
      level := ?_ }
  · intro w g
    by_cases h : w = v
    · subst w
      simpa [sec', translateLocalAt, rtr] using Fam.f_analytic v (g * k)
    · simpa [sec', translateLocalAt, h] using Fam.f_analytic w g
  · intro w hw g
    by_cases h : w = v
    · subst w
      have hEq : (fun s => intertwine (P.loc v) (μ v) ((sec' s).f v) g) =
          fun s => intertwine (P.loc v) (μ v) ((Fam.sec s).f v) (g * k) := by
        funext s
        rw [show (sec' s).f v = rtr k ((Fam.sec s).f v) by simp [sec', translateLocalAt]]
        have h := congrFun (intertwine_rtr (P.loc v) (μ v) ((Fam.sec s).f v) k) g
        simpa [rtr] using h
      rw [hEq]
      exact sphericalIntertwine_analytic Fam hT v hv (g * k)
    · have hwOld : w ∈ Fam.T0 := by
        rcases Finset.mem_insert.mp hw with hEq | hwOld
        · exact (h hEq).elim
        · exact hwOld
      simpa [sec', translateLocalAt, h] using Fam.M_analytic w hwOld g
  · intro w hw g
    by_cases h : w = v
    · subst w
      have hsec : ∀ s, IsSection (P.loc v) (G.T v) s ((Fam.sec s).f v) :=
        fun s => (Fam.sec s).f_sec v
      have h1 : ∀ s, (Fam.sec s).f v 1 = (G.B v hv).e 0 := fun s =>
        (Fam.sec s).f_sph v (hvsec s) |>.1
      have hK : ∀ s g' k', k' ∈ (P.tame v hv).Kmax →
          (Fam.sec s).f v (g' * k') = (Fam.sec s).f v g' := by
        intro s g' k' hk
        exact (Fam.sec s).f_sph v (hvsec s) |>.2 g' k' hk
      have hEq : (fun s => jacquet (P.loc v) A (μ v)
          (rtr g ((sec' s).f v))) =
          fun s => jacquet (P.loc v) A (μ v)
            (rtr (g * k) ((Fam.sec s).f v)) := by
        funext s
        have htrans : rtr g ((sec' s).f v) = rtr (g * k) ((Fam.sec s).f v) := by
          have hself : (sec' s).f v = rtr k ((Fam.sec s).f v) := by
            simp [sec', translateLocalAt]
          rw [hself]
          funext z
          simp [rtr, mul_assoc]
        exact congrArg (jacquet (P.loc v) A (μ v)) htrans
      rw [hEq]
      exact spherical_jacquet_analytic μ v hv (fun s => (Fam.sec s).f v)
        hsec h1 hK (g * k)
    · have hwOld : w ∈ Fam.T0 := by
        rcases Finset.mem_insert.mp hw with hEq | hwOld
        · exact (h hEq).elim
        · exact hwOld
      simpa [sec', translateLocalAt, h] using Fam.J_analytic w hwOld g
  · intro w hw
    by_cases h : w = v
    · subst w
      let τ := P.tame v hv
      let U : Set (P.loc v).L := {q | k⁻¹ * q * k ∈ τ.Kmax}
      have hcont : Continuous (fun q : (P.loc v).L => k⁻¹ * q * k) := by fun_prop
      have hopen : IsOpen U := by
        change IsOpen ((fun q : (P.loc v).L => k⁻¹ * q * k) ⁻¹' (τ.Kmax : Set (P.loc v).L))
        exact τ.open_.preimage hcont
      have hone : U ∈ 𝓝 (1 : (P.loc v).L) := hopen.mem_nhds (by simp [U])
      obtain ⟨m, hm0, hmU⟩ := (P.loc v).Kc_nhds U hone
      refine ⟨m, hm0, ?_⟩
      intro s g' q hq
      have hconj : k⁻¹ * q * k ∈ τ.Kmax := hmU hq
      have hbaseK : ∀ g'', (Fam.sec s).f v (g'' * (k⁻¹ * q * k)) = (Fam.sec s).f v g'' :=
        fun g'' => (Fam.sec s).f_sph v (hvsec s) |>.2 g'' (k⁻¹ * q * k) hconj
      have halg : g' * q * k = (g' * k) * (k⁻¹ * q * k) := by group
      have hself : (sec' s).f v = rtr k ((Fam.sec s).f v) := by
        simp [sec', translateLocalAt]
      rw [hself]
      simp only [rtr]
      rw [halg]
      exact hbaseK (g' * k)
    · have hwOld : w ∈ Fam.T0 := by
        rcases Finset.mem_insert.mp hw with hEq | hwOld
        · exact (h hEq).elim
        · exact hwOld
      obtain ⟨m, hm0, hlevel⟩ := Fam.level w hwOld
      refine ⟨m, hm0, ?_⟩
      intro s g' q hq
      simpa [sec', translateLocalAt, h] using hlevel s g' q hq

theorem scalarOf_translateExteriorFamily {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ)
    (hT : Fam.T0 = S.Sf) (v : FinPlace F) (hv : v ∉ S.Sf)
    (k : (P.loc v).L) (s : ℂ) (x : P.RP) :
    scalarOf P G ((translateExteriorFamily Fam hT v hv k).sec s).f
        ((translateExteriorFamily Fam hT v hv k).sec s).fC (P.q x) =
      scalarOf P G (Fam.sec s).f (Fam.sec s).fC (P.q x * P.emb v k) := by
  classical
  let TF := translateExteriorFamily Fam hT v hv k
  have hL := scalarOf_q P G (TF.sec s) x
  have hR := scalarOf_q P G (Fam.sec s) (x * P.incl v k)
  have hprod : (∏ᶠ w : FinPlace F,
      G.lam w ((TF.sec s).f w (P.compF w x))) =
      ∏ᶠ w : FinPlace F,
        G.lam w ((Fam.sec s).f w (P.compF w (x * P.incl v k))) := by
    apply finprod_congr
    intro w
    by_cases h : w = v
    · subst w
      simp [TF, translateExteriorFamily, translateLocalAt, P.incl_compF, map_mul, rtr]
    · have hother : P.compF w (P.incl v k) = 1 := P.incl_compF_other v w (Ne.symm h) k
      simp [TF, translateExteriorFamily, translateLocalAt, h, map_mul, hother, rtr]
  have harch : (∏ w : InfinitePlace F,
      (TF.sec s).fC w (P.compC w x)) =
      ∏ w : InfinitePlace F,
        (Fam.sec s).fC w (P.compC w (x * P.incl v k)) := by
    apply Finset.prod_congr rfl
    intro w hw
    have hincl : P.compC w (P.incl v k) = 1 := P.incl_compC v k w
    simp [TF, translateExteriorFamily, map_mul, hincl]
  have hq : P.q (x * P.incl v k) = P.q x * P.emb v k := by
    rw [map_mul, P.q_incl]
  calc
    scalarOf P G (TF.sec s).f (TF.sec s).fC (P.q x) =
        (∏ᶠ w : FinPlace F, G.lam w ((TF.sec s).f w (P.compF w x))) *
          ∏ w : InfinitePlace F, (TF.sec s).fC w (P.compC w x) := hL.2
    _ = (∏ᶠ w : FinPlace F,
          G.lam w ((Fam.sec s).f w (P.compF w (x * P.incl v k)))) *
          ∏ w : InfinitePlace F, (Fam.sec s).fC w (P.compC w (x * P.incl v k)) := by
            rw [hprod, harch]
    _ = scalarOf P G (Fam.sec s).f (Fam.sec s).fC (P.q x * P.emb v k) := by
            rw [← hq]
            exact hR.2.symm

def thetaWhitAdapted {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ) (g : P.tc.G) : Prop :=
  ∃ (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (Pd : Set (InfinitePlace F → ℂ)),
    𝔞 ≠ 0 ∧
      (∀ s, ∀ ξ, ξ ∈ (𝔞 : Submodule (𝓞 F) F) → ∀ h,
        scalarOf P G (Fam.sec s).f (Fam.sec s).fC (h * (g⁻¹ * nFin P ξ * g)) =
          scalarOf P G (Fam.sec s).f (Fam.sec s).fC h) ∧
      MeasureTheory.IsAddFundamentalDomain
        ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom)
        Pd MeasureTheory.volume ∧ Bornology.IsBounded Pd ∧
      ∀ ξ, ξ ∈ (𝔞 : Submodule (𝓞 F) F) → psiInf 1 (infEmbA ξ) = 1

theorem thetaWhit_translateExteriorFamily {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ)
    (hT : Fam.T0 = S.Sf) (v : FinPlace F) (hv : v ∉ S.Sf)
    (k : (P.loc v).L) (C : ContinuedEis Fam)
    (C' : ContinuedEis (translateExteriorFamily Fam hT v hv k)) (g : P.tc.G) :
    thetaWhit C' g = thetaWhit C (g * P.emb v k) := by
  classical
  let TF := translateExteriorFamily Fam hT v hv k
  let E := P.emb v k
  have hscalar (s : ℂ) (y : P.tc.G) :
      scalarOf P G (TF.sec s).f (TF.sec s).fC y =
        scalarOf P G (Fam.sec s).f (Fam.sec s).fC (y * E) := by
    obtain ⟨x, hx⟩ := P.q_surj y
    calc
      scalarOf P G (TF.sec s).f (TF.sec s).fC y =
          scalarOf P G (TF.sec s).f (TF.sec s).fC (P.q x) := by rw [← hx]
      _ = scalarOf P G (Fam.sec s).f (Fam.sec s).fC (P.q x * E) :=
          scalarOf_translateExteriorFamily Fam hT v hv k s x
      _ = scalarOf P G (Fam.sec s).f (Fam.sec s).fC (y * E) := by rw [hx]
  have hBack (hB : thetaWhitAdapted Fam (g * E)) : thetaWhitAdapted TF g := by
    rcases hB with ⟨𝔞, Pd, h𝔞, hfix, hPd, hb, hψ⟩
    refine ⟨𝔞, Pd, h𝔞, ?_, hPd, hb, hψ⟩
    intro s ξ hξ h
    have hgroup : (h * E) * ((g * E)⁻¹ * nFin P ξ * (g * E)) =
        (h * (g⁻¹ * nFin P ξ * g)) * E := by group
    calc
      scalarOf P G (TF.sec s).f (TF.sec s).fC (h * (g⁻¹ * nFin P ξ * g)) =
        scalarOf P G (Fam.sec s).f (Fam.sec s).fC
          ((h * (g⁻¹ * nFin P ξ * g)) * E) := hscalar s _
      _ = scalarOf P G (Fam.sec s).f (Fam.sec s).fC
          ((h * E) * ((g * E)⁻¹ * nFin P ξ * (g * E))) := by
            exact congrArg (scalarOf P G (Fam.sec s).f (Fam.sec s).fC) hgroup.symm
      _ = scalarOf P G (Fam.sec s).f (Fam.sec s).fC (h * E) := hfix s ξ hξ (h * E)
      _ = scalarOf P G (TF.sec s).f (TF.sec s).fC h := (hscalar s h).symm
  have hOff : ∀ s w, w ≠ v → (TF.sec s).f w = (Fam.sec s).f w := by
    intro s w hw
    simpa [TF, translateExteriorFamily, translateLocalAt, hw]
  have hAt : ∀ s, (TF.sec s).f v = rtr k ((Fam.sec s).f v) := by
    intro s
    simpa [TF, translateExteriorFamily]
  have htheta : ∀ z : P.tc.G, C'.theta z = C.theta (z * E) :=
    (theta_linear_translate (P := P) (G := G) (μ := μ) v Fam TF TF C C' C').2 k hOff hAt
  by_cases hA : thetaWhitAdapted TF g
  · rcases hA with ⟨𝔞, Pd, h𝔞, hfixA, hPd, hb, hψ⟩
    have hfixB : ∀ s, ∀ ξ, ξ ∈ (𝔞 : Submodule (𝓞 F) F) → ∀ h,
        scalarOf P G (Fam.sec s).f (Fam.sec s).fC
            (h * ((g * E)⁻¹ * nFin P ξ * (g * E))) =
          scalarOf P G (Fam.sec s).f (Fam.sec s).fC h := by
      intro s ξ hξ h
      let h' := h * E⁻¹
      have hgroup : h * ((g * E)⁻¹ * nFin P ξ * (g * E)) =
          (h' * (g⁻¹ * nFin P ξ * g)) * E := by dsimp [h']; group
      calc
        scalarOf P G (Fam.sec s).f (Fam.sec s).fC
            (h * ((g * E)⁻¹ * nFin P ξ * (g * E))) =
          scalarOf P G (Fam.sec s).f (Fam.sec s).fC
            ((h' * (g⁻¹ * nFin P ξ * g)) * E) := by rw [hgroup]
        _ = scalarOf P G (TF.sec s).f (TF.sec s).fC
            (h' * (g⁻¹ * nFin P ξ * g)) := (hscalar s _).symm
        _ = scalarOf P G (TF.sec s).f (TF.sec s).fC h' := hfixA s ξ hξ h'
        _ = scalarOf P G (Fam.sec s).f (Fam.sec s).fC h := by
          rw [hscalar s h']
          dsimp [h']
          congr 1
          group
    have hν : ∀ ξ, ξ ∈ (𝔞 : Submodule (𝓞 F) F) →
        psiInf ((1 : Fˣ) : F) (infEmbA ξ) = 1 := by
      simpa using hψ
    have hdiag : diagGL (1 : Fˣ) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [diagGL]
    have hCoeffA := theta_fourierCoeff TF C' g 𝔞 h𝔞 hfixA Pd hPd hb (1 : Fˣ) hν
    have hCoeffB := theta_fourierCoeff Fam C (g * E) 𝔞 h𝔞 hfixB Pd hPd hb (1 : Fˣ) hν
    have hWhitA : thetaWhit C' g = torusCoeff P C'.theta g Pd 1 := by
      simpa [hdiag] using hCoeffA.symm
    have hWhitB : thetaWhit C (g * E) = torusCoeff P C.theta (g * E) Pd 1 := by
      simpa [hdiag] using hCoeffB.symm
    have htorus : torusCoeff P C'.theta g Pd 1 =
        torusCoeff P C.theta (g * E) Pd 1 := by
      unfold torusCoeff
      have hfun : (fun x => C'.theta (nInf P x * g) * psiInf (-1) x) =
          fun x => C.theta (nInf P x * (g * E)) * psiInf (-1) x := by
        funext x
        rw [htheta]
        simp [mul_assoc]
      rw [hfun]
    calc
      thetaWhit C' g = torusCoeff P C'.theta g Pd 1 := hWhitA
      _ = torusCoeff P C.theta (g * E) Pd 1 := htorus
      _ = thetaWhit C (g * E) := hWhitB.symm
  · have hB : ¬ thetaWhitAdapted Fam (g * E) := by
      intro hB
      exact hA (hBack hB)
    change (if h : thetaWhitAdapted TF g then
        torusCoeff P C'.theta g h.choose_spec.choose 1 else 0) =
      if h : thetaWhitAdapted Fam (g * E) then
        torusCoeff P C.theta (g * E) h.choose_spec.choose 1 else 0
    simp [hA, hB]

end ArtinPrimitiveRoots.A1.Theta
