import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ArtinPrimitiveRoots.Theta.Proofs.TH_COVER.CompletionCompact
import ArtinPrimitiveRoots.Vendor.TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_e

open ArtinPrimitiveRoots.A1
open ArtinPrimitiveRoots.Proofs.a1_weil_sol

variable {F : Type} [Field F] [NumberField F]

local instance completionMeasurable (v : FinPlace F) :
    MeasurableSpace (v.adicCompletion F) := borel _

local instance completionBorel (v : FinPlace F) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

private def ballZ (v : FinPlace F) (n : ℤ) : Set (v.adicCompletion F) :=
  {x | Valued.v x ≤ WithZero.exp n}

private theorem ballZ_open (v : FinPlace F) (n : ℤ) : IsOpen (ballZ v n) := by
  exact v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero

private theorem ballZ_add (v : FinPlace F) (n : ℤ) {x y : v.adicCompletion F}
    (hx : x ∈ ballZ v n) (hy : y ∈ ballZ v n) : x + y ∈ ballZ v n := by
  change Valued.v x ≤ WithZero.exp n at hx
  change Valued.v y ≤ WithZero.exp n at hy
  change Valued.v (x + y) ≤ WithZero.exp n
  exact (Valued.v.map_add x y).trans (max_le hx hy)

private theorem ballZ_neg (v : FinPlace F) (n : ℤ) {x : v.adicCompletion F}
    (hx : x ∈ ballZ v n) : -x ∈ ballZ v n := by
  change Valued.v x ≤ WithZero.exp n at hx
  change Valued.v (-x) ≤ WithZero.exp n
  simpa using hx

private theorem value_eq_exp_of_between (v : FinPlace F) (n : ℤ)
    (x : v.adicCompletion F) (hlo : WithZero.exp (n - 1) < Valued.v x)
    (hhi : Valued.v x ≤ WithZero.exp n) : Valued.v x = WithZero.exp n := by
  by_cases hx0 : Valued.v x = 0
  · rw [hx0] at hlo
    exact False.elim ((not_lt_of_ge WithZero.exp_pos.le) hlo)
  · lift Valued.v x to ℤ using hx0 with k hk
    have hklo : n - 1 < k := by
      exact WithZero.exp_lt_exp.mp hlo
    have hkhi : k ≤ n := by
      exact WithZero.exp_le_exp.mp hhi
    have hkn : k = n := by omega
    rw [hkn]

private theorem ballZ_sdiff_eq_shell (v : FinPlace F) (n : ℤ) :
    ballZ v n \ ballZ v (n - 1) = {x | Valued.v x = WithZero.exp n} := by
  ext x
  simp only [Set.mem_sdiff, Set.mem_setOf_eq, ballZ]
  constructor
  · rintro ⟨hhi, hlo⟩
    apply value_eq_exp_of_between v n x _ hhi
    exact lt_of_not_ge hlo
  · intro hx
    constructor
    · rw [hx]
    · intro hle
      rw [hx] at hle
      have : WithZero.exp n ≤ WithZero.exp (n - 1) := hle
      exact (not_le_of_gt (WithZero.exp_lt_exp.mpr (by omega))) this

private theorem ballZ_compact (v : FinPlace F) (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) (n : ℤ) :
    IsCompact (ballZ v n) := by
  let O := v.adicCompletionIntegers F
  letI : CompactSpace O := ArtinPrimitiveRoots.Proofs.th_cover_sol.compact_adicCompletionIntegers v
  let f : O → v.adicCompletion F := fun x => ((π ^ (-n) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x.1
  have hpow (z : ℤ) : Valued.v ((π ^ z : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      WithZero.exp (-z) := by
    rw [show Valued.v ((π ^ z : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      Valued.v (π : v.adicCompletion F) ^ z by simp, hπ, ← WithZero.exp_zsmul]
    simp only [zsmul_eq_mul]
    congr 1
    norm_num
  have hrange : Set.range f = ballZ v n := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      change Valued.v (((π ^ (-n) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x.1) ≤ _
      rw [Valuation.map_mul, hpow]
      simp only [neg_neg]
      have hx : Valued.v (x.1 : v.adicCompletion F) ≤ 1 := by
        rw [← HeightOneSpectrum.mem_adicCompletionIntegers]
        exact x.2
      calc
        WithZero.exp n * Valued.v (x.1 : v.adicCompletion F) ≤ WithZero.exp n * 1 := by
          gcongr
        _ = WithZero.exp n := by simp
    · intro hy
      change Valued.v y ≤ WithZero.exp n at hy
      let y' : v.adicCompletion F :=
        ((π ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y
      have hy' : Valued.v y' ≤ 1 := by
        calc
          Valued.v y' = WithZero.exp (-n) * Valued.v y := by
            dsimp [y']
            rw [Valuation.map_mul, hpow]
          _ ≤ WithZero.exp (-n) * WithZero.exp n := by gcongr
          _ = 1 := by rw [← WithZero.exp_add]; simp
      let x : O := ⟨y', by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers]
        exact hy'⟩
      refine ⟨x, ?_⟩
      dsimp [f, x, y']
      have hcancel :
          ((π ^ (-n) : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
              ((π ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
        have hu : π ^ (-n) * π ^ n = (1 : (v.adicCompletion F)ˣ) := by group
        simpa only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_one] using
          congrArg (fun z : (v.adicCompletion F)ˣ => (z : v.adicCompletion F)) hu
      rw [show
        ((π ^ (-n) : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
            (((π ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y) = y by
          rw [← mul_assoc, hcancel, one_mul]]
  have hf : Continuous f := by
    dsimp [f]
    exact (continuous_const_mul _).comp continuous_subtype_val
  rw [← hrange]
  exact isCompact_range hf

private theorem addChar_continuous (A : AddCharData F) (v : FinPlace F) :
    Continuous (A.ψ v) := by
  have hloc : IsLocallyConstant (A.ψ v) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    let U : Set (v.adicCompletion F) := {y | y - x ∈ v.adicCompletionIntegers F}
    have hUopen : IsOpen U := by
      exact (Valued.isOpen_valuationSubring (v.adicCompletion F)).preimage
        (continuous_id.sub continuous_const)
    refine ⟨U, hUopen, ?_, ?_⟩
    · change x - x ∈ v.adicCompletionIntegers F
      simp [HeightOneSpectrum.mem_adicCompletionIntegers]
    · intro y hy
      have hψ := (A.ψ v).map_add_eq_mul x (y - x)
      have hxy : x + (y - x) = y := by ring
      rw [hxy, A.integral v (y - x) hy, mul_one] at hψ
      exact hψ
  exact hloc.continuous

private theorem integral_addChar_zero_on_ball (A : AddCharData F) (v : FinPlace F)
    (μ : Measure (v.adicCompletion F)) [Measure.IsAddHaarMeasure μ]
    (m : ℤ) (k b : v.adicCompletion F)
    (hb : b ∈ ballZ v m) (hψ : A.ψ v (k * b) ≠ 1) :
    ∫ x in ballZ v m, A.ψ v (k * x) ∂μ = 0 := by
  classical
  let f : v.adicCompletion F → ℂ :=
    (ballZ v m).indicator (fun x => A.ψ v (k * x))
  have hcoset (x : v.adicCompletion F) : b + x ∈ ballZ v m ↔ x ∈ ballZ v m := by
    constructor
    · intro hx
      have h := ballZ_add v m hx (ballZ_neg v m hb)
      simpa [add_assoc] using h
    · intro hx
      have h := ballZ_add v m hb hx
      simpa [add_comm] using h
  have htrans (x : v.adicCompletion F) : f (b + x) = A.ψ v (k * b) * f x := by
    by_cases hx : x ∈ ballZ v m
    · have hbx : b + x ∈ ballZ v m := (hcoset x).2 hx
      have hchar : A.ψ v (k * (b + x)) = A.ψ v (k * b) * A.ψ v (k * x) := by
        rw [show k * (b + x) = k * b + k * x by ring, AddChar.map_add_eq_mul]
      simp [f, hx, hbx, hchar]
    · have hbx : b + x ∉ ballZ v m := fun h => hx ((hcoset x).1 h)
      simp [f, hx, hbx]
  let I : ℂ := ∫ x, f x ∂μ
  have hI : I = A.ψ v (k * b) * I := by
    calc
      I = ∫ x, f (b + x) ∂μ := (integral_add_left_eq_self f b).symm
      _ = ∫ x, A.ψ v (k * b) * f x ∂μ := by
        rw [show (fun x => f (b + x)) = fun x => A.ψ v (k * b) * f x from funext htrans]
      _ = A.ψ v (k * b) * I := by rw [integral_const_mul]
  have hmul : (A.ψ v (k * b) - 1) * I = 0 := by
    calc
      (A.ψ v (k * b) - 1) * I = A.ψ v (k * b) * I - I := by ring
      _ = I - I := by rw [← hI]
      _ = 0 := by ring
  have hcoef : A.ψ v (k * b) - 1 ≠ 0 := sub_ne_zero.mpr hψ
  have hI0 : I = 0 := (mul_eq_zero.mp hmul).resolve_left hcoef
  have hmass : ∫ x in ballZ v m, A.ψ v (k * x) ∂μ = 0 := by
    rw [← integral_indicator (ballZ_open v m).measurableSet]
    simpa [I, f] using hI0
  exact hmass

variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private theorem exterior_two_valuation (S : SData F CE condη) (v : FinPlace F)
    (hv : v ∉ S.Sf) : Valued.v (2 : v.adicCompletion F) = 1 := by
  let r : 𝓞 F := 2
  have h6not : (6 : 𝓞 F) ∉ v.asIdeal := by
    intro h6
    exact hv (S.over6 v h6)
  have h2not : r ∉ v.asIdeal := by
    intro h2
    apply h6not
    simpa only [r, show (3 : 𝓞 F) * 2 = 6 by norm_num] using
      v.asIdeal.mul_mem_left (3 : 𝓞 F) h2
  have hle : v.valuation F (algebraMap (𝓞 F) F r) ≤ 1 :=
    v.valuation_le_one (K := F) r
  have hnotlt : ¬ v.valuation F (algebraMap (𝓞 F) F r) < 1 := by
    intro hlt
    have hval : v.valuation F (algebraMap (𝓞 F) F r) < 1 := hlt
    have hmem : r ∈ v.asIdeal := (v.valuation_lt_one_iff_mem (K := F) (r := r)).mp hval
    exact h2not hmem
  have hglobal : v.valuation F (algebraMap (𝓞 F) F r) = 1 :=
    le_antisymm hle (le_of_not_gt hnotlt)
  have hglobalF : v.valuation F (r : F) = 1 := by
    change v.valuation F (algebraMap (𝓞 F) F r) = 1
    exact hglobal
  have hcastF : algebraMap F (v.adicCompletion F) (r : F) =
      (2 : v.adicCompletion F) := by
    dsimp [r]
    exact map_natCast (algebraMap F (v.adicCompletion F)) 2
  calc
    Valued.v (2 : v.adicCompletion F) =
        Valued.v (algebraMap F (v.adicCompletion F) (r : F)) := congrArg Valued.v hcastF.symm
    _ = v.valuation F (r : F) := v.valuedAdicCompletion_eq_valuation' (r : F)
    _ = 1 := hglobalF

theorem exterior_global_unit_valuation (v : FinPlace F) (a : Fˣ)
    (ha : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) = 0) :
    Valued.v (toLoc v a : v.adicCompletion F) = 1 := by
  have hcount := ArtinPrimitiveRoots.A2.qs_nq0_count_spanSingleton_eq_neg_log_valuation
    v (a : F) a.ne_zero
  rw [hcount] at ha
  have hlog : WithZero.log (v.valuation F (a : F)) = 0 := by omega
  have hglobal : v.valuation F (a : F) = 1 := by
    have hne : v.valuation F (a : F) ≠ 0 := (v.valuation F).ne_zero_iff.mpr a.ne_zero
    calc
      v.valuation F (a : F) = WithZero.exp (WithZero.log (v.valuation F (a : F))) :=
        (WithZero.exp_log hne).symm
      _ = 1 := by rw [hlog]; simp
  calc
    Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = v.valuation F (a : F) :=
      v.valuedAdicCompletion_eq_valuation' (a : F)
    _ = 1 := hglobal

theorem absFin_eq_one_of_valued_eq_one (v : FinPlace F)
    {x : v.adicCompletion F} (hx : Valued.v x = 1) : absFin v x = 1 := by
  dsimp [absFin]
  rw [dif_pos (HeightOneSpectrum.absNorm_ne_zero v), hx]
  simp

private theorem shell_translation_preserves (v : FinPlace F) (n : ℤ) (hn : 0 < n)
    {x h : v.adicCompletion F} (hx : Valued.v x = WithZero.exp n)
    (hh : h ∈ ballZ v (1 - n)) : Valued.v (x + h) = WithZero.exp n := by
  have hsmall : Valued.v h < WithZero.exp n := by
    change Valued.v h ≤ WithZero.exp (1 - n) at hh
    exact hh.trans_lt (WithZero.exp_lt_exp.mpr (by omega))
  have hupper : Valued.v (x + h) ≤ WithZero.exp n := by
    calc
      Valued.v (x + h) ≤ max (Valued.v x) (Valued.v h) := Valued.v.map_add x h
      _ = WithZero.exp n := by rw [hx]; exact max_eq_left hsmall.le
  have hlower : WithZero.exp n ≤ Valued.v (x + h) := by
    by_contra hnot
    have hlt : Valued.v (x + h) < WithZero.exp n := lt_of_not_ge hnot
    have hneg : Valued.v (-h) < WithZero.exp n := by simpa using hsmall
    have hmax : max (Valued.v (x + h)) (Valued.v (-h)) < WithZero.exp n :=
      max_lt_iff.mpr ⟨hlt, hneg⟩
    have hsum := Valued.v.map_add (x + h) (-h)
    have hrec : (x + h) + (-h) = x := by ring
    rw [hrec, hx] at hsum
    exact (not_le_of_gt hmax) hsum
  exact le_antisymm hupper hlower

private theorem unit_quadratic_shell_integral_zero (S : SData F CE condη)
    (A : AddCharData F) (v : FinPlace F) (μ : Measure (v.adicCompletion F))
    [Measure.IsAddHaarMeasure μ] (c : (v.adicCompletion F)ˣ)
    (hv : v ∉ S.Sf) (hc : Valued.v (c : v.adicCompletion F) = 1)
    (n : ℤ) (hn : 0 < n) :
    ∫ x in {x | Valued.v x = WithZero.exp n},
      A.ψ v ((c : v.adicCompletion F) * x ^ 2) ∂μ = 0 := by
  classical
  let K := v.adicCompletion F
  let shell : Set K := {x | Valued.v x = WithZero.exp n}
  let H : Set K := ballZ v (1 - n)
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer F v
  have hπne : π ≠ 0 := by
    intro h
    subst π
    have hval0 : v.valuation F (0 : F) = 0 := map_zero (v.valuation F)
    rw [hval0] at hπ
    have hpos : (0 : WithZero (Multiplicative ℤ)) < WithZero.exp (-1 : ℤ) :=
      WithZero.exp_pos
    rw [← hπ] at hpos
    exact (lt_irrefl 0) hpos
  have hπK : Valued.v (algebraMap F K π) = WithZero.exp (-1 : ℤ) := by
    calc
      Valued.v (algebraMap F K π) = v.valuation F π := v.valuedAdicCompletion_eq_valuation' π
      _ = WithZero.exp (-1 : ℤ) := hπ
  let πU : Fˣ := Units.mk0 π hπne
  let πloc : Kˣ := toLoc v πU
  have hπloc : Valued.v (πloc : K) = WithZero.exp (-1 : ℤ) := by
    change Valued.v (algebraMap F K π) = _
    exact hπK
  have hdiff : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal := by
    intro h
    exact hv (S.different_mem v h)
  obtain ⟨x₀, hx₀ψ⟩ := (A.unramified v hdiff).2 π hπ
  let w : K := algebraMap F K ((x₀ : F) / π)
  have hwψ : A.ψ v w ≠ 1 := hx₀ψ
  have hx₀val : v.valuation F (x₀ : F) ≤ 1 := by
    change v.valuation F (algebraMap (𝓞 F) F x₀) ≤ 1
    exact v.valuation_le_one (K := F) x₀
  have hwval : Valued.v w ≤ WithZero.exp (1 : ℤ) := by
    change Valued.v (algebraMap F K ((x₀ : F) / π)) ≤ _
    have hval : v.valuation F ((x₀ : F) / π) ≤ WithZero.exp (1 : ℤ) := by
      rw [(v.valuation F).map_div, hπ]
      have hinv : (WithZero.exp (-1 : ℤ))⁻¹ = WithZero.exp (1 : ℤ) := by
        rw [WithZero.exp_neg, inv_inv]
      rw [div_eq_mul_inv, hinv]
      calc
        v.valuation F (x₀ : F) * WithZero.exp (1 : ℤ) ≤ 1 * WithZero.exp (1 : ℤ) := by
          gcongr
        _ = WithZero.exp (1 : ℤ) := by simp
    calc
      Valued.v (algebraMap F K ((x₀ : F) / π)) = v.valuation F ((x₀ : F) / π) :=
        v.valuedAdicCompletion_eq_valuation' ((x₀ : F) / π)
      _ ≤ WithZero.exp (1 : ℤ) := hval
  have h2val := exterior_two_valuation S v hv
  have hshellOpen : IsOpen shell := by
    have hset : shell = ballZ v n \ ballZ v (n - 1) :=
      (ballZ_sdiff_eq_shell v n).symm
    rw [hset]
    exact (ballZ_open v n).sdiff (ballZ_compact v πloc hπloc (n - 1)).isClosed
  have hshellCompact : IsCompact shell := by
    have hset : shell = ballZ v n \ ballZ v (n - 1) :=
      (ballZ_sdiff_eq_shell v n).symm
    have hclosed : IsClosed shell := by
      rw [hset, Set.diff_eq]
      exact (ballZ_compact v πloc hπloc n).isClosed.inter
        (ballZ_open v (n - 1)).isClosed_compl
    exact (ballZ_compact v πloc hπloc n).of_isClosed_subset hclosed (by
      rw [hset]
      intro x hx
      exact hx.1)
  have hHopen : IsOpen H := ballZ_open v (1 - n)
  have hHcompact : IsCompact H := ballZ_compact v πloc hπloc (1 - n)
  have hHzero : (0 : K) ∈ H := by
    change Valued.v (0 : K) ≤ WithZero.exp (1 - n)
    simp
  let E : Set (K × K) := shell ×ˢ H
  have hEopen : IsOpen E := hshellOpen.prod hHopen
  have hEcompact : IsCompact E := hshellCompact.prod hHcompact
  have hEmeas : MeasurableSet E := hEopen.measurableSet
  let g₀ : K × K → ℂ := fun z => A.ψ v ((c : K) * z.1 ^ 2)
  let g₁ : K × K → ℂ := fun z => A.ψ v ((c : K) * (z.1 + z.2) ^ 2)
  let f₀ : K × K → ℂ := E.indicator g₀
  let f₁ : K × K → ℂ := E.indicator g₁
  have hg₀ : Continuous g₀ := by
    dsimp [g₀]
    exact (addChar_continuous A v).comp
      ((continuous_const_mul (c : K)).comp (continuous_fst.pow 2))
  have hg₁ : Continuous g₁ := by
    dsimp [g₁]
    exact (addChar_continuous A v).comp
      ((continuous_const_mul (c : K)).comp ((continuous_fst.add continuous_snd).pow 2))
  have hf₀ : Integrable f₀ (μ.prod μ) :=
    (hg₀.continuousOn.integrableOn_compact hEcompact).integrable_indicator hEmeas
  have hf₁ : Integrable f₁ (μ.prod μ) :=
    (hg₁.continuousOn.integrableOn_compact hEcompact).integrable_indicator hEmeas
  have hvaladd (x h : K) (hx : x ∈ shell) (hh : h ∈ H) : x + h ∈ shell :=
    shell_translation_preserves v n hn hx hh
  let e : K × K ≃ᵐ K × K :=
    (MeasurableEquiv.prodComm (α := K) (β := K)).trans
      ((MeasurableEquiv.shearAddRight K).trans
        (MeasurableEquiv.prodComm (α := K) (β := K)))
  have he (z : K × K) : e z = (z.1 + z.2, z.2) := by
    rcases z with ⟨x, h⟩
    simp [e, MeasurableEquiv.prodComm, MeasurableEquiv.shearAddRight,
      Equiv.prodComm_apply, Equiv.prodShear_apply, add_comm]
  have hEinv (z : K × K) : e z ∈ E ↔ z ∈ E := by
    rcases z with ⟨x, h⟩
    rw [he (x, h)]
    change (x + h ∈ shell ∧ h ∈ H) ↔ (x ∈ shell ∧ h ∈ H)
    constructor
    · rintro ⟨hxh, hh⟩
      refine ⟨?_, hh⟩
      have hxrec : (x + h) + (-h) = x := by ring
      rw [← hxrec]
      exact shell_translation_preserves v n hn hxh (ballZ_neg v (1 - n) hh)
    · rintro ⟨hx, hh⟩
      exact ⟨hvaladd x h hx hh, hh⟩
  have hfe : (fun z => f₀ (e z)) = f₁ := by
    funext z
    simp only [f₀, f₁, Set.indicator_apply, g₀, g₁]
    have htuple : (z.1 + z.2, z.2) ∈ E ↔ z ∈ E := by
      rw [← he z]
      exact hEinv z
    simp only [he z]
    simp [htuple]
  let μs : ℂ := (μ.real H : ℂ)
  let I : ℂ := ∫ x in shell, A.ψ v ((c : K) * x ^ 2) ∂μ
  have hinner₀ (x : K) :
      ∫ h, f₀ (x, h) ∂μ =
        if x ∈ shell then μs * A.ψ v ((c : K) * x ^ 2) else 0 := by
    by_cases hx : x ∈ shell
    · have hfun : (fun h => f₀ (x, h)) = H.indicator
        (fun _ => A.ψ v ((c : K) * x ^ 2)) := by
        funext h
        by_cases hh : h ∈ H <;> simp [f₀, E, g₀, hx, hh]
      rw [hfun, integral_indicator hHopen.measurableSet, setIntegral_const]
      simp [μs, hx, smul_eq_mul]
    · have hfun : (fun h => f₀ (x, h)) = fun _ => (0 : ℂ) := by
        funext h
        simp [f₀, E, hx]
      rw [hfun]
      rw [if_neg hx]
      exact integral_eq_zero_of_ae (Filter.Eventually.of_forall fun _ => rfl)
  have hinner₁ (x : K) : ∫ h, f₁ (x, h) ∂μ = 0 := by
    by_cases hx : x ∈ shell
    · have hfun : (fun h => f₁ (x, h)) = H.indicator
        (fun h => A.ψ v ((c : K) * (x + h) ^ 2)) := by
        funext h
        by_cases hh : h ∈ H <;> simp [f₁, E, g₁, hx, hh]
      rw [hfun, integral_indicator hHopen.measurableSet]
      let k : K := (2 : K) * (c : K) * x
      have hkval : Valued.v k = WithZero.exp n := by
        dsimp [k]
        rw [Valuation.map_mul, Valuation.map_mul, h2val, hc, hx]
        simp
      have hkne : k ≠ 0 := by
        intro hzero
        rw [hzero] at hkval
        have hpos : (0 : WithZero (Multiplicative ℤ)) < WithZero.exp n := WithZero.exp_pos
        rw [← hkval] at hpos
        have hfalse : (0 : WithZero (Multiplicative ℤ)) < 0 := by simpa using hpos
        exact (lt_irrefl (0 : WithZero (Multiplicative ℤ))) hfalse
      let b : K := k⁻¹ * w
      have hbval : Valued.v b ≤ WithZero.exp (1 - n) := by
        dsimp [b]
        rw [Valuation.map_mul, Valuation.map_inv, hkval]
        calc
          WithZero.exp (-n) * Valued.v w ≤ WithZero.exp (-n) * WithZero.exp 1 := by gcongr
          _ = WithZero.exp (1 - n) := by rw [← WithZero.exp_add]; congr 1 <;> ring
      have hb : b ∈ H := hbval
      have hkb : k * b = w := by
        dsimp [b]
        rw [← mul_assoc, mul_inv_cancel₀ hkne, one_mul]
      have hlin : A.ψ v (k * b) ≠ 1 := by simpa [hkb] using hwψ
      have hlinInt : ∫ h in H, A.ψ v (k * h) ∂μ = 0 := by
        simpa [H] using integral_addChar_zero_on_ball A v μ (1 - n) k b hb hlin
      have hquadO (h : K) (hh : h ∈ H) :
          (c : K) * h ^ 2 ∈ v.adicCompletionIntegers F := by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers]
        have hhval : Valued.v h ≤ WithZero.exp (1 - n) := hh
        calc
          Valued.v ((c : K) * h ^ 2) = Valued.v (c : K) * Valued.v h ^ 2 := by simp
          _ ≤ 1 * (WithZero.exp (1 - n)) ^ 2 := by rw [hc]; gcongr
          _ = WithZero.exp (2 * (1 - n)) := by
            rw [one_mul]
            calc
              WithZero.exp (1 - n) ^ (2 : ℕ) =
                  WithZero.exp (1 - n) ^ (2 : ℤ) :=
                (zpow_natCast (WithZero.exp (1 - n)) 2).symm
              _ = WithZero.exp ((2 : ℤ) • (1 - n)) := by rw [← WithZero.exp_zsmul]
              _ = WithZero.exp (2 * (1 - n)) := by simp [zsmul_eq_mul]
          _ ≤ 1 := WithZero.exp_le_exp.mpr (by omega)
      have hpoint (h : K) (hh : h ∈ H) :
          A.ψ v ((c : K) * (x + h) ^ 2) =
            A.ψ v ((c : K) * x ^ 2) * A.ψ v (k * h) := by
        have harg : (c : K) * (x + h) ^ 2 =
            (c : K) * x ^ 2 + k * h + (c : K) * h ^ 2 := by
          dsimp [k]
          ring
        rw [harg, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
          A.integral v ((c : K) * h ^ 2) (hquadO h hh), mul_one]
      rw [setIntegral_congr_fun hHopen.measurableSet (fun h hh => hpoint h hh)]
      rw [integral_const_mul, hlinInt]
      simp
    · have hfun : (fun h => f₁ (x, h)) = fun _ => (0 : ℂ) := by
        funext h
        simp [f₁, E, hx]
      rw [hfun]
      exact integral_eq_zero_of_ae (Filter.Eventually.of_forall fun _ => rfl)
  have hprod₀ : ∫ z, f₀ z ∂(μ.prod μ) = μs * I := by
    rw [integral_prod f₀ hf₀]
    have houter : (fun x => ∫ h, f₀ (x, h) ∂μ) =
        shell.indicator (fun x => μs * A.ψ v ((c : K) * x ^ 2)) := by
      funext x
      rw [hinner₀ x]
      by_cases hx : x ∈ shell <;> simp [hx]
    rw [houter, integral_indicator hshellOpen.measurableSet, integral_const_mul]
  have hprod₁ : ∫ z, f₁ z ∂(μ.prod μ) = 0 := by
    rw [integral_prod f₁ hf₁]
    have houter : (fun x => ∫ h, f₁ (x, h) ∂μ) = fun _ => (0 : ℂ) := by
      funext x
      exact hinner₁ x
    rw [houter]
    simp
  have hMP : MeasurePreserving (fun z : K × K => e z) (μ.prod μ) (μ.prod μ) := by
    convert measurePreserving_add_prod μ μ using 1
    funext z
    exact he z
  have hshift : ∫ z, f₀ (e z) ∂(μ.prod μ) = ∫ z, f₀ z ∂(μ.prod μ) :=
    hMP.integral_comp e.measurableEmbedding f₀
  have hzero : μs * I = 0 := by
    calc
      μs * I = ∫ z, f₀ z ∂(μ.prod μ) := hprod₀.symm
      _ = ∫ z, f₀ (e z) ∂(μ.prod μ) := hshift.symm
      _ = ∫ z, f₁ z ∂(μ.prod μ) := by rw [hfe]
      _ = 0 := hprod₁
  have hμHpos : 0 < μ.real H := by
    have hpos : 0 < μ H := hHopen.measure_pos μ ⟨0, hHzero⟩
    exact ENNReal.toReal_pos hpos.ne' hHcompact.measure_lt_top.ne
  have hμs : μs ≠ 0 := by
    dsimp [μs]
    exact_mod_cast hμHpos.ne'
  exact (mul_eq_zero.mp hzero).resolve_left hμs

theorem unit_quadraticIntegral_eq_integer_mass (S : SData F CE condη)
    (A : AddCharData F) (v : FinPlace F) (μ : Measure (v.adicCompletion F))
    [Measure.IsAddHaarMeasure μ] (c : (v.adicCompletion F)ˣ)
    (hv : v ∉ S.Sf) (hc : Valued.v (c : v.adicCompletion F) = 1) (N : ℕ) :
    quadraticIntegral A v μ c N =
      (μ.real (v.adicCompletionIntegers F) : ℂ) := by
  classical
  let K := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer F v
  have hπne : π ≠ 0 := by
    intro h
    subst π
    have hval0 : v.valuation F (0 : F) = 0 := by simp
    rw [hval0] at hπ
    have hpos : (0 : WithZero (Multiplicative ℤ)) < WithZero.exp (-1 : ℤ) := WithZero.exp_pos
    rw [← hπ] at hpos
    exact (lt_irrefl (0 : WithZero (Multiplicative ℤ))) (by simpa using hpos)
  have hπK : Valued.v (algebraMap F K π) = WithZero.exp (-1 : ℤ) := by
    calc
      Valued.v (algebraMap F K π) = v.valuation F π := v.valuedAdicCompletion_eq_valuation' π
      _ = WithZero.exp (-1 : ℤ) := hπ
  let πU : Fˣ := Units.mk0 π hπne
  let πloc : Kˣ := toLoc v πU
  have hπloc : Valued.v (πloc : K) = WithZero.exp (-1 : ℤ) := by
    change Valued.v (algebraMap F K π) = _
    exact hπK
  have hOopen : IsOpen (O : Set K) := Valued.isOpen_valuationSubring K
  have hOmem : ∀ x : K, x ∈ O ↔ Valued.v x ≤ 1 := by
    intro x
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have hquadO (x : K) (hx : x ∈ O) : (c : K) * x ^ 2 ∈ O := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have hxval : Valued.v x ≤ 1 := (hOmem x).mp hx
    calc
      Valued.v ((c : K) * x ^ 2) = Valued.v (c : K) * Valued.v x ^ 2 := by simp
      _ ≤ 1 * 1 ^ 2 := by rw [hc]; gcongr
      _ = 1 := by simp
  have hball0 : localBall v 0 = (O : Set K) := by
    ext x
    change Valued.v x ≤ WithZero.exp (0 : ℤ) ↔ x ∈ O
    rw [hOmem]
    simp
  have hbase : quadraticIntegral A v μ c 0 = (μ.real O : ℂ) := by
    change ∫ x in localBall v 0, A.ψ v ((c : K) * x ^ 2) ∂μ = _
    rw [hball0]
    have hconst : ∀ x ∈ (O : Set K), A.ψ v ((c : K) * x ^ 2) = 1 := by
      intro x hx
      exact A.integral v ((c : K) * x ^ 2) (hquadO x hx)
    rw [setIntegral_congr_fun hOopen.measurableSet hconst, setIntegral_const]
    simp
  have hcont : Continuous (fun x : K => A.ψ v ((c : K) * x ^ 2)) := by
    exact (addChar_continuous A v).comp
      ((continuous_const_mul (c : K)).comp (continuous_id.pow 2))
  have hall (m : ℕ) :
      quadraticIntegral A v μ c m = (μ.real O : ℂ) := by
    induction m with
    | zero => exact hbase
    | succ m ih =>
      let n : ℤ := (m : ℤ) + 1
      have hn : 0 < n := by dsimp [n]; omega
      let Bbig : Set K := ballZ v n
      let Bsmall : Set K := ballZ v (m : ℤ)
      let g : K → ℂ := fun x => A.ψ v ((c : K) * x ^ 2)
      have hBbigCompact : IsCompact Bbig := by
        exact ballZ_compact v πloc hπloc n
      have hBsmallOpen : IsOpen Bsmall := ballZ_open v (m : ℤ)
      have hBsubset : Bsmall ⊆ Bbig := by
        intro x hx
        change Valued.v x ≤ WithZero.exp (m : ℤ) at hx
        change Valued.v x ≤ WithZero.exp n
        exact hx.trans (WithZero.exp_le_exp.mpr (by dsimp [n]; omega))
      have hsmallIntegral :
          ∫ x in Bsmall, g x ∂μ = (μ.real O : ℂ) := by
        have hchange :
            (∫ x in Bsmall, g x ∂μ) = quadraticIntegral A v μ c m := by
          rfl
        exact hchange.trans ih
      have hbigShell :
          Bbig \ Bsmall = {x | Valued.v x = WithZero.exp n} := by
        dsimp [Bbig, Bsmall, n]
        simpa using (ballZ_sdiff_eq_shell v ((m : ℤ) + 1))
      have hbigIntegrable : IntegrableOn g Bbig μ :=
        hcont.continuousOn.integrableOn_compact hBbigCompact
      have hdiffIntegral := setIntegral_sdiff hBsmallOpen.measurableSet hbigIntegrable hBsubset
      have hshellIntegral : ∫ x in Bbig \ Bsmall, g x ∂μ = 0 := by
        rw [hbigShell]
        simpa [g] using unit_quadratic_shell_integral_zero S A v μ c hv hc n hn
      have hsubZero :
          (∫ x in Bbig, g x ∂μ) - ∫ x in Bsmall, g x ∂μ = 0 := by
        calc
          _ = ∫ x in Bbig \ Bsmall, g x ∂μ := hdiffIntegral.symm
          _ = 0 := hshellIntegral
      have hbigEq :
          ∫ x in Bbig, g x ∂μ = ∫ x in Bsmall, g x ∂μ := sub_eq_zero.mp hsubZero
      change ∫ x in localBall v (m + 1), A.ψ v ((c : K) * x ^ 2) ∂μ = _
      have hlocal : localBall v (m + 1) = Bbig := by
        ext x
        change Valued.v x ≤ WithZero.exp ((m : ℤ) + 1) ↔
          Valued.v x ≤ WithZero.exp n
        simp [n]
      rw [hlocal]
      change ∫ x in Bbig, g x ∂μ = (μ.real O : ℂ)
      rw [hbigEq, hsmallIntegral]
  exact hall N

end ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_e
