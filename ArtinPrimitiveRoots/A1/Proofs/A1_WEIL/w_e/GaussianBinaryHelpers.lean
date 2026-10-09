import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianUnit

set_option autoImplicit false
set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_e

open ArtinPrimitiveRoots.A1
open ArtinPrimitiveRoots.Proofs.a1_weil_sol

variable {F : Type} [Field F] [NumberField F]

local instance binaryCompletionMeasurable (v : FinPlace F) :
    MeasurableSpace (v.adicCompletion F) := borel _

local instance binaryCompletionBorel (v : FinPlace F) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

private def binaryBall (v : FinPlace F) (n : ℤ) : Set (v.adicCompletion F) :=
  {x | Valued.v x ≤ WithZero.exp n}

private theorem binaryBall_open (v : FinPlace F) (n : ℤ) : IsOpen (binaryBall v n) := by
  exact v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero

private theorem binaryBall_add (v : FinPlace F) (n : ℤ)
    {x y : v.adicCompletion F} (hx : x ∈ binaryBall v n) (hy : y ∈ binaryBall v n) :
    x + y ∈ binaryBall v n := by
  change Valued.v x ≤ WithZero.exp n at hx
  change Valued.v y ≤ WithZero.exp n at hy
  change Valued.v (x + y) ≤ WithZero.exp n
  exact (Valued.v.map_add x y).trans (max_le hx hy)

private theorem binaryBall_neg (v : FinPlace F) (n : ℤ)
    {x : v.adicCompletion F} (hx : x ∈ binaryBall v n) : -x ∈ binaryBall v n := by
  change Valued.v x ≤ WithZero.exp n at hx
  change Valued.v (-x) ≤ WithZero.exp n
  simpa using hx

private theorem binaryBall_compact (v : FinPlace F) (n : ℤ) :
    IsCompact (binaryBall v n) := by
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
  have hπK : Valued.v (algebraMap F (v.adicCompletion F) π) = WithZero.exp (-1 : ℤ) := by
    calc
      Valued.v (algebraMap F (v.adicCompletion F) π) = v.valuation F π :=
        v.valuedAdicCompletion_eq_valuation' π
      _ = WithZero.exp (-1 : ℤ) := hπ
  let πU : Fˣ := Units.mk0 π hπne
  let πloc : (v.adicCompletion F)ˣ := toLoc v πU
  have hπloc : Valued.v (πloc : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    change Valued.v (algebraMap F (v.adicCompletion F) π) = _
    exact hπK
  change IsCompact {x | Valued.v x ≤ WithZero.exp n}
  simpa [binaryBall] using ballZ_compact_api v πloc hπloc n

private theorem binary_value_exp (v : FinPlace F) {x : v.adicCompletion F}
    (hx : x ≠ 0) : ∃ k : ℤ, Valued.v x = WithZero.exp k := by
  have hv : Valued.v x ≠ 0 := Valued.v.ne_zero_iff.mpr hx
  lift Valued.v x to ℤ using hv with k hk
  exact ⟨k, rfl⟩

private theorem character_conductor_cutoff (D : FieldData F) (A : AddCharData F)
    (v : FinPlace F) :
    ∃ C : ℤ, 0 ≤ C ∧
      (∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp C → A.ψ v x = 1) ∧
      ∃ x : v.adicCompletion F,
        Valued.v x ≤ WithZero.exp (C + 1) ∧ A.ψ v x ≠ 1 := by
  classical
  have hψne : A.ψ v ≠ 1 := (local_character_regular D A v).2.1
  have hnotall : ¬ ∀ x : v.adicCompletion F, A.ψ v x = 1 := by
    intro hall
    apply hψne
    ext x
    exact hall x
  obtain ⟨w, hw⟩ := not_forall.mp hnotall
  have hwO : w ∉ v.adicCompletionIntegers F := by
    intro hO
    exact hw (A.integral v w hO)
  have hwgt : (1 : WithZero (Multiplicative ℤ)) < Valued.v w := by
    have hnotle : ¬ Valued.v w ≤ 1 := by
      intro hle
      apply hwO
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      exact hle
    exact lt_of_not_ge hnotle
  have hwne : w ≠ 0 := by
    intro hw0
    subst w
    simpa using hwgt
  obtain ⟨kw, hkw⟩ := binary_value_exp v (x := w) hwne
  have hkwpos : 0 < kw := by
    rw [hkw] at hwgt
    exact WithZero.exp_lt_exp.mp hwgt
  let k : ℕ := kw.toNat
  have hkwk : (k : ℤ) = kw := Int.toNat_of_nonneg hkwpos.le
  let P : ℕ → Prop := fun n =>
    ∃ x : v.adicCompletion F, x ∈ binaryBall v (n : ℤ) ∧ A.ψ v x ≠ 1
  have hkP : P k := by
    refine ⟨w, ?_, hw⟩
    change Valued.v w ≤ WithZero.exp (k : ℤ)
    rw [hkw, hkwk]
  have hex : ∃ n, P n := ⟨k, hkP⟩
  have hP0 : ¬ P 0 := by
    rintro ⟨x, hx, hxψ⟩
    have hO : x ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v x ≤ WithZero.exp (0 : ℤ) at hx
      simpa using hx
    exact hxψ (A.integral v x hO)
  let n := Nat.find hex
  have hnP : P n := Nat.find_spec hex
  have hnpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    exact hP0 (by simpa [n, hn0] using hnP)
  have hnprev : ¬ P (n - 1) := Nat.find_min hex (by omega)
  let C : ℤ := (n : ℤ) - 1
  refine ⟨C, ?_, ?_, ?_⟩
  · dsimp [C]
    omega
  · intro x hx
    by_contra hψ
    apply hnprev
    refine ⟨x, ?_, hψ⟩
    change Valued.v x ≤ WithZero.exp ((n - 1 : ℕ) : ℤ)
    have hcast : ((n - 1 : ℕ) : ℤ) = C := by dsimp [C]; omega
    rw [hcast]
    change Valued.v x ≤ WithZero.exp C at hx
    exact hx
  · rcases hnP with ⟨x, hx, hxψ⟩
    refine ⟨x, ?_, hxψ⟩
    change Valued.v x ≤ WithZero.exp (C + 1)
    rw [show C + 1 = (n : ℤ) by dsimp [C]; omega]
    change Valued.v x ≤ WithZero.exp (n : ℤ) at hx
    exact hx

private theorem binary_linearIntegral_eq_mass (A : AddCharData F) (v : FinPlace F)
    (μ : Measure (v.adicCompletion F)) [Measure.IsAddHaarMeasure μ]
    (m : ℤ) (k : v.adicCompletion F)
    (htriv : ∀ x ∈ binaryBall v m, A.ψ v (k * x) = 1) :
    ∫ x in binaryBall v m, A.ψ v (k * x) ∂μ = (μ.real (binaryBall v m) : ℂ) := by
  rw [setIntegral_congr_fun (binaryBall_open v m).measurableSet htriv]
  simp

private theorem binary_valued_mul_le (v : FinPlace F) {x y : v.adicCompletion F}
    {kx ky : ℤ} (hx : Valued.v x ≤ WithZero.exp kx) (hy : Valued.v y ≤ WithZero.exp ky) :
    Valued.v (x * y) ≤ WithZero.exp (kx + ky) := by
  rw [Valuation.map_mul]
  calc
    Valued.v x * Valued.v y ≤ WithZero.exp kx * WithZero.exp ky := by gcongr
    _ = WithZero.exp (kx + ky) := by rw [← WithZero.exp_add]

private theorem binary_valued_square_mul_le (v : FinPlace F) {x c : v.adicCompletion F}
    {kx kc : ℤ} (hx : Valued.v x ≤ WithZero.exp kx)
    (hc : Valued.v c ≤ WithZero.exp kc) :
    Valued.v (c * x ^ 2) ≤ WithZero.exp (kc + 2 * kx) := by
  have hxx : Valued.v (x ^ 2) ≤ WithZero.exp (2 * kx) := by
    rw [Valuation.map_pow]
    calc
      Valued.v x ^ 2 ≤ WithZero.exp kx ^ 2 := by gcongr
      _ = WithZero.exp (2 * kx) := by
        rw [show WithZero.exp kx ^ (2 : ℕ) = WithZero.exp kx ^ (2 : ℤ) by
          exact (zpow_natCast _ _).symm]
        rw [← WithZero.exp_zsmul]
        simp [zsmul_eq_mul]
  exact binary_valued_mul_le v hc hxx

private theorem binary_valued_mul3_le (v : FinPlace F)
    {x y z : v.adicCompletion F} {kx ky kz : ℤ}
    (hx : Valued.v x ≤ WithZero.exp kx) (hy : Valued.v y ≤ WithZero.exp ky)
    (hz : Valued.v z ≤ WithZero.exp kz) :
    Valued.v (x * y * z) ≤ WithZero.exp (kx + ky + kz) := by
  calc
    Valued.v (x * y * z) ≤ WithZero.exp (kx + ky) * WithZero.exp kz := by
      rw [Valuation.map_mul]
      gcongr
      exact binary_valued_mul_le v hx hy
    _ = WithZero.exp (kx + ky + kz) := by rw [← WithZero.exp_add]

private theorem binary_valued_mul4_le (v : FinPlace F)
    {x y z w : v.adicCompletion F} {kx ky kz kw : ℤ}
    (hx : Valued.v x ≤ WithZero.exp kx) (hy : Valued.v y ≤ WithZero.exp ky)
    (hz : Valued.v z ≤ WithZero.exp kz) (hw : Valued.v w ≤ WithZero.exp kw) :
    Valued.v (x * y * z * w) ≤ WithZero.exp (kx + ky + kz + kw) := by
  calc
    Valued.v (x * y * z * w) ≤ WithZero.exp (kx + ky + kz) * WithZero.exp kw := by
      rw [Valuation.map_mul]
      gcongr
      exact binary_valued_mul3_le v hx hy hz
    _ = WithZero.exp (kx + ky + kz + kw) := by rw [← WithZero.exp_add]

private theorem binary_shift_integral (D : FieldData F) (A : AddCharData F)
    (v : FinPlace F) (μ : Measure (v.adicCompletion F)) [Measure.IsAddHaarMeasure μ]
    (c d : (v.adicCompletion F)ˣ) (C m kTwo kC kD : ℤ)
    (hC : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp C → A.ψ v x = 1)
    (hCnext : ∃ x : v.adicCompletion F,
      Valued.v x ≤ WithZero.exp (C + 1) ∧ A.ψ v x ≠ 1)
    (hTwo : Valued.v (2 : v.adicCompletion F) = WithZero.exp kTwo)
    (hCval : Valued.v (c : v.adicCompletion F) = WithZero.exp kC)
    (hDval : Valued.v (d : v.adicCompletion F) = WithZero.exp kD)
    (hmNonpos : m ≤ 0) (hmC : kC + 2 * m ≤ 0) (hmD : kD + 2 * m ≤ 0)
    (hRmC : m ≤ C - kTwo - kC - m) (hRmD : m ≤ C - kTwo - kD - m)
    (hR0C : 0 ≤ C - kTwo - kC - m) (hR0D : 0 ≤ C - kTwo - kD - m)
    (x y : v.adicCompletion F) :
    ∫ z in binaryBall v m ×ˢ binaryBall v m,
      A.ψ v ((c : v.adicCompletion F) * (x + z.1) ^ 2 +
        (d : v.adicCompletion F) * (y + z.2) ^ 2) ∂(μ.prod μ) =
      if x ∈ binaryBall v (C - kTwo - kC - m) ∧
          y ∈ binaryBall v (C - kTwo - kD - m) then
        ((μ.real (binaryBall v m) : ℂ) * (μ.real (binaryBall v m) : ℂ)) *
          A.ψ v ((c : v.adicCompletion F) * x ^ 2 + (d : v.adicCompletion F) * y ^ 2)
      else 0 := by
  classical
  let K := v.adicCompletion F
  let H : Set K := binaryBall v m
  let q : K × K → K := fun p => (c : K) * p.1 ^ 2 + (d : K) * p.2 ^ 2
  have hHopen : IsOpen H := binaryBall_open v m
  have hHprodOpen : IsOpen (H ×ˢ H) := hHopen.prod hHopen
  have hHprodMeas : MeasurableSet (H ×ˢ H) := hHprodOpen.measurableSet
  have hquadhterm (u : K) (hu : u ∈ H) :
      (c : K) * u ^ 2 ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have huval : Valued.v u ≤ WithZero.exp m := hu
    have hval := binary_valued_square_mul_le v huval (le_of_eq hCval)
    exact hval.trans (WithZero.exp_le_exp.mpr hmC)
  have hquadhterm' (u : K) (hu : u ∈ H) :
      (d : K) * u ^ 2 ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have huval : Valued.v u ≤ WithZero.exp m := hu
    have hval := binary_valued_square_mul_le v huval (le_of_eq hDval)
    exact hval.trans (WithZero.exp_le_exp.mpr hmD)
  have hpoint (u w : K) (hu : u ∈ H) (hw : w ∈ H) :
      A.ψ v ((c : K) * (x + u) ^ 2 + (d : K) * (y + w) ^ 2) =
        A.ψ v ((c : K) * x ^ 2 + (d : K) * y ^ 2) *
          A.ψ v ((2 : K) * (c : K) * x * u) *
          A.ψ v ((2 : K) * (d : K) * y * w) := by
    have harg : (c : K) * (x + u) ^ 2 + (d : K) * (y + w) ^ 2 =
        ((c : K) * x ^ 2 + (d : K) * y ^ 2) +
          ((2 : K) * (c : K) * x * u) + ((2 : K) * (d : K) * y * w) +
            (c : K) * u ^ 2 + (d : K) * w ^ 2 := by ring
    rw [harg]
    simp only [AddChar.map_add_eq_mul]
    rw [A.integral v ((c : K) * u ^ 2) (hquadhterm u hu),
      A.integral v ((d : K) * w ^ 2) (hquadhterm' w hw)]
    ring
  have hlinearOne :
      ∫ u in H, A.ψ v ((2 : K) * (c : K) * x * u) ∂μ =
        if x ∈ binaryBall v (C - kTwo - kC - m) then
          (μ.real H : ℂ) else 0 := by
    by_cases hx : x ∈ binaryBall v (C - kTwo - kC - m)
    · rw [if_pos hx]
      have hmass := binary_linearIntegral_eq_mass A v μ m ((2 : K) * (c : K) * x) (by
        intro u hu
        have hxval : Valued.v x ≤ WithZero.exp (C - kTwo - kC - m) := hx
        have huval : Valued.v u ≤ WithZero.exp m := hu
        have hval : Valued.v ((2 : K) * (c : K) * x * u) ≤
            WithZero.exp (kTwo + kC + (C - kTwo - kC - m) + m) := by
          exact binary_valued_mul4_le v (le_of_eq hTwo) (le_of_eq hCval) hxval huval
        have hExp : kTwo + kC + (C - kTwo - kC - m) + m = C := by omega
        exact hC _ (hval.trans_eq (congrArg WithZero.exp hExp)))
      simpa [H] using hmass
    · rw [if_neg hx]
      have hx0 : x ≠ 0 := by
        intro hz
        apply hx
        subst x
        change Valued.v (0 : K) ≤ WithZero.exp (C - kTwo - kC - m)
        simp
      obtain ⟨kx, hkx⟩ := binary_value_exp v hx0
      have hkxgt : C - kTwo - kC - m < kx := by
        have hlt : WithZero.exp (C - kTwo - kC - m) < Valued.v x := by
          exact lt_of_not_ge (by simpa [binaryBall] using hx)
        rw [hkx] at hlt
        exact WithZero.exp_lt_exp.mp hlt
      rcases hCnext with ⟨w, hwval, hwψ⟩
      let k : K := (2 : K) * (c : K) * x
      have hkval : Valued.v k = WithZero.exp (kTwo + kC + kx) := by
        dsimp [k]
        rw [Valuation.map_mul, Valuation.map_mul, hTwo, hCval, hkx]
      have hkne : k ≠ 0 := by
        dsimp [k]
        exact mul_ne_zero (mul_ne_zero (by norm_num) c.ne_zero) hx0
      let b : K := w / k
      have hbval : Valued.v b ≤ WithZero.exp m := by
        dsimp [b]
        rw [Valuation.map_div, hkval]
        have hExp : C + 1 - (kTwo + kC + kx) ≤ m := by omega
        calc
          Valued.v w / WithZero.exp (kTwo + kC + kx) ≤
              WithZero.exp (C + 1) / WithZero.exp (kTwo + kC + kx) := by
                gcongr
                exact WithZero.exp_pos.le
          _ = WithZero.exp (C + 1 - (kTwo + kC + kx)) := by
                rw [div_eq_mul_inv, ← WithZero.exp_neg, ← WithZero.exp_add]
                congr 1 <;> omega
          _ ≤ WithZero.exp m := WithZero.exp_le_exp.mpr hExp
      have hb : b ∈ H := hbval
      have hkb : k * b = w := by
        dsimp only [b]
        calc
          k * (w / k) = (k * w) / k := by rw [mul_div_assoc]
          _ = w := mul_div_cancel_left₀ w hkne
      have hψkb : A.ψ v (k * b) ≠ 1 := by simpa [hkb] using hwψ
      have hzero := integral_addChar_zero_on_ball_api A v μ m k b hb hψkb
      simpa [H, binaryBall, k] using hzero
  have hlinearTwo :
      ∫ w in H, A.ψ v ((2 : K) * (d : K) * y * w) ∂μ =
        if y ∈ binaryBall v (C - kTwo - kD - m) then
          (μ.real H : ℂ) else 0 := by
    by_cases hy : y ∈ binaryBall v (C - kTwo - kD - m)
    · rw [if_pos hy]
      have hmass := binary_linearIntegral_eq_mass A v μ m ((2 : K) * (d : K) * y) (by
        intro w hw
        have hyval : Valued.v y ≤ WithZero.exp (C - kTwo - kD - m) := hy
        have hwval : Valued.v w ≤ WithZero.exp m := hw
        have hval : Valued.v ((2 : K) * (d : K) * y * w) ≤
            WithZero.exp (kTwo + kD + (C - kTwo - kD - m) + m) := by
          exact binary_valued_mul4_le v (le_of_eq hTwo) (le_of_eq hDval) hyval hwval
        have hExp : kTwo + kD + (C - kTwo - kD - m) + m = C := by omega
        exact hC _ (hval.trans_eq (congrArg WithZero.exp hExp)))
      simpa [H] using hmass
    · rw [if_neg hy]
      have hy0 : y ≠ 0 := by
        intro hz
        apply hy
        subst y
        change Valued.v (0 : K) ≤ WithZero.exp (C - kTwo - kD - m)
        simp
      obtain ⟨ky, hky⟩ := binary_value_exp v hy0
      have hkygt : C - kTwo - kD - m < ky := by
        have hlt : WithZero.exp (C - kTwo - kD - m) < Valued.v y :=
          lt_of_not_ge (by simpa [binaryBall] using hy)
        rw [hky] at hlt
        exact WithZero.exp_lt_exp.mp hlt
      rcases hCnext with ⟨w₀, hwval, hwψ⟩
      let k : K := (2 : K) * (d : K) * y
      have hkval : Valued.v k = WithZero.exp (kTwo + kD + ky) := by
        dsimp [k]
        rw [Valuation.map_mul, Valuation.map_mul, hTwo, hDval, hky]
      have hkne : k ≠ 0 := by
        dsimp [k]
        exact mul_ne_zero (mul_ne_zero (by norm_num) d.ne_zero) hy0
      let b : K := w₀ / k
      have hbval : Valued.v b ≤ WithZero.exp m := by
        dsimp [b]
        rw [Valuation.map_div, hkval]
        have hExp : C + 1 - (kTwo + kD + ky) ≤ m := by omega
        calc
          Valued.v w₀ / WithZero.exp (kTwo + kD + ky) ≤
              WithZero.exp (C + 1) / WithZero.exp (kTwo + kD + ky) := by
                gcongr
                exact WithZero.exp_pos.le
          _ = WithZero.exp (C + 1 - (kTwo + kD + ky)) := by
                rw [div_eq_mul_inv, ← WithZero.exp_neg, ← WithZero.exp_add]
                congr 1 <;> omega
          _ ≤ WithZero.exp m := WithZero.exp_le_exp.mpr hExp
      have hb : b ∈ H := hbval
      have hkb : k * b = w₀ := by
        dsimp only [b]
        calc
          k * (w₀ / k) = (k * w₀) / k := by rw [mul_div_assoc]
          _ = w₀ := mul_div_cancel_left₀ w₀ hkne
      have hψkb : A.ψ v (k * b) ≠ 1 := by simpa [hkb] using hwψ
      have hzero := integral_addChar_zero_on_ball_api A v μ m k b hb hψkb
      simpa [H, binaryBall, k] using hzero
  have hshift :
      ∫ z in H ×ˢ H,
        A.ψ v ((c : K) * (x + z.1) ^ 2 + (d : K) * (y + z.2) ^ 2) ∂(μ.prod μ) =
        A.ψ v ((c : K) * x ^ 2 + (d : K) * y ^ 2) *
          (∫ u in H, A.ψ v ((2 : K) * (c : K) * x * u) ∂μ) *
          (∫ w in H, A.ψ v ((2 : K) * (d : K) * y * w) ∂μ) := by
    calc
      _ = ∫ z in H ×ˢ H,
          A.ψ v ((c : K) * x ^ 2 + (d : K) * y ^ 2) *
            (A.ψ v ((2 : K) * (c : K) * x * z.1) *
              A.ψ v ((2 : K) * (d : K) * y * z.2)) ∂(μ.prod μ) := by
            apply setIntegral_congr_fun hHprodMeas
            rintro ⟨u, w⟩ ⟨hu, hw⟩
            simpa [mul_assoc] using hpoint u w hu hw
      _ = A.ψ v ((c : K) * x ^ 2 + (d : K) * y ^ 2) *
            (∫ z in H ×ˢ H,
              A.ψ v ((2 : K) * (c : K) * x * z.1) *
                A.ψ v ((2 : K) * (d : K) * y * z.2) ∂(μ.prod μ)) := by
            rw [integral_const_mul]
      _ = _ := by
        have hprod :
            ∫ z in H ×ˢ H,
              A.ψ v ((2 : K) * (c : K) * x * z.1) *
                A.ψ v ((2 : K) * (d : K) * y * z.2) ∂(μ.prod μ) =
              (∫ u in H, A.ψ v ((2 : K) * (c : K) * x * u) ∂μ) *
                ∫ w in H, A.ψ v ((2 : K) * (d : K) * y * w) ∂μ := by
          exact setIntegral_prod_mul (μ := μ) (ν := μ)
            (fun u : K => A.ψ v ((2 : K) * (c : K) * x * u))
            (fun w : K => A.ψ v ((2 : K) * (d : K) * y * w)) H H
        rw [hprod]
        ring
  rw [hshift, hlinearOne, hlinearTwo]
  by_cases hx : x ∈ binaryBall v (C - kTwo - kC - m) <;>
    by_cases hy : y ∈ binaryBall v (C - kTwo - kD - m) <;>
    simp [hx, hy, H, mul_assoc] <;> ring

private theorem binary_compactOpen_integral (D : FieldData F) (A : AddCharData F)
    (v : FinPlace F) (μ : Measure (v.adicCompletion F)) [Measure.IsAddHaarMeasure μ]
    (c d : (v.adicCompletion F)ˣ) (C m kTwo kC kD : ℤ)
    (hC : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp C → A.ψ v x = 1)
    (hCnext : ∃ x : v.adicCompletion F,
      Valued.v x ≤ WithZero.exp (C + 1) ∧ A.ψ v x ≠ 1)
    (hTwo : Valued.v (2 : v.adicCompletion F) = WithZero.exp kTwo)
    (hCval : Valued.v (c : v.adicCompletion F) = WithZero.exp kC)
    (hDval : Valued.v (d : v.adicCompletion F) = WithZero.exp kD)
    (hmNonpos : m ≤ 0) (hmC : kC + 2 * m ≤ 0) (hmD : kD + 2 * m ≤ 0)
    (hRmC : m ≤ C - kTwo - kC - m) (hRmD : m ≤ C - kTwo - kD - m)
    (hR0C : 0 ≤ C - kTwo - kC - m) (hR0D : 0 ≤ C - kTwo - kD - m)
    (L : Set ((v.adicCompletion F) × (v.adicCompletion F)))
    (hLopen : IsOpen L) (hLcompact : IsCompact L)
    (hLshift : ∀ z h, h ∈ binaryBall v m ×ˢ binaryBall v m →
      (z + h ∈ L ↔ z ∈ L))
    (hcore : binaryBall v (C - kTwo - kC - m) ×ˢ
      binaryBall v (C - kTwo - kD - m) ⊆ L) :
    ∫ z in L, A.ψ v ((c : v.adicCompletion F) * z.1 ^ 2 +
      (d : v.adicCompletion F) * z.2 ^ 2) ∂(μ.prod μ) =
    ∫ z in binaryBall v (C - kTwo - kC - m) ×ˢ
      binaryBall v (C - kTwo - kD - m),
      A.ψ v ((c : v.adicCompletion F) * z.1 ^ 2 +
        (d : v.adicCompletion F) * z.2 ^ 2) ∂(μ.prod μ) := by
  classical
  let K := v.adicCompletion F
  let V := K × K
  let ν := μ.prod μ
  let B := binaryBall v m
  let H : Set V := B ×ˢ B
  let R₁ := binaryBall v (C - kTwo - kC - m)
  let R₂ := binaryBall v (C - kTwo - kD - m)
  let core : Set V := R₁ ×ˢ R₂
  let E : Set (V × V) := L ×ˢ H
  let phase : V → ℂ := fun z => A.ψ v ((c : K) * z.1 ^ 2 + (d : K) * z.2 ^ 2)
  haveI : Measure.IsAddHaarMeasure ν := by
    dsimp [ν]
    infer_instance
  haveI : IsFiniteMeasureOnCompacts ν := by infer_instance
  haveI : SFinite ν := by infer_instance
  haveI : IsFiniteMeasureOnCompacts (ν.prod ν) := by infer_instance
  have hBopen : IsOpen B := binaryBall_open v m
  have hBcompact : IsCompact B := binaryBall_compact v m
  have hHopen : IsOpen H := hBopen.prod hBopen
  have hHcompact : IsCompact H := hBcompact.prod hBcompact
  have hHmeas : MeasurableSet H := hHopen.measurableSet
  have hCoreOpen : IsOpen core := (binaryBall_open v _).prod (binaryBall_open v _)
  have hCoreMeas : MeasurableSet core := hCoreOpen.measurableSet
  have hEopen : IsOpen E := hLopen.prod hHopen
  have hEcompact : IsCompact E := hLcompact.prod hHcompact
  have hEmeas : MeasurableSet E := hEopen.measurableSet
  have hHzero : (0 : V) ∈ H := by
    have hBzero : (0 : K) ∈ B := by
      change Valued.v (0 : K) ≤ WithZero.exp m
      simp
    exact ⟨hBzero, hBzero⟩
  let μH : ℂ := (ν.real H : ℂ)
  let IL : ℂ := ∫ z in L, phase z ∂ν
  let IC : ℂ := ∫ z in core, phase z ∂ν
  have hmass : μH = (μ.real B : ℂ) * (μ.real B : ℂ) := by
    simp [μH, ν, H, B]
  have hμHpos : 0 < ν.real H := by
    have hpos : 0 < ν H := hHopen.measure_pos ν ⟨0, hHzero⟩
    exact ENNReal.toReal_pos hpos.ne' hHcompact.measure_lt_top.ne
  have hμHne : μH ≠ 0 := by
    dsimp [μH]
    exact_mod_cast hμHpos.ne'
  have hphase : Continuous phase := by
    dsimp [phase]
    have hq : Continuous (fun z : V => (c : K) * z.1 ^ 2 + (d : K) * z.2 ^ 2) :=
      ((continuous_const_mul (c : K)).comp (continuous_fst.pow 2)).add
        ((continuous_const_mul (d : K)).comp (continuous_snd.pow 2))
    exact (local_character_regular D A v).1.comp hq
  let g₀ : V × V → ℂ := fun z => phase z.1
  let g₁ : V × V → ℂ := fun z => phase (z.1 + z.2)
  let f₀ : V × V → ℂ := E.indicator g₀
  let f₁ : V × V → ℂ := E.indicator g₁
  have hg₀ : Continuous g₀ := hphase.comp continuous_fst
  have hg₁ : Continuous g₁ := hphase.comp (continuous_fst.add continuous_snd)
  have hf₀ : Integrable f₀ (ν.prod ν) :=
    (hg₀.continuousOn.integrableOn_compact hEcompact).integrable_indicator hEmeas
  have hf₁ : Integrable f₁ (ν.prod ν) :=
    (hg₁.continuousOn.integrableOn_compact hEcompact).integrable_indicator hEmeas
  have hinner₀ (z : V) : ∫ h, f₀ (z, h) ∂ν =
      if z ∈ L then μH * phase z else 0 := by
    by_cases hz : z ∈ L
    · have hfun : (fun h => f₀ (z, h)) = H.indicator (fun _ => phase z) := by
        funext h
        by_cases hh : h ∈ H <;> simp [f₀, E, g₀, hz, hh]
      rw [hfun, integral_indicator hHmeas, setIntegral_const]
      simp [μH, hz, smul_eq_mul]
    · have hfun : (fun h => f₀ (z, h)) = fun _ => (0 : ℂ) := by
        funext h
        simp [f₀, E, hz]
      rw [hfun, if_neg hz]
      exact integral_eq_zero_of_ae (Filter.Eventually.of_forall fun _ => rfl)
  have hinner₁ (z : V) : ∫ h, f₁ (z, h) ∂ν =
      if z ∈ core then μH * phase z else 0 := by
    by_cases hz : z ∈ L
    · have hfun : (fun h => f₁ (z, h)) = H.indicator (fun h => phase (z + h)) := by
        funext h
        by_cases hh : h ∈ H <;> simp [f₁, E, g₁, hz, hh]
      rw [hfun, integral_indicator hHmeas]
      have hshifted := binary_shift_integral D A v μ c d C m kTwo kC kD hC hCnext
        hTwo hCval hDval hmNonpos hmC hmD hRmC hRmD hR0C hR0D z.1 z.2
      rw [hmass]
      change
        (∫ x in binaryBall v m ×ˢ binaryBall v m,
          A.ψ v ((c : K) * (z.1 + x.1) ^ 2 + (d : K) * (z.2 + x.2) ^ 2)
            ∂(μ.prod μ)) =
          if z.1 ∈ binaryBall v (C - kTwo - kC - m) ∧
              z.2 ∈ binaryBall v (C - kTwo - kD - m) then
            ((μ.real (binaryBall v m) : ℂ) * (μ.real (binaryBall v m) : ℂ)) *
              A.ψ v ((c : K) * z.1 ^ 2 + (d : K) * z.2 ^ 2)
          else 0
      exact hshifted
    · have hfun : (fun h => f₁ (z, h)) = fun _ => (0 : ℂ) := by
        funext h
        simp [f₁, E, hz]
      have hzcore : z ∉ core := by
        intro hmem
        exact hz (hcore hmem)
      rw [hfun, if_neg hzcore]
      exact integral_eq_zero_of_ae (Filter.Eventually.of_forall fun _ => rfl)
  have houter₀ : (fun z => ∫ h, f₀ (z, h) ∂ν) =
      L.indicator (fun z => μH * phase z) := by
    funext z
    rw [hinner₀ z]
    by_cases hz : z ∈ L <;> simp [hz]
  have houter₁ : (fun z => ∫ h, f₁ (z, h) ∂ν) =
      core.indicator (fun z => μH * phase z) := by
    funext z
    rw [hinner₁ z]
    by_cases hz : z ∈ core <;> simp [hz]
  have hprod₀ : ∫ z, f₀ z ∂(ν.prod ν) = μH * IL := by
    rw [integral_prod f₀ hf₀, houter₀, integral_indicator hLopen.measurableSet,
      integral_const_mul]
  have hprod₁ : ∫ z, f₁ z ∂(ν.prod ν) = μH * IC := by
    rw [integral_prod f₁ hf₁, houter₁, integral_indicator hCoreMeas,
      integral_const_mul]
  let e : (V × V) ≃ᵐ (V × V) :=
    (MeasurableEquiv.prodComm (α := V) (β := V)).trans
      ((MeasurableEquiv.shearAddRight V).trans
        (MeasurableEquiv.prodComm (α := V) (β := V)))
  have he (z : V × V) : e z = (z.1 + z.2, z.2) := by
    rcases z with ⟨z, h⟩
    simp [e, MeasurableEquiv.prodComm, MeasurableEquiv.shearAddRight,
      Equiv.prodComm_apply, Equiv.prodShear_apply, add_comm]
  have hEinv (z : V × V) : e z ∈ E ↔ z ∈ E := by
    rcases z with ⟨z, h⟩
    rw [he (z, h)]
    change (z + h ∈ L ∧ h ∈ H) ↔ (z ∈ L ∧ h ∈ H)
    constructor
    · rintro ⟨hzh, hh⟩
      exact ⟨(hLshift z h hh).1 hzh, hh⟩
    · rintro ⟨hz, hh⟩
      exact ⟨(hLshift z h hh).2 hz, hh⟩
  have hfe : (fun z => f₀ (e z)) = f₁ := by
    funext z
    simp only [f₀, f₁, Set.indicator_apply, g₀, g₁]
    have htuple : (z.1 + z.2, z.2) ∈ E ↔ z ∈ E := by
      rw [← he z]
      exact hEinv z
    simp only [he z]
    simp [htuple]
  have hMP : MeasurePreserving e (ν.prod ν) (ν.prod ν) := by
    convert measurePreserving_add_prod ν ν using 1
    funext z
    exact he z
  have hshift : ∫ z, f₀ (e z) ∂(ν.prod ν) = ∫ z, f₀ z ∂(ν.prod ν) :=
    hMP.integral_comp e.measurableEmbedding f₀
  have hEq : μH * IL = μH * IC := by
    calc
      μH * IL = ∫ z, f₀ z ∂(ν.prod ν) := hprod₀.symm
      _ = ∫ z, f₀ (e z) ∂(ν.prod ν) := hshift.symm
      _ = ∫ z, f₁ z ∂(ν.prod ν) := by rw [hfe]
      _ = μH * IC := hprod₁
  have hIL : IL = IC := mul_left_cancel₀ hμHne hEq
  simpa [IL, IC, ν, core, R₁, R₂, phase] using hIL

private theorem binary_map_haar (v : FinPlace F)
    (μ : Measure (v.adicCompletion F)) [Measure.IsAddHaarMeasure μ]
    (α β : v.adicCompletion F) (hαβ : α + β = 1) :
    MeasurePreserving (fun z : (v.adicCompletion F) × (v.adicCompletion F) =>
      (α * z.1 + β * z.2, z.1 - z.2)) (μ.prod μ) (μ.prod μ) := by
  let K := v.adicCompletion F
  have hsub : MeasurePreserving (fun z : K × K => (z.1 - z.2, z.2))
      (μ.prod μ) (μ.prod μ) := by
    simpa using measurePreserving_sub_prod μ μ
  have hshear : MeasurePreserving (fun z : K × K => (z.1, α * z.1 + z.2))
      (μ.prod μ) (μ.prod μ) := by
    haveI : SFinite μ := by infer_instance
    refine MeasurePreserving.skew_product (μa := μ) (μb := μ) (μc := μ) (μd := μ)
      (f := id) (g := fun x y : K => α * x + y) (MeasurePreserving.id μ) ?_ ?_
    · fun_prop
    · filter_upwards [] with x
      simpa using (map_add_left_eq_self μ (α * x))
  have hswap : MeasurePreserving (fun z : K × K => z.swap)
      (μ.prod μ) (μ.prod μ) := by
    simpa using (Measure.measurePreserving_swap (μ := μ) (ν := μ))
  have hcomp := hswap.comp (hshear.comp hsub)
  have hβ : 1 - α = β := by
    calc
      1 - α = (α + β) - α := by rw [hαβ]
      _ = β := by ring
  have hfirst (x y : K) : α * (x - y) + y = α * x + β * y := by
    calc
      α * (x - y) + y = α * x + (1 - α) * y := by ring
      _ = α * x + β * y := by rw [hβ]
  convert hcomp using 1
  funext z
  rcases z with ⟨x, y⟩
  exact Prod.ext (hfirst x y).symm rfl

private theorem binary_rectangle_factor (A : AddCharData F) (v : FinPlace F)
    (μ : Measure (v.adicCompletion F)) [Measure.IsAddHaarMeasure μ]
    (c d : (v.adicCompletion F)ˣ)
    (N M : ℕ) :
    ∫ z in binaryBall v (N : ℤ) ×ˢ binaryBall v (M : ℤ),
      A.ψ v ((c : v.adicCompletion F) * z.1 ^ 2 +
        (d : v.adicCompletion F) * z.2 ^ 2) ∂(μ.prod μ) =
      quadraticIntegral A v μ c N * quadraticIntegral A v μ d M := by
  classical
  let B₁ := binaryBall v (N : ℤ)
  let B₂ := binaryBall v (M : ℤ)
  have hB₁open : IsOpen B₁ := binaryBall_open v _
  have hB₂open : IsOpen B₂ := binaryBall_open v _
  have hrect : MeasurableSet (B₁ ×ˢ B₂) := (hB₁open.prod hB₂open).measurableSet
  have hpoint (z : v.adicCompletion F × v.adicCompletion F) :
      A.ψ v ((c : v.adicCompletion F) * z.1 ^ 2 + (d : v.adicCompletion F) * z.2 ^ 2) =
        A.ψ v ((c : v.adicCompletion F) * z.1 ^ 2) *
          A.ψ v ((d : v.adicCompletion F) * z.2 ^ 2) := by
    rw [← AddChar.map_add_eq_mul]
  calc
    _ = ∫ z in B₁ ×ˢ B₂,
          A.ψ v ((c : v.adicCompletion F) * z.1 ^ 2) *
            A.ψ v ((d : v.adicCompletion F) * z.2 ^ 2) ∂(μ.prod μ) := by
          apply setIntegral_congr_fun hrect
          intro z hz
          exact hpoint z
    _ = (∫ x in B₁, A.ψ v ((c : v.adicCompletion F) * x ^ 2) ∂μ) *
          ∫ y in B₂, A.ψ v ((d : v.adicCompletion F) * y ^ 2) ∂μ := by
          exact setIntegral_prod_mul (μ := μ) (ν := μ)
            (fun x : v.adicCompletion F => A.ψ v ((c : v.adicCompletion F) * x ^ 2))
            (fun y : v.adicCompletion F => A.ψ v ((d : v.adicCompletion F) * y ^ 2)) B₁ B₂
    _ = quadraticIntegral A v μ c N * quadraticIntegral A v μ d M := by
          congr 1 <;> simp [quadraticIntegral, localBall, B₁, B₂, binaryBall]

private theorem binary_int_le_natAbs (q : ℤ) : q ≤ (q.natAbs : ℤ) := by
  cases q with
  | ofNat n => simp
  | negSucc n => simp; omega

private theorem binary_int_neg_le_natAbs (q : ℤ) : -q ≤ (q.natAbs : ℤ) := by
  have h := binary_int_le_natAbs (-q)
  simpa using h

private theorem binary_linear_add_bound (v : FinPlace F)
    {x y g : v.adicCompletion F} {kx ky kg N : ℤ}
    (hx : Valued.v x ≤ WithZero.exp kx) (hy : Valued.v y ≤ WithZero.exp ky)
    (hg : Valued.v g = WithZero.exp kg) (hkx : kx ≤ N) (hkgky : kg + ky ≤ N) :
    Valued.v (x + g * y) ≤ WithZero.exp N := by
  have hgy := binary_valued_mul_le v (le_of_eq hg) hy
  have hxN : Valued.v x ≤ WithZero.exp N := hx.trans (WithZero.exp_le_exp.mpr hkx)
  have hgyN : Valued.v (g * y) ≤ WithZero.exp N :=
    hgy.trans (WithZero.exp_le_exp.mpr hkgky)
  exact (Valued.v.map_add x (g * y)).trans (max_le hxN hgyN)

private theorem binary_linear_sub_bound (v : FinPlace F)
    {x y g : v.adicCompletion F} {kx ky kg N : ℤ}
    (hx : Valued.v x ≤ WithZero.exp kx) (hy : Valued.v y ≤ WithZero.exp ky)
    (hg : Valued.v g = WithZero.exp kg) (hkx : kx ≤ N) (hkgky : kg + ky ≤ N) :
    Valued.v (x - g * y) ≤ WithZero.exp N := by
  have hgy := binary_valued_mul_le v (le_of_eq hg) hy
  have hneg : Valued.v (-(g * y)) ≤ WithZero.exp (kg + ky) := by
    rw [Valuation.map_neg]
    exact hgy
  have hxN : Valued.v x ≤ WithZero.exp N := hx.trans (WithZero.exp_le_exp.mpr hkx)
  have hnegN : Valued.v (-(g * y)) ≤ WithZero.exp N :=
    hneg.trans (WithZero.exp_le_exp.mpr hkgky)
  simpa [sub_eq_add_neg] using
    (Valued.v.map_add x (-(g * y))).trans (max_le hxN hnegN)

theorem local_index_binary_actual (D : FieldData F) (A : AddCharData F)
    (W : LocalGaussianData A) (v : FinPlace F)
    (a b : (v.adicCompletion F)ˣ)
    (hab : (a : v.adicCompletion F) + (b : v.adicCompletion F) ≠ 0) :
    W.index v a * W.index v b =
      W.index v (Units.mk0 _ hab) * W.index v (a * b / Units.mk0 _ hab) := by
  classical
  let K := v.adicCompletion F
  let μ := W.measure v
  letI : Measure.IsAddHaarMeasure μ := W.isHaar v
  let c : Kˣ := Units.mk0 ((a : K) + (b : K)) hab
  let d : Kˣ := a * b / c
  let α : K := (a : K) / (c : K)
  let β : K := (b : K) / (c : K)
  have hcval : (c : K) = (a : K) + (b : K) := rfl
  have hαβ : α + β = 1 := by
    dsimp [α, β]
    calc
      (a : K) / (c : K) + (b : K) / (c : K) = ((a : K) + (b : K)) / (c : K) := by
        rw [← add_div]
      _ = 1 := by
        rw [hcval]
        exact div_self hab
  let eEquiv : (K × K) ≃ (K × K) :=
    { toFun := fun z => (α * z.1 + β * z.2, z.1 - z.2)
      invFun := fun z => (z.1 + β * z.2, z.1 - α * z.2)
      left_inv := by
        intro z
        rcases z with ⟨x, y⟩
        apply Prod.ext
        · calc
            (α * x + β * y) + β * (x - y) = (α + β) * x := by ring
            _ = x := by rw [hαβ, one_mul]
        · calc
            (α * x + β * y) - α * (x - y) = (α + β) * y := by ring
            _ = y := by rw [hαβ, one_mul]
      right_inv := by
        intro z
        rcases z with ⟨x, y⟩
        apply Prod.ext
        · calc
            α * (x + β * y) + β * (x - α * y) = (α + β) * x := by ring
            _ = x := by rw [hαβ, one_mul]
        · calc
            (x + β * y) - (x - α * y) = (α + β) * y := by ring
            _ = y := by rw [hαβ, one_mul] }
  let e : (K × K) ≃ᵐ (K × K) :=
    { toEquiv := eEquiv
      measurable_toFun := by
        change Measurable (fun z : K × K => (α * z.1 + β * z.2, z.1 - z.2))
        fun_prop
      measurable_invFun := by
        change Measurable (fun z : K × K => (z.1 + β * z.2, z.1 - α * z.2))
        fun_prop }
  have hecont : Continuous e := by
    change Continuous (fun z : K × K => (α * z.1 + β * z.2, z.1 - z.2))
    fun_prop
  have heInvCont : Continuous e.symm := by
    change Continuous (fun z : K × K => (z.1 + β * z.2, z.1 - α * z.2))
    fun_prop
  have heSymm (z : K × K) : e.symm z = (z.1 + β * z.2, z.1 - α * z.2) := rfl
  have hinvAdd (z h : K × K) : e.symm (z + h) = e.symm z + e.symm h := by
    rw [heSymm, heSymm, heSymm]
    rcases z with ⟨x, y⟩
    rcases h with ⟨u, w⟩
    apply Prod.ext <;> simp [Prod.fst_add, Prod.snd_add] <;> ring
  obtain ⟨C, hCnonneg, hC, hCnext⟩ := character_conductor_cutoff D A v
  have hTwoNe : (2 : K) ≠ 0 := by norm_num
  obtain ⟨kTwo, hTwo⟩ := binary_value_exp v (x := (2 : K)) hTwoNe
  obtain ⟨kC, hCvalExp⟩ := binary_value_exp v (x := (c : K)) c.ne_zero
  obtain ⟨kD, hDvalExp⟩ := binary_value_exp v (x := (d : K)) d.ne_zero
  have hαne : α ≠ 0 := div_ne_zero a.ne_zero c.ne_zero
  have hβne : β ≠ 0 := div_ne_zero b.ne_zero c.ne_zero
  obtain ⟨kAlpha, hAlphaVal⟩ := binary_value_exp v (x := α) hαne
  obtain ⟨kBeta, hBetaVal⟩ := binary_value_exp v (x := β) hβne
  let M : ℕ := C.natAbs + kTwo.natAbs + kC.natAbs + kD.natAbs +
    W.cutoff v c + W.cutoff v d + 1
  let m : ℤ := -(M : ℤ)
  have hMbase : (C.natAbs : ℤ) + kTwo.natAbs + kC.natAbs + kD.natAbs +
      (W.cutoff v c : ℤ) + W.cutoff v d + 1 ≤ (M : ℤ) := by
    dsimp [M]
    push_cast
    omega
  have hAbsC : -C ≤ (C.natAbs : ℤ) := binary_int_neg_le_natAbs C
  have hAbsTwo : kTwo ≤ (kTwo.natAbs : ℤ) := binary_int_le_natAbs kTwo
  have hAbsCVal : kC ≤ (kC.natAbs : ℤ) := binary_int_le_natAbs kC
  have hAbsDVal : kD ≤ (kD.natAbs : ℤ) := binary_int_le_natAbs kD
  have hMnonneg : 0 ≤ (M : ℤ) := by dsimp [M]; omega
  have hmNonpos : m ≤ 0 := by dsimp [m]; omega
  have hmC : kC + 2 * m ≤ 0 := by dsimp [m]; omega
  have hmD : kD + 2 * m ≤ 0 := by dsimp [m]; omega
  have hRmC : m ≤ C - kTwo - kC - m := by dsimp [m]; omega
  have hRmD : m ≤ C - kTwo - kD - m := by dsimp [m]; omega
  have hR0C : 0 ≤ C - kTwo - kC - m := by dsimp [m]; omega
  have hR0D : 0 ≤ C - kTwo - kD - m := by dsimp [m]; omega
  have hCutC : (W.cutoff v c : ℤ) ≤ C - kTwo - kC - m := by
    dsimp [m]
    omega
  have hCutD : (W.cutoff v d : ℤ) ≤ C - kTwo - kD - m := by
    dsimp [m]
    omega
  let nC : ℕ := (C - kTwo - kC - m).toNat
  let nD : ℕ := (C - kTwo - kD - m).toNat
  have hnCcast : (nC : ℤ) = C - kTwo - kC - m :=
    Int.toNat_of_nonneg hR0C
  have hnDcast : (nD : ℤ) = C - kTwo - kD - m :=
    Int.toNat_of_nonneg hR0D
  have hNC : W.cutoff v c ≤ nC := by
    have h : (W.cutoff v c : ℤ) ≤ (nC : ℤ) := by rw [hnCcast]; exact hCutC
    exact_mod_cast h
  have hND : W.cutoff v d ≤ nD := by
    have h : (W.cutoff v d : ℤ) ≤ (nD : ℤ) := by rw [hnDcast]; exact hCutD
    exact_mod_cast h
  let N : ℕ := W.cutoff v a + W.cutoff v b + M +
    (C - kTwo - kC - m).natAbs + (C - kTwo - kD - m).natAbs +
      kAlpha.natAbs + kBeta.natAbs
  have hNcutA : W.cutoff v a ≤ N := by dsimp [N]; omega
  have hNcutB : W.cutoff v b ≤ N := by dsimp [N]; omega
  have hNgeMNat : M ≤ N := by dsimp [N]; omega
  have hNgeM : (M : ℤ) ≤ (N : ℤ) := by exact_mod_cast hNgeMNat
  have hNm : m ≤ (N : ℤ) := by dsimp [m]; omega
  have hNalphaAbsNat : kAlpha.natAbs ≤ N := by dsimp [N]; omega
  have hNbetaAbsNat : kBeta.natAbs ≤ N := by dsimp [N]; omega
  have hNR1AbsNat : (C - kTwo - kC - m).natAbs ≤ N := by dsimp [N]; omega
  have hNR2AbsNat : (C - kTwo - kD - m).natAbs ≤ N := by dsimp [N]; omega
  have hNalphaAbs : (kAlpha.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hNalphaAbsNat
  have hNbetaAbs : (kBeta.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hNbetaAbsNat
  have hNR1Abs : ((C - kTwo - kC - m).natAbs : ℤ) ≤ (N : ℤ) := by
    exact_mod_cast hNR1AbsNat
  have hNR2Abs : ((C - kTwo - kD - m).natAbs : ℤ) ≤ (N : ℤ) := by
    exact_mod_cast hNR2AbsNat
  have hNalphaM : kAlpha + m ≤ (N : ℤ) := by
    have hAabs := binary_int_le_natAbs kAlpha
    have hstep : kAlpha + m ≤ (kAlpha.natAbs : ℤ) := by dsimp [m]; omega
    exact hstep.trans hNalphaAbs
  have hNbetaM : kBeta + m ≤ (N : ℤ) := by
    have hBabs := binary_int_le_natAbs kBeta
    have hstep : kBeta + m ≤ (kBeta.natAbs : ℤ) := by dsimp [m]; omega
    exact hstep.trans hNbetaAbs
  have hNR1 : C - kTwo - kC - m ≤ (N : ℤ) := by
    have h := binary_int_le_natAbs (C - kTwo - kC - m)
    exact h.trans hNR1Abs
  have hNR2 : C - kTwo - kD - m ≤ (N : ℤ) := by
    have h := binary_int_le_natAbs (C - kTwo - kD - m)
    exact h.trans hNR2Abs
  have hNBetaR2 : kBeta + (C - kTwo - kD - m) ≤ (N : ℤ) := by
    have hBabs := binary_int_le_natAbs kBeta
    have hRabs := binary_int_le_natAbs (C - kTwo - kD - m)
    have hsum : kBeta + (C - kTwo - kD - m) ≤
        (kBeta.natAbs : ℤ) + (C - kTwo - kD - m).natAbs := by omega
    have hsumNnat : kBeta.natAbs + (C - kTwo - kD - m).natAbs ≤ N := by
      dsimp [N]
      omega
    have hsumN : (kBeta.natAbs : ℤ) + (C - kTwo - kD - m).natAbs ≤ (N : ℤ) :=
      by exact_mod_cast hsumNnat
    exact hsum.trans hsumN
  have hNAlphaR2 : kAlpha + (C - kTwo - kD - m) ≤ (N : ℤ) := by
    have hAabs := binary_int_le_natAbs kAlpha
    have hRabs := binary_int_le_natAbs (C - kTwo - kD - m)
    have hsum : kAlpha + (C - kTwo - kD - m) ≤
        (kAlpha.natAbs : ℤ) + (C - kTwo - kD - m).natAbs := by omega
    have hsumNnat : kAlpha.natAbs + (C - kTwo - kD - m).natAbs ≤ N := by
      dsimp [N]
      omega
    have hsumN : (kAlpha.natAbs : ℤ) + (C - kTwo - kD - m).natAbs ≤ (N : ℤ) :=
      by exact_mod_cast hsumNnat
    exact hsum.trans hsumN
  have hRectOpen : IsOpen (binaryBall v (N : ℤ) ×ˢ binaryBall v (N : ℤ)) :=
    (binaryBall_open v _).prod (binaryBall_open v _)
  have hRectCompact : IsCompact (binaryBall v (N : ℤ) ×ˢ binaryBall v (N : ℤ)) :=
    (binaryBall_compact v _).prod (binaryBall_compact v _)
  let rect : Set (K × K) := binaryBall v (N : ℤ) ×ˢ binaryBall v (N : ℤ)
  let L : Set (K × K) := e '' rect
  have hRectMeas : MeasurableSet rect := hRectOpen.measurableSet
  have hLmem (z : K × K) : z ∈ L ↔ e.symm z ∈ rect := by
    dsimp [L]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hx
      exact ⟨e.symm z, hx, by simp⟩
  have hLdef : L = e.symm ⁻¹' rect := by
    ext z
    exact hLmem z
  have hLopen : IsOpen L := by
    rw [hLdef]
    exact hRectOpen.preimage heInvCont
  have hLcompact : IsCompact L := by
    dsimp [L]
    exact hRectCompact.image hecont
  have hRectAdd : ∀ x y : K × K, x ∈ rect → y ∈ rect → x + y ∈ rect := by
    intro x y hx hy
    have hx' := (Set.mem_prod_eq.mp hx)
    have hy' := (Set.mem_prod_eq.mp hy)
    apply Set.mem_prod_eq.mpr
    exact ⟨binaryBall_add v (N : ℤ) hx'.1 hy'.1,
      binaryBall_add v (N : ℤ) hx'.2 hy'.2⟩
  have hRectNeg : ∀ x : K × K, x ∈ rect → -x ∈ rect := by
    intro x hx
    have hx' := (Set.mem_prod_eq.mp hx)
    apply Set.mem_prod_eq.mpr
    exact ⟨binaryBall_neg v (N : ℤ) hx'.1, binaryBall_neg v (N : ℤ) hx'.2⟩
  have hsmallRect : ∀ h₀ : K × K, h₀ ∈ binaryBall v m ×ˢ binaryBall v m →
      e.symm h₀ ∈ rect := by
    intro h₀ hh
    rcases h₀ with ⟨x, y⟩
    have hh' := (Set.mem_prod_eq.mp hh)
    have hxv : Valued.v x ≤ WithZero.exp m := hh'.1
    have hyv : Valued.v y ≤ WithZero.exp m := hh'.2
    have hfirst : Valued.v (x + β * y) ≤ WithZero.exp (N : ℤ) :=
      binary_linear_add_bound v hxv hyv hBetaVal hNm hNbetaM
    have hsecond : Valued.v (x - α * y) ≤ WithZero.exp (N : ℤ) :=
      binary_linear_sub_bound v hxv hyv hAlphaVal hNm hNalphaM
    change Valued.v (e.symm (x, y)).1 ≤ WithZero.exp (N : ℤ) ∧
      Valued.v (e.symm (x, y)).2 ≤ WithZero.exp (N : ℤ)
    rw [heSymm]
    exact ⟨hfirst, hsecond⟩
  have hcoreRect : ∀ z : K × K, z ∈
      binaryBall v (C - kTwo - kC - m) ×ˢ binaryBall v (C - kTwo - kD - m) →
      e.symm z ∈ rect := by
    intro z hz
    have hz' := (Set.mem_prod_eq.mp hz)
    have hz1 : Valued.v z.1 ≤ WithZero.exp (C - kTwo - kC - m) := hz'.1
    have hz2 : Valued.v z.2 ≤ WithZero.exp (C - kTwo - kD - m) := hz'.2
    have hfirst : Valued.v (z.1 + β * z.2) ≤ WithZero.exp (N : ℤ) :=
      binary_linear_add_bound v hz1 hz2 hBetaVal hNR1 hNBetaR2
    have hsecond : Valued.v (z.1 - α * z.2) ≤ WithZero.exp (N : ℤ) :=
      binary_linear_sub_bound v hz1 hz2 hAlphaVal hNR1 hNAlphaR2
    change Valued.v (e.symm z).1 ≤ WithZero.exp (N : ℤ) ∧
      Valued.v (e.symm z).2 ≤ WithZero.exp (N : ℤ)
    rw [heSymm]
    exact ⟨hfirst, hsecond⟩
  have hLcore :
      binaryBall v (C - kTwo - kC - m) ×ˢ
        binaryBall v (C - kTwo - kD - m) ⊆ L := by
    intro z hz
    exact (hLmem z).2 (hcoreRect z hz)
  have hLadd (x y : K × K) (hx : x ∈ L) (hy : y ∈ L) : x + y ∈ L := by
    apply (hLmem (x + y)).2
    rw [hinvAdd]
    exact hRectAdd _ _ ((hLmem x).1 hx) ((hLmem y).1 hy)
  have hLneg (x : K × K) (hx : x ∈ L) : -x ∈ L := by
    apply (hLmem (-x)).2
    have hlinv : e.symm (-x) = -(e.symm x) := by
      rw [heSymm]
      rcases x with ⟨x, y⟩
      apply Prod.ext <;> simp [heSymm] <;> ring
    rw [hlinv]
    exact hRectNeg _ ((hLmem x).1 hx)
  have hLshift : ∀ z h₀, h₀ ∈ binaryBall v m ×ˢ binaryBall v m →
      (z + h₀ ∈ L ↔ z ∈ L) := by
    intro z h₀ hh
    have hhL : h₀ ∈ L := (hLmem h₀).2 (hsmallRect h₀ hh)
    constructor
    · intro hzh
      have hneg := hLneg h₀ hhL
      have hsum := hLadd (z + h₀) (-h₀) hzh hneg
      have hcancel : (z + h₀) + (-h₀) = z := by
        calc
          (z + h₀) + (-h₀) = z + (h₀ + (-h₀)) := by rw [add_assoc]
          _ = z := by simp
      rw [hcancel] at hsum
      exact hsum
    · intro hz
      exact hLadd z h₀ hz hhL
  have hquadratic (x y : K) :
      (a : K) * x ^ 2 + (b : K) * y ^ 2 =
        (c : K) * (α * x + β * y) ^ 2 + (d : K) * (x - y) ^ 2 := by
    change (a : K) * x ^ 2 + (b : K) * y ^ 2 =
      ((a : K) + (b : K)) *
          (((a : K) / ((a : K) + (b : K)) * x +
            (b : K) / ((a : K) + (b : K)) * y) ^ 2) +
        (((a : K) * (b : K)) / ((a : K) + (b : K))) * (x - y) ^ 2
    field_simp [hab]
    ring
  let phase : K × K → ℂ := fun z => A.ψ v ((c : K) * z.1 ^ 2 + (d : K) * z.2 ^ 2)
  have hphaseMap (z : K × K) :
      A.ψ v ((a : K) * z.1 ^ 2 + (b : K) * z.2 ^ 2) = phase (e z) := by
    rw [hquadratic]
    rfl
  have hMP : MeasurePreserving e (μ.prod μ) (μ.prod μ) := by
    have h := binary_map_haar v μ α β hαβ
    convert h using 1
  let f : K × K → ℂ := L.indicator phase
  have hpre (z : K × K) : e z ∈ L ↔ z ∈ rect := by
    rw [hLmem]
    simp
  have hfun : (fun z => f (e z)) = rect.indicator (fun z => phase (e z)) := by
    funext z
    by_cases hz : z ∈ rect
    · have hez : e z ∈ L := (hpre z).2 hz
      simp [f, hz, hez]
    · have hez : e z ∉ L := fun h => hz ((hpre z).1 h)
      simp [f, hz, hez]
  have hchange :
      ∫ z in rect, phase (e z) ∂(μ.prod μ) =
        ∫ z in L, phase z ∂(μ.prod μ) := by
    calc
      ∫ z in rect, phase (e z) ∂(μ.prod μ) =
          ∫ z, rect.indicator (fun z => phase (e z)) z ∂(μ.prod μ) := by
            rw [← integral_indicator hRectMeas]
      _ = ∫ z, f (e z) ∂(μ.prod μ) := by rw [← hfun]
      _ = ∫ z, f z ∂(μ.prod μ) := hMP.integral_comp e.measurableEmbedding f
      _ = ∫ z in L, phase z ∂(μ.prod μ) := by
            rw [← integral_indicator hLopen.measurableSet]
  have hsourceTransform :
      ∫ z in rect,
        A.ψ v ((a : K) * z.1 ^ 2 + (b : K) * z.2 ^ 2) ∂(μ.prod μ) =
        ∫ z in L, phase z ∂(μ.prod μ) := by
    calc
      _ = ∫ z in rect, phase (e z) ∂(μ.prod μ) := by
            apply setIntegral_congr_fun hRectMeas
            intro z hz
            exact hphaseMap z
      _ = _ := hchange
  have hcentral := binary_compactOpen_integral D A v μ c d C m kTwo kC kD
    hC hCnext hTwo hCvalExp hDvalExp hmNonpos hmC hmD hRmC hRmD hR0C hR0D
    L hLopen hLcompact hLshift hLcore
  have hrectFactAB := binary_rectangle_factor A v μ a b N N
  have hrectFactCD := binary_rectangle_factor A v μ c d nC nD
  have hGaussianCutoff :
      quadraticIntegral A v μ a N * quadraticIntegral A v μ b N =
        quadraticIntegral A v μ c nC * quadraticIntegral A v μ d nD := by
    calc
      _ = ∫ z in rect,
          A.ψ v ((a : K) * z.1 ^ 2 + (b : K) * z.2 ^ 2) ∂(μ.prod μ) := hrectFactAB.symm
      _ = ∫ z in L, phase z ∂(μ.prod μ) := hsourceTransform
      _ = ∫ z in binaryBall v (C - kTwo - kC - m) ×ˢ
          binaryBall v (C - kTwo - kD - m),
            A.ψ v ((c : K) * z.1 ^ 2 + (d : K) * z.2 ^ 2) ∂(μ.prod μ) := hcentral
      _ = _ := by simpa [hnCcast, hnDcast] using hrectFactCD
  have hNa : W.cutoff v a ≤ N := hNcutA
  have hNb : W.cutoff v b ≤ N := hNcutB
  have hstableA : W.stableValue v a = quadraticIntegral A v μ a N := by
    simpa [LocalGaussianData.stableValue, μ] using (W.stable v a N hNa).symm
  have hstableB : W.stableValue v b = quadraticIntegral A v μ b N := by
    simpa [LocalGaussianData.stableValue, μ] using (W.stable v b N hNb).symm
  have hstableC : W.stableValue v c = quadraticIntegral A v μ c nC := by
    simpa [LocalGaussianData.stableValue, μ] using (W.stable v c nC hNC).symm
  have hstableD : W.stableValue v d = quadraticIntegral A v μ d nD := by
    simpa [LocalGaussianData.stableValue, μ] using (W.stable v d nD hND).symm
  have hstableProduct :
      W.stableValue v a * W.stableValue v b = W.stableValue v c * W.stableValue v d := by
    calc
      _ = quadraticIntegral A v μ a N * quadraticIntegral A v μ b N := by
            rw [hstableA, hstableB]
      _ = quadraticIntegral A v μ c nC * quadraticIntegral A v μ d nD := hGaussianCutoff
      _ = _ := by rw [← hstableC, ← hstableD]
  have habsMul := (ArtinPrimitiveRoots.Proofs.a1_weil_sol.local_absolute_value v).2.2
  have hapos := (ArtinPrimitiveRoots.Proofs.a1_weil_sol.local_absolute_value v).2.1
  have hcd : c * d = a * b := by
    apply Units.ext
    change ((a : K) + (b : K)) *
        (((a : K) * (b : K)) / ((a : K) + (b : K))) =
      (a : K) * (b : K)
    calc
      ((a : K) + (b : K)) * (((a : K) * (b : K)) / ((a : K) + (b : K))) =
          (((a : K) + (b : K)) * ((a : K) * (b : K))) / ((a : K) + (b : K)) := by
            rw [← mul_div_assoc]
      _ = (a : K) * (b : K) :=
        mul_div_cancel_left₀ (b := (a : K) * (b : K))
          (a := (a : K) + (b : K)) hab
  have habs : absFin v (a : K) * absFin v (b : K) =
      absFin v (c : K) * absFin v (d : K) := by
    calc
      absFin v (a : K) * absFin v (b : K) = absFin v ((a * b : Kˣ) : K) :=
        (habsMul a b).symm
      _ = absFin v ((c * d : Kˣ) : K) := by rw [← hcd]
      _ = absFin v (c : K) * absFin v (d : K) := habsMul c d
  let ra : ℝ := absFin v (a : K)
  let rb : ℝ := absFin v (b : K)
  let rc : ℝ := absFin v (c : K)
  let rd : ℝ := absFin v (d : K)
  have hra : 0 < ra := by simpa [ra] using hapos a
  have hrb : 0 < rb := by simpa [rb] using hapos b
  have hrc : 0 < rc := by simpa [rc] using hapos c
  have hrd : 0 < rd := by simpa [rd] using hapos d
  have hroot : ra ^ (1 / 2 : ℝ) * rb ^ (1 / 2 : ℝ) =
      rc ^ (1 / 2 : ℝ) * rd ^ (1 / 2 : ℝ) := by
    have habs' : ra * rb = rc * rd := by simpa [ra, rb, rc, rd] using habs
    calc
      ra ^ (1 / 2 : ℝ) * rb ^ (1 / 2 : ℝ) = (ra * rb) ^ (1 / 2 : ℝ) :=
        (Real.mul_rpow hra.le hrb.le).symm
      _ = (rc * rd) ^ (1 / 2 : ℝ) := by rw [habs']
      _ = rc ^ (1 / 2 : ℝ) * rd ^ (1 / 2 : ℝ) := Real.mul_rpow hrc.le hrd.le
  let qa : ℂ := ((ra ^ (1 / 2 : ℝ) : ℝ) : ℂ)
  let qb : ℂ := ((rb ^ (1 / 2 : ℝ) : ℝ) : ℂ)
  let qc : ℂ := ((rc ^ (1 / 2 : ℝ) : ℝ) : ℂ)
  let qd : ℂ := ((rd ^ (1 / 2 : ℝ) : ℝ) : ℂ)
  have hrootC : qa * qb = qc * qd := by
    dsimp [qa, qb, qc, qd]
    exact_mod_cast hroot
  have hden : W.stableValue v (1 : Kˣ) ≠ 0 := W.integral_ne_zero v 1
  apply Units.ext
  change ((qa * W.stableValue v a / W.stableValue v (1 : Kˣ)) *
      (qb * W.stableValue v b / W.stableValue v (1 : Kˣ))) =
    ((qc * W.stableValue v c / W.stableValue v (1 : Kˣ)) *
      (qd * W.stableValue v d / W.stableValue v (1 : Kˣ)))
  field_simp [hden]
  calc
    qa * W.stableValue v a * qb * W.stableValue v b =
      (qa * qb) * (W.stableValue v a * W.stableValue v b) := by ring
    _ = ((qc * qd) *
        (W.stableValue v c * W.stableValue v d)) := by rw [hrootC, hstableProduct]
    _ = qc * W.stableValue v c * qd * W.stableValue v d := by ring

end ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_e
