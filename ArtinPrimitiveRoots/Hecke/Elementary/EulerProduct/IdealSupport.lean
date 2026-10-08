/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.

This module reuses TauCeti's canonical Dedekind-ideal support API and adds the eventual
finite-set support lemma needed by the local Euler-product proof.
-/
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.NumberTheory.NumberField.Basic
import TauCeti.RingTheory.DedekindDomain.Ideal

public section

open _root_.IsDedekindDomain
open scoped nonZeroDivisors NumberField

/-! A finite set containing every prime divisor of an ideal eventually supports that ideal. -/
theorem eventually_isPrimeTo_compl {K : Type*} [Field K] [NumberField K]
    (A : (Ideal (𝓞 K))⁰) :
    ∀ᶠ S : Finset (HeightOneSpectrum (𝓞 K)) in Filter.atTop,
      Ideal.IsPrimeTo (A : Ideal (𝓞 K)) (S : Set (HeightOneSpectrum (𝓞 K)))ᶜ := by
  classical
  let F := Ideal.finite_factors (nonZeroDivisors.coe_ne_zero A)
  let T : Finset (HeightOneSpectrum (𝓞 K)) := F.toFinset
  filter_upwards [Filter.eventually_ge_atTop T] with S hTS
  rw [Ideal.isPrimeTo_iff]
  refine ⟨nonZeroDivisors.coe_ne_zero A, fun P hP hPdvd ↦ hP ?_⟩
  exact hTS (F.mem_toFinset.mpr hPdvd)

end
