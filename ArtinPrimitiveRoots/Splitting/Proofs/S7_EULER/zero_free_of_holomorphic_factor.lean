import ArtinPrimitiveRoots.Splitting.Proofs.S7_EULER.dedekindZetaSharp_meromorphic

set_option autoImplicit false
open scoped NumberField BigOperators
open scoped Topology
open NumberField IsDedekindDomain
open Filter
noncomputable section
namespace ArtinPrimitiveRoots.Splitting
open ClassFieldTheory ArtinPrimitiveRoots.Hecke

/-- A holomorphic factor has nonnegative order, so nonpositive upstairs orders
descend to the base. Guide: ../sol-thin-s7/PROOFS.md:524–550.
Uses `dedekindZetaSharp_meromorphic` and meromorphic order multiplication;
feeds `spl_kummer_zero_free`. -/
theorem zero_free_of_holomorphic_factor (B T : Type*)
    [Field B] [NumberField B] [Field T] [NumberField T]
    (δ : ℝ)
    (hTop : ∀ s : ℂ, 1 - δ < s.re → meromorphicOrderAt (dedekindZetaSharp T) s ≤ 0)
    (Q : ℂ → ℂ) (hQ : DifferentiableOn ℂ Q {s : ℂ | 1 - δ < s.re})
    (hfactor : ∀ s : ℂ, 1 - δ < s.re →
      dedekindZetaSharp T s = dedekindZetaSharp B s * Q s) :
    ∀ s : ℂ, 1 - δ < s.re → meromorphicOrderAt (dedekindZetaSharp B) s ≤ 0 := by
  intro s hs
  have hHopen : IsOpen {z : ℂ | 1 - δ < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hQanalytic : AnalyticAt ℂ Q s := by
    apply hQ.analyticAt
    exact hHopen.mem_nhds hs
  have hTmer : MeromorphicAt (dedekindZetaSharp T) s :=
    dedekindZetaSharp_meromorphic T s
  have hBmer : MeromorphicAt (dedekindZetaSharp B) s :=
    dedekindZetaSharp_meromorphic B s
  have hfactorNear : (fun z => dedekindZetaSharp T z) =ᶠ[𝓝[≠] s]
      (fun z => dedekindZetaSharp B z * Q z) := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (hHopen.mem_nhds hs)] with z hz
    exact hfactor z hz
  have horderEq := meromorphicOrderAt_congr hfactorNear
  have horderMul : meromorphicOrderAt (fun z => dedekindZetaSharp B z * Q z) s =
      meromorphicOrderAt (dedekindZetaSharp B) s + meromorphicOrderAt Q s :=
    meromorphicOrderAt_mul hBmer hQanalytic.meromorphicAt
  have htotal : meromorphicOrderAt (dedekindZetaSharp T) s =
      meromorphicOrderAt (dedekindZetaSharp B) s + meromorphicOrderAt Q s :=
    horderEq.trans horderMul
  have hbaseLe : meromorphicOrderAt (dedekindZetaSharp B) s ≤
      meromorphicOrderAt (dedekindZetaSharp T) s := by
    calc
      meromorphicOrderAt (dedekindZetaSharp B) s =
          meromorphicOrderAt (dedekindZetaSharp B) s + 0 := by simp
      _ ≤ meromorphicOrderAt (dedekindZetaSharp B) s + meromorphicOrderAt Q s :=
        by
          simpa [add_comm] using
            (add_le_add_left hQanalytic.meromorphicOrderAt_nonneg
              (meromorphicOrderAt (dedekindZetaSharp B) s))
      _ = meromorphicOrderAt (dedekindZetaSharp T) s := htotal.symm
  exact hbaseLe.trans (hTop s hs)

end ArtinPrimitiveRoots.Splitting
end
