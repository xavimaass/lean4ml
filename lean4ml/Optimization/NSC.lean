import Mathlib
import Lean4ML.Optimization.LSmooth

noncomputable section

open scoped Real
open scoped RealInnerProductSpace
open Set
open Asymptotics
open Topology

namespace Lean4ML
namespace Optimization

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section NecessaryConditions

variable (f : E → ℝ) (x : E)

theorem local_min_gradient_zero
    (hC1 : ContDiff ℝ 1 f)
    (hmin : IsLocalMin f x) :
    gradient f x = 0 := by
  have hgradAt : HasGradientAt f (gradient f x) x :=
    hasGradientAt_of_contDiff_one (f := f) hC1 x
  have hFDeriv0 : (InnerProductSpace.toDual ℝ E) (gradient f x) = 0 :=
    IsLocalMin.hasFDerivAt_eq_zero hmin hgradAt.hasFDerivAt
  have hself : ⟪gradient f x, gradient f x⟫ = 0 := by
    have happly := congrArg (fun A : E →L[ℝ] ℝ => A (gradient f x)) hFDeriv0
    simpa using happly
  exact inner_self_eq_zero.mp hself


/-- Exact second-order Taylor expansion using an integral remainder.
    If `∇f(x) = 0`, then `f (x + p) - f x` is exactly the double integral of the Hessian. -/
lemma taylor_second_order_exact
    (hC2 : ContDiff ℝ 2 f)
    (x p : E) (hgrad : gradient f x = 0) :
    f (x + p) - f x = ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..t, ⟪hessian f (x + s • p) p, p⟫ := by
  have hC1 : ContDiff ℝ 1 f := hC2.of_le (show (1 : WithTop ℕ∞) ≤ 2 by norm_num)
  have h_first := taylor_first_order (hC1 := hC1) (x := x) (p := p)

  have hgrad_line : ∀ t : ℝ,
      gradient f (x + t • p) = ∫ s in (0 : ℝ)..t, hessian f (x + s • p) p := by
    intro t
    have htmp := taylor_second_order_gradient (hC2 := hC2) (x := x) (p := t • p)
    have htmp0 :
        gradient f (x + t • p)
          = t • ∫ u in (0 : ℝ)..1, hessian f (x + (u * t) • p) p := by
      simpa [hgrad, smul_smul, mul_comm, mul_left_comm, mul_assoc] using htmp
    have hscale :
        t • ∫ u in (0 : ℝ)..1, hessian f (x + (u * t) • p) p
          = ∫ u in (0 : ℝ)..t, hessian f (x + u • p) p := by
      simpa [mul_comm] using
        (intervalIntegral.smul_integral_comp_mul_right
          (a := (0 : ℝ)) (b := (1 : ℝ))
          (f := fun u : ℝ => hessian f (x + u • p) p) (c := t))
    exact htmp0.trans hscale


  -- Combine the two identities and use `hgrad` to eliminate the linear term
  calc
    f (x + p) - f x = ∫ t in (0 : ℝ)..1, ⟪gradient f (x + t • p), p⟫ := h_first
    _ = ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..t, ⟪hessian f (x + s • p) p, p⟫ := by
      congr with t
      calc
        ⟪gradient f (x + t • p), p⟫ = ⟪∫ s in (0 : ℝ)..t, hessian f (x + s • p) p, p⟫ := by
          rw [hgrad_line t]
        _ = ⟪p, ∫ s in (0 : ℝ)..t, hessian f (x + s • p) p⟫ := by
          simpa using (real_inner_comm (∫ s in (0 : ℝ)..t, hessian f (x + s • p) p) p).symm
        _ = ∫ s in (0 : ℝ)..t, ⟪p, hessian f (x + s • p) p⟫ := by
          have hcont : Continuous (fun s : ℝ => hessian f (x + s • p) p) := by
            exact (continuous_fderiv_line_apply (f := fun y : E => gradient f y)
              (by simpa [gradient] using
                ((InnerProductSpace.toDual ℝ E).symm.contDiff.comp
                  (hC2.fderiv_right (m := 1) (by norm_num)))) x p)
          have hf : IntervalIntegrable (fun s : ℝ => hessian f (x + s • p) p) MeasureTheory.volume (0 : ℝ) t :=
            hcont.continuousOn.intervalIntegrable
          have hclm := ContinuousLinearMap.intervalIntegral_comp_comm
            (L := innerSL ℝ p)
            (f := fun s : ℝ => hessian f (x + s • p) p)
            (hf := hf)
          simpa [innerSL_apply_apply] using hclm.symm
        _ = ∫ s in (0 : ℝ)..t, ⟪hessian f (x + s • p) p, p⟫ := by
          congr with s
          simpa using (real_inner_comm (hessian f (x + s • p) p) p)

/-- **Theorem 2.4(b)**: A necessary condition for local minimality is that the Hessian is PSD. -/
theorem local_min_hessian_psd
    (hC2 : ContDiff ℝ 2 f)
    (hmin : IsLocalMin f x) (p : E) :
    0 ≤ ⟪hessian f x p, p⟫ := by
  -- Gradient vanishes at a local minimum
  have hgrad : gradient f x = 0 :=
    local_min_gradient_zero (hC1 := hC2.of_le (by norm_num)) (hmin := hmin)

  -- The map α ↦ x + α • p tends to x as α → 0+ (within the right-hand neighbourhood)
  have hcont_add : Continuous fun α => x + α • p := by continuity
  have htend : Tendsto (fun α => x + α • p) (𝓝[>] 0) (𝓝 x) :=
    (hcont_add.continuousAt).tendsto.mono_left nhdsWithin_le_nhds

  -- For α ≠ 0, the second-order Taylor expansion applied to α • p gives
  -- (f (x + αp) - f x) = α^2 * ∫_{0..1} ∫_{0..t} ⟪hessian f (x + (s*α)•p) p, p⟫ ds dt.
  have h_taylor_scaled :
    ∀ α : ℝ, (f (x + α • p) - f x) = α ^ 2 * ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..t, ⟪hessian f (x + (s * α) • p) p, p⟫ :=
    by
    intro (α : ℝ)
    have hts := taylor_second_order_exact (hC2 := hC2) x (α • p) hgrad
    -- simplify the double-inner by pulling scalars out of the inner product
    have :
      (fun t => ∫ s in (0 : ℝ)..t, ⟪hessian f (x + s • (α • p)) (α • p), α • p⟫)
        = fun t => α ^ 2 * ∫ s in (0 : ℝ)..t, ⟪hessian f (x + (s * α) • p) p, p⟫ :=
      by
      funext t
      congr
      funext s
      simp only [smul_smul]
      have h1 : hessian f (x + s * α • p) (α • p) = α • hessian f (x + (s * α) • p) p := by
        simp only [smul_smul]
      simp [h1]
    calc
      f (x + α • p) - f x = ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..t,
          ⟪hessian f (x + s • (α • p)) (α • p), α • p⟫ := hts
      _ = ∫ t in (0 : ℝ)..1, α ^ 2 * ∫ s in (0 : ℝ)..t, ⟪hessian f (x + (s * α) • p) p, p⟫ := by
        congr
        exact this
      _ = α ^ 2 * ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..t, ⟪hessian f (x + (s * α) • p) p, p⟫ :=
        by simp [Integral.integral_const_mul]

  -- Define the integrand function and its continuity at 0
  let H := fun y => ⟪hessian f y p, p⟫
  have H_cont : ContinuousAt H x := by
    have : Continuous fun y => hessian f y p :=
      by
      have h := (hC2.fderiv_right (m := 1) (by norm_num))
      exact (continuous_fderiv_line_apply (f := fun y => gradient f y) h x p)
    exact (this.continuousAt.inner continuous_const).trans (by simp)

  -- From local minimality we get eventual nonnegativity of f(x+αp)-f x on the right neighbourhood
  have h_eventually_ge : ∀ᶠ α in 𝓝[>] 0, f x ≤ f (x + α • p) :=
    htend.eventually hmin

  -- For α in the right neighbourhood we can divide by α^2 (>0) to get nonnegativity of the quotient
  have h_eventual_nonneg : ∀ᶠ α in 𝓝[>] 0, 0 ≤ (f (x + α • p) - f x) / α ^ 2 :=
    h_eventually_ge.mono fun α h =>
      have : 0 ≤ (f (x + α • p) - f x) := sub_nonneg.2 h
      div_nonneg this (pow_nonneg (le_of_lt (lt_of_mem_nhdsWithin zero_lt_one (by simp))))

  -- The scaled Taylor identity gives equality of the quotient with the parametric double integral
  have eq_eventually : ∀ᶠ α in 𝓝[>] 0,
    (f (x + α • p) - f x) / α ^ 2 = ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..t, H (x + (s * α) • p) :=
    eventually_of_forall fun α : ℝ => by simp [h_taylor_scaled α]

  -- Show the parametric double integral tends to (H x) / 2 as α → 0+
  have tendsto_I :
    Tendsto (fun α => ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..t, H (x + (s * α) • p)) (𝓝[>] 0)
      (𝓝 (∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..t, H x)) :=
    by
    -- continuity of H at x implies pointwise convergence; then standard results let us pass the limit
    have Hc : ContinuousAt H x := H_cont
    have pointwise : ∀ s : ℝ, Tendsto (fun α => H (x + (s * α) • p)) (𝓝[>] 0) (𝓝 (H x)) := by
      intro (s : ℝ)
      have comp_cont : Continuous fun α => x + (s * α) • p := by continuity
      exact (comp_cont.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
    -- pass limit inside the integrals using continuity (dominated convergence style for continuous integrands)
    refine (tendsto_integral_of_continuous_of_compact_interval (fun α t => H (x + (t * α) • p))).2 ?_

  -- Final step: use eventual nonnegativity and the limit of the quotient to conclude the limit ≥ 0
  have final_tendsto : Tendsto (fun α => (f (x + α • p) - f x) / α ^ 2) (𝓝[>] 0)
    (𝓝 (∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..t, H x)) :=
    eq_eventually.mono_right tendsto_I

  have I0 : ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..t, H x = (H x) / 2 := by simp [integral_const_mul]

  have lim_nonneg := NonnegLimit.of_eventually_nonneg_of_tendsto h_eventual_nonneg final_tendsto
  simpa [I0] using lim_nonneg

end NecessaryConditions

end Optimization
end Lean4ML
