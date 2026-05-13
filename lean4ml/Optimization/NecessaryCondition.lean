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


/-- The map `t ↦ hessian f (x + t • p) p` is continuous.
    This is a specialisation of `continuous_fderiv_line_apply` to the gradient map. -/
lemma continuous_hessian_line
    (hC2 : ContDiff ℝ 2 f) (x p : E) :
    Continuous (fun t : ℝ => hessian f (x + t • p) p) := by
  apply continuous_fderiv_line_apply (f := fun y : E => gradient f y)
  simpa [gradient] using
    (InnerProductSpace.toDual ℝ E).symm.contDiff.comp
      (hC2.fderiv_right (m := 1) (by norm_num))

/-- The quadratic form of the Hessian scales as `α²`:
    `⟪hessian f x (α • p), α • p⟫ = α² * ⟪hessian f x p, p⟫`. -/
lemma hessian_inner_smul
    (x p : E) (α : ℝ) :
    ⟪hessian f x (α • p), α • p⟫ = α ^ 2 * ⟪hessian f x p, p⟫ := by
  simp [real_inner_smul_left, real_inner_smul_right]
  ring

  /-- The gradient along the line `t ↦ x + t • p` equals the integral of the Hessian.
    This is `taylor_second_order_gradient` re-parametrised to an arbitrary endpoint `t`,
    using the substitution `u ↦ u * t`. -/
lemma gradient_line_eq_integral_hessian
    (hC2 : ContDiff ℝ 2 f) (x p : E) (hgrad : gradient f x = 0) (t : ℝ) :
    gradient f (x + t • p) = ∫ s in (0 : ℝ)..t, hessian f (x + s • p) p := by
  have htmp := taylor_second_order_gradient (hC2 := hC2) (x := x) (p := t • p)
  have htmp0 :
      gradient f (x + t • p)
        = t • ∫ u in (0 : ℝ)..1, hessian f (x + (u * t) • p) p := by
    simpa [hgrad, smul_smul, mul_comm, mul_left_comm, mul_assoc] using htmp
  have hscale :
      t • ∫ u in (0 : ℝ)..1, hessian f (x + (u * t) • p) p
        = ∫ u in (0 : ℝ)..t, hessian f (x + u • p) p := by
    simpa [mul_comm] using
      intervalIntegral.smul_integral_comp_mul_right
        (a := (0 : ℝ)) (b := (1 : ℝ))
        (f := fun u : ℝ => hessian f (x + u • p) p) (c := t)
  exact htmp0.trans hscale

/-- Exact second-order Taylor expansion using an integral remainder.
    If `∇f(x) = 0`, then `f (x + p) - f x` is exactly the double integral of the Hessian. -/
lemma taylor_second_order_exact
    (hC2 : ContDiff ℝ 2 f)
    (x p : E) (hgrad : gradient f x = 0) :
    f (x + p) - f x
      = ∫ t in (0 : ℝ)..1,
          ∫ s in (0 : ℝ)..t,
            ⟪hessian f (x + s • p) p, p⟫ := by
  have hC1 : ContDiff ℝ 1 f := hC2.of_le (by norm_num)

  calc
    f (x + p) - f x
        = ∫ t in (0 : ℝ)..1, ⟪gradient f (x + t • p), p⟫ := taylor_first_order (hC1 := hC1) (x := x) (p := p)
    _ = ∫ t in (0 : ℝ)..1,
          ∫ s in (0 : ℝ)..t,
            ⟪hessian f (x + s • p) p, p⟫ := by
        congr with t
        rw [gradient_line_eq_integral_hessian (f := f) (hC2 := hC2) (x := x) (p := p) (hgrad := hgrad) (t := t)]
        have hcont := continuous_hessian_line (f := f) hC2 x p
        have hf :
            IntervalIntegrable
              (fun s : ℝ => hessian f (x + s • p) p)
              MeasureTheory.volume
              (0 : ℝ) t :=
          hcont.continuousOn.intervalIntegrable
        rw [← real_inner_comm]
        have hclm :=
          ContinuousLinearMap.intervalIntegral_comp_comm
            (L := innerSL ℝ p)
            (f := fun s : ℝ => hessian f (x + s • p) p)
            (hf := hf)
        simpa [innerSL_apply_apply, real_inner_comm] using hclm.symm


/-- Pointwise bound: for `s ∈ [0, t] ⊆ [0, 1]` and `|s * α| < δ`,
    the Hessian quadratic form at `(x + s•(α•p))` in direction `α•p` is bounded by `α² * (c / 2)`.
    This is the key estimate used inside `local_min_hessian_psd`. -/
lemma hessian_inner_smul_bound
    {f : E → ℝ} {x p : E} {α δ c : ℝ}
    (Hline : ℝ → ℝ) (hHline : Hline = fun u => ⟪hessian f (x + u • p) p, p⟫)
    (hδ : ∀ u ∈ Metric.ball (0 : ℝ) δ, Hline u ≤ c)
    {s : ℝ} (hs_nonneg : 0 ≤ s) (hs_le : s ≤ 1)
    (hαsmall : |α| < δ)
    (hα_sq_nonneg : 0 ≤ α ^ 2) :
    ⟪hessian f (x + s • (α • p)) (α • p), α • p⟫ ≤ α ^ 2 * c := by
  have hmul_abs : |s * α| < δ := by
    calc |s * α| = |s| * |α| := abs_mul s α
      _ ≤ 1 * |α| := by gcongr; simpa [abs_of_nonneg hs_nonneg]
      _ = |α| := one_mul _
      _ < δ := hαsmall
  have hs_ball : s * α ∈ Metric.ball (0 : ℝ) δ := by
    simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hmul_abs
  have hHle : Hline (s * α) ≤ c := hδ _ hs_ball
  have hrewrite :
      ⟪hessian f (x + s • (α • p)) (α • p), α • p⟫ = α ^ 2 * Hline (s * α) := by
    have heq : x + s • (α • p) = x + (s * α) • p := by
      simp [smul_smul]
    rw [hHline, heq, hessian_inner_smul]
  linarith [hrewrite ▸ mul_le_mul_of_nonneg_left hHle hα_sq_nonneg]

/-- Upper bound on the inner integral: for `t ∈ [0, 1]`,
    `∫ s in 0..t, ⟪hessian f (x + s•(α•p)) (α•p), α•p⟫ ≤ α² * c * t`. -/
lemma inner_integral_bound
    {f : E → ℝ} {x p : E} {α δ c : ℝ}
    (hC2 : ContDiff ℝ 2 f)
    (Hline : ℝ → ℝ) (hHline : Hline = fun u => ⟪hessian f (x + u • p) p, p⟫)
    (hδ : ∀ u ∈ Metric.ball (0 : ℝ) δ, Hline u ≤ c)
    (hαsmall : |α| < δ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ s in (0 : ℝ)..t, ⟪hessian f (x + s • (α • p)) (α • p), α • p⟫)
      ≤ α ^ 2 * c * t := by
  have hα_sq_nonneg : 0 ≤ α ^ 2 := sq_nonneg α
  have hcont : Continuous (fun s : ℝ =>
      ⟪hessian f (x + s • (α • p)) (α • p), α • p⟫) := by
    exact (continuous_hessian_line f hC2 x (α • p)).inner continuous_const
  have h_int_mono :
      (∫ s in (0 : ℝ)..t, ⟪hessian f (x + s • (α • p)) (α • p), α • p⟫)
        ≤ ∫ s in (0 : ℝ)..t, α ^ 2 * c := by
    apply intervalIntegral_mono_of_continuous ht.1
      hcont continuous_const
    intro s hs
    exact hessian_inner_smul_bound Hline hHline hδ hs.1 (hs.2.trans ht.2) hαsmall hα_sq_nonneg
  calc (∫ s in (0 : ℝ)..t, ⟪hessian f (x + s • (α • p)) (α • p), α • p⟫)
      ≤ ∫ s in (0 : ℝ)..t, α ^ 2 * c := h_int_mono
    _ = α ^ 2 * c * t := by
          simp [mul_comm, mul_left_comm, intervalIntegral.integral_const]

/-- Upper bound on the double integral (and hence on `f(x + α•p) - f(x)`):
    `g α ≤ α² * c / 2`. -/
lemma double_integral_bound
    {f : E → ℝ} {x p : E} {α δ c : ℝ}
    (hC2 : ContDiff ℝ 2 f)
    (hgrad : gradient f x = 0)
    (Hline : ℝ → ℝ) (hHline : Hline = fun u => ⟪hessian f (x + u • p) p, p⟫)
    (hδ : ∀ u ∈ Metric.ball (0 : ℝ) δ, Hline u ≤ c)
    (hαsmall : |α| < δ) :
    f (x + α • p) - f x ≤ α ^ 2 * c / 2 := by
  have hφ_cont : Continuous (fun s : ℝ =>
      ⟪hessian f (x + s • (α • p)) (α • p), α • p⟫) :=
    (continuous_hessian_line f hC2 x (α • p)).inner continuous_const
  have htaylor : f (x + α • p) - f x =
      ∫ t in (0 : ℝ)..1,
        ∫ s in (0 : ℝ)..t, ⟪hessian f (x + s • (α • p)) (α • p), α • p⟫ :=
    taylor_second_order_exact f hC2 x (α • p) hgrad
  have houter : f (x + α • p) - f x ≤ ∫ t in (0 : ℝ)..1, α ^ 2 * c * t := by
    rw [htaylor]
    apply intervalIntegral_mono_of_continuous (by norm_num)
      (intervalIntegral.continuous_primitive
        (fun a b => hφ_cont.continuousOn.intervalIntegrable) 0)
      (continuous_const.mul continuous_id)
    intro t ht
    exact inner_integral_bound hC2 Hline hHline hδ hαsmall ht
  have h_eval : ∫ t in (0 : ℝ)..1, α ^ 2 * c * t = α ^ 2 * c / 2 := by
    rw [intervalIntegral.integral_const_mul]
    simp [integral_id]
    ring
  linarith [houter.trans_eq h_eval]

/-- **Theorem 2.4(b)**: If `x` is a local minimizer of `f ∈ C²`,
then the Hessian is positive semidefinite. -/
theorem local_min_hessian_psd
    (hC2 : ContDiff ℝ 2 f)
    (hmin : IsLocalMin f x) (p : E) :
    0 ≤ ⟪hessian f x p, p⟫ := by

  have hgrad : gradient f x = 0 := local_min_gradient_zero f x (hC2.of_le (by norm_num)) hmin

  by_contra hneg
  have hneg' : ⟪hessian f x p, p⟫ < 0 := lt_of_not_ge hneg

  set hxpp : ℝ := ⟪hessian f x p, p⟫
  set Hline : ℝ → ℝ := fun u => ⟪hessian f (x + u • p) p, p⟫

  have hcontH : Continuous Hline := by
    dsimp [Hline]
    simpa using (continuous_hessian_line (f := f) hC2 x p).inner continuous_const

  have hcenter_lt : Hline 0 < hxpp / 2 := by
    dsimp [Hline, hxpp]
    simp
    linarith

  have hnear : {u : ℝ | Hline u < hxpp / 2} ∈ 𝓝 (0 : ℝ) :=
    hcontH.continuousAt.eventually (Iio_mem_nhds hcenter_lt)
  rcases Metric.mem_nhds_iff.mp hnear with ⟨δ, hδpos, hδmem⟩

  -- Local minimality gives eventual nonnegativity.
  let g : ℝ → ℝ := fun α => f (x + α • p) - f x
  have h_eventually_ge : ∀ᶠ α in 𝓝[>] 0, 0 ≤ g α := by
    have htend0 : Filter.Tendsto (fun α : ℝ => x + α • p) (𝓝[>] (0 : ℝ)) (𝓝 (x + (0 : ℝ) • p)) :=
      (continuous_const.add (continuous_id.smul continuous_const)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    have htend : Filter.Tendsto (fun α : ℝ => x + α • p) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
      simpa using htend0
    exact htend.eventually hmin |>.mono fun α h => sub_nonneg.mpr h

  -- Small α remain inside the neighborhood.
  have h_small : ∀ᶠ α in 𝓝[>] (0 : ℝ), |α| < δ := by
    have hball : Metric.ball (0 : ℝ) δ ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ hδpos
    have hball' : {α : ℝ | |α| < δ} ∈ 𝓝 (0 : ℝ) := by
      simpa [Metric.ball, Real.dist_eq, abs_sub_comm] using hball
    exact nhdsWithin_le_nhds hball'

  have h_eventually_lt : ∀ᶠ α in 𝓝[>] (0 : ℝ), f (x + α • p) - f x < 0 := by
    refine (h_small.and self_mem_nhdsWithin).mono ?_
    intro α hα
    have hαsmall : |α| < δ := hα.1
    have hαpos : 0 < α := hα.2
    have hbound : f (x + α • p) - f x ≤ α ^ 2 * (hxpp / 2) / 2 := by
      have :=
        double_integral_bound
          (hC2) (hgrad) (Hline) (hHline := rfl)
          (hδ := fun u hu => le_of_lt (hδmem hu))
          (hαsmall) (f := f) (x := x)
          (p := p) (α := α) (c := hxpp / 2)
      simpa [hxpp] using this

    have hstrict : α ^ 2 * (hxpp / 2) / 2 < 0 := by
      have hsq : 0 < α ^ 2 := sq_pos_of_pos hαpos
      have hneg2 : hxpp / 2 < 0 := by linarith
      nlinarith
    exact lt_of_le_of_lt hbound hstrict

  have hfalse : ∀ᶠ α in 𝓝[>] (0 : ℝ), False := by
    refine (h_eventually_ge.and h_eventually_lt).mono ?_
    intro α hα
    exact (not_lt_of_ge hα.1) hα.2
  have hbot : (𝓝[>] (0 : ℝ)) = ⊥ :=
    Filter.eventually_false_iff_eq_bot.mp hfalse
  have hne : (𝓝[>] (0 : ℝ)).NeBot := by infer_instance
  exact hne.ne hbot

end NecessaryConditions


end Optimization
end Lean4ML
