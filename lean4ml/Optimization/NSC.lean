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
  have hgrad : gradient f x = 0 :=
    local_min_gradient_zero f x (hC2.of_le (by norm_num)) hmin
  by_contra hneg
  have hneg' : ⟪hessian f x p, p⟫ < 0 := by
    exact lt_of_not_ge hneg

  let g : ℝ → ℝ := fun α => f (x + α • p) - f x
  let hxpp : ℝ := ⟪hessian f x p, p⟫
  let Hline : ℝ → ℝ := fun u => ⟪hessian f (x + u • p) p, p⟫

  have hcont_vec : Continuous (fun u : ℝ => hessian f (x + u • p) p) := by
    exact (continuous_fderiv_line_apply (f := fun y : E => gradient f y)
      (by simpa [gradient] using
        ((InnerProductSpace.toDual ℝ E).symm.contDiff.comp
          (hC2.fderiv_right (m := 1) (by norm_num)))) x p)
  have hcontH : Continuous Hline := by
    simpa [Hline] using hcont_vec.inner continuous_const
  have hcenter_lt : Hline 0 < hxpp / 2 := by
    dsimp [Hline, hxpp]
    simpa using (show ⟪hessian f x p, p⟫ < ⟪hessian f x p, p⟫ / 2 by linarith [hneg'])
  have hnear_set : {u : ℝ | Hline u < hxpp / 2} ∈ 𝓝 (0 : ℝ) :=
    hcontH.continuousAt.eventually (Iio_mem_nhds hcenter_lt)
  rcases Metric.mem_nhds_iff.mp hnear_set with ⟨δ, hδpos, hδmem⟩

  have h_eventually_ge : ∀ᶠ α in 𝓝[>] 0, 0 ≤ g α := by
    have htend0 : Filter.Tendsto (fun α : ℝ => x + α • p) (𝓝[>] (0 : ℝ)) (𝓝 (x + (0 : ℝ) • p)) :=
      (continuous_const.add (continuous_id.smul continuous_const)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    have htend : Filter.Tendsto (fun α : ℝ => x + α • p) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
      simpa using htend0
    exact htend.eventually hmin |>.mono fun α h => sub_nonneg.mpr h

  have h_small : ∀ᶠ α in 𝓝[>] (0 : ℝ), |α| < δ := by
    have hball : Metric.ball (0 : ℝ) δ ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds (0 : ℝ) hδpos
    have hball' : {α : ℝ | |α| < δ} ∈ 𝓝 (0 : ℝ) := by
      simpa [Metric.ball, Real.dist_eq, abs_sub_comm, sub_eq_add_neg] using hball
    exact nhdsWithin_le_nhds hball'

  have h_eventually_lt : ∀ᶠ α in 𝓝[>] (0 : ℝ), g α < 0 := by
    refine (h_small.and self_mem_nhdsWithin).mono ?_
    intro α hα
    have hαsmall : |α| < δ := hα.1
    have hαpos : 0 < α := hα.2
    have hαsq_pos : 0 < α ^ (2 : ℕ) := sq_pos_of_pos hαpos

    have hinner_bound :
        ∀ t ∈ Icc (0 : ℝ) 1,
          (∫ s in (0 : ℝ)..t, ⟪hessian f (x + s • (α • p)) (α • p), α • p⟫)
            ≤ α ^ (2 : ℕ) * (hxpp / 2) * t := by
      intro t ht
      have h_int_mono :
          (∫ s in (0 : ℝ)..t, ⟪hessian f (x + s • (α • p)) (α • p), α • p⟫)
            ≤ ∫ s in (0 : ℝ)..t, α ^ (2 : ℕ) * (hxpp / 2) := by
        refine intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := t)
          (f := fun s => ⟪hessian f (x + s • (α • p)) (α • p), α • p⟫)
          (g := fun _s => α ^ (2 : ℕ) * (hxpp / 2)) ht.1 ?_ ?_ ?_
        · have hcont : Continuous (fun s : ℝ => ⟪hessian f (x + s • (α • p)) (α • p), α • p⟫) := by
            have hvec : Continuous (fun s : ℝ => hessian f (x + s • (α • p)) (α • p)) := by
              exact (continuous_fderiv_line_apply (f := fun y : E => gradient f y)
                (by simpa [gradient] using
                  ((InnerProductSpace.toDual ℝ E).symm.contDiff.comp
                    (hC2.fderiv_right (m := 1) (by norm_num)))) x (α • p))
            simpa using hvec.inner continuous_const
          exact hcont.continuousOn.intervalIntegrable
        · exact intervalIntegrable_const
        · intro s hs
          have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans ht.2⟩
          have hs_nonneg : 0 ≤ s := hs01.1
          have hs_le_one : s ≤ 1 := hs01.2
          have hsabs : |s| ≤ 1 := by
            simpa [abs_of_nonneg hs_nonneg] using hs_le_one
          have hmul_abs : |s * α| < δ := by
            calc
              |s * α| = |s| * |α| := by rw [abs_mul]
              _ ≤ 1 * |α| := by gcongr
              _ = |α| := by ring
              _ < δ := hαsmall
          have hs_ball : s * α ∈ Metric.ball (0 : ℝ) δ := by
            simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm, sub_eq_add_neg] using hmul_abs
          have hHlt : Hline (s * α) < hxpp / 2 := hδmem hs_ball
          have hHle : Hline (s * α) ≤ hxpp / 2 := le_of_lt hHlt
          have hαsq_nonneg : 0 ≤ α ^ (2 : ℕ) := sq_nonneg α
          have hrewrite :
              ⟪hessian f (x + s • (α • p)) (α • p), α • p⟫
                = α ^ (2 : ℕ) * Hline (s * α) := by
            dsimp [Hline]
            have : x + s • (α • p) = x + (s * α) • p := by
              simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]
            rw [this]
            calc
              ⟪hessian f (x + (s * α) • p) (α • p), α • p⟫
                  = ⟪α • hessian f (x + (s * α) • p) p, α • p⟫ := by simp
              _ = α * (α * ⟪hessian f (x + (s * α) • p) p, p⟫) := by
                    simp [real_inner_smul_left, real_inner_smul_right, mul_assoc]
              _ = α ^ (2 : ℕ) * ⟪hessian f (x + (s * α) • p) p, p⟫ := by ring
          have hpoint :
              ⟪hessian f (x + s • (α • p)) (α • p), α • p⟫ ≤ α ^ (2 : ℕ) * (hxpp / 2) := by
            calc
              ⟪hessian f (x + s • (α • p)) (α • p), α • p⟫ = α ^ (2 : ℕ) * Hline (s * α) :=
                hrewrite
              _ ≤ α ^ (2 : ℕ) * (hxpp / 2) := by gcongr
          exact hpoint
      calc
        (∫ s in (0 : ℝ)..t, ⟪hessian f (x + s • (α • p)) (α • p), α • p⟫)
            ≤ ∫ s in (0 : ℝ)..t, α ^ (2 : ℕ) * (hxpp / 2) := h_int_mono
        _ = α ^ (2 : ℕ) * (hxpp / 2) * t := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              (intervalIntegral.integral_const (a := (0 : ℝ)) (b := t)
                (c := α ^ (2 : ℕ) * (hxpp / 2)))

    have htaylor :
        g α
          = ∫ t in (0 : ℝ)..1,
              ∫ s in (0 : ℝ)..t, ⟪hessian f (x + s • (α • p)) (α • p), α • p⟫ := by
      dsimp [g]
      simpa using taylor_second_order_exact f hC2 x (α • p) hgrad

    have houter_bound :
        g α ≤ ∫ t in (0 : ℝ)..1, (α ^ (2 : ℕ) * (hxpp / 2) * t) := by
      rw [htaylor]
      let φ : ℝ → ℝ := fun s => ⟪hessian f (x + s • (α • p)) (α • p), α • p⟫
      have hcontφ : Continuous φ := by
        dsimp [φ]
        have hvec : Continuous (fun s : ℝ => hessian f (x + s • (α • p)) (α • p)) := by
          exact (continuous_fderiv_line_apply (f := fun y : E => gradient f y)
            (by simpa [gradient] using
              ((InnerProductSpace.toDual ℝ E).symm.contDiff.comp
                (hC2.fderiv_right (m := 1) (by norm_num)))) x (α • p))
        simpa using hvec.inner continuous_const
      have hcont_f : Continuous (fun t : ℝ => ∫ s in (0 : ℝ)..t, φ s) := by
        have h_int_all : ∀ a b : ℝ, IntervalIntegrable φ MeasureTheory.volume a b := by
          intro a b
          exact hcontφ.continuousOn.intervalIntegrable
        exact intervalIntegral.continuous_primitive h_int_all (0 : ℝ)
      refine intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := (1 : ℝ))
        (f := fun t => ∫ s in (0 : ℝ)..t, φ s)
        (g := fun t => α ^ (2 : ℕ) * (hxpp / 2) * t) (by norm_num) ?_ ?_ ?_
      · exact hcont_f.continuousOn.intervalIntegrable
      · exact (continuous_const.mul continuous_id).continuousOn.intervalIntegrable
      · intro t ht
        exact hinner_bound t ht

    have h_eval_outer :
        ∫ t in (0 : ℝ)..1, (α ^ (2 : ℕ) * (hxpp / 2) * t)
          = α ^ (2 : ℕ) * (hxpp / 4) := by
      calc
        ∫ t in (0 : ℝ)..1, (α ^ (2 : ℕ) * (hxpp / 2) * t)
            = α ^ (2 : ℕ) * (hxpp / 2) * ∫ t in (0 : ℝ)..1, t := by
                simpa [mul_comm, mul_left_comm, mul_assoc] using
                  (intervalIntegral.integral_const_mul (a := (0 : ℝ)) (b := (1 : ℝ))
                    (r := α ^ (2 : ℕ) * (hxpp / 2)) (f := fun t : ℝ => t))
        _ = α ^ (2 : ℕ) * (hxpp / 2) * (1 / 2 : ℝ) := by simp
        _ = α ^ (2 : ℕ) * (hxpp / 4) := by ring

    have hstrict : α ^ (2 : ℕ) * (hxpp / 4) < 0 := by
      have hqx : hxpp / 4 < 0 := by
        dsimp [hxpp]
        linarith
      exact mul_neg_of_pos_of_neg hαsq_pos hqx

    exact lt_of_le_of_lt (houter_bound.trans_eq h_eval_outer) hstrict

  have hfalse : ∀ᶠ α in 𝓝[>] (0 : ℝ), False := by
    refine (h_eventually_ge.and h_eventually_lt).mono ?_
    intro α hα
    exact (not_lt_of_ge hα.1) hα.2
  have hbot : (𝓝[>] (0 : ℝ)) = ⊥ := (Filter.eventually_false_iff_eq_bot.mp hfalse)
  have hne : (𝓝[>] (0 : ℝ)).NeBot := by infer_instance
  exact hne.ne hbot
end NecessaryConditions

end Optimization
end Lean4ML
