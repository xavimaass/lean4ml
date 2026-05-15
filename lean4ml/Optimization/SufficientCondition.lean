import lean4ml.Optimization.Defs
import lean4ml.Optimization.NecessaryCondition

noncomputable section

open scoped Real
open scoped RealInnerProductSpace
open Set Topology Metric

namespace Lean4ML
namespace Optimization

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-!
## Theorem 2.5 — Second-Order Sufficient Conditions for a Strict Local Minimizer

This file is *incremental*: we first prove a clean “Taylor lower bound from a
uniform Hessian lower bound” (this is already mostly in your draft, but cleaned),
and then state the final theorem in a way that avoids the hard functional-analytic
step “positive definite ⇒ uniform positive lower bound on a ball”.

That missing step is genuinely nontrivial in infinite-dimensional Hilbert spaces
(and even in finite dimensions it usually goes through eigenvalues / compactness
of the unit sphere). In Mathlib, the cleanest route is typically to assume
**strong convexity / strong monotonicity** or an explicit coercivity lower bound
already, rather than “pointwise positive definite”.

So:
* `taylor_lower_bound_from_hessian_lb` is fully proved.
* The final theorem `strict_local_min_of_gradient_zero_hessian_uniform_lb` is fully proved.
* The “PD ⇒ uniform LB” lemma (`hessian_pd_local_lower_bound`) is now fully proved
  in finite dimensions, via compactness of the unit sphere.
-/

section SufficientConditions

variable (f : E → ℝ)

-- ---------------------------------------------------------------------------
-- Lemma A — Taylor lower bound from a uniform Hessian quadratic-form lower bound
-- ---------------------------------------------------------------------------

/-- If `⟪hessian f y p, p⟫ ≥ ε * ‖p‖²` for all `y` in a ball of radius `ρ` around `x`
    and all `p`, and `∇f(x) = 0`, then
    `f(x + p) - f(x) ≥ (ε / 2) * ‖p‖²` for all `p` with `‖p‖ < ρ`. -/
lemma taylor_lower_bound_from_hessian_lb
    (hC2 : ContDiff ℝ 2 f)
    (x : E)
    (hgrad : gradient f x = 0)
    (ε ρ : ℝ) (_hε : 0 < ε) (_hρ : 0 < ρ)
    (hHess_lb : ∀ y ∈ ball x ρ, ∀ p : E, ε * ‖p‖ ^ 2 ≤ ⟪hessian f y p, p⟫) :
    ∀ p : E, ‖p‖ < ρ → (ε / 2) * ‖p‖ ^ 2 ≤ f (x + p) - f x := by
  intro p hp_small
  have htaylor :
      f (x + p) - f x =
        ∫ t in (0 : ℝ)..1,
          ∫ s in (0 : ℝ)..t,
            ⟪hessian f (x + s • p) p, p⟫ :=
    taylor_second_order_exact f hC2 x p hgrad

  have h_in_ball : ∀ s ∈ Icc (0 : ℝ) 1, x + s • p ∈ ball x ρ := by
    intro s hs
    rw [mem_ball, dist_eq_norm]
    simpa using (show ‖(x + s • p) - x‖ < ρ by
      simp
      calc
        ‖s • p‖ = |s| * ‖p‖ := norm_smul s p
        _ = s * ‖p‖ := by rw [abs_of_nonneg hs.1]
        _ ≤ 1 * ‖p‖ := by gcongr; exact hs.2
        _ = ‖p‖ := one_mul _
        _ < ρ := hp_small)

  have h_inner_lb : ∀ t ∈ Icc (0 : ℝ) 1,
      ε * ‖p‖ ^ 2 * t ≤ ∫ s in (0 : ℝ)..t, ⟪hessian f (x + s • p) p, p⟫ := by
    intro t ht
    have hcont_inner :
        Continuous (fun s : ℝ => ⟪hessian f (x + s • p) p, p⟫) :=
      (continuous_hessian_line (f := f) hC2 x p).inner continuous_const
    have h_mono :
        ∫ s in (0 : ℝ)..t, ε * ‖p‖ ^ 2 ≤
          ∫ s in (0 : ℝ)..t, ⟪hessian f (x + s • p) p, p⟫ := by
      apply intervalIntegral_mono_of_continuous (a := (0 : ℝ)) (b := t)
        (hab := ht.1) continuous_const hcont_inner
      intro s hs
      have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans ht.2⟩
      exact hHess_lb _ (h_in_ball s hs01) p
    simpa [intervalIntegral.integral_const, mul_assoc, mul_left_comm, mul_comm] using h_mono

  have h_outer_mono :
      ∫ t in (0 : ℝ)..1, (ε * ‖p‖ ^ 2 * t) ≤
        ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..t, ⟪hessian f (x + s • p) p, p⟫ := by
    have hcont_primitive :
        Continuous (fun t : ℝ =>
          ∫ s in (0 : ℝ)..t, ⟪hessian f (x + s • p) p, p⟫) :=
      intervalIntegral.continuous_primitive
        (fun a b =>
          ((continuous_hessian_line (f := f) hC2 x p).inner continuous_const).continuousOn.intervalIntegrable)
        0
    have hcont_lb : Continuous (fun t : ℝ => ε * ‖p‖ ^ 2 * t) := by continuity
    apply intervalIntegral_mono_of_continuous (a := (0 : ℝ)) (b := 1)
      (hab := by norm_num) hcont_lb hcont_primitive
    intro t ht
    exact h_inner_lb t ht

  have h_eval :
      ∫ t in (0 : ℝ)..1, (ε * ‖p‖ ^ 2 * t) = (ε / 2) * ‖p‖ ^ 2 := by
    rw [intervalIntegral.integral_const_mul]
    simp [integral_id]
    ring

  have : (ε / 2) * ‖p‖ ^ 2 ≤
      ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..t, ⟪hessian f (x + s • p) p, p⟫ := by
    linarith [h_eval, h_outer_mono]
  simpa [htaylor] using this

-- ---------------------------------------------------------------------------
-- Lemma B — (optional) PD ⇒ uniform LB on a ball (hard in general)
-- ---------------------------------------------------------------------------

/-!
This is the missing analytic step in your draft. In full generality on an
arbitrary (possibly infinite-dimensional) Hilbert space, “positive definite”
(`∀ p ≠ 0, 0 < ⟪H p,p⟫`) does **not** automatically give a *uniform* coercivity
constant `ε` unless you assume additional structure.

In finite-dimensional `E` you can use compactness of the unit sphere; in general
Hilbert spaces you typically assume a *strongly positive* operator, e.g.
`∃ ε > 0, ∀ p, ε * ‖p‖² ≤ ⟪H p,p⟫`, which is exactly the uniform bound we want.

So we keep the development modular:
* the final theorem only needs the uniform bound hypothesis (and is finished);
* if later you specialize to `E := EuclideanSpace ℝ (Fin n)` you can prove this
  lemma and then obtain the classical statement.
-/

/-
In finite dimensions, a positive-definite continuous linear map has a
uniform coercivity constant: `∃ ε > 0, ∀ p, ε * ‖p‖² ≤ ⟪H p, p⟫`.
-/
omit [CompleteSpace E] in
lemma inner_coercive_of_pd [FiniteDimensional ℝ E]
    (H : E →L[ℝ] E) (hPD : ∀ p : E, p ≠ 0 → 0 < ⟪H p, p⟫) :
    ∃ ε > (0 : ℝ), ∀ p : E, ε * ‖p‖ ^ 2 ≤ ⟪H p, p⟫ := by
  by_cases h_subsingleton : Subsingleton E;
  · exact ⟨ 1, zero_lt_one, fun p => by simp +decide [ Subsingleton.elim p 0 ] ⟩;
  · -- By the extreme value theorem, there exists a minimum value $m$ of $⟪H p, p⟫$ on the unit sphere.
    obtain ⟨m, hm⟩ : ∃ m ∈ (Set.image (fun p : E => ⟪H p, p⟫) (Metric.sphere 0 1)), ∀ y ∈ (Set.image (fun p : E => ⟪H p, p⟫) (Metric.sphere 0 1)), m ≤ y := by
      apply_rules [ IsCompact.exists_isLeast, isCompact_sphere ];
      · exact IsCompact.image ( isCompact_sphere _ _ ) ( Continuous.inner ( H.continuous ) continuous_id' );
      · obtain ⟨ p, hp ⟩ := not_subsingleton_iff_nontrivial.mp h_subsingleton;
        exact ⟨ _, ⟨ ‖p - hp.choose‖⁻¹ • ( p - hp.choose ), by simp +decide [ norm_smul, sub_ne_zero.2 hp.choose_spec ], rfl ⟩ ⟩;
    refine' ⟨ m, _, _ ⟩;
    · aesop;
    · intro p; by_cases hp : p = 0 <;> simp_all +decide ;
      have := hm.2 ( ‖p‖⁻¹ • p ) ?_ <;> simp_all +decide [ norm_smul, inner_smul_left, inner_smul_right ];
      rw [ inv_mul_eq_div, inv_mul_eq_div, div_div, le_div_iff₀ ] at this <;> first | positivity | nlinarith;

/-
The map `y ↦ hessian f y` is continuous when `f` is `C²`.
-/
lemma continuous_hessian (hC2 : ContDiff ℝ 2 f) :
    Continuous (fun y => hessian f y) := by
  -- The gradient is C¹, hence its derivative (the Hessian) is continuous.
  have hGradC1 : ContDiff ℝ 1 (fun y => gradient f y) := by
    exact ContDiff.comp ( LinearIsometryEquiv.contDiff _ ) ( hC2.fderiv_right ( by norm_num ) );
  convert hGradC1.continuous_fderiv ( by norm_num ) using 1

lemma hessian_pd_local_lower_bound [FiniteDimensional ℝ E]
    (hC2 : ContDiff ℝ 2 f)
    (x : E)
    (hPD : ∀ p : E, p ≠ 0 → 0 < ⟪hessian f x p, p⟫) :
    ∃ ε > (0 : ℝ), ∃ ρ > (0 : ℝ), ∀ y ∈ ball x ρ, ∀ p : E,
      ε * ‖p‖ ^ 2 ≤ ⟪hessian f y p, p⟫ := by
  obtain ⟨ε₀, hε₀_pos, hε₀⟩ := inner_coercive_of_pd (hessian f x) hPD
  have hcont_diff : Continuous (fun y => hessian f y - hessian f x) :=
    (continuous_hessian f hC2).sub continuous_const
  have hcont_norm : Continuous (fun y => ‖hessian f y - hessian f x‖) :=
    continuous_norm.comp hcont_diff
  have h0 : ‖hessian f x - hessian f x‖ = 0 := by simp
  have hlt : ε₀ / 2 > 0 := half_pos hε₀_pos
  have hmem : {y | ‖hessian f y - hessian f x‖ < ε₀ / 2} ∈ 𝓝 x :=
    hcont_diff.norm.continuousAt.preimage_mem_nhds (by rw [h0]; exact Iio_mem_nhds hlt)
  obtain ⟨ρ, hρ_pos, hρ⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨ε₀ / 2, hlt, ρ, hρ_pos, fun y hy p => ?_⟩
  have hynorm : ‖hessian f y - hessian f x‖ < ε₀ / 2 := by
    have := hρ hy
    simpa [Metric.mem_ball, Real.dist_eq] using this
  have hpert : |⟪(hessian f y - hessian f x) p, p⟫| ≤ ‖hessian f y - hessian f x‖ * ‖p‖ ^ 2 := by
    calc |⟪(hessian f y - hessian f x) p, p⟫|
        ≤ ‖(hessian f y - hessian f x) p‖ * ‖p‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖hessian f y - hessian f x‖ * ‖p‖) * ‖p‖ := by
            gcongr; exact ContinuousLinearMap.le_opNorm _ _
      _ = ‖hessian f y - hessian f x‖ * ‖p‖ ^ 2 := by ring
  have hlow : -(ε₀ / 2) * ‖p‖ ^ 2 ≤ ⟪(hessian f y - hessian f x) p, p⟫ := by
    have := (abs_le.mp hpert).1
    nlinarith [sq_nonneg ‖p‖]
  have hsplit : ⟪hessian f y p, p⟫ = ⟪hessian f x p, p⟫ + ⟪(hessian f y - hessian f x) p, p⟫ := by
    simp [ContinuousLinearMap.sub_apply, inner_sub_left]
  linarith [hε₀ p]

-- ---------------------------------------------------------------------------
-- Theorem 2.5 (usable form): strict local min from uniform Hessian LB
-- ---------------------------------------------------------------------------

/-- A clean sufficient condition (Theorem 2.5, “operational form”):
if `∇f(x)=0` and the Hessian has a uniform quadratic-form lower bound on a ball,
then `x` is a strict local minimizer. -/
theorem strict_local_min_of_gradient_zero_hessian_uniform_lb
  [FiniteDimensional ℝ E]
    (hC2 : ContDiff ℝ 2 f)
    (x : E)
    (hgrad : gradient f x = 0)
    (ε ρ : ℝ) (_hε : 0 < ε) (hρ : 0 < ρ)
    (hHess_lb : ∀ y ∈ ball x ρ, ∀ p : E, ε * ‖p‖ ^ 2 ≤ ⟪hessian f y p, p⟫) :
    IsStrictLocalMin f x := by
  rw [IsStrictLocalMin]
  refine ⟨ball x ρ, Metric.ball_mem_nhds x hρ, ?_⟩
  intro y hy hy_ne
  set p : E := y - x
  have hy_eq : y = x + p := by simp [p, add_sub_cancel]
  have hp_small : ‖p‖ < ρ := by
    simpa [p, dist_eq_norm] using hy
  have hp_ne : p ≠ 0 := by
    intro hp0
    apply hy_ne
    have : y = x := by
      have : y - x = 0 := hp0
      simpa [sub_eq_zero] using this
    simp [this]
  have hlb :
      (ε / 2) * ‖p‖ ^ 2 ≤ f (x + p) - f x :=
    taylor_lower_bound_from_hessian_lb (f := f) hC2 x hgrad ε ρ _hε hρ hHess_lb p hp_small
  have hpos : 0 < (ε / 2) * ‖p‖ ^ 2 := by
    have : 0 < ‖p‖ := norm_pos_iff.2 hp_ne
    have : 0 < ‖p‖ ^ (2 : ℕ) := by nlinarith
    nlinarith [_hε]
  have : f x < f (x + p) := by linarith
  simpa [hy_eq] using this

/-- Theorem 2.5: if you can produce ε,ρ and a uniform Hessian lower bound,
then `x` is a strict local minimizer.

(Once `hessian_pd_local_lower_bound` is proved in your intended setting, you can
derive the ε, ρ, and `hHess_lb` automatically and use this theorem.) -/
theorem second_order_sufficient_condition
  [FiniteDimensional ℝ E]
    (hC2 : ContDiff ℝ 2 f)
    (x : E)
    (hgrad : gradient f x = 0)
    (hPD : ∀ p : E, p ≠ 0 → 0 < ⟪hessian f x p, p⟫) :
    IsStrictLocalMin f x := by
  rcases hessian_pd_local_lower_bound (f := f) hC2 x hPD with ⟨ε, hε, ρ, hρ, hHess_lb⟩
  exact strict_local_min_of_gradient_zero_hessian_uniform_lb
    (f := f) hC2 x hgrad ε ρ hε hρ hHess_lb

end SufficientConditions

end Optimization
end Lean4ML
