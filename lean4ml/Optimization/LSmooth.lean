import Mathlib
import Lean4ML.Optimization.Defs

noncomputable section

open scoped Real
open scoped RealInnerProductSpace
open Set

namespace Lean4ML
namespace Optimization

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Derivative operator norm bound extracted from a Lipschitz-on-set hypothesis. -/
lemma opNorm_fderiv_le_of_lipschitz
    {g : E → E} {L : NNReal} {s : Set E} {x : E}
    (hL : LipschitzOnWith L g s)
    (hf : HasFDerivAt g (fderiv ℝ g x) x)
    (hs : s ∈ nhds x) :
    ‖fderiv ℝ g x‖ ≤ (L : ℝ) := by
  let _ := (inferInstance : CompleteSpace E)
  simpa using hf.le_of_lipschitzOn (x₀ := x) (s := s) hs hL

/-- Inner-product control by operator norm and squared vector norm. -/
lemma inner_le_opNorm_mul_norm_sq
    (A : E →L[ℝ] E) (p : E) :
    ⟪A p, p⟫ ≤ ‖A‖ * ‖p‖ ^ (2 : ℕ) := by
  let _ := (inferInstance : CompleteSpace E)
  calc
    ⟪A p, p⟫ ≤ ‖A p‖ * ‖p‖ := real_inner_le_norm _ _
    _ ≤ (‖A‖ * ‖p‖) * ‖p‖ := by
          gcongr
          exact ContinuousLinearMap.le_opNorm A p
    _ = ‖A‖ * ‖p‖ ^ (2 : ℕ) := by ring

section TaylorAndSmoothness

variable (f : E → ℝ) (L : NNReal) (s : Set E)
variable {x y p : E} {γ : ℝ}

/-- A `C^1` real-valued map on a Hilbert space has gradient everywhere. -/
lemma hasGradientAt_of_contDiff_one
    (hC1 : ContDiff ℝ 1 f) :
    ∀ z, HasGradientAt f (gradient f z) z := by
  intro z
  exact (hC1.contDiffAt.differentiableAt one_ne_zero).hasGradientAt

/-- Norm form of `LSmoothOn`: gradient differences are bounded by `L * ‖x-y‖`. -/
lemma norm_gradient_sub_le
    (hL : LSmoothOn f L s) (hx : x ∈ s) (hy : y ∈ s) :
    ‖gradient f x - gradient f y‖ ≤ (L : ℝ) * ‖x - y‖ := by
  let _ := (inferInstance : CompleteSpace E)
  have h_edist := hL hx hy
  simp only [edist_dist, dist_eq_norm] at h_edist
  have L_nonneg : (0 : ℝ) ≤ (L : ℝ) := by
    norm_cast
    norm_num
  have L_eq :
      ↑L * ENNReal.ofReal ‖x - y‖ = ENNReal.ofReal ((L : ℝ) * ‖x - y‖) := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul L_nonneg]
  have key : ENNReal.ofReal ‖gradient f x - gradient f y‖ ≤
      ENNReal.ofReal ((L : ℝ) * ‖x - y‖) := by
    rw [L_eq] at h_edist
    exact h_edist
  have h_nonneg : 0 ≤ (L : ℝ) * ‖x - y‖ := by positivity
  exact (ENNReal.ofReal_le_ofReal_iff h_nonneg).mp key

/-- Continuity of `t ↦ (Df (x + t p)) p` along a line. -/
lemma continuous_fderiv_line_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} (hC1 : ContDiff ℝ 1 f) (x p : E) :
    Continuous (fun t : ℝ => (fderiv ℝ f (x + t • p)) p) := by
  let _ := (inferInstance : CompleteSpace E)
  have hpair_cont : Continuous (fun t : ℝ => (x + t • p, p)) :=
    ((continuous_const).add (continuous_id.smul continuous_const)).prodMk continuous_const
  simpa [Function.comp] using (hC1.continuous_fderiv_apply one_ne_zero).comp hpair_cont

/-- Continuity of `t ↦ ⟪∇f(x + t p), p⟫` along a line. -/
lemma continuous_inner_gradient_line
    (hC1 : ContDiff ℝ 1 f) (x p : E) :
    Continuous (fun t : ℝ => ⟪gradient f (x + t • p), p⟫) := by
  have hf := hasGradientAt_of_contDiff_one (f := f) hC1
  have h_eq :
      (fun t : ℝ => ⟪gradient f (x + t • p), p⟫)
        = (fun t : ℝ => (fderiv ℝ f (x + t • p)) p) := by
    funext t
    simpa using ((hf (x + t • p)).fderiv_apply (y := p)).symm
  simpa [h_eq] using continuous_fderiv_line_apply (f := f) hC1 x p

/-- Integrability of the line integrand `t ↦ ⟪∇f(x + t p), p⟫` on any interval. -/
lemma intervalIntegrable_inner_gradient_line
    (hC1 : ContDiff ℝ 1 f) (x p : E) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => ⟪gradient f (x + t • p), p⟫)
      MeasureTheory.volume a b :=
  (continuous_inner_gradient_line (f := f) hC1 x p).continuousOn.intervalIntegrable

/-- A line segment displacement has norm `γ * ‖y - x‖` for `γ ≥ 0`. -/
lemma norm_add_smul_sub_eq (hγ : 0 ≤ γ) (x y : E) :
    ‖(x + γ • (y - x)) - x‖ = γ * ‖y - x‖ := by
  let _ := (inferInstance : CompleteSpace E)
  rw [show (x + γ • (y - x)) - x = γ • (y - x) by abel]
  simp [norm_smul, Real.norm_of_nonneg hγ]

/-- Derivative of the line map `τ ↦ x + τ • p`. -/
lemma hasDerivAt_line_add_smul (x p : E) (t : ℝ) :
    HasDerivAt (fun τ : ℝ => x + τ • p) p t := by
  let _ := (inferInstance : CompleteSpace E)
  simpa [one_smul] using ((hasDerivAt_id t).smul_const p).const_add x

/-- Chain rule for composing a map with the line `τ ↦ x + τ • p`. -/
lemma hasDerivAt_comp_line
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f : E → F} (x p : E) (t : ℝ)
  (hf : HasFDerivAt f (fderiv ℝ f (x + t • p)) (x + t • p)) :
    HasDerivAt (fun τ : ℝ => f (x + τ • p))
      ((fderiv ℝ f (x + t • p)) p) t := by
  let _ := (inferInstance : CompleteSpace E)
  simpa using hf.comp_hasDerivAt t (hasDerivAt_line_add_smul (x := x) (p := p) (t := t))

/-- Integrate an inner-product difference by splitting off the constant term. -/
lemma integral_inner_sub_const
    (g : ℝ → E) (c w : E) (a b : ℝ)
    (hg : IntervalIntegrable (fun t : ℝ => ⟪g t, w⟫) MeasureTheory.volume a b) :
    ∫ t in a..b, ⟪g t - c, w⟫ =
      (∫ t in a..b, ⟪g t, w⟫) - ∫ _t in a..b, ⟪c, w⟫ := by
  let _ := (inferInstance : CompleteSpace E)
  have hconst :
      IntervalIntegrable (fun _t : ℝ => ⟪c, w⟫) MeasureTheory.volume a b :=
    intervalIntegrable_const
  calc
    ∫ t in a..b, ⟪g t - c, w⟫
        = ∫ t in a..b, (⟪g t, w⟫ - ⟪c, w⟫) := by
            congr with t
            simp [sub_eq_add_neg, inner_add_left]
    _ = (∫ t in a..b, ⟪g t, w⟫) - ∫ _t in a..b, ⟪c, w⟫ := by
          simpa using intervalIntegral.integral_sub hg hconst

/-- Monotonicity of interval integrals, with continuity used to discharge integrability. -/
lemma intervalIntegral_mono_of_continuous
    {φ ψ : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (h_le : ∀ t ∈ Icc a b, φ t ≤ ψ t) :
    ∫ t in a..b, φ t ≤ ∫ t in a..b, ψ t := by
  refine intervalIntegral.integral_mono_on (a := a) (b := b) (f := φ) (g := ψ)
    hab ?_ ?_ h_le
  · exact hφ.continuousOn.intervalIntegrable
  · exact hψ.continuousOn.intervalIntegrable

/-- Useful linearity rewrite in the first inner-product argument. -/
lemma inner_sub_left_eq (u v w : E) :
    ⟪u, w⟫ - ⟪v, w⟫ = ⟪u - v, w⟫ := by
  let _ := (inferInstance : CompleteSpace E)
  simp [sub_eq_add_neg, inner_add_left]

/-- Segment point written as `x + t • (y - x)` remains in a convex set for `t ∈ [0,1]`. -/
lemma Convex.add_smul_sub_mem_unit
    (hConv : Convex ℝ s) (hx : x ∈ s) (hy : y ∈ s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    x + t • (y - x) ∈ s := by
  let _ := (inferInstance : CompleteSpace E)
  exact hConv.add_smul_sub_mem hx hy ht

/-- A vector-valued first-order Taylor formula along a line segment. -/
theorem taylor_first_order_vector
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E → F) (hC1 : ContDiff ℝ 1 f) (x p : E) :
    f (x + p) - f x = ∫ t in (0 : ℝ)..1, (fderiv ℝ f (x + t • p)) p := by
  let g : ℝ → F := fun t => f (x + t • p)
  have hg_deriv :
      ∀ t, HasDerivAt g ((fderiv ℝ f (x + t • p)) p) t := by
    intro t
    have hf' : HasFDerivAt f (fderiv ℝ f (x + t • p)) (x + t • p) :=
      (hC1.contDiffAt.differentiableAt one_ne_zero).hasFDerivAt
    simpa [g] using hasDerivAt_comp_line (f := f) (x := x) (p := p) (t := t) hf'
  have hg_deriv_uIcc :
      ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt g ((fderiv ℝ f (x + t • p)) p) t := by
    intro t _
    exact hg_deriv t
  have h_int :
      IntervalIntegrable (fun t : ℝ => (fderiv ℝ f (x + t • p)) p)
        MeasureTheory.volume (0 : ℝ) 1 :=
    (continuous_fderiv_line_apply (f := f) hC1 x p).continuousOn.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hg_deriv_uIcc h_int
  simpa [g] using hFTC.symm

/-- Scalar-valued first-order Taylor formula, as a corollary of the vector-valued version. -/
theorem taylor_first_order
  (hC1 : ContDiff ℝ 1 f)
  (x p : E) :
  f (x + p) - f x =
    ∫ t in (0 : ℝ)..1, ⟪gradient f (x + t • p), p⟫ := by
  have hvec := taylor_first_order_vector (E := E) (F := ℝ) f hC1 x p
  have h_integrand_eq :
      (∫ t in (0 : ℝ)..1, (fderiv ℝ f (x + t • p)) p)
        = ∫ t in (0 : ℝ)..1, ⟪gradient f (x + t • p), p⟫ := by
    congr with t
    have hf := hasGradientAt_of_contDiff_one (f := f) hC1 (x + t • p)
    simpa using hf.fderiv_apply (y := p)
  simpa [h_integrand_eq] using hvec

/-- First-order expansion of the gradient, i.e. second-order Taylor along a line. -/
theorem taylor_second_order_gradient
  (hC2 : ContDiff ℝ 2 f)
  (x p : E) :
  gradient f (x + p) - gradient f x =
    ∫ t in (0 : ℝ)..1, hessian f (x + t • p) p := by
  have hgradC1 : ContDiff ℝ 1 (fun y : E => gradient f y) := by
    simpa [gradient] using
      ((InnerProductSpace.toDual ℝ E).symm.contDiff.comp
        (hC2.fderiv_right (m := 1) (by norm_num)))
  simpa [hessian] using
    taylor_first_order_vector (E := E) (F := E) (fun y : E => gradient f y) hgradC1 x p


theorem lipschitz_gradient_pointwise
  (hL : LSmoothOn f L s)
  (hx : x ∈ s)
  (hγ : x + γ • (y - x) ∈ s)
  (hγpos : 0 ≤ γ) :
  ⟪gradient f (x + γ • (y - x)) - gradient f x, y - x⟫
    ≤ (L : ℝ) * γ * ‖y - x‖ ^ 2 := by

  -- Step 1: Get Lipschitz bound in norm form
  have hnorm :
      ‖gradient f (x + γ • (y - x)) - gradient f x‖
        ≤ (L : ℝ) * γ * ‖y - x‖ := by
    have h_basic : ‖gradient f (x + γ • (y - x)) - gradient f x‖ ≤
        (L : ℝ) * ‖(x + γ • (y - x)) - x‖ :=
      norm_gradient_sub_le (f := f) (L := L) (s := s)
        (x := x + γ • (y - x)) (y := x) hL hγ hx
    calc ‖gradient f (x + γ • (y - x)) - gradient f x‖
        ≤ (L : ℝ) * ‖(x + γ • (y - x)) - x‖ := h_basic
      _ = (L : ℝ) * (γ * ‖y - x‖) := by rw [norm_add_smul_sub_eq (x := x) (y := y) hγpos]
      _ = (L : ℝ) * γ * ‖y - x‖ := by ring

  -- Step 2: Cauchy-Schwarz
  calc ⟪gradient f (x + γ • (y - x)) - gradient f x, y - x⟫
      ≤ ‖gradient f (x + γ • (y - x)) - gradient f x‖ * ‖y - x‖ :=
          real_inner_le_norm _ _
    _ ≤ ((L : ℝ) * γ * ‖y - x‖) * ‖y - x‖ := by gcongr
    _ = (L : ℝ) * γ * ‖y - x‖ ^ 2 := by ring

/-- Non-parametric gradient-inner bound implied by `L`-smoothness on `s`. -/
lemma inner_grad_diff_le_L
    (hL : LSmoothOn f L s)
    (hx : x ∈ s) (hy : y ∈ s) :
    ⟪gradient f y - gradient f x, y - x⟫
      ≤ (L : ℝ) * ‖y - x‖ ^ (2 : ℕ) := by
  have : x + (1 : ℝ) • (y - x) = y := by simp
  simpa using
    lipschitz_gradient_pointwise (f := f) (L := L) (s := s)
      (x := x) (y := y) (γ := 1) hL hx (by simpa using hy) (by norm_num : 0 ≤ (1 : ℝ))

theorem l_smooth_quadratic_upper_bound
  (hC1 : ContDiff ℝ 1 f)
  (hL : LSmoothOn f L s)
  (hConv : Convex ℝ s)
  (hx : x ∈ s)
  (hy : y ∈ s) :
  f y ≤ f x + ⟪gradient f x, y - x⟫ + ((L : ℝ) / 2) * ‖y - x‖ ^ 2 := by

  let p := y - x
  -- 1. Get the exact integral for f y - f x using your previous lemma
  have h_taylor := taylor_first_order f hC1 x p

  -- 2. Subtract the constant gradient term ⟪gradient f x, p⟫ from both sides inside the integral
  have h_sub : f y - f x - ⟪gradient f x, p⟫ = ∫ t in (0:ℝ)..1, ⟪gradient f (x + t • p) - gradient f x, p⟫ := by
    have h_taylor' : f y - f x = ∫ t in (0 : ℝ)..1, ⟪gradient f (x + t • p), p⟫ := by
      simpa [p, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h_taylor
    have h_int_grad :
        IntervalIntegrable (fun t : ℝ => ⟪gradient f (x + t • p), p⟫) MeasureTheory.volume (0 : ℝ) 1 := by
      simpa using intervalIntegrable_inner_gradient_line (f := f) hC1 x p (0 : ℝ) 1
    calc
      f y - f x - ⟪gradient f x, p⟫
          = (∫ t in (0 : ℝ)..1, ⟪gradient f (x + t • p), p⟫) - ⟪gradient f x, p⟫ := by
              simp [h_taylor']
      _ = (∫ t in (0 : ℝ)..1, ⟪gradient f (x + t • p), p⟫)
            - ∫ _t in (0 : ℝ)..1, ⟪gradient f x, p⟫ := by
              simp
      _ = ∫ t in (0 : ℝ)..1, ⟪gradient f (x + t • p) - gradient f x, p⟫ := by
              simpa using (integral_inner_sub_const
                (g := fun t : ℝ => gradient f (x + t • p))
                (c := gradient f x) (w := p) (a := (0 : ℝ)) (b := 1) h_int_grad).symm

  -- 3. Integrate the pointwise bound you proved in `lipschitz_gradient_pointwise`
  have h_bound : ∫ t in (0:ℝ)..1, ⟪gradient f (x + t • p) - gradient f x, p⟫
               ≤ ∫ t in (0:ℝ)..1, (L : ℝ) * t * ‖p‖ ^ 2 := by
    have hcont_grad :
        Continuous (fun t : ℝ => ⟪gradient f (x + t • p), p⟫) := by
      simpa using continuous_inner_gradient_line (f := f) hC1 x p
    have hcont_left :
        Continuous (fun t : ℝ => ⟪gradient f (x + t • p) - gradient f x, p⟫) := by
      have hconst : Continuous (fun _t : ℝ => ⟪gradient f x, p⟫) := continuous_const
      simpa [inner_sub_left_eq] using hcont_grad.sub hconst
    have hcont_right : Continuous (fun t : ℝ => (L : ℝ) * t * ‖p‖ ^ 2) := by
      continuity
    refine intervalIntegral_mono_of_continuous (a := (0 : ℝ)) (b := 1)
      (hab := by norm_num) hcont_left hcont_right ?_
    intro t ht
    have hγ : x + t • (y - x) ∈ s := Convex.add_smul_sub_mem_unit (s := s) hConv hx hy ht
    have ht0 : 0 ≤ t := ht.1
    simpa [p] using
      (lipschitz_gradient_pointwise (f := f) (L := L) (s := s)
        (x := x) (y := y) (γ := t) hL hx hγ ht0)

  -- 4. The integral of (L * t * ‖p‖^2) from 0 to 1 evaluates exactly to (L / 2) * ‖p‖^2
  have h_eval : ∫ t in (0:ℝ)..1, (L : ℝ) * t * ‖p‖ ^ 2 = ((L : ℝ) / 2) * ‖p‖ ^ 2 := by
    have h_id : ∫ t in (0 : ℝ)..1, t = (1 : ℝ) / 2 := by
      norm_num [integral_id]
    calc
      ∫ t in (0 : ℝ)..1, (L : ℝ) * t * ‖p‖ ^ 2
          = (∫ t in (0 : ℝ)..1, (L : ℝ) * t) * ‖p‖ ^ 2 := by
              rw [intervalIntegral.integral_mul_const]
      _ = ((L : ℝ) * (∫ t in (0 : ℝ)..1, t)) * ‖p‖ ^ 2 := by
              rw [intervalIntegral.integral_const_mul]
      _ = ((L : ℝ) * ((1 : ℝ) / 2)) * ‖p‖ ^ 2 := by rw [h_id]
      _ = ((L : ℝ) / 2) * ‖p‖ ^ 2 := by ring

  -- 5. Conclude
  linarith

end TaylorAndSmoothness

section HessianVsSmoothness

variable (f : E → ℝ) (L : NNReal)

/-- Statement of Lemma 2.3 (→): Hessian bound implies global `L`-smoothness. -/
def HessianBoundImpliesLSmoothOnUnivStatement : Prop :=
  (∀ x, HasFDerivAt (fun y => gradient f y) (hessian f x) x) →
    (∀ x, ‖hessian f x‖ ≤ (L : ℝ)) →
    LSmoothOn f L Set.univ

/-- Statement of Lemma 2.3 (← direction in quadratic-form style). -/
def LSmoothOnUnivImpliesHessianQuadraticFormBoundStatement : Prop :=
  LSmoothOn f L Set.univ →
    (∀ x, HasFDerivAt (fun y => gradient f y) (hessian f x) x) →
    ∀ x p, ⟪hessian f x p, p⟫ ≤ (L : ℝ) * ‖p‖ ^ (2 : ℕ)

/-
Proof notes for implementation:
* `HessianBoundImpliesLSmoothOnUnivStatement` should use a Mathlib Lipschitz theorem from
  derivative operator-norm bounds on convex domains.
* `LSmoothOnUnivImpliesHessianQuadraticFormBoundStatement` follows via the quadratic model,
  second-order expansion, and a limit argument.
-/

/-- If the Hessian operator norm is globally bounded by `L`, then `f` is globally `L`-smooth. -/
theorem hessianBoundImpliesLSmoothOnUniv
    (hHasFDeriv : ∀ x, HasFDerivAt (fun y => gradient f y) (hessian f x) x)
    (hBound : ∀ x, ‖hessian f x‖ ≤ (L : ℝ)) :
    LSmoothOn f L Set.univ := by
  have hDiff : ∀ x, DifferentiableAt ℝ (fun y => gradient f y) x :=
    fun x => (hHasFDeriv x).differentiableAt
  have hBound' : ∀ x, ‖fderiv ℝ (fun y => gradient f y) x‖₊ ≤ L := by
    intro x
    rw [← NNReal.coe_le_coe]
    simpa [hessian] using hBound x
  exact lipschitzOnWith_univ.2 <|
    lipschitzWith_of_nnnorm_fderiv_le hDiff hBound'

/-- Global `L`-smoothness implies the Hessian quadratic-form upper bound everywhere. -/
theorem lSmoothOnUnivImpliesHessianQuadraticFormBound
    (hL : LSmoothOn f L Set.univ)
    (hHasFDeriv : ∀ x, HasFDerivAt (fun y => gradient f y) (hessian f x) x) :
    ∀ x p, ⟪hessian f x p, p⟫ ≤ (L : ℝ) * ‖p‖ ^ (2 : ℕ) := by
  intro x p
  have hOpNorm : ‖hessian f x‖ ≤ (L : ℝ) := by
    simpa [hessian] using
      opNorm_fderiv_le_of_lipschitz
        (hL := hL)
        (hf := hHasFDeriv x)
        (hs := Filter.univ_mem)
  calc
    ⟪hessian f x p, p⟫ ≤ ‖hessian f x‖ * ‖p‖ ^ (2 : ℕ) :=
      inner_le_opNorm_mul_norm_sq (A := hessian f x) p
    _ ≤ (L : ℝ) * ‖p‖ ^ (2 : ℕ) := by gcongr

theorem hessianBoundImpliesLSmoothOnUnivStatement_true :
    HessianBoundImpliesLSmoothOnUnivStatement (f := f) (L := L) := by
  intro hHasFDeriv hBound
  exact hessianBoundImpliesLSmoothOnUniv (f := f) (L := L) hHasFDeriv hBound

theorem lSmoothOnUnivImpliesHessianQuadraticFormBoundStatement_true :
    LSmoothOnUnivImpliesHessianQuadraticFormBoundStatement (f := f) (L := L) := by
  intro hL hHasFDeriv x p
  exact lSmoothOnUnivImpliesHessianQuadraticFormBound (f := f) (L := L) hL hHasFDeriv x p

end HessianVsSmoothness

end Optimization
end Lean4ML
