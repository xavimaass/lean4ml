import Mathlib
import lean4ml.Optimization.Defs

noncomputable section

open scoped Real
open scoped RealInnerProductSpace
open Set

namespace Lean4ML
namespace Optimization

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The canonical line map through `x` in direction `p`. -/
def lineMap (x p : E) : ℝ → E := fun t => x + t • p

@[simp]
theorem lineMap_apply (x p : E) (t : ℝ) : lineMap x p t = x + t • p := by
  let _ := (inferInstance : CompleteSpace E)
  rfl

/- Continuity of `t ↦ (Df (x + t p)) p` along a line. -/
lemma continuous_fderiv_line_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} (hC1 : ContDiff ℝ 1 f) (x p : E) :
    Continuous (fun t : ℝ => (fderiv ℝ f (x + t • p)) p) := by
  let _ := (inferInstance : CompleteSpace E)
  have hpair_cont : Continuous (fun t : ℝ => (x + t • p, p)) :=
    ((continuous_const).add (continuous_id.smul continuous_const)).prodMk continuous_const
  simpa [Function.comp] using (hC1.continuous_fderiv_apply one_ne_zero).comp hpair_cont

lemma continuous_inner_gradient_line
    (f : E → ℝ) (hC1 : ContDiff ℝ 1 f) (x p : E) :
    Continuous (fun t : ℝ => ⟪gradient f (x + t • p), p⟫) := by
  let _ := (inferInstance : CompleteSpace E)
  have hf := hasGradientAt_of_contDiff_one f hC1
  have h_eq : (fun t : ℝ => ⟪gradient f (x + t • p), p⟫) = (fun t : ℝ => (fderiv ℝ f (x + t • p)) p) := by
    funext t
    simpa using ((hf (x + t • p)).fderiv_apply (y := p)).symm
  simpa [h_eq] using continuous_fderiv_line_apply (hC1 := hC1) (x := x) (p := p)

/-- Integrability of the line integrand `t ↦ ⟪∇f(x + t p), p⟫` on any interval. -/
lemma intervalIntegrable_inner_gradient_line
    (f : E → ℝ) (hC1 : ContDiff ℝ 1 f) (x p : E) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => ⟪gradient f (x + t • p), p⟫)
      MeasureTheory.volume a b :=
  let _ := (inferInstance : CompleteSpace E)
  (continuous_inner_gradient_line f hC1 x p).continuousOn.intervalIntegrable


/-- Chain rule for composing a map with the line `τ ↦ x + τ • p`. -/
lemma hasDerivAt_comp_line
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f : E → F} (x p : E) (t : ℝ)
  (hf : HasFDerivAt f (fderiv ℝ f (x + t • p)) (x + t • p)) :
    HasDerivAt (fun τ : ℝ => f (x + τ • p))
      ((fderiv ℝ f (x + t • p)) p) t := by
  let _ := (inferInstance : CompleteSpace E)
  simpa [one_smul] using hf.comp_hasDerivAt t (((hasDerivAt_id t).smul_const p).const_add x)


/-- Distance from `x` to a point on the line: `dist (x + t • p) x = |t| * ‖p‖`. -/
theorem dist_lineMap (x p : E) (t : ℝ) :
    dist (lineMap x p t) x = |t| * ‖p‖ := by
  let _ := (inferInstance : CompleteSpace E)
  simp [lineMap_apply, dist_eq_norm, norm_smul]

/-- Norm of a segment displacement: `‖(x + t • p) - x‖ = |t| * ‖p‖`. -/
theorem norm_sub_lineMap (x p : E) (t : ℝ) :
    ‖(lineMap x p t) - x‖ = |t| * ‖p‖ := by
  let _ := (inferInstance : CompleteSpace E)
  simp [lineMap_apply, norm_smul]

/-- Segment point `x + t • (y - x)` remains in a convex set for `t ∈ [0,1]`. -/
theorem Convex.add_smul_sub_mem_unit (s : Set E)
    (hConv : Convex ℝ s) (x y : E) (hx : x ∈ s) (hy : y ∈ s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    x + t • (y - x) ∈ s := by
  let _ := (inferInstance : CompleteSpace E)
  exact hConv.add_smul_sub_mem hx hy ht

/-- The quadratic form of the Hessian scales as `α²`:
    `⟪hessian f x (α • p), α • p⟫ = α² * ⟪hessian f x p, p⟫`. -/
theorem hessian_inner_smul
    {f : E → ℝ} (x p : E) (α : ℝ) :
    ⟪hessian f x (α • p), α • p⟫ = α ^ 2 * ⟪hessian f x p, p⟫ := by
  let _ := (inferInstance : CompleteSpace E)
  simp [real_inner_smul_left, real_inner_smul_right]
  ring

/-- The map `t ↦ hessian f (x + t • p) p` is continuous. -/
lemma continuous_hessian_line
    (f : E → ℝ) (hC2 : ContDiff ℝ 2 f) (x p : E) :
    Continuous (fun t : ℝ => hessian f (x + t • p) p) := by
  let _ := (inferInstance : CompleteSpace E)
  apply continuous_fderiv_line_apply (f := fun y : E => gradient f y)
  simpa [gradient] using
    (InnerProductSpace.toDual ℝ E).symm.contDiff.comp
      (hC2.fderiv_right (m := 1) (by norm_num))

end Optimization
end Lean4ML
