import Mathlib

noncomputable section

open scoped Real
open Set

namespace Lean4ML
namespace Optimization

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The canonical line map through `x` in direction `p`. -/
def lineMap (x p : E) : ℝ → E := fun t => x + t • p

@[simp]
theorem lineMap_apply (x p : E) (t : ℝ) : lineMap x p t = x + t • p := rfl

/-- Distance from `x` to a point on the line: `dist (x + t • p) x = |t| * ‖p‖`. -/
theorem dist_lineMap (x p : E) (t : ℝ) :
    dist (lineMap x p t) x = |t| * ‖p‖ := by
  simp [lineMap_apply, dist_eq_norm, norm_smul]

/-- Norm of a segment displacement: `‖(x + t • p) - x‖ = |t| * ‖p‖`. -/
theorem norm_sub_lineMap (x p : E) (t : ℝ) :
    ‖(lineMap x p t) - x‖ = |t| * ‖p‖ := by
  simp [lineMap_apply, norm_smul]

/-- Segment point `x + t • (y - x)` remains in a convex set for `t ∈ [0,1]`. -/
theorem Convex.add_smul_sub_mem_unit (s : Set E)
    (hConv : Convex ℝ s) (x y : E) (hx : x ∈ s) (hy : y ∈ s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    x + t • (y - x) ∈ s := by
  exact hConv.add_smul_sub_mem hx hy ht

end Optimization
end Lean4ML
