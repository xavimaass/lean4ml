import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Basic

noncomputable section

open scoped Real
open scoped RealInnerProductSpace
open Set Topology

namespace Lean4ML
namespace Optimization

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- `L`-smoothness on a set `s`, encoded as Lipschitz continuity of the gradient. -/
def LSmoothOn (f : E → ℝ) (L : NNReal) (s : Set E) : Prop :=
  LipschitzOnWith L (fun x => gradient f x) s

/-- A function `f : E → ℝ` is globally `L`-smooth if its gradient is `L`-Lipschitz. -/
def LSmoothfn (f : E → ℝ) (L : NNReal) : Prop :=
  LipschitzWith L (fun x => gradient f x)

lemma lSmooth_iff_lSmoothOn_univ {f : E → ℝ} {L : NNReal} :
    LSmoothfn f L ↔ LSmoothOn f L Set.univ := by
  simp [LSmoothfn, LSmoothOn, lipschitzOnWith_univ]

lemma LSmoothOn_mono {f : E → ℝ} {L : NNReal} {S T : Set E}
    (hf : LSmoothOn f L S) (hST : T ⊆ S) : LSmoothOn f L T :=
  LipschitzOnWith.mono hf hST

/-- Hessian of `f` represented as the Fréchet derivative of the gradient. -/
def hessian (f : E → ℝ) (x : E) : E →L[ℝ] E :=
  fderiv ℝ (fun y => gradient f y) x


/-- Strict local minimizer: there is a neighborhood `U` of `x` where `f x < f y` for `y ≠ x`. -/
def IsStrictLocalMin (f : E → ℝ) (x : E) : Prop :=
  ∃ U ∈ 𝓝 x, ∀ y ∈ U, y ≠ x → f x < f y


/-- Continuity of `t ↦ ⟪∇f(x + t p), p⟫` along a line. -/
lemma hasGradientAt_of_contDiff_one
    (f : E → ℝ) (hC1 : ContDiff ℝ 1 f) :
    ∀ z, HasGradientAt f (gradient f z) z := by
  intro z
  exact (hC1.contDiffAt.differentiableAt one_ne_zero).hasGradientAt

end Optimization
end Lean4ML
