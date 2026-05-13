import Mathlib

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

/-- Quadratic upper bound model used in descent lemmas. -/
def QuadraticUpperBound (f : E → ℝ) (L : NNReal) (s : Set E) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s,
    f y ≤ f x + ⟪gradient f x, y - x⟫ + ((L : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ)

/-- Hessian of `f` represented as the Fréchet derivative of the gradient. -/
def hessian (f : E → ℝ) (x : E) : E →L[ℝ] E :=
  fderiv ℝ (fun y => gradient f y) x

end Optimization
end Lean4ML
