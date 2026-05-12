import Mathlib

open scoped Real
open scoped RealInnerProductSpace
open Set

namespace Lean4ML
namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : E → ℝ} {s : Set E}

def minimizersOn (f : E → ℝ) (s : Set E) : Set E :=
  {x ∈ s | IsMinOn f s x}

-- theorem 2.6 - a)
#check IsMinOn.of_isLocalMinOn_of_convexOn

-- theorem 2.6 - b)
theorem ConvexOn.convex_minimizers_instructional
    (h_conv : ConvexOn ℝ s f) :
    Convex ℝ (minimizersOn f s) := by
  set M := (minimizersOn f s) with hM
  by_cases h : Set.Nonempty M
  ·
    intro x hx y hy a b ha hb hab
    obtain ⟨hx_in_s, hx_is_min⟩ := hx
    obtain ⟨hy_in_s, hy_is_min⟩ := hy
    set z := a • x + b • y
    change z ∈ s ∧ IsMinOn f s z
    constructor
    ·
      exact h_conv.left hx_in_s hy_in_s ha hb hab
    ·
      intro w hw
      have h_convex := h_conv.right hx_in_s hy_in_s ha hb hab
      have hx_bound := (hx_is_min hw)
      have hy_bound := (hy_is_min hw)

      dsimp only [Set.mem_setOf_eq] at hx_bound
      dsimp only [Set.mem_setOf_eq] at hy_bound
      dsimp only [Set.mem_setOf_eq]

      calc f z
          ≤ a • f x + b • f y := h_convex
        _ ≤ a • f w + b • f w := (by
          have h1 := smul_le_smul_of_nonneg_left hx_bound ha
          have h2 := smul_le_smul_of_nonneg_left hy_bound hb
          exact add_le_add h1 h2
        )
        _ = (a + b) • f w     := by rw [add_smul]
        _ = (1 : ℝ) • f w     := by rw [hab];
        _ = f w               := by rw [one_smul]
  ·
    have h_empty : M = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [h_empty]
    exact convex_empty

-- theorem 2.6 - b)
theorem ConvexOn.convex_minimizers_mathlib
    (h_conv : ConvexOn ℝ s f) :
    Convex ℝ (minimizersOn f s) := by
  rintro x ⟨hx_s, hx_min⟩ y ⟨hy_s, hy_min⟩ a b ha hb hab
  refine ⟨h_conv.1 hx_s hy_s ha hb hab, fun w hw => ?_⟩
  calc
    f (a • x + b • y) ≤ a • f x + b • f y := h_conv.2 hx_s hy_s ha hb hab
    _ ≤ a • f w + b • f w                 := by gcongr; exacts [hx_min hw, hy_min hw]
    _ = f w                               := by rw [← add_smul, hab, one_smul]
