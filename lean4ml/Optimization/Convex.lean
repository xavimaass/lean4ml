import Mathlib

open scoped Real
open scoped RealInnerProductSpace
open scoped Topology
open Set

namespace Lean4ML
namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : E → ℝ} {s : Set E}
variable {x y : E}

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

-- first-order characterization of convexity
lemma ConvexOn.add_fderiv_le
    (h_conv : ConvexOn ℝ s f)
    (h_diff : DifferentiableAt ℝ f x)
    (hx : x ∈ s) (hy : y ∈ s) :
    f x + fderiv ℝ f x (y - x) ≤ f y := by

    -- Step 1: upper bound to middle point
    have h_convex: ∀ (α : ℝ), 0 ≤ α → α ≤ 1 →
      f (x + α • (y - x)) ≤ (1 - α) * f x + α * f y := by
      intro α hα_nonneg hα_le_one
      calc f (x + α • (y - x))
        _ = f ((1 - α) • x + α • y) := by simp [sub_smul, smul_sub]; abel_nf
        _ ≤ (1 - α) * f x + α * f y :=
          h_conv.2 hx hy (sub_nonneg.mpr hα_le_one) hα_nonneg (sub_add_cancel 1 α)

    -- Step 2: arrange terms
    have h_arranged: ∀ (α : ℝ), 0 < α → α ≤ 1 →
      (f (x + α • (y - x)) - f (x)) / α ≤ (f y - f x) := by
      intro α hα_pos hα_le_one
      rw [div_le_iff₀ hα_pos]
      calc f (x + α • (y - x)) - f x
        _ ≤ ((1 - α) * f x + α * f y) - f x :=
          sub_le_sub_right (h_convex α hα_pos.le hα_le_one) (f x)
        _ = (f y - f x) * α                 := by ring

    -- Step 3: Taylor expansion / Taking the limit
    -- 3a. compute the derivative of line segment
    have h_path : HasDerivAt (fun (α : ℝ) ↦ x + α • (y - x)) (y - x) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (y - x) |>.const_add x
    -- 3b. compute the derivative of the full function
    have h_deriv : HasDerivAt (fun (α : ℝ) ↦ f (x + α • (y - x))) (fderiv ℝ f x (y - x)) (0 : ℝ) := by
      apply HasFDerivAt.comp_hasDerivAt 0 _ h_path
      simpa using h_diff.hasFDerivAt
    -- 3c. extract the limit of the difference quotient from the derivative
    have h_limit : Filter.Tendsto (fun α : ℝ ↦ (f (x + α • (y - x)) - f x) / α)
          (𝓝[>] (0 : ℝ)) (𝓝 (fderiv ℝ f x (y - x))) := by
      have key := (hasDerivAt_iff_tendsto_slope.mp h_deriv).mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) from
          nhdsWithin_mono 0 fun α (hα : α ∈ Set.Ioi 0) => hα.ne')
      refine key.congr' (eventually_nhdsWithin_of_forall fun α _ => ?_)
      simp only [slope, sub_zero, zero_smul, add_zero, smul_eq_mul, vsub_eq_sub]
      ring
    -- 3d. Pass the limit through the inequality
    have h_le : fderiv ℝ f x (y - x) ≤ f y - f x := by
      apply le_of_tendsto h_limit
      filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with α hα using h_arranged α hα.1 hα.2.le
    linarith

-- theorem 2.7
theorem ConvexOn.isMinOn_of_hasDerivAt_eq_zero
    (h_conv : ConvexOn ℝ s f)
    (h_diff : HasFDerivAt f (0 : E →L[ℝ] ℝ) x)
    (hx : x ∈ s) :
    IsMinOn f s x := by
  intro y hy
  have h := ConvexOn.add_fderiv_le h_conv h_diff.differentiableAt hx hy
  simp [h_diff.fderiv] at h
  exact h
