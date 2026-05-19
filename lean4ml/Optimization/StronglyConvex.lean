import Mathlib
import Mathlib.Analysis.InnerProductSpace.Calculus

-- Custom --
import lean4ml.Optimization.Defs
import lean4ml.Optimization.Convex

open scoped Real
open scoped RealInnerProductSpace
open scoped Topology
open Set

namespace Lean4ML
namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ} {s : Set E} {m : ℝ} {L : NNReal}
variable {x y : E}

-- first-order characterization of convexity
omit [CompleteSpace E] in
lemma StronglyConvexOn.add_fderiv_le
    (h_conv : StrongConvexOn s m f)
    (h_diff : DifferentiableAt ℝ f x)
    (hx : x ∈ s) (hy : y ∈ s) :
    f x + fderiv ℝ f x (y - x) + m / 2 * ‖x-y‖ ^ 2 ≤ f y := by
    have h_conv2 := ConvexOn.add_fderiv_le
      (strongConvexOn_iff_convex.mp h_conv)
      (h_diff.sub ((differentiableAt_id.norm_sq ℝ).const_mul (m / 2)))
      hx hy
    have h_fderiv : fderiv ℝ (fun y : E => f y - m / 2 * ‖y‖ ^ 2) x =
        fderiv ℝ f x - fderiv ℝ (fun y : E => m / 2 * ‖y‖ ^ 2) x :=
      fderiv_sub h_diff ((differentiableAt_id.norm_sq ℝ).const_mul _)
    rw [h_fderiv] at h_conv2
    simp only [ContinuousLinearMap.sub_apply] at h_conv2
    suffices - m / 2 * ‖x‖ ^ 2 - (fderiv ℝ (fun y ↦ m / 2 * ‖y‖ ^ 2) x) (y - x) + m / 2 * ‖y‖ ^ 2 = m / 2 * ‖x-y‖ ^ 2 by
      linarith
    have h_deriv : (fderiv ℝ (fun y ↦ m / 2 * ‖y‖ ^ 2) x) (y - x) = m * ⟪x, y - x⟫ := by
      simp_rw [← real_inner_self_eq_norm_sq, ← smul_eq_mul]
      change (fderiv ℝ ((m / 2) • fun y ↦ ⟪y, y⟫) x) (y - x) = _
      rw [fderiv_const_smul]
      simp
      ring
      apply DifferentiableAt.inner
      · exact differentiableAt_id
      · exact differentiableAt_id
    rw [h_deriv]
    simp_rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    rw [real_inner_comm y x]
    ring

-- theorem 2.8: unique global minimizer
omit [CompleteSpace E] in
theorem StrongConvexOn.isMinOn_of_fderiv_eq_zero
    (h_conv : StrongConvexOn s m f)
    (h_diff : DifferentiableAt ℝ f x)
    (h_stat : fderiv ℝ f x = 0)
    (hm : 0 < m) (hx : x ∈ s) :
    IsMinOn f s x ∧ ∀ y ∈ s, IsMinOn f s y → y = x := by
  have part1 : IsMinOn f s x := by
    intro z hz;
    have := StronglyConvexOn.add_fderiv_le h_conv h_diff hx hz;
    simp_all;
    exact le_trans ( le_add_of_nonneg_right ( by positivity ) ) this;
  refine' ⟨ part1, fun y hy hy' => _ ⟩
  have h_eq : f x = f y := by
    exact le_antisymm ( part1 hy ) ( hy' hx )
  have h_dist : ‖x - y‖ = 0 := by
    have := h_conv.2 hx hy ( by positivity ) ( by positivity ) ( show ( 1 / 2 : ℝ ) + ( 1 / 2 ) = 1 by norm_num );
    simp_all +decide [ StrongConvexOn ];
    exact Classical.not_not.1 fun h => absurd
      (
        part1 (show ( 1 / 2 : ℝ ) • x + ( 1 / 2 : ℝ ) • y ∈ s from h_conv.1 hx hy ( by norm_num ) ( by norm_num ) ( by norm_num ))
      )
      (
        by norm_num; nlinarith [ show 0 < m * ‖x - y‖ ^ 2 by exact mul_pos hm ( sq_pos_of_pos ( norm_pos_iff.mpr h ) ) ]
      )
  have h_eq' : x = y := by
    exact sub_eq_zero.mp ( norm_eq_zero.mp h_dist )
  exact h_eq'.symm

-- lemma 2.9: hessian characterization of strong convexity
lemma strongConvexOn_iff_hessian_lb
    (h_smooth : ContDiff ℝ 2 f) :
    StrongConvexOn s m f ↔ ∀ x ∈ s, ∀ u : E, m * ‖u‖ ^ 2 ≤ ⟪hessian f x u, u⟫ := by
  sorry

-- corollary 2.10: hessian sandwich characterization of L-smooth convex functions
lemma convexOn_lSmoothOn_iff_hessian_sandwich
    (h_smooth : ContDiff ℝ 2 f)
    (h_conv : ConvexOn ℝ s f) :
    LSmoothOn f L s ↔ ∀ x ∈ s, ∀ u : E, ⟪hessian f x u, u⟫ ≤ ↑L * ‖u‖ ^ 2 := by
  sorry
