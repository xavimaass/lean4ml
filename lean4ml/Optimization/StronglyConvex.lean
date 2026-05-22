import lean4ml.Optimization.Convex
import lean4ml.Optimization.LSmooth
import lean4ml.Optimization.NecessaryCondition
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.InnerProductSpace.Calculus

open scoped Real
open scoped RealInnerProductSpace
open scoped Topology
open Set

namespace Lean4ML
namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ} {s : Set E} {m : ℝ} {L : NNReal}
variable {x y : E}

-- expansion of ‖a + r • b‖² in a real inner product space
omit [CompleteSpace E] in
lemma norm_add_smul_sq (a b : E) (r : ℝ) :
    ‖a + r • b‖ ^ 2 = ‖a‖ ^ 2 + 2 * r * ⟪a, b⟫ + r ^ 2 * ‖b‖ ^ 2 := by
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
  ring

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

/-
Simple corollary: for a C¹ strongly convex function, any stationary point is a global minimizer
and the infimum of f equals its value at that point.
-/
omit [CompleteSpace E] in
theorem StrongConvexOn.isMinOn_of_stationary
    (h_conv : StrongConvexOn univ m f)
    (h_diff : Differentiable ℝ f)
    (hm : 0 < m) {x : E}
    (h_stat : fderiv ℝ f x = 0) :
    IsMinOn f univ x ∧ iInf f = f x := by
  have h := StrongConvexOn.isMinOn_of_fderiv_eq_zero h_conv (h_diff x) h_stat hm (mem_univ x)
  have hmin : IsMinOn f univ x := h.1
  have h_lb : ∀ y : E, f x ≤ f y := by
    intro y
    exact hmin (mem_univ y)
  have h_le_inf : f x ≤ iInf f := le_ciInf h_lb
  have h_bdd : BddBelow (Set.range f) :=
    ⟨f x, by
      rintro _ ⟨y, rfl⟩
      exact h_lb y⟩
  have h_inf_le : iInf f ≤ f x := ciInf_le h_bdd x
  have h_eq : iInf f = f x := by linarith [h_le_inf, h_inf_le]
  exact ⟨hmin, h_eq⟩


/-
Strong convexity midpoint bound: the distance between any two points is controlled
  by the average of their function values minus the infimum.
-/
omit [CompleteSpace E] in
lemma StrongConvexOn.midpoint_dist_bound
    {f : E → ℝ} {μ : ℝ} (_ : 0 < μ)
    (hSC : StrongConvexOn univ μ f)
    (hbdd : BddBelow (Set.range f))
    (x y : E) :
    μ / 8 * ‖x - y‖ ^ 2 ≤ (f x + f y) / 2 - iInf f := by
  -- By strong convexity definition (UniformConvexOn) with a = b = 1/2:
  have h_midpoint : f ((1/2 : ℝ) • x + (1/2 : ℝ) • y) + μ / 2 * ‖x - y‖ ^ 2 * (1/2 * 1/2) ≤ (1/2 : ℝ) * f x + (1/2 : ℝ) * f y := by
    have := hSC.2;
    specialize this ( Set.mem_univ x ) ( Set.mem_univ y ) ( show 0 ≤ ( 1 / 2 : ℝ ) by norm_num ) ( show 0 ≤ ( 1 / 2 : ℝ ) by norm_num ) ( by norm_num ) ; norm_num at * ; linarith;
  linarith [ show iInf f ≤ f ( ( 1 / 2 : ℝ ) • x + ( 1 / 2 : ℝ ) • y ) from ciInf_le hbdd _ ]

/-
For a strongly convex function with local gradient information, any point provides
a uniform lower bound on the entire function.
-/
lemma StrongConvexOn.quadratic_lower_bound_at_point
    (h_conv : StrongConvexOn univ m f)
    (h_diff : DifferentiableAt ℝ f x)
    (hm : 0 < m) :
    ∀ z : E, f x - 1 / (2 * m) * ‖gradient f x‖ ^ 2 ≤ f z := by
  intro z
  set g := gradient f x
  have h_two_m_pos : (0:ℝ) < 2 * m := by linarith
  -- From strong convexity: f(z) ≥ f(x) + ⟨∇f(x), z-x⟩ + m/2 ‖x-z‖²
  have h_fo_z : f x + fderiv ℝ f x (z - x) + m / 2 * ‖x - z‖ ^ 2 ≤ f z :=
    StronglyConvexOn.add_fderiv_le h_conv h_diff (mem_univ x) (mem_univ z)
  -- Express fderiv in terms of gradient
  have h_inner : fderiv ℝ f x (z - x) = ⟪g, z - x⟫ := by simp [g, gradient]
  rw [h_inner, norm_sub_rev x z] at h_fo_z
  -- Complete the square using ‖g + m•(z-x)‖² ≥ 0
  have h_sq_expanded : (0:ℝ) ≤ ‖g‖ ^ 2 + 2 * m * ⟪g, z - x⟫ + m ^ 2 * ‖z - x‖ ^ 2 :=
    (norm_add_smul_sq g (z - x) m) ▸ sq_nonneg _
  -- Multiply h_fo_z by 2m and combine with h_sq_expanded
  have h_fo_2m : 2 * m * f x + 2 * m * ⟪g, z - x⟫ + m ^ 2 * ‖z - x‖ ^ 2 ≤ 2 * m * f z := by
    nlinarith [mul_le_mul_of_nonneg_left h_fo_z h_two_m_pos.le]
  have h_combine : 2 * m * f x - ‖g‖ ^ 2 ≤ 2 * m * f z := by linarith
  -- Divide by 2m to get the result
  have h_div := (div_le_div_iff_of_pos_right h_two_m_pos).mpr h_combine
  have h_eq1 : (2 * m * f x - ‖g‖ ^ 2) / (2 * m) = f x - 1 / (2 * m) * ‖g‖ ^ 2 := by field_simp
  have h_eq2 : (2 * m * f z) / (2 * m) = f z := by field_simp
  linarith [h_div, h_eq1, h_eq2]

/-
A strongly convex differentiable function is bounded below.
-/
lemma StrongConvexOn.bddBelow_from_differentiable
    (h_conv : StrongConvexOn univ m f)
    (h_diff : Differentiable ℝ f)
    (hm : 0 < m) :
    BddBelow (Set.range f) := by
  -- Pick any point x₀ and use its lower bound for the entire function
  use f (0:E) - 1 / (2 * m) * ‖gradient f 0‖ ^ 2
  rintro _ ⟨z, rfl⟩
  exact StrongConvexOn.quadratic_lower_bound_at_point h_conv (h_diff 0) hm z

/-
A C¹ strongly convex function on all of E is bounded below.
-/
lemma StrongConvexOn.bddBelow_range
    {f : E → ℝ} {μ : ℝ} (hμ : 0 < μ)
    (hSC : StrongConvexOn univ μ f)
    (hC1 : ContDiff ℝ 1 f) :
    BddBelow (Set.range f) :=
  StrongConvexOn.bddBelow_from_differentiable hSC (hC1.differentiable (by norm_num)) hμ

/-
A C¹ strongly convex function on a complete Hilbert space attains its infimum;
  i.e., it has a global minimizer.
-/
theorem StrongConvexOn.exists_minimizer
    {f : E → ℝ} {μ : ℝ} (hμ : 0 < μ)
    (hC1 : ContDiff ℝ 1 f)
    (hSC : StrongConvexOn univ μ f) :
    ∃ xstar : E, IsMinOn f univ xstar := by
  -- By definition of strong convexity, f is bounded below.
  have h_bdd_below : BddBelow (Set.range f) := by
    exact StrongConvexOn.bddBelow_range hμ hSC hC1
  -- Construct a minimizing sequence: for each n : ℕ, use `exists_lt_of_ciInf_lt` to get xₙ with f(xₙ) < iInf f + 1/(n+1).
  have h_min_seq : ∃ (x : ℕ → E), ∀ n, f (x n) < iInf f + 1 / (n + 1) := by
    exact ⟨ fun n => Classical.choose ( exists_lt_of_ciInf_lt ( show iInf f < iInf f + 1 / ( n + 1 ) from lt_add_of_pos_right _ <| by positivity ) ), fun n => Classical.choose_spec ( exists_lt_of_ciInf_lt ( show iInf f < iInf f + 1 / ( n + 1 ) from lt_add_of_pos_right _ <| by positivity ) ) ⟩;
  -- Show the sequence is Cauchy: for n, m, use `StrongConvexOn.midpoint_dist_bound` to get μ/8 * ‖xₙ - xₘ‖² ≤ (f(xₙ) + f(xₘ))/2 - iInf f. Since f(xₙ), f(xₘ) < iInf f + 1/(n+1) + 1/(m+1), the RHS → 0. Use Metric.cauchySeq_iff or cauchySeq_of_le_geometric or show CauchySeq directly.
  obtain ⟨x, hx⟩ := h_min_seq
  have h_cauchy : CauchySeq x := by
    have h_cauchy : ∀ n m : ℕ, μ / 8 * ‖x n - x m‖ ^ 2 ≤ (f (x n) + f (x m)) / 2 - iInf f := by
      intro n m;
      apply_rules [ StrongConvexOn.midpoint_dist_bound ];
    have h_cauchy : ∀ n m : ℕ, ‖x n - x m‖ ^ 2 ≤ (8 / μ) * ((1 / (n + 1) + 1 / (m + 1)) / 2) := by
      intro n m; rw [ div_mul_eq_mul_div, le_div_iff₀ ] <;> nlinarith [ h_cauchy n m, hx n, hx m ] ;
    fapply cauchySeq_of_le_tendsto_0';
    use fun n => Real.sqrt ( 8 / μ * ( ( 1 / ( n + 1 ) + 1 / ( n + 1 ) ) / 2 ) );
    · intro n m hnm; rw [ dist_eq_norm ] ; exact Real.le_sqrt_of_sq_le ( le_trans ( h_cauchy n m ) ( by gcongr ) ) ;
    · exact le_trans ( Filter.Tendsto.sqrt <| tendsto_const_nhds.mul <| Filter.Tendsto.div_const ( Filter.Tendsto.add ( tendsto_one_div_add_atTop_nhds_zero_nat ) ( tendsto_one_div_add_atTop_nhds_zero_nat ) ) _ ) ( by norm_num );
  obtain ⟨ xstar, hxstar ⟩ := cauchySeq_tendsto_of_complete h_cauchy;
  -- By continuity of $f$, we have $f(xstar) = \lim_{n \to \infty} f(x_n) = \inf f$.
  have h_cont : f xstar = iInf f := by
    refine' tendsto_nhds_unique ( hC1.continuous.continuousAt.tendsto.comp hxstar ) ( tendsto_order.2 ⟨ _, _ ⟩ );
    · exact fun a ha => Filter.Eventually.of_forall fun n => lt_of_lt_of_le ha ( ciInf_le h_bdd_below _ );
    · exact fun a ha => by filter_upwards [ Filter.eventually_gt_atTop ⌈ ( a - iInf f ) ⁻¹⌉₊ ] with n hn using lt_of_lt_of_le ( hx n ) ( by nlinarith [ Nat.ceil_le.mp hn.le, mul_inv_cancel₀ ( by linarith : ( a - iInf f ) ≠ 0 ), one_div_mul_cancel ( by linarith : ( n : ℝ ) + 1 ≠ 0 ) ] ) ;
  exact ⟨ xstar, fun y hy => h_cont ▸ ciInf_le h_bdd_below y ⟩

/-
For a C¹ strongly convex function, the quadratic growth condition holds at any minimizer:
    `μ / 2 * ‖y - x*‖² ≤ f y - f x*`.
-/
omit [CompleteSpace E] in
lemma StrongConvexOn.quadratic_growth_at_minimizer
    {f : E → ℝ} {μ : ℝ}
    (hSC : StrongConvexOn univ μ f)
    (hC1 : ContDiff ℝ 1 f)
    {xstar : E} (hmin : IsMinOn f univ xstar) (y : E) :
    μ / 2 * ‖y - xstar‖ ^ 2 ≤ f y - f xstar := by
  have h_fderiv_zero : fderiv ℝ f xstar = 0 :=
    IsMinOn.fderiv_eq_zero_of_isMinOn_univ (f := f) hmin
  have h_strong_convex :
      f y ≥ f xstar + fderiv ℝ f xstar (y - xstar) + μ / 2 * ‖xstar - y‖ ^ 2 := by
    exact StronglyConvexOn.add_fderiv_le hSC (hC1.contDiffAt.differentiableAt (by norm_num))
      (by simp) (by simp)
  rw [h_fderiv_zero] at h_strong_convex
  simp_all +decide [norm_sub_rev]
  linarith

section HessianStrongConvexity

/- The gradient of f is C¹ when f is C². -/
lemma gradient_contDiff_one (h_smooth : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (fun y => gradient f y) := by
  simp [gradient]
  exact (LinearIsometryEquiv.contDiff _).comp (h_smooth.fderiv_right (m := 1) (by norm_num))

/- HasFDerivAt for the gradient at each point, when f is C². -/
lemma hasFDerivAt_gradient (h_smooth : ContDiff ℝ 2 f) (x : E) :
    HasFDerivAt (fun y => gradient f y) (hessian f x) x := by
  have := gradient_contDiff_one h_smooth
  exact (this.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt

/-
Forward direction: strong convexity implies Hessian lower bound.
    Key idea: apply first-order characterization at (x, x+tu) and (x+tu, x),
    add them to get ⟨∇f(x+tu) - ∇f(x), u⟩ ≥ m*t*‖u‖², divide by t, take t→0.
-/
set_option maxHeartbeats 400000 in
lemma strongConvexOn_imp_hessian_lb
    (h_smooth : ContDiff ℝ 2 f)
    (h_conv : StrongConvexOn univ m f) :
    ∀ x : E, ∀ u : E, m * ‖u‖ ^ 2 ≤ ⟪hessian f x u, u⟫ := by
  intro x u
  have h_forward : ∀ t : ℝ, 0 < t → (fderiv ℝ f (x + t • u) u - fderiv ℝ f x u) / t ≥ m * ‖u‖ ^ 2 := by
    intro t ht
    have h_add : f x + fderiv ℝ f x (t • u) + m / 2 * ‖t • u‖ ^ 2 ≤ f (x + t • u) := by
      have := h_conv.2 ( Set.mem_univ x ) ( Set.mem_univ ( x + t • u ) );
      have h_lim : Filter.Tendsto (fun a : ℝ => (f (a • x + (1 - a) • (x + t • u)) - f x) / (1 - a)) (nhdsWithin 1 (Set.Iio 1)) (nhds ((fderiv ℝ f x) (t • u))) := by
        have h_lim : HasDerivAt (fun a : ℝ => f (a • x + (1 - a) • (x + t • u))) ((fderiv ℝ f x) (t • u) * (-1)) 1 := by
          convert HasFDerivAt.hasDerivAt ( HasFDerivAt.comp 1 ( h_smooth.contDiffAt.differentiableAt ( by norm_num ) |> DifferentiableAt.hasFDerivAt ) ( HasFDerivAt.add ( HasFDerivAt.smul ( hasFDerivAt_id 1 ) ( hasFDerivAt_const _ _ ) ) ( HasFDerivAt.smul ( hasFDerivAt_id 1 |> HasFDerivAt.const_sub <| 1 ) ( hasFDerivAt_const _ _ ) ) ) ) using 1 ; norm_num;
        rw [ hasDerivAt_iff_tendsto_slope ] at h_lim;
        convert h_lim.neg.mono_left <| nhdsWithin_mono _ _ using 2 <;> norm_num [ div_eq_inv_mul, slope_def_field ];
        rw [ ← neg_sub, inv_neg ] ; ring;
      have h_lim_le : ∀ᶠ a in nhdsWithin 1 (Set.Iio 1), (f (a • x + (1 - a) • (x + t • u)) - f x) / (1 - a) ≤ f (x + t • u) - f x - a * (m / 2) * ‖t • u‖ ^ 2 := by
        filter_upwards [ Ioo_mem_nhdsLT zero_lt_one ] with a ha;
        rw [ div_le_iff₀ ] <;> norm_num at *;
        · convert this ha.1.le ( sub_nonneg.2 ha.2.le ) ( by linarith ) using 1 ; ring;
        · linarith;
      have h_lim_le : (fderiv ℝ f x) (t • u) ≤ f (x + t • u) - f x - 1 * (m / 2) * ‖t • u‖ ^ 2 := by
        exact le_of_tendsto_of_tendsto h_lim ( Filter.Tendsto.sub ( tendsto_const_nhds ) ( Filter.Tendsto.mul ( Filter.Tendsto.mul ( Filter.tendsto_id.mono_left inf_le_left ) tendsto_const_nhds ) tendsto_const_nhds ) ) h_lim_le |> le_trans <| by norm_num;
      linarith
    have h_add' : f (x + t • u) + fderiv ℝ f (x + t • u) (-t • u) + m / 2 * ‖-t • u‖ ^ 2 ≤ f x := by
      have := h_conv.2 ( Set.mem_univ ( x + t • u ) ) ( Set.mem_univ x );
      have h_add' : Filter.Tendsto (fun s : ℝ => (f (x + t • u + s • (-t • u)) - f (x + t • u)) / s) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((fderiv ℝ f (x + t • u)) (-t • u))) := by
        have h_add' : HasDerivAt (fun s : ℝ => f (x + t • u + s • (-t • u))) ((fderiv ℝ f (x + t • u)) (-t • u)) 0 := by
          convert HasFDerivAt.hasDerivAt ( HasFDerivAt.comp 0 ( h_smooth.contDiffAt.differentiableAt ( by norm_num ) |> DifferentiableAt.hasFDerivAt ) ( HasFDerivAt.add ( hasFDerivAt_const _ _ ) ( HasFDerivAt.smul ( hasFDerivAt_id 0 ) ( hasFDerivAt_const _ _ ) ) ) ) using 1 ; norm_num;
        simpa [ div_eq_inv_mul ] using h_add'.tendsto_slope_zero_right;
      have h_add' : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0), (f (x + t • u + s • (-t • u)) - f (x + t • u)) / s ≤ (f x - f (x + t • u)) - (1 / 2) * m * ‖-t • u‖ ^ 2 * (1 - s) := by
        filter_upwards [ Ioo_mem_nhdsGT zero_lt_one ] with s hs;
        have := @this ( 1 - s ) s ( by linarith [ hs.1, hs.2 ] ) ( by linarith [ hs.1, hs.2 ] ) ( by linarith [ hs.1, hs.2 ] ) ; simp_all +decide [ div_le_iff₀, norm_smul, sq ] ;
        convert this using 1 <;> ring_nf;
        simp +decide [ sub_smul ] ; abel_nf;
      have h_add' : (fderiv ℝ f (x + t • u)) (-t • u) ≤ f x - f (x + t • u) - (1 / 2) * m * ‖-t • u‖ ^ 2 := by
        have h_add' : Filter.Tendsto (fun s : ℝ => f x - f (x + t • u) - (1 / 2) * m * ‖-t • u‖ ^ 2 * (1 - s)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x - f (x + t • u) - (1 / 2) * m * ‖-t • u‖ ^ 2)) := by
          exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ ( by norm_num ) );
        exact le_of_tendsto_of_tendsto ‹_› ‹_› ‹_›;
      linarith
    simp_all +decide [ norm_smul, sq ];
    rw [ le_div_iff₀' ht ] ; rw [ abs_of_pos ht ] at * ; nlinarith [ mul_pos ht ht ] ;
  have h_limit : Filter.Tendsto (fun t : ℝ => ((fderiv ℝ f (x + t • u)) u - (fderiv ℝ f x) u) / t) (nhdsWithin 0 (Set.Ioi 0)) (nhds (fderiv ℝ (fun y => fderiv ℝ f y u) x u)) := by
    have h_limit : HasDerivAt (fun t : ℝ => (fderiv ℝ f (x + t • u)) u) ((fderiv ℝ (fun y => fderiv ℝ f y u) x) u) 0 := by
      have h_diff : DifferentiableAt ℝ (fun y => fderiv ℝ f y u) x := by
        fun_prop
      have h_limit : HasDerivAt (fun t : ℝ => (fderiv ℝ f (x + t • u)) u) ((fderiv ℝ (fun y => fderiv ℝ f y u) x) u) 0 := by
        have h_chain : HasDerivAt (fun t : ℝ => x + t • u) u 0 := by
          simpa using hasDerivAt_id ( 0 : ℝ ) |> HasDerivAt.smul_const <| u
        convert HasFDerivAt.comp_hasDerivAt _ _ h_chain using 1;
        congr! 1;
        rotate_left;
        exacts [ fun y => ( fderiv ℝ f y ) u, by simpa using h_diff.hasFDerivAt, funext fun t => rfl ];
      exact h_limit;
    simpa [ div_eq_inv_mul ] using h_limit.tendsto_slope_zero_right;
  have h_limit_ge : (fderiv ℝ (fun y => fderiv ℝ f y u) x) u ≥ m * ‖u‖ ^ 2 := by
    exact le_of_tendsto_of_tendsto tendsto_const_nhds h_limit ( Filter.eventually_of_mem self_mem_nhdsWithin fun t ht => h_forward t ht );
  have h_hessian : (fderiv ℝ (fun y => fderiv ℝ f y u) x) u = ⟪(fderiv ℝ (fun y => gradient f y) x) u, u⟫ := by
    convert HasFDerivAt.fderiv ( HasFDerivAt.inner ℝ ( hasFDerivAt_gradient h_smooth x ) ( hasFDerivAt_const _ _ ) ) |> congr_arg ( fun f => f u ) using 1;
    any_goals exact u;
    · simp +decide [ gradient ];
    · simp +decide [ hessian, fderivInnerCLM ];
  exact h_hessian ▸ h_limit_ge

/-
Backward direction: Hessian lower bound implies strong convexity.
    Use strongConvexOn_iff_convex to reduce to showing g(y) = f(y) - m/2*‖y‖² is convex.
    For any line restriction φ(t) = g(x + t*d), φ''(t) = ⟨H_f(x+td)d,d⟩ - m‖d‖² ≥ 0,
    so φ is convex, hence g is convex.
-/
set_option maxHeartbeats 800000 in
lemma hessian_lb_imp_strongConvexOn
    (h_smooth : ContDiff ℝ 2 f)
    (h_hess : ∀ x : E, ∀ u : E, m * ‖u‖ ^ 2 ≤ ⟪hessian f x u, u⟫) :
    StrongConvexOn univ m f := by
  have h_second_deriv_nonneg : ∀ x : E, ∀ d : E, ∀ t : ℝ, 0 ≤ deriv^[2] (fun t => f (x + t • d) - m / (2 : ℝ) * ‖x + t • d‖ ^ 2) t := by
    intro x d t
    have h_second_deriv_nonneg : deriv^[2] (fun t => f (x + t • d) - m / (2 : ℝ) * ‖x + t • d‖ ^ 2) t = ⟪hessian f (x + t • d) d, d⟫ - m * ‖d‖ ^ 2 := by
      have h_second_deriv_nonneg : deriv^[2] (fun t => f (x + t • d)) t = ⟪hessian f (x + t • d) d, d⟫ := by
        have h_second_deriv_nonneg : deriv^[2] (fun t => f (x + t • d)) t = deriv (fun t => ⟪gradient f (x + t • d), d⟫) t := by
          refine' Filter.EventuallyEq.deriv_eq _;
          filter_upwards [ ] with t;
          convert HasDerivAt.deriv ( _ ) using 1;
          convert HasFDerivAt.hasDerivAt ( HasFDerivAt.comp t ( h_smooth.contDiffAt.differentiableAt ( by norm_num ) |> DifferentiableAt.hasFDerivAt ) ( HasFDerivAt.add ( hasFDerivAt_const _ _ ) ( HasFDerivAt.smul ( hasFDerivAt_id t ) ( hasFDerivAt_const _ _ ) ) ) ) using 1;
          simp +decide [ gradient ];
        convert HasDerivAt.deriv ( _ ) using 1;
        have h_second_deriv_nonneg : HasDerivAt (fun t => gradient f (x + t • d)) (hessian f (x + t • d) d) t := by
          convert HasFDerivAt.hasDerivAt ( HasFDerivAt.comp t ( hasFDerivAt_gradient h_smooth _ ) ( HasFDerivAt.add ( hasFDerivAt_const _ _ ) ( HasFDerivAt.smul ( hasFDerivAt_id t ) ( hasFDerivAt_const _ _ ) ) ) ) using 1;
          simp +decide [ hessian ];
        convert h_second_deriv_nonneg.inner ℝ ( hasDerivAt_const _ _ ) using 1;
        simp +decide [ gradient ];
      convert congr_arg₂ ( · - · ) h_second_deriv_nonneg ( show deriv^[2] ( fun t => m / 2 * ‖x + t • d‖ ^ 2 ) t = m * ‖d‖ ^ 2 from ?_ ) using 1;
      · simp +zetaDelta at *;
        rw [ show deriv ( fun t => f ( x + t • d ) - m / 2 * ‖x + t • d‖ ^ 2 ) = fun t => deriv ( fun t => f ( x + t • d ) ) t - m / 2 * deriv ( fun t => ‖x + t • d‖ ^ 2 ) t from funext fun t => ?_ ];
        · convert deriv_sub _ _ using 1;
          · norm_num;
          · fun_prop;
          · norm_num [ norm_add_sq_real, norm_smul, mul_assoc, mul_comm, mul_left_comm ];
            norm_num [ mul_pow, inner_smul_right ];
            fun_prop;
        · convert deriv_sub _ _ using 1;
          · norm_num;
          · exact DifferentiableAt.comp t ( h_smooth.contDiffAt.differentiableAt ( by norm_num ) ) ( DifferentiableAt.add ( differentiableAt_const _ ) ( differentiableAt_id.smul_const _ ) );
          · exact DifferentiableAt.mul ( differentiableAt_const _ ) ( DifferentiableAt.norm_sq ℝ ( DifferentiableAt.add ( differentiableAt_const _ ) ( differentiableAt_id.smul_const _ ) ) );
      · norm_num [ norm_add_sq_real, norm_smul, mul_pow ] ; ring_nf;
        norm_num [ inner_smul_right, mul_assoc, mul_comm, mul_left_comm ] ; ring_nf;
        unfold deriv ; norm_num [ fderiv_apply_one_eq_deriv ] ; ring_nf ; norm_num;
        have h : deriv (fun x_1 ↦ deriv (fun x_2 ↦ ‖x‖^2 + x_2 * ⟪x, d⟫ * 2 + x_2^2 * ‖d‖^2) x_1) t
         = 2 * ‖d‖^2 := by
          simp (disch := fun_prop) [
            deriv_const, deriv_id''
          ]
          left
          have h_eta : (HMul.hMul (2 : ℝ) : ℝ → ℝ) = fun x => 2 * x := rfl
          rw [h_eta, deriv_const_mul _ (by fun_prop), deriv_id'']
          simp
        left
        rw [h]
        ring
    linarith [ h_hess ( x + t • d ) d ];
  have h_convex : ∀ x : E, ∀ d : E, ConvexOn ℝ Set.univ (fun t : ℝ => f (x + t • d) - m / (2 : ℝ) * ‖x + t • d‖ ^ 2) := by
    intro x d
    apply convexOn_of_deriv2_nonneg' (convex_univ);
    · refine' DifferentiableOn.sub _ _;
      · exact Differentiable.differentiableOn ( h_smooth.differentiable ( by norm_num ) |> Differentiable.comp <| Differentiable.add ( differentiable_const _ ) <| differentiable_id.smul_const _ );
      · exact Differentiable.differentiableOn ( by exact Differentiable.const_mul ( by exact Differentiable.norm_sq ℝ ( by exact Differentiable.add ( differentiable_const _ ) ( differentiable_id.smul_const _ ) ) ) _ );
    · -- Since $f$ is $C^2$, the composition $t \mapsto f(x + t \cdot d)$ is also $C^2$.
      have h_comp : ContDiff ℝ 2 (fun t : ℝ => f (x + t • d)) := by
        exact h_smooth.comp ( contDiff_const.add ( contDiff_id.smul contDiff_const ) );
      have h_comp : ContDiff ℝ 2 (fun t : ℝ => f (x + t • d) - m / (2 : ℝ) * ‖x + t • d‖ ^ 2) := by
        exact h_comp.sub ( ContDiff.mul ( contDiff_const ) ( ContDiff.norm_sq ℝ ( contDiff_const.add ( contDiff_id.smul contDiff_const ) ) ) );
      fun_prop;
    · exact fun t _ => h_second_deriv_nonneg x d t;
  convert strongConvexOn_iff_convex.mpr _ using 1;
  refine' ⟨ convex_univ, fun x _ y _ a b ha hb hab => _ ⟩;
  have := h_convex x ( y - x );
  have := this.2 ( Set.mem_univ 0 ) ( Set.mem_univ 1 ) ha hb hab; simp_all +decide [ ← eq_sub_iff_add_eq' ] ;
  convert this using 1 <;> simp +decide [ sub_smul, smul_sub ] ; abel_nf;
  exact Or.inl ( congr_arg Norm.norm ( by abel1 ) )

-- lemma 2.9: hessian characterization of strong convexity
lemma strongConvexOn_iff_hessian_lb
    (h_smooth : ContDiff ℝ 2 f) :
    StrongConvexOn univ m f ↔ ∀ x : E, ∀ u : E, m * ‖u‖ ^ 2 ≤ ⟪hessian f x u, u⟫ := by
  exact ⟨strongConvexOn_imp_hessian_lb h_smooth, hessian_lb_imp_strongConvexOn h_smooth⟩

end HessianStrongConvexity

section HessianSandwich
/-
Forward: L-smoothness implies Hessian upper bound.
-/
lemma lSmooth_imp_hessian_ub
    (h_smooth : ContDiff ℝ 2 f)
    (hL : LSmoothfn f L) :
    ∀ x : E, ∀ u : E, ⟪hessian f x u, u⟫ ≤ ↑L * ‖u‖ ^ 2 := by
  exact lSmoothOnUnivImpliesHessianQuadraticFormBound f L hL (fun x => hasFDerivAt_gradient h_smooth x)

/-
For a self-adjoint, PSD operator with ⟨Au,u⟩ ≤ c*‖u‖², we have ‖A‖ ≤ c.
    Proof: by polarization, ⟨Au,v⟩ = 1/4(⟨A(u+v),u+v⟩ - ⟨A(u-v),u-v⟩).
    So |⟨Au,v⟩| ≤ c/2*(‖u‖² + ‖v‖²). Setting v = (‖u‖/‖Au‖)*Au gives ‖Au‖ ≤ c*‖u‖.
-/
omit [CompleteSpace E] in
lemma opNorm_le_of_inner_le_of_symm_of_nonneg
    (A : E →L[ℝ] E) (c : ℝ) (hc : 0 ≤ c)
    (h_symm : ∀ u v : E, ⟪A u, v⟫ = ⟪u, A v⟫)
    (h_nonneg : ∀ u : E, 0 ≤ ⟪A u, u⟫)
    (h_ub : ∀ u : E, ⟪A u, u⟫ ≤ c * ‖u‖ ^ 2) :
    ‖A‖ ≤ c := by
  -- We show $\|Au\| \le c\|u\|$ for all $u$. This follows from the polarization identity.
  have h_polarization : ∀ u v : E, |⟪A u, v⟫| ≤ c / 2 * (‖u‖^2 + ‖v‖^2) := by
    -- Use the parallelogram law to relate the norm of the sum to the inner product.
    have h_parallelogram : ∀ u v : E, ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + 2 * ⟪u, v⟫ + ‖v‖ ^ 2 ∧ ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - 2 * ⟪u, v⟫ + ‖v‖ ^ 2 := by
      simp +decide [ @norm_add_sq ℝ, @norm_sub_sq ℝ ];
    intro u v
    have h_polarization : 4 * ⟪A u, v⟫ = ⟪A (u + v), u + v⟫ - ⟪A (u - v), u - v⟫ := by
      simp +decide [ h_symm, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right ] ; ring_nf;
      grind;
    have h_polarization : 4 * ⟪A u, v⟫ ≤ c * ‖u + v‖ ^ 2 ∧ -4 * ⟪A u, v⟫ ≤ c * ‖u - v‖ ^ 2 := by
      constructor <;> linarith [ h_ub ( u + v ), h_ub ( u - v ), h_nonneg ( u + v ), h_nonneg ( u - v ) ];
    exact abs_le.mpr ⟨ by nlinarith [ h_parallelogram u v ], by nlinarith [ h_parallelogram u v ] ⟩;
  refine' ContinuousLinearMap.opNorm_le_bound _ hc fun u => _;
  by_cases hu : u = 0 <;> specialize h_polarization u ( ( ‖u‖ / ‖A u‖ ) • A u ) <;> simp_all +decide [ norm_smul, inner_smul_right ];
  by_cases h : A u = 0 <;> simp_all;
  rw [ abs_of_nonneg ( by positivity ), div_mul_eq_mul_div, div_le_iff₀ ( by positivity ) ] at h_polarization;
  have := h_symm u ( A u ) ; simp_all +decide [ real_inner_comm ] ;
  cases abs_cases ( ⟪u, A ( A u )⟫ ) <;> nlinarith [ norm_pos_iff.mpr hu, norm_pos_iff.mpr h, mul_pos ( norm_pos_iff.mpr hu ) ( norm_pos_iff.mpr h ) ]

/-
The Hessian of a C² function is self-adjoint.
-/
lemma hessian_isSymmetric
    (h_smooth : ContDiff ℝ 2 f) (x : E) :
    ∀ u v : E, ⟪hessian f x u, v⟫ = ⟪u, hessian f x v⟫ := by
      have h_second_deriv_symm : ∀ u v : E, (fderiv ℝ (fderiv ℝ f) x) u v = (fderiv ℝ (fderiv ℝ f) x) v u := by
        apply_rules [ ContDiffAt.isSymmSndFDerivAt ];
        exacts [ h_smooth.contDiffAt, by norm_num [ minSmoothness ] ];
      -- By definition of the gradient, we know that
      have h_grad_def : ∀ u : E, gradient f u = (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f u) := by
        -- By definition of the gradient, we know that the gradient of f at u is the dual of the derivative of f at u.
        simp [gradient];
      unfold hessian;
      rw [ show ( fun y => gradient f y ) = ( InnerProductSpace.toDual ℝ E ).symm ∘ ( fderiv ℝ f ) from funext h_grad_def ];
      rw [ fderiv_comp ] <;> norm_num [ h_smooth.contDiffAt.differentiableAt ];
      · intro u v;
        rw [
          show ( fderiv ℝ ⇑( InnerProductSpace.toDual ℝ E ).symm ) ( fderiv ℝ f x )
            = ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
                : (StrongDual ℝ E) →L[ℝ] E) from ?_
        ]
        simp +decide;
        · erw [ InnerProductSpace.toDual_symm_apply, real_inner_comm, InnerProductSpace.toDual_symm_apply ]
          exact h_second_deriv_symm u v;
        · exact HasFDerivAt.fderiv ( by exact ( InnerProductSpace.toDual ℝ E ).symm.toContinuousLinearEquiv.hasFDerivAt );
      · exact ( InnerProductSpace.toDual ℝ E ).symm.differentiableAt;
      · fun_prop

/-
Backward: Hessian upper bound + convexity implies L-smoothness.
    We need ‖hessian f x‖ ≤ L for all x. Since f is convex, Hessian is PSD.
    Combined with ⟨Hu,u⟩ ≤ L‖u‖² and self-adjointness (from C²), we get ‖H‖ ≤ L.
-/
lemma hessian_ub_imp_lSmooth
    (h_smooth : ContDiff ℝ 2 f)
    (h_conv : ConvexOn ℝ univ f)
    (h_hess : ∀ x : E, ∀ u : E, ⟪hessian f x u, u⟫ ≤ ↑L * ‖u‖ ^ 2) :
    LSmoothfn f L := by
  apply_rules [ hessianBoundImpliesLSmoothOnUniv ];
  · exact fun x => hasFDerivAt_gradient h_smooth x;
  · intro x;
    apply_rules [ opNorm_le_of_inner_le_of_symm_of_nonneg ];
    · exact NNReal.coe_nonneg L;
    · exact fun u v => hessian_isSymmetric h_smooth x u v;
    · exact fun u => by simpa using strongConvexOn_imp_hessian_lb h_smooth ( strongConvexOn_zero.mpr h_conv ) x u

-- corollary 2.10: hessian sandwich characterization of L-smooth convex functions
lemma convexOn_lSmoothOn_iff_hessian_sandwich
    (h_smooth : ContDiff ℝ 2 f)
    (h_conv : ConvexOn ℝ univ f) :
    LSmoothfn f L ↔ ∀ x : E, ∀ u : E, ⟪hessian f x u, u⟫ ≤ ↑L * ‖u‖ ^ 2 := by
  exact ⟨lSmooth_imp_hessian_ub h_smooth, hessian_ub_imp_lSmooth h_smooth h_conv⟩

end HessianSandwich

section HessianPL

-- every strongly convex function is globally PL
theorem StrongConvexOn.globallyPL
    (h_conv : StrongConvexOn univ m f)
    (h_diff : Differentiable ℝ f)
    (hm : 0 < m) :
    GloballyPL f m hm := by
  intro x
  set g := gradient f x
  -- Lower bound: f(z) ≥ f(x) - 1/(2m) ‖g‖² for all z
  have h_lower := StrongConvexOn.quadratic_lower_bound_at_point h_conv (h_diff x) hm
  -- Apply infimum bound
  have h_inf_ge := le_ciInf h_lower
  -- From h_inf_ge, derive ‖g‖² ≥ 2m (f x - iInf f)
  show ‖g‖ ^ 2 ≥ 2 * m * (f x - iInf f)
  have h1 : 2 * m * (f x - 1 / (2 * m) * ‖g‖ ^ 2) ≤ 2 * m * iInf f := by nlinarith [h_inf_ge]
  have h2 : 2 * m * f x - ‖g‖ ^ 2 ≤ 2 * m * iInf f := by
    field_simp at h1 ⊢
    nlinarith [h1, hm]
  nlinarith [h2]

end HessianPL
