import lean4ml.Optimization.NecessaryCondition
import lean4ml.Optimization.GradientFlow
import lean4ml.Optimization.StronglyConvex

noncomputable section

open scoped Real RealInnerProductSpace NNReal
open Set Filter

namespace Lean4ML
namespace Optimization

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- If `f` is `C¹`, `L`-smooth, and strongly convex, then the global gradient flow
converges in function value to `iInf f`. -/
theorem gradientFlow_strongConvex_tendsto
    {f : E → ℝ} {x₀ : E} {μ : ℝ} {hμ : 0 < μ}
    (hC1 : ContDiff ℝ 1 f)
    (hSC : StrongConvexOn univ μ f)
    (φ : GradientFlowGlobal f x₀) :
    Filter.Tendsto (fun t => f (φ.trajectory t)) Filter.atTop (nhds (iInf f)) := by
  have hPL : GloballyPL f μ hμ :=
    StrongConvexOn.globallyPL (h_conv := hSC) (h_diff := hC1.differentiable one_ne_zero) hμ
  have hbdd : BddBelow (Set.range f) :=
    StrongConvexOn.bddBelow_range (f := f) (μ := μ) hμ hSC hC1
  exact gradientFlow_PL_tendsto (f := f) (μ := μ) (hμ := hμ) hC1 hPL hbdd φ

/-! ### Trajectory convergence for strongly convex gradient flow -/

/-- For a C¹, strongly convex function, the gradient flow trajectory converges to the
unique minimizer `x*` of `f`. -/
theorem gradientFlow_strongConvex_trajectory_tendsto
    {f : E → ℝ} {x₀ : E} {μ : ℝ} {hμ : 0 < μ}
    (hC1 : ContDiff ℝ 1 f)
    (hSC : StrongConvexOn univ μ f)
    (φ : GradientFlowGlobal f x₀) :
    ∃ xstar : E, IsMinOn f univ xstar ∧
      (∀ y : E, IsMinOn f univ y → y = xstar) ∧
      Filter.Tendsto φ.trajectory Filter.atTop (nhds xstar) := by
  -- By `StrongConvexOn.exists_minimizer hμ hC1 hSC`, there exists a unique minimizer `xstar`.
  obtain ⟨xstar, hxstar⟩ : ∃ xstar : E, IsMinOn f univ xstar := by
    exact StrongConvexOn.exists_minimizer hμ hC1 hSC
  generalize_proofs at *; (
  refine' ⟨ xstar, hxstar, _, _ ⟩ <;> simp_all +decide [ IsMinOn, IsMinFilter ];
  · intro y hy; have := hSC.2; simp_all +decide ; (
    contrapose! this;
    refine' ⟨ y, xstar, 1 / 2, 1 / 2, _, _, _, _ ⟩ <;> ring_nf <;> norm_num [ hμ ];
    exact lt_add_of_le_of_pos ( by linarith [ hy ( ( 1 / 2 : ℝ ) • y + ( 1 / 2 : ℝ ) • xstar ), hxstar ( ( 1 / 2 : ℝ ) • y + ( 1 / 2 : ℝ ) • xstar ) ] ) ( by exact mul_pos ( mul_pos hμ ( sq_pos_of_pos ( norm_pos_iff.mpr ( sub_ne_zero.mpr this ) ) ) ) ( by norm_num ) ));
  · -- By `gradientFlow_strongConvex_tendsto`, we have `Filter.Tendsto (fun t => f (φ.trajectory t)) Filter.atTop (nhds (iInf f))`.
    have h_tendsto : Filter.Tendsto (fun t => f (φ.trajectory t)) Filter.atTop (nhds (iInf f)) := by
      convert gradientFlow_strongConvex_tendsto hC1 hSC φ using 1;
      exact hμ
    generalize_proofs at *; (
    -- By `StrongConvexOn.quadratic_growth_at_minimizer`, we have `μ / 2 * ‖φ(t) - xstar‖ ^ 2 ≤ f(φ(t)) - f(xstar)`.
    have h_quad_growth : ∀ t ≥ 0, μ / 2 * ‖φ.trajectory t - xstar‖ ^ 2 ≤ f (φ.trajectory t) - f xstar := by
      exact fun t ht => StrongConvexOn.quadratic_growth_at_minimizer hSC hC1 (fun x _ => hxstar x) (φ.trajectory t)
        |> le_trans <| by simp +decide ;
    generalize_proofs at *; (
    -- Since $f(xstar) = iInf f$, we have $f(φ(t)) - f(xstar) \to 0$ as $t \to \infty$.
    have h_diff_zero : Filter.Tendsto (fun t => f (φ.trajectory t) - f xstar) Filter.atTop (nhds 0) := by
      convert h_tendsto.sub_const ( f xstar ) using 2 ; ring!; (
      rw [ eq_comm, sub_eq_zero ] ; exact le_antisymm ( csInf_le ⟨ f xstar, Set.forall_mem_range.2 hxstar ⟩ ⟨ xstar, rfl ⟩ ) ( le_csInf ⟨ f xstar, Set.mem_range_self xstar ⟩ ( Set.forall_mem_range.2 hxstar ) ) ;)
    generalize_proofs at *; (
    -- Since $μ / 2 * ‖φ(t) - xstar‖ ^ 2 ≤ f(φ(t)) - f(xstar)$ and $f(φ(t)) - f(xstar) \to 0$, we have $‖φ(t) - xstar‖ ^ 2 \to 0$.
    have h_norm_sq_zero : Filter.Tendsto (fun t => ‖φ.trajectory t - xstar‖ ^ 2) Filter.atTop (nhds 0) := by
      have h_norm_sq_zero : Filter.Tendsto (fun t => μ / 2 * ‖φ.trajectory t - xstar‖ ^ 2) Filter.atTop (nhds 0) := by
        exact squeeze_zero_norm' ( Filter.eventually_atTop.mpr ⟨ 0, fun t ht => by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact h_quad_growth t ht ⟩ ) h_diff_zero
      generalize_proofs at *; (
      convert h_norm_sq_zero.const_mul ( 2 / μ ) using 2 <;> ring_nf ; norm_num [ hμ.ne' ])
    generalize_proofs at *; (
    exact tendsto_iff_norm_sub_tendsto_zero.mpr ( by simpa [ Real.sqrt_sq ( norm_nonneg _ ) ] using h_norm_sq_zero.sqrt ))))))

end Optimization
end Lean4ML
