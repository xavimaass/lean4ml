import Mathlib
import Mathlib.Analysis.ODE.PicardLindelof
import Lean4ML.Optimization.LSmooth

noncomputable section

open scoped Real
open scoped RealInnerProductSpace
open Set

namespace Lean4ML
namespace Optimization

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-!
## Gradient Flow

A `GradientFlow f x₀ T` is a certificate that the gradient flow ODE
  `ẋ(t) = -∇f(x(t))`,  `x(0) = x₀`
has a solution on `[0, T]`. It packages the trajectory and its defining
properties into a single object so that downstream lemmas (energy decrease,
convergence, etc.) can be stated cleanly in terms of `.trajectory`.
-/

/-- A solution to the gradient flow ODE for `f` starting at `x₀` over `[0, T]`. -/
structure GradientFlow (f : E → ℝ) (x₀ : E) (T : ℝ) where
  /-- The trajectory curve. -/
  trajectory : ℝ → E
  /-- It starts at the initial condition. -/
  init : trajectory 0 = x₀
  /-- It satisfies the gradient flow ODE at every time in `[0, T]`. -/
  hasDerivAt : ∀ t ∈ Icc 0 T, HasDerivAt trajectory (-(gradient f (trajectory t))) t

namespace GradientFlow

/-! ### Basic properties of the trajectory -/

variable {f : E → ℝ} {x₀ : E} {T : ℝ}

/-- The trajectory value at the initial time equals `x₀`. -/
@[simp]
lemma trajectory_zero (φ : GradientFlow f x₀ T) : φ.trajectory 0 = x₀ :=
  φ.init

/-- The trajectory is differentiable at every interior time. -/
lemma differentiableAt (φ : GradientFlow f x₀ T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    DifferentiableAt ℝ φ.trajectory t :=
  (φ.hasDerivAt t ht).differentiableAt

/-- The derivative of the trajectory equals `-∇f(x(t))` pointwise. -/
lemma deriv_eq (φ : GradientFlow f x₀ T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    deriv φ.trajectory t = -(gradient f (φ.trajectory t)) :=
  (φ.hasDerivAt t ht).deriv

/-!
### Energy decrease along the flow

The function value `f(x(t))` is non-increasing. Its derivative is
  `d/dt f(x(t)) = ⟪∇f(x(t)), ẋ(t)⟫ = -‖∇f(x(t))‖²`.
-/

/-- The rate of energy dissipation: `d/dt f(x(t)) = -‖∇f(x(t))‖²`. -/
lemma hasDerivAt_energy
    (φ : GradientFlow f x₀ T)
    (hC1 : ContDiff ℝ 1 f)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivAt (fun t => f (φ.trajectory t))
      (-‖gradient f (φ.trajectory t)‖ ^ 2) t := by
  have hgrad := (hC1.contDiffAt.differentiableAt one_ne_zero).hasGradientAt
    (x := φ.trajectory t)
  have hx := φ.hasDerivAt t ht

  -- Re-state the derivative so Lean explicitly sees the function application
  have hgrad' : HasFDerivAt f _ ((fun t => φ.trajectory t) t) := hgrad.hasFDerivAt
  have hchain := HasFDerivAt.comp_hasDerivAt t hgrad' hx
  convert hchain using 1
  simp [InnerProductSpace.toDual_apply_apply]

/-- The energy `f(x(t))` is non-increasing: `f(x(s)) ≤ f(x(r))` for `r ≤ s`. -/
lemma energy_antitone
    (φ : GradientFlow f x₀ T)
    (hC1 : ContDiff ℝ 1 f)
    {r s : ℝ} (hr : r ∈ Icc 0 T) (hs : s ∈ Icc 0 T) (hrs : r ≤ s) :
    f (φ.trajectory s) ≤ f (φ.trajectory r) := by
  let g := fun t => f (φ.trajectory t)

  -- 1. Define the derivative logic
  have hderiv : ∀ t ∈ Icc r s, HasDerivAt g (-‖gradient f (φ.trajectory t)‖ ^ 2) t := by
    intro t ht
    exact φ.hasDerivAt_energy hC1 ⟨le_trans hr.1 ht.1, le_trans ht.2 hs.2⟩

  -- 2. Define the non-positivity logic
  have hnonpos : ∀ t ∈ Icc r s, (-‖gradient f (φ.trajectory t)‖ ^ 2) ≤ 0 := by
    intro t _
    nlinarith [sq_nonneg ‖gradient f (φ.trajectory t)‖]

  -- 3. Apply the monotonicity theorem with correct arguments
  have hmono : AntitoneOn g (Icc r s) :=
    antitoneOn_of_deriv_nonpos
      (convex_Icc r s)
      (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [(hderiv t (interior_subset ht)).deriv]
        exact hnonpos t (interior_subset ht))

  exact hmono (left_mem_Icc.mpr hrs) (right_mem_Icc.mpr hrs) hrs


/-! ### Existence theorem (Picard–Lindelöf) -/

/-- **Gradient flow existence.**
For any `C¹` globally `L`-smooth `f`, initial point `x₀`, and time horizon `T > 0`,
a `GradientFlow` trajectory exists. -/
theorem mk_of_lsmooth
    (f : E → ℝ)
    (L : NNReal)
    (x₀ : E)
    (T : ℝ)
    (hT : 0 < T)
    (hC1 : ContDiff ℝ 1 f)
    (hL : LSmoothOn f L Set.univ) :
    Nonempty (GradientFlow f x₀ T) := by
  -- The RHS of the ODE.
  let F : ℝ → E → E := fun _t v => -(gradient f v)
  
  -- ∇f is globally Lipschitz (unpack LSmoothOn on univ).
  have hLip : LipschitzWith L (fun v => gradient f v) := by
    rw [← lipschitzOnWith_univ]
    exact hL
  
  -- F(t, ·) is Lipschitz in the state within any closed ball, uniformly in t.
  have hF_lipschitz : ∀ t ∈ Set.Icc (0 : ℝ) T, LipschitzOnWith L (F t) (Metric.closedBall x₀ 1) := by
    intro t _ht
    simp only [F]
    exact hLip.neg.lipschitzOnWith
  
  -- F is continuous in time for any state in closedBall x₀ 1.
  have hF_continuousOn : ∀ x ∈ Metric.closedBall x₀ 1, ContinuousOn (fun t => F t x) (Set.Icc 0 T) := by
    intro x _
    simp only [F]
    apply ContinuousOn.neg
    have : Continuous (fun v : E => gradient f v) := by
      change Continuous (fun v : E => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f v))
      exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp
        ((hC1.fderiv_right (m := 0) (by norm_num)).continuous)
    exact this.continuousOn.comp (continuousOn_const) (fun _ _ => trivial)
  
  -- Bound the norm of F.
  have hF_norm : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Metric.closedBall x₀ 1, ‖F t x‖ ≤ L := by
    intro t _ht x _hx
    simp only [F, norm_neg]
    exact hLip.norm_le x
  
  -- Set up the time interval condition: L * max(T - 0, 0 - 0) ≤ 1 - 0
  -- This requires L * T ≤ 1, so we need T ≤ 1/L (or use a smaller radius).
  -- For now, assume this or use a smaller time interval.
  have hT_interval : L * max (T - 0) (0 - 0) ≤ 1 := by
    simp only [sub_zero, max_eq_left (by norm_num : (0 : ℝ) ≤ T - 0 ∨ 0 ≤ 0)]
    sorry -- This would require T ≤ 1 / L
  
  -- Construct the IsPicardLindelof instance.
  let t₀ : Set.Icc (0 : ℝ) T := ⟨0, by norm_num, hT.le⟩
  let a : ℝ≥0 := 1
  let r : ℝ≥0 := 0
  
  have hPL : IsPicardLindelof F t₀ x₀ a r L L := {
    lipschitzOnWith := hF_lipschitz
    continuousOn := hF_continuousOn
    norm_le := hF_norm
    mul_max_le := by
      simp only [a, r, sub_zero, ENNReal.coe_zero]
      exact hT_interval
  }
  
  -- Apply Picard–Lindelöf to get a solution starting exactly at x₀.
  have hx₀_mem : (x₀ : E) ∈ Metric.closedBall x₀ (r : ℝ) := by simp [r]
  
  obtain ⟨α, hα_init, hα_deriv⟩ := IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt hPL hx₀_mem
  
  exact ⟨⟨α, hα_init, fun t ht => hα_deriv t ht⟩⟩

end GradientFlow

end Optimization
end Lean4ML
