import Mathlib
import lean4ml.Optimization.LSmooth

noncomputable section

open scoped Real RealInnerProductSpace NNReal
open Set Filter

namespace Lean4ML
namespace Optimization

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-!
## Gradient Flow

A `GradientFlow f x₀ T` is a certificate that the gradient flow ODE
  `ẋ(t) = -∇f(x(t))`,  `x(0) = x₀`
has a solution on `[0, T]`.
-/

/-- A solution to the gradient flow ODE for `f` starting at `x₀` over `[0, T]`. -/
structure GradientFlow (f : E → ℝ) (x₀ : E) (T : ℝ) where
  /-- The flow trajectory. -/
  trajectory : ℝ → E
  /-- The initial condition `trajectory 0 = x₀`. -/
  init : trajectory 0 = x₀
  /-- The derivative equation `ẋ(t) = -∇f(x(t))`. -/
  hasDerivAt : ∀ t ∈ Icc 0 T, HasDerivAt trajectory (-(gradient f (trajectory t))) t

namespace GradientFlow

variable {f : E → ℝ} {x₀ : E} {T : ℝ}

@[simp]
lemma trajectory_zero (φ : GradientFlow f x₀ T) : φ.trajectory 0 = x₀ := φ.init

lemma differentiableAt (φ : GradientFlow f x₀ T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    DifferentiableAt ℝ φ.trajectory t :=
  (φ.hasDerivAt t ht).differentiableAt

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
  have h_chain : HasDerivAt (fun t => f (φ.trajectory t)) (inner ℝ (gradient f (φ.trajectory t)) (deriv φ.trajectory t)) t := by
    have h_chain : HasDerivAt (fun t => f (φ.trajectory t)) (fderiv ℝ f (φ.trajectory t) (deriv φ.trajectory t)) t := by
      convert HasFDerivAt.comp_hasDerivAt _ _ _ using 1;
      · exact DifferentiableAt.hasFDerivAt ( hC1.contDiffAt.differentiableAt ( by norm_num ) );
      · exact hasDerivAt_deriv_iff.mpr ( φ.differentiableAt ht );
    convert h_chain using 1;
    simp +decide [ gradient ];
  convert h_chain using 1;
  rw [ φ.deriv_eq ht, inner_neg_right, real_inner_self_eq_norm_sq ]

/-- The energy `f(x(t))` is non-increasing: `f(x(s)) ≤ f(x(r))` for `r ≤ s`. -/
lemma energy_antitone
    (φ : GradientFlow f x₀ T)
    (hC1 : ContDiff ℝ 1 f)
    {r s : ℝ} (hr : r ∈ Icc 0 T) (hs : s ∈ Icc 0 T) (hrs : r ≤ s) :
    f (φ.trajectory s) ≤ f (φ.trajectory r) := by
  by_contra h;
  -- Apply the mean value theorem to the interval [r, s].
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo r s, deriv (fun t => f (φ.trajectory t)) c = (f (φ.trajectory s) - f (φ.trajectory r)) / (s - r) := by
    apply_rules [ exists_deriv_eq_slope ];
    · exact hrs.lt_of_ne ( by rintro rfl; linarith );
    · refine' hC1.continuous.comp_continuousOn _;
      exact continuousOn_of_forall_continuousAt fun t ht => DifferentiableAt.continuousAt ( φ.differentiableAt ⟨ by linarith [ ht.1, hr.1 ], by linarith [ ht.2, hs.2 ] ⟩ );
    · exact fun t ht => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.comp t ( hC1.contDiffAt.differentiableAt ( by norm_num ) ) ( φ.differentiableAt ( by constructor <;> linarith [ ht.1, ht.2, hr.1, hr.2, hs.1, hs.2 ] ) ) );
  rw [ eq_div_iff ] at hc <;> try linarith [ hc.1.1, hc.1.2 ];
  rw [ show deriv ( fun t => f ( φ.trajectory t ) ) c = -‖gradient f ( φ.trajectory c )‖ ^ 2 by exact HasDerivAt.deriv ( φ.hasDerivAt_energy hC1 <| by constructor <;> linarith [ hc.1.1, hc.1.2, hr.1, hr.2, hs.1, hs.2 ] ) ] at hc ; nlinarith [ hc.1.1, hc.1.2, hr.1, hr.2, hs.1, hs.2, norm_nonneg ( gradient f ( φ.trajectory c ) ) ]

end GradientFlow

/-! ### Extension (chaining) lemma -/

/-- Piecewise trajectory: follow `φ₁` up to time `T`, then `φ₂` (shifted). -/
def piecewiseTrajectory (φ₁ : ℝ → E) (φ₂ : ℝ → E) (T : ℝ) : ℝ → E :=
  fun t => if t ≤ T then φ₁ t else φ₂ (t - T)

omit [CompleteSpace E] in
private lemma hasDerivAt_shifted {g : ℝ → E} {v : E} {t c : ℝ}
    (hg : HasDerivAt g v (t - c)) :
    HasDerivAt (fun s => g (s - c)) v t := by
  have h1 : HasDerivAt (fun s : ℝ => s - c) 1 t := by
    have := (hasDerivAt_id t).sub (hasDerivAt_const t c)
    simp [sub_zero] at this; exact this
  convert HasDerivAt.scomp t hg h1 using 1; simp

/-- Extension lemma: chain two gradient flows into one on `[0, T + δ]`. -/
def gradientFlow_extend
    {f : E → ℝ} {x₀ : E} {T δ : ℝ}
    (φ : GradientFlow f x₀ T)
    (ψ : GradientFlow f (φ.trajectory T) δ)
    (hT : 0 ≤ T) (hδ : 0 ≤ δ) :
    GradientFlow f x₀ (T + δ) where
  trajectory := piecewiseTrajectory φ.trajectory ψ.trajectory T
  init := by unfold piecewiseTrajectory; simp [hT, φ.init]
  hasDerivAt := by
    intro t ⟨h0t, htTd⟩
    -- Abbreviations for the piecewise function
    set Φ := piecewiseTrajectory φ.trajectory ψ.trajectory T
    -- Key facts about the piecewise definition
    have pw_le : ∀ s, s ≤ T → Φ s = φ.trajectory s := fun s hs =>
      show (if s ≤ T then _ else _) = _ from if_pos hs
    have pw_gt : ∀ s, T < s → Φ s = ψ.trajectory (s - T) := fun s hs =>
      show (if s ≤ T then _ else _) = _ from if_neg (not_le.mpr hs)
    rcases lt_trichotomy t T with htT | htT | htT
    · -- Case t < T: Φ agrees with φ.trajectory near t
      have h_val : Φ t = φ.trajectory t := pw_le t (le_of_lt htT)
      rw [h_val]
      have h_eq : Φ =ᶠ[nhds t] φ.trajectory :=
        eventually_of_mem (Iio_mem_nhds htT) fun s hs => pw_le s (le_of_lt hs)
      exact (φ.hasDerivAt t ⟨h0t, le_of_lt htT⟩).congr_of_eventuallyEq h_eq
    · -- Case t = T: combine left and right derivatives via union
      have h_val : Φ T = φ.trajectory T := pw_le T le_rfl
      rw [htT, h_val, ← hasDerivWithinAt_univ, ← Iic_union_Ici]
      apply HasDerivWithinAt.union
      · -- Left derivative from φ (on Iic T)
        exact (φ.hasDerivAt T ⟨hT, le_refl T⟩).hasDerivWithinAt.congr
          (fun s hs => pw_le s hs) (pw_le T le_rfl)
      · -- Right derivative from ψ (on Ici T)
        have hψ0 := ψ.hasDerivAt 0 ⟨le_refl 0, hδ⟩
        rw [ψ.init] at hψ0
        have hd_shift : HasDerivAt (fun s => ψ.trajectory (s - T))
            (-(gradient f (φ.trajectory T))) T :=
          hasDerivAt_shifted (by simp; exact hψ0)
        refine hd_shift.hasDerivWithinAt.congr (fun s (hs : T ≤ s) => ?_) ?_
        · -- Φ s = ψ.trajectory(s - T) for s ∈ Ici T
          rcases eq_or_lt_of_le hs with rfl | hlt
          · -- s = T
            rw [pw_le T le_rfl, sub_self, ψ.init]
          · -- s > T
            exact pw_gt s hlt
        · -- Φ T = ψ.trajectory(T - T) = ψ.trajectory 0 = φ.trajectory T
          rw [pw_le T le_rfl, sub_self, ψ.init]
    · -- Case t > T: Φ agrees with ψ.trajectory(· - T) near t
      have h_val : Φ t = ψ.trajectory (t - T) := pw_gt t htT
      rw [h_val]
      have h_eq : Φ =ᶠ[nhds t] (fun s => ψ.trajectory (s - T)) :=
        eventually_of_mem (Ioi_mem_nhds htT) fun s hs => pw_gt s hs
      have ht_in : t - T ∈ Icc 0 δ := ⟨by linarith, by linarith⟩
      exact (hasDerivAt_shifted (ψ.hasDerivAt (t - T) ht_in)).congr_of_eventuallyEq h_eq

/-! ### Helper lemmas -/

lemma gradient_continuous {f : E → ℝ} (hC1 : ContDiff ℝ 1 f) :
    Continuous (fun x : E => gradient f x) := by
  unfold gradient; fun_prop

lemma gradient_norm_bound {f : E → ℝ} {L : ℝ≥0}
    (hLip : LipschitzWith L (fun x => gradient f x)) (x y : E) :
    ‖gradient f x‖ ≤ ‖gradient f y‖ + L * ‖x - y‖ := by
  have h := hLip.dist_le_mul x y
  rw [dist_eq_norm, dist_eq_norm] at h
  linarith [norm_sub_norm_le (gradient f x) (gradient f y)]

/-! ### Local existence via Picard-Lindelöf -/

/-
**Local gradient flow existence.**
For any `C¹` function with `L`-Lipschitz gradient, a gradient flow
exists on some positive time interval `[0, δ]` starting from any point.
-/
theorem gradientFlow_local_existence
    (f : E → ℝ) (L : ℝ≥0) (x₀ : E)
  (_hC1 : ContDiff ℝ 1 f)
    (hL : LSmoothfn f L) :
    ∃ δ > (0 : ℝ), Nonempty (GradientFlow f x₀ δ) := by
  -- Apply the Picard-Lindelöf theorem to the interval [-ε, 2ε] with ε = 1/(4*(L:ℝ)+4), t₀ = 0, ball radius a_val = ‖gradient f x₀‖ + 1, r = 0, norm bound M_val = ‖gradient f x₀‖ + L * a_val, and Lipschitz constant K = L.
  set ε : ℝ := 1 / (4 * (L : ℝ) + 4)
  have hε_pos : 0 < ε := by
    positivity;
  -- Set up the constants for the Picard-Lindelöf theorem.
  set a_val : ℝ := ‖gradient f x₀‖ + 1
  set M_val : ℝ := ‖gradient f x₀‖ + L * a_val
  set K_val : ℝ≥0 := L
  have h_mul_max_le : M_val * max (2 * ε) ε ≤ a_val := by
    rw [ max_eq_left ( by linarith ) ];
    simp +zetaDelta at *;
    nlinarith [ inv_mul_cancel_left₀ hε_pos.ne' ( ‖gradient f x₀‖ ), inv_mul_cancel₀ hε_pos.ne', norm_nonneg ( gradient f x₀ ), show ( L : ℝ ) ≥ 0 by positivity ];
  -- Apply the Picard-Lindelöf theorem to obtain the existence of a solution on the interval [-ε, 2ε].
  obtain ⟨α, hα_init, hα_deriv⟩ : ∃ α : ℝ → E, α 0 = x₀ ∧ ∀ t ∈ Set.Icc (-ε) (2 * ε), HasDerivWithinAt α (-(gradient f (α t))) (Set.Icc (-ε) (2 * ε)) t := by
    convert IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀ ( show IsPicardLindelof ( fun t x => -gradient f x ) 0 x₀ ( ⟨ a_val, by positivity ⟩ : ℝ≥0 ) 0 ⟨ M_val, by positivity ⟩ ⟨ K_val, by positivity ⟩ from ?_ ) using 1;
    rotate_left;
    exact -ε;
    exact 2 * ε;
    exact ⟨ 0, ⟨ by linarith, by linarith ⟩ ⟩;
    · constructor;
      · intro t ht;
        exact hL.neg.lipschitzOnWith;
      · exact fun _ _ => continuousOn_const;
      · simp +zetaDelta at *;
        exact fun t ht₁ ht₂ x hx => by
          have hx' : ‖x - x₀‖ ≤ ‖gradient f x₀‖ + 1 := by
            have hx'' : dist x x₀ ≤ ‖gradient f x₀‖ + 1 := by
              simpa [coe_nndist] using hx
            simpa [dist_eq_norm] using hx''
          have hmul : (L : ℝ) * ‖x - x₀‖ ≤ (L : ℝ) * (‖gradient f x₀‖ + 1) := by
            exact mul_le_mul_of_nonneg_left hx' (show (0 : ℝ) ≤ L by positivity)
          calc
            ‖gradient f x‖ ≤ ‖gradient f x₀‖ + (L : ℝ) * ‖x - x₀‖ := gradient_norm_bound hL x x₀
            _ ≤ ‖gradient f x₀‖ + (L : ℝ) * (‖gradient f x₀‖ + 1) := by
              simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hmul ‖gradient f x₀‖
            _ = M_val := by rfl
      · aesop;
    · rfl;
  refine' ⟨ ε, hε_pos, ⟨ ⟨ α, hα_init, fun t ht => _ ⟩ ⟩ ⟩;
  exact HasDerivWithinAt.hasDerivAt ( hα_deriv t ⟨ by linarith [ ht.1 ], by linarith [ ht.2 ] ⟩ ) ( Icc_mem_nhds ( by linarith [ ht.1 ] ) ( by linarith [ ht.2 ] ) )

/-! ### Restricting a gradient flow to a shorter interval -/

/-- A gradient flow on `[0, S]` restricts to `[0, T]` for any `T ≤ S`. -/
def gradientFlow_restrict
    {f : E → ℝ} {x₀ : E} {S : ℝ}
    (φ : GradientFlow f x₀ S) {T : ℝ} (hTS : T ≤ S) :
    GradientFlow f x₀ T where
  trajectory := φ.trajectory
  init := φ.init
  hasDerivAt := fun t ht => φ.hasDerivAt t ⟨ht.1, le_trans ht.2 hTS⟩

/-- Extending a gradient flow by one local step. -/
lemma gradientFlow_extend_step
    (f : E → ℝ) (L : ℝ≥0) (x₀ : E) (S : ℝ) (hS : 0 ≤ S)
    (hC1 : ContDiff ℝ 1 f) (hL : LSmoothfn f L)
    (φ : GradientFlow f x₀ S) :
    ∃ δ > (0 : ℝ), Nonempty (GradientFlow f x₀ (S + δ)) := by
  obtain ⟨δ, hδ_pos, ⟨ψ⟩⟩ := gradientFlow_local_existence f L (φ.trajectory S) hC1 hL
  exact ⟨δ, hδ_pos, ⟨gradientFlow_extend φ ψ hS (le_of_lt hδ_pos)⟩⟩

/-
A concrete gradient flow on `[0, 1/(4L+4)]` starting from any point.
-/
/-- A concrete local gradient flow on `[0, 1/(4L+4)]` starting from any point. -/
def mk_local_flow
    (f : E → ℝ) (L : ℝ≥0) (x₀ : E)
  (_hC1 : ContDiff ℝ 1 f) (hL : LSmoothfn f L) :
    GradientFlow f x₀ (1 / (4 * (L : ℝ) + 4)) := by
  have _ : ContDiff ℝ 1 f := _hC1
  -- Same construction as gradientFlow_local_existence
  set ε : ℝ := 1 / (4 * (L : ℝ) + 4) with hε_def
  have hε_pos : 0 < ε := by positivity
  set a_val : ℝ := ‖gradient f x₀‖ + 1
  set M_val : ℝ := ‖gradient f x₀‖ + L * a_val
  have h_mul_max_le : M_val * max (2 * ε) ε ≤ a_val := by
    rw [max_eq_left (by linarith)]
    simp +zetaDelta at *
    nlinarith [inv_mul_cancel_left₀ hε_pos.ne' (‖gradient f x₀‖), inv_mul_cancel₀ hε_pos.ne',
              norm_nonneg (gradient f x₀), show (L : ℝ) ≥ 0 by positivity]
  -- Build IsPicardLindelof instance on [-ε, 2ε]
  set t₀_sub : ↑(Set.Icc (-ε) (2 * ε)) := ⟨0, by constructor <;> linarith⟩
  have hPL : IsPicardLindelof (fun (_t : ℝ) (x : E) => -gradient f x)
      t₀_sub x₀ ⟨a_val, by positivity⟩ 0 ⟨M_val, by positivity⟩ L := by
    constructor
    · intro t _ht; exact hL.neg.lipschitzOnWith
    · exact fun _ _ => continuousOn_const
    · intro t _ht x hx
      simp only [norm_neg]
      have hx' : ‖x - x₀‖ ≤ a_val := by
        rwa [Metric.mem_closedBall, dist_eq_norm] at hx
      calc ‖gradient f x‖ ≤ ‖gradient f x₀‖ + ↑L * ‖x - x₀‖ := gradient_norm_bound hL x x₀
        _ ≤ ‖gradient f x₀‖ + ↑L * a_val := by nlinarith [show (↑L : ℝ) ≥ 0 by positivity]
        _ = M_val := rfl
    · show M_val * max (2 * ε - 0) (0 - -ε) ≤ a_val - 0
      simp only [sub_zero, sub_neg_eq_add, zero_add]
      exact h_mul_max_le
  choose α hα_init hα_deriv using hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨α, hα_init, fun t ht => ?_⟩
  exact HasDerivWithinAt.hasDerivAt
    (hα_deriv t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))

/-- **Uniform local gradient flow existence.**
The step size `δ = 1/(4L+4)` works for ANY starting point. -/
theorem gradientFlow_local_existence_uniform
    (f : E → ℝ) (L : ℝ≥0)
    (hC1 : ContDiff ℝ 1 f) (hL : LSmoothfn f L) :
    ∃ δ > (0 : ℝ), ∀ x₀ : E, Nonempty (GradientFlow f x₀ δ) :=
  ⟨1 / (4 * (L : ℝ) + 4), by positivity, fun x₀ => ⟨mk_local_flow f L x₀ hC1 hL⟩⟩

/-
By Nat.rec, build a gradient flow on `[0, n * δ]`.
-/
lemma gradientFlow_iterate
    {f : E → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (h_local : ∀ x₀ : E, Nonempty (GradientFlow f x₀ δ))
    (x₀ : E) (n : ℕ) :
    Nonempty (GradientFlow f x₀ (n * δ)) := by
  induction' n with n ih generalizing x₀ <;> simp_all +decide [ add_mul ];
  · obtain ⟨ φ ⟩ := h_local x₀;
    exact ⟨ gradientFlow_restrict φ ( by linarith ) ⟩;
  · obtain ⟨ φ ⟩ := ih x₀
    obtain ⟨ ψ ⟩ := h_local ( φ.trajectory ( n * δ ) )
    exact ⟨ gradientFlow_extend φ ψ ( by positivity ) ( by positivity ) ⟩

/-! ### General existence theorem -/

/-- **Gradient flow existence.**
For any `C¹` globally `L`-smooth `f`, initial point `x₀`, and time horizon `T > 0`,
a `GradientFlow` trajectory exists on `[0, T]`. -/
theorem gradientFlow_existence
  (f : E → ℝ) (L : ℝ≥0) (x₀ : E) (T : ℝ) (_hT : 0 < T)
    (_hC1 : ContDiff ℝ 1 f) (hL : LSmoothfn f L) :
    Nonempty (GradientFlow f x₀ T) := by
  obtain ⟨δ, hδ_pos, h_local⟩ := gradientFlow_local_existence_uniform f L _hC1 hL
  have h_iter := gradientFlow_iterate hδ_pos h_local x₀ (⌈T / δ⌉₊ + 1)
  obtain ⟨φ⟩ := h_iter
  exact ⟨gradientFlow_restrict φ (by
    have h1 : T / δ ≤ ↑(⌈T / δ⌉₊ + 1) := by
      calc T / δ ≤ ↑⌈T / δ⌉₊ := Nat.le_ceil _
        _ ≤ ↑(⌈T / δ⌉₊ + 1) := by exact_mod_cast Nat.le_succ _
    have h2 : T ≤ ↑(⌈T / δ⌉₊ + 1) * δ := by
      have := (div_le_iff₀ hδ_pos).mp h1
      linarith
    linarith)⟩

/-! ### Unbounded time gradient flow -/

/-- A global solution to the gradient flow ODE defined for all `t ≥ 0`. -/
structure GradientFlowGlobal (f : E → ℝ) (x₀ : E) where
  /-- The global trajectory. -/
  trajectory : ℝ → E
  /-- The initial condition `trajectory 0 = x₀`. -/
  init : trajectory 0 = x₀
  /-- The derivative equation for all nonnegative times. -/
  hasDerivAt : ∀ t : ℝ, 0 ≤ t → HasDerivAt trajectory (-(gradient f (trajectory t))) t

/-- A global gradient flow restricts to a bounded one. -/
def GradientFlowGlobal.restrict {f : E → ℝ} {x₀ : E}
  (φ : GradientFlowGlobal f x₀) (T : ℝ) (_hT : 0 ≤ T) : GradientFlow f x₀ T where
  trajectory := φ.trajectory
  init := φ.init
  hasDerivAt := fun t ht => by
    have _ : 0 ≤ T := _hT
    exact φ.hasDerivAt t ht.1

/-
Two gradient flows from the same initial point have the same trajectory
    (ODE uniqueness from Gronwall).
-/
lemma gradientFlow_unique
  {f : E → ℝ} {x₀ : E} {L : ℝ≥0} {T : ℝ} (_hT : 0 ≤ T)
    (hL : LSmoothfn f L)
    (φ ψ : GradientFlow f x₀ T) :
    Set.EqOn φ.trajectory ψ.trajectory (Icc 0 T) := by
  intro t ht;
  have h_cont : ContinuousOn φ.trajectory (Set.Icc 0 T) ∧ ContinuousOn ψ.trajectory (Set.Icc 0 T) := by
    exact ⟨ fun t ht => ( φ.hasDerivAt t ht |> HasDerivAt.continuousAt |> ContinuousAt.continuousWithinAt ), fun t ht => ( ψ.hasDerivAt t ht |> HasDerivAt.continuousAt |> ContinuousAt.continuousWithinAt ) ⟩;
  have h_unique : ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt φ.trajectory (-(gradient f (φ.trajectory t))) (Set.Ici t) t ∧ HasDerivWithinAt ψ.trajectory (-(gradient f (ψ.trajectory t))) (Set.Ici t) t := by
    exact fun t ht => ⟨ φ.hasDerivAt t ⟨ ht.1, ht.2.le ⟩ |> HasDerivAt.hasDerivWithinAt, ψ.hasDerivAt t ⟨ ht.1, ht.2.le ⟩ |> HasDerivAt.hasDerivWithinAt ⟩;
  have := @ODE_solution_unique;
  contrapose! this;
  refine' ⟨ E, inferInstance, inferInstance, fun t x => -gradient f x, L, φ.trajectory, ψ.trajectory, 0, T, _, _, _, _ ⟩ <;> simp_all +decide [ EqOn ];
  · exact hL.neg;
  · exact ⟨ t, ht.1, ht.2, this ⟩

/-
Two flows on [0, n+1] and [0, m+1] with n ≤ m agree on [0, n+1].
-/
lemma flows_consistent_of_le
    {f : E → ℝ} {x₀ : E} {L : ℝ≥0}
    (hL : LSmoothfn f L)
    (φ : (n : ℕ) → GradientFlow f x₀ ((n : ℝ) + 1))
    {n m : ℕ} (hnm : n ≤ m)
    {s : ℝ} (hs : s ∈ Icc 0 ((n : ℝ) + 1)) :
    (φ n).trajectory s = (φ m).trajectory s := by
  have hEq := gradientFlow_unique (L := L) (by linarith [hs.1, hs.2]) hL (φ n)
    (gradientFlow_restrict (φ m) (by exact_mod_cast Nat.succ_le_succ hnm))
  exact hEq hs

/-- For any two indices n, m, flows agree at any point in both their domains. -/
lemma flows_consistent_at
    {f : E → ℝ} {x₀ : E} {L : ℝ≥0}
    (hL : LSmoothfn f L)
    (φ : (n : ℕ) → GradientFlow f x₀ ((n : ℝ) + 1))
    (n m : ℕ)
    {s : ℝ} (hs_n : s ∈ Icc 0 ((n : ℝ) + 1)) (hs_m : s ∈ Icc 0 ((m : ℝ) + 1)) :
    (φ n).trajectory s = (φ m).trajectory s := by
  rcases le_total n m with hnm | hmn
  · exact flows_consistent_of_le hL φ hnm hs_n
  · exact (flows_consistent_of_le hL φ hmn hs_m).symm

/-
The global trajectory `(φ ⌈t⌉₊).trajectory t` agrees with `(φ ⌈t⌉₊).trajectory`
    near `t`.
-/
lemma global_traj_eventuallyEq
    {f : E → ℝ} {x₀ : E} {L : ℝ≥0}
    (hL : LSmoothfn f L)
    (φ : (n : ℕ) → GradientFlow f x₀ ((n : ℝ) + 1))
    {t : ℝ} (ht : 0 ≤ t) :
    (fun s => (φ ⌈s⌉₊).trajectory s) =ᶠ[nhds t] (φ ⌈t⌉₊).trajectory := by
  have h_eventuallyEq : ∀ᶠ s in nhdsWithin t {s | 0 ≤ s}, (φ ⌈s⌉₊).trajectory s = (φ ⌈t⌉₊).trajectory s := by
    refine' eventually_nhdsWithin_iff.mpr _;
    filter_upwards [ Ioo_mem_nhds ( show t - 1 < t by linarith ) ( show t < ⌈t⌉₊ + 1 by linarith [ Nat.le_ceil t ] ) ] with s hs hs' using flows_consistent_at hL φ ⌈s⌉₊ ⌈t⌉₊ ( by constructor <;> linarith [ hs.1, hs.2, Nat.le_ceil s ] ) ( by constructor <;> linarith [ hs.1, hs.2, Nat.le_ceil t ] );
  by_cases h : t = 0;
  · rw [ eventually_nhdsWithin_iff ] at h_eventuallyEq;
    filter_upwards [ h_eventuallyEq, Metric.ball_mem_nhds t zero_lt_one ] with s hs hs' ; by_cases hs'' : 0 ≤ s <;> simp_all +decide;
    rw [ Nat.ceil_eq_zero.mpr ( by linarith [ abs_lt.mp hs' ] ), h, Nat.ceil_zero ];
  · rw [ eventually_nhdsWithin_iff ] at h_eventuallyEq;
    filter_upwards [ h_eventuallyEq, lt_mem_nhds ( show 0 < t by positivity ) ] with s hs hs' using hs hs'.le

/-- **Global gradient flow existence.**
For any `C¹` globally `L`-smooth `f` and initial point `x₀`,
a gradient flow exists for all time `t ≥ 0`. -/
theorem gradientFlowGlobal_existence
    (f : E → ℝ) (L : ℝ≥0) (x₀ : E)
    (hC1 : ContDiff ℝ 1 f) (hL : LSmoothfn f L) :
    Nonempty (GradientFlowGlobal f x₀) := by
  -- For each n, choose a flow on [0, n+1]
  have φ : (n : ℕ) → GradientFlow f x₀ ((n : ℝ) + 1) :=
    fun n => (gradientFlow_existence f L x₀ ((n : ℝ) + 1) (by positivity) hC1 hL).some
  -- Define the global trajectory: traj(t) = (φ ⌈t⌉₊).trajectory t
  -- Note: ⌈t⌉₊ = 0 for t ≤ 0, so traj t = (φ 0).trajectory t for t ≤ 0
  refine ⟨⟨fun t => (φ ⌈t⌉₊).trajectory t, ?_, ?_⟩⟩
  · -- init: traj 0 = x₀
    simp
  · -- HasDerivAt for all t ≥ 0
    intro t ht
    have h_mem : t ∈ Icc 0 ((⌈t⌉₊ : ℝ) + 1) :=
      ⟨ht, by linarith [Nat.le_ceil t]⟩
    have h_ev := global_traj_eventuallyEq hL φ ht
    exact ((φ ⌈t⌉₊).hasDerivAt t h_mem).congr_of_eventuallyEq h_ev

end Optimization
end Lean4ML
