import ContinuousFlexibility.Analysis.SmoothDirectionsOneHighLimit
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Angular differentiation of genuine parameter jets

Uniform seminorm bounds first transfer angular continuity from the actual
functions to every parameter jet. The fundamental theorem of calculus
then gives an angular integral identity. Differentiating that identity
along an actual parameter line, with domination supplied by the next
parameter jet, proves that angular differentiation commutes with every
parameter jet. No mixed derivative or endpoint regularity is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped Topology BigOperators ContDiff

local instance smoothDirectionsAngularJetsRealNormedSpace : NormedSpace ℝ ℝ := NormedField.toNormedSpace

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E}

/-- The actual tower at the limiting angle is identified by uniqueness,
so continuity is proved for the original jets, not replacement jets. -/
theorem smoothDirections_angular_jet_continuous
    {f : ℝ → E → ℝ} (J : ∀ θ, SmoothDirections U (f θ))
    (hU : IsOpen U) (hc : Convex ℝ U)
    (hf : ∀ x ∈ U, Continuous (fun θ => f θ x))
    (hbound : UniformScalarJetSeminormBounds J)
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    Continuous (fun θ => (J θ).D n x v) := by
  apply continuous_iff_continuousAt.mpr
  intro θ
  change Tendsto (fun ψ => (J ψ).D n x v) (𝓝 θ) (𝓝 ((J θ).D n x v))
  obtain ⟨K, hK⟩ := exists_smoothDirections_of_uniform_seminorm_bounds
    (l := 𝓝 θ) J hU hc (fun y hy => (hf y hy).tendsto θ) hbound
  have heq : K.D n x = (J θ).D n x := K.unique (J θ) n x hx
  simpa only [heq] using hK n x hx v

/-- The complete joint continuity follows from uniform equicontinuity
in the base point and directions, and pointwise angular continuity. -/
theorem continuousOn_joint_of_equicontinuous_slices
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {V : Set X} {F : Y → X → ℝ}
    (hV : IsOpen V) (heq : EquicontinuousOn F V)
    (hpoint : ∀ x ∈ V, Continuous (fun y => F y x)) :
    ContinuousOn (fun p : Y × X => F p.1 p.2) (univ ×ˢ V) := by
  intro p hp
  apply ContinuousAt.continuousWithinAt
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  have heqAt : EquicontinuousAt F p.2 := by
    simpa only [EquicontinuousWithinAt, EquicontinuousAt,
      nhdsWithin_eq_nhds.mpr (hV.mem_nhds hp.2)] using heq p.2 hp.2
  have hX := Metric.equicontinuousAt_iff_right.mp heqAt (ε / 2) (by positivity)
  have hY : ∀ᶠ y in 𝓝 p.1, dist (F y p.2) (F p.1 p.2) < ε / 2 :=
    (hpoint p.2 hp.2).continuousAt.eventually
      (Metric.ball_mem_nhds _ (by positivity))
  have hX' : ∀ᶠ q : Y × X in 𝓝 p,
      ∀ y, dist (F y p.2) (F y q.2) < ε / 2 :=
    continuous_snd.continuousAt.eventually hX
  have hY' : ∀ᶠ q : Y × X in 𝓝 p,
      dist (F q.1 p.2) (F p.1 p.2) < ε / 2 :=
    continuous_fst.continuousAt.eventually hY
  filter_upwards [hX', hY'] with q hqx hqy
  have hqx' : dist (F q.1 q.2) (F q.1 p.2) < ε / 2 := by
    simpa only [dist_comm] using hqx q.1
  exact (dist_triangle _ (F q.1 p.2) _).trans_lt
    ((add_lt_add hqx' hqy).trans_eq (by ring))

theorem smoothDirections_angular_jet_joint_continuous
    {f : ℝ → E → ℝ} (J : ∀ θ, SmoothDirections U (f θ))
    (hU : IsOpen U) (hc : Convex ℝ U)
    (hf : ∀ x ∈ U, Continuous (fun θ => f θ x))
    (hbound : UniformScalarJetSeminormBounds J) (n : ℕ) :
    ContinuousOn (fun z : ℝ × (E × (Fin n → E)) => (J z.1).D n z.2.1 z.2.2)
      (univ ×ˢ (U ×ˢ univ)) := by
  apply continuousOn_joint_of_equicontinuous_slices (hU.prod isOpen_univ)
    (equicontinuous_jets_of_uniform_seminorm_bounds J hU hc hbound n)
  intro z hz
  exact smoothDirections_angular_jet_continuous J hU hc hf hbound n z.1 hz.1 z.2

/-- A fixed jet on a short affine line has a bound uniform in the
angular label. Only its stated continuous seminorm estimate is used. -/
theorem local_line_jet_bound_of_uniform_seminorm_bounds
    {f : ℝ → E → ℝ} (J : ∀ θ, SmoothDirections U (f θ))
    (hU : IsOpen U) (hbound : UniformScalarJetSeminormBounds J)
    (n : ℕ) (x : E) (hx : x ∈ U) (w : E) (v : Fin n → E) :
    ∃ δ B : ℝ, 0 < δ ∧ 0 ≤ B ∧
      (∀ t : ℝ, |t| < δ → x + t • w ∈ U) ∧
      ∀ θ t, |t| < δ → |(J θ).D n (x + t • w) v| ≤ B := by
  obtain ⟨p, B, _, hB, hb⟩ := hbound n
  have hline : {t : ℝ | x + t • w ∈ U} ∈ 𝓝 (0 : ℝ) := by
    have hcont : Continuous (fun t : ℝ => x + t • w) :=
      continuous_const.add (continuous_id.smul continuous_const)
    exact hcont.continuousAt.eventually (hU.mem_nhds
      (by simpa only [zero_smul, add_zero] using hx))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hline
  let K : ℝ := B * (1 + p x + p w) * ∏ i, p (v i)
  have hK : 0 ≤ K :=
    mul_nonneg (mul_nonneg hB
      (add_nonneg (add_nonneg zero_le_one (apply_nonneg p x)) (apply_nonneg p w)))
      (Finset.prod_nonneg (fun i _ => apply_nonneg p (v i)))
  have hmem (t : ℝ) (ht : |t| < min δ 1) : x + t • w ∈ U :=
    hball (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using
      ht.trans_le (min_le_left δ 1))
  refine ⟨min δ 1, K, lt_min hδ zero_lt_one, hK, hmem, ?_⟩
  intro θ t ht
  have ht1 : |t| ≤ 1 := (ht.trans_le (min_le_right δ 1)).le
  have hpa : p (x + t • w) ≤ p x + p w := by
    calc
      _ ≤ p x + p (t • w) := map_add_le_add _ _ _
      _ = p x + |t| * p w := by rw [map_smul_eq_mul, Real.norm_eq_abs]
      _ ≤ p x + p w := add_le_add le_rfl (mul_le_of_le_one_left (apply_nonneg p w) ht1)
  exact (hb θ _ (hmem t ht) v).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by linarith only [hpa]) hB)
      (Finset.prod_nonneg (fun i _ => apply_nonneg p (v i))))

/-- Differentiate an angular integral along an actual parameter line.
Angular continuity supplies measurability; the next parameter jet
supplies an integrable constant dominating the local derivatives. -/
theorem hasDerivAt_integral_directional_jet
    {f : ℝ → E → ℝ} (J : ∀ θ, SmoothDirections U (f θ))
    (hU : IsOpen U) (hbound : UniformScalarJetSeminormBounds J)
    (hcont : ∀ n x, x ∈ U → ∀ v : Fin n → E,
      Continuous (fun θ => (J θ).D n x v))
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) (w : E) (a b : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ θ in a..b, (J θ).D n (x + t • w) v)
      (∫ θ in a..b, (J θ).D (n + 1) x (Fin.cons w v)) 0 := by
  obtain ⟨δ, B, hδ, _, hmem, hbound'⟩ :=
    local_line_jet_bound_of_uniform_seminorm_bounds J hU hbound
      (n + 1) x hx w (Fin.cons w v)
  have hnbhd : Ioo (-δ) δ ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) hδ
  have hsmall (t : ℝ) (ht : t ∈ Ioo (-δ) δ) : |t| < δ := abs_lt.mpr ht
  have hmeas : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
      AEStronglyMeasurable (fun θ => (J θ).D n (x + t • w) v)
        (volume.restrict (uIoc a b)) := by
    filter_upwards [hnbhd] with t ht
    exact (hcont n _ (hmem t (hsmall t ht)) v).aestronglyMeasurable
  have hzero : x + (0 : ℝ) • w = x := by rw [zero_smul, add_zero]
  have hInt : IntervalIntegrable (fun θ => (J θ).D n (x + (0 : ℝ) • w) v) volume a b := by
    rw [hzero]
    exact (hcont n x hx v).intervalIntegrable a b
  have hDmeas : AEStronglyMeasurable
      (fun θ => (J θ).D (n + 1) (x + (0 : ℝ) • w) (Fin.cons w v))
        (volume.restrict (uIoc a b)) := by
    rw [hzero]
    exact (hcont (n + 1) x hx (Fin.cons w v)).aestronglyMeasurable
  have hD := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t θ => (J θ).D n (x + t • w) v)
    (F' := fun t θ => (J θ).D (n + 1) (x + t • w) (Fin.cons w v))
    (bound := fun _ => B) hnbhd hmeas hInt hDmeas
    (Eventually.of_forall (fun θ _ t ht => by
      simpa only [Real.norm_eq_abs] using hbound' θ t (hsmall t ht)))
    intervalIntegrable_const
    (Eventually.of_forall (fun θ _ t ht =>
      (J θ).hasDerivAt_line_jet x w n v (hmem t (hsmall t ht))))).2
  simpa only [zero_smul, add_zero] using hD

/-- The angular fundamental-theorem identity transfers from one
parameter order to the next by uniqueness of an actual scalar derivative. -/
theorem angular_integral_identity_next_directional_jet
    {f g : ℝ → E → ℝ}
    (J : ∀ θ, SmoothDirections U (f θ)) (K : ∀ θ, SmoothDirections U (g θ))
    (hU : IsOpen U) (hbound : UniformScalarJetSeminormBounds K)
    (hcont : ∀ n x, x ∈ U → ∀ v : Fin n → E,
      Continuous (fun θ => (K θ).D n x v))
    {n : ℕ}
    (hangular : ∀ θ x, x ∈ U → ∀ v : Fin n → E,
      HasDerivAt (fun ψ => (J ψ).D n x v) ((K θ).D n x v) θ)
    (x : E) (hx : x ∈ U) (v : Fin n → E) (w : E) (a b : ℝ) :
    (J b).D (n + 1) x (Fin.cons w v) - (J a).D (n + 1) x (Fin.cons w v) =
      ∫ θ in a..b, (K θ).D (n + 1) x (Fin.cons w v) := by
  have hI := hasDerivAt_integral_directional_jet K hU hbound hcont n x hx v w a b
  have hx0 : x + (0 : ℝ) • w ∈ U := by simpa only [zero_smul, add_zero] using hx
  have hleft := (J b).hasDerivAt_line_jet x w n v hx0
  have hright := (J a).hasDerivAt_line_jet x w n v hx0
  have hD : HasDerivAt
      (fun t : ℝ => (J b).D n (x + t • w) v - (J a).D n (x + t • w) v)
      ((J b).D (n + 1) x (Fin.cons w v) - (J a).D (n + 1) x (Fin.cons w v)) 0 := by
    simpa only [zero_smul, add_zero] using hleft.fun_sub hright
  have hline : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), x + t • w ∈ U :=
    (continuous_const.add (continuous_id.smul continuous_const)).continuousAt.eventually
      (hU.mem_nhds hx0)
  have heq : (fun t : ℝ => ∫ θ in a..b, (K θ).D n (x + t • w) v) =ᶠ[𝓝 (0 : ℝ)]
      (fun t : ℝ => (J b).D n (x + t • w) v - (J a).D n (x + t • w) v) := by
    filter_upwards [hline] with t ht
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun θ _ => hangular θ _ ht v) ((hcont n _ ht v).intervalIntegrable a b)
  exact hD.unique (hI.congr_of_eventuallyEq heq.symm)

/-- Angular differentiation commutes with all parameter jets in the
given towers. The only angular derivative premise concerns the actual
zeroth-order functions. -/
theorem smoothDirections_angular_jet_hasDerivAt
    {f : ℕ → ℝ → E → ℝ} (J : ∀ b θ, SmoothDirections U (f b θ))
    (hU : IsOpen U) (hc : Convex ℝ U)
    (hbound : ∀ b, UniformScalarJetSeminormBounds (J b))
    (hangular : ∀ b θ x, x ∈ U →
      HasDerivAt (fun ψ => f b ψ x) (f (b + 1) θ x) θ) :
    ∀ k b θ x, x ∈ U → ∀ v : Fin k → E,
      HasDerivAt (fun ψ => (J b ψ).D k x v) ((J (b + 1) θ).D k x v) θ := by
  have hcont : ∀ b n x, x ∈ U → ∀ v : Fin n → E,
      Continuous (fun θ => (J b θ).D n x v) := by
    intro b n x hx v
    exact smoothDirections_angular_jet_continuous (J b) hU hc
      (fun y hy => continuous_iff_continuousAt.mpr (fun θ => (hangular b θ y hy).continuousAt))
      (hbound b) n x hx v
  intro k
  induction k with
  | zero =>
      intro b θ x hx v
      have hv : v = Fin.elim0 := Subsingleton.elim _ _
      have heq : (fun ψ => (J b ψ).D 0 x v) = (fun ψ => f b ψ x) := by
        funext ψ
        rw [hv, (J b ψ).zero x hx]
      rw [heq, hv, (J (b + 1) θ).zero x hx]
      exact hangular b θ x hx
  | succ k ih =>
      intro b θ x hx v
      have hidentity (ψ : ℝ) :
          (J b ψ).D (k + 1) x v - (J b θ).D (k + 1) x v =
            ∫ t in θ..ψ, (J (b + 1) t).D (k + 1) x v := by
        simpa only [Fin.cons_self_tail] using
          angular_integral_identity_next_directional_jet (J b) (J (b + 1)) hU
            (hbound (b + 1)) (hcont (b + 1)) (ih b)
              x hx (Fin.tail v) (v 0) θ ψ
      have hcontinuous := hcont (b + 1) (k + 1) x hx v
      have hI := (hcontinuous.integral_hasStrictDerivAt θ θ).hasDerivAt
      have heq : (fun ψ => (J b ψ).D (k + 1) x v) =ᶠ[𝓝 θ]
          (fun ψ => (J b θ).D (k + 1) x v +
            ∫ t in θ..ψ, (J (b + 1) t).D (k + 1) x v) :=
        Eventually.of_forall (fun ψ => by linarith only [hidentity ψ])
      exact (hI.const_add ((J b θ).D (k + 1) x v)).congr_of_eventuallyEq heq

theorem smoothDirections_angular_jet_contDiff
    {f : ℕ → ℝ → E → ℝ} (J : ∀ b θ, SmoothDirections U (f b θ))
    (hU : IsOpen U) (hc : Convex ℝ U)
    (hbound : ∀ b, UniformScalarJetSeminormBounds (J b))
    (hangular : ∀ b θ x, x ∈ U →
      HasDerivAt (fun ψ => f b ψ x) (f (b + 1) θ x) θ)
    (k b : ℕ) (x : E) (hx : x ∈ U) (v : Fin k → E) :
    ContDiff ℝ ∞ (fun θ => (J b θ).D k x v) := by
  have hD := smoothDirections_angular_jet_hasDerivAt J hU hc hbound hangular
  have hfinite : ∀ n b : ℕ, ContDiff ℝ n (fun θ => (J b θ).D k x v) := by
    intro n
    induction n with
    | zero =>
        intro b
        exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr
          (fun θ => (hD k b θ x hx v).continuousAt))
    | succ n ih =>
        intro b
        have heq : deriv (fun θ => (J b θ).D k x v) =
            (fun θ => (J (b + 1) θ).D k x v) :=
          funext (fun θ => (hD k b θ x hx v).deriv)
        have hh : ContDiff ℝ ((n : ℕ∞ω) + 1) (fun θ => (J b θ).D k x v) :=
          contDiff_succ_iff_deriv.mpr ⟨fun θ => (hD k b θ x hx v).differentiableAt,
            by simp, by rw [heq]; exact ih (b + 1)⟩
        simpa only [Nat.cast_add, Nat.cast_one] using hh
  exact contDiff_infty.mpr (fun n => hfinite n b)

theorem smoothDirections_angular_jet_iteratedDeriv
    {f : ℕ → ℝ → E → ℝ} (J : ∀ b θ, SmoothDirections U (f b θ))
    (hU : IsOpen U) (hc : Convex ℝ U)
    (hbound : ∀ b, UniformScalarJetSeminormBounds (J b))
    (hangular : ∀ b θ x, x ∈ U →
      HasDerivAt (fun ψ => f b ψ x) (f (b + 1) θ x) θ)
    (k b n : ℕ) (x : E) (hx : x ∈ U) (v : Fin k → E) (θ : ℝ) :
    iteratedDeriv n (fun ψ => (J b ψ).D k x v) θ = (J (b + n) θ).D k x v := by
  induction n generalizing θ with
  | zero => simp only [iteratedDeriv_zero, Nat.add_zero]
  | succ n ih =>
      have heq : iteratedDeriv n (fun ψ => (J b ψ).D k x v) =
          (fun ψ => (J (b + n) ψ).D k x v) := by
        funext ψ
        exact ih ψ
      rw [iteratedDeriv_succ, heq]
      simpa only [Nat.add_succ, Nat.add_zero] using
        (smoothDirections_angular_jet_hasDerivAt J hU hc hbound hangular k (b + n) θ x hx v).deriv

end ContinuousFlexibility.Analysis
