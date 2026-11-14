module

public import ContinuousFlexibility.Analysis.N04FlowJetGronwall
public import ContinuousFlexibility.Analysis.N04FlowTimeReversal
public import ContinuousFlexibility.Analysis.RootRescaledFieldJets

/-!
# Difference estimates for the actual regularized root flows

The two flows have the same initial angle. Subtracting their genuine
integral equations therefore removes the initial jet at every order.
The resulting Gronwall estimate is linear in its forcing bound, including
any sampled height factor carried by that bound.

The root field is linear in its two coefficient functions. Its actual
mixed spatial difference jets consequently satisfy the same-order root
field estimate without an added constant. The value comparison below
applies throughout the closed parameter box and the closed time interval,
and applies also to the actual inverse endpoint flows by time reversal.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Subtracting integral equations with the same initial value leaves
a linear forcing cost, with no absolute initial-jet contribution. -/
theorem flowJet_difference_norm_le_of_integral_equations
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {u u₀ q q₀ : ℝ → V} {c : V} {α : ℝ → ℝ} {M Λ : ℝ}
    (hu : ContinuousOn u (Icc (0 : ℝ) 1))
    (hu₀ : ContinuousOn u₀ (Icc (0 : ℝ) 1))
    (hq : ContinuousOn q (Icc (0 : ℝ) 1))
    (hq₀ : ContinuousOn q₀ (Icc (0 : ℝ) 1))
    (hα : ContinuousOn α (Icc (0 : ℝ) 1))
    (hα0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ α t)
    (hM : 0 ≤ M) (hΛ : (∫ t in (0 : ℝ)..1, α t) ≤ Λ)
    (heq : ∀ t ∈ Icc (0 : ℝ) 1, u t = c + ∫ r in (0 : ℝ)..t, q r)
    (heq₀ : ∀ t ∈ Icc (0 : ℝ) 1, u₀ t = c + ∫ r in (0 : ℝ)..t, q₀ r)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖q t - q₀ t‖ ≤ α t * ‖u t - u₀ t‖ + M) :
    ∀ t ∈ Icc (0 : ℝ) 1, ‖u t - u₀ t‖ ≤ M * Real.exp Λ := by
  have hsub (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      u t - u₀ t = (0 : V) + ∫ r in (0 : ℝ)..t, q r - q₀ r := by
    have hqI : IntervalIntegrable q volume 0 t :=
      (hq.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
    have hq₀I : IntervalIntegrable q₀ volume 0 t :=
      (hq₀.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
    rw [heq t ht, heq₀ t ht, zero_add, intervalIntegral.integral_sub hqI hq₀I]
    abel
  have hb := flowJet_norm_le_of_integral_equation
    (hu.sub hu₀) (hq.sub hq₀) hα hα0 hM hΛ hsub hbound
  simpa only [Pi.sub_apply, norm_zero, zero_add] using hb

/-- The ordinary mixed derivative of a difference of two actual flows
obeys the zero-initial-data estimate at every spatial order. -/
theorem n04Flow_spatialJet_difference_norm_le_of_composed_bound
    {F F₀ : ℝ × N04FlowPoint → ℝ}
    {Θ Θ₀ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hF₀ : ContDiff ℝ ∞ F₀)
    (hperiod : ∀ t v, Function.Periodic (fun θ : ℝ => F (t, (v, θ))) Real.pi)
    (hperiod₀ : ∀ t v, Function.Periodic (fun θ : ℝ => F₀ (t, (v, θ))) Real.pi)
    (hΘ : N04FlowEquations F Θ) (hΘ₀ : N04FlowEquations F₀ Θ₀)
    (n : ℕ) (q : N04FlowPoint) {α : ℝ → ℝ} {M Λ : ℝ}
    (hα : ContinuousOn α (Icc (0 : ℝ) 1))
    (hα0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ α t)
    (hM : 0 ≤ M) (hΛ : (∫ t in (0 : ℝ)..1, α t) ≤ Λ)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖parametricSpatialJet (n04FlowComposedField F Θ) n (q, t) -
        parametricSpatialJet (n04FlowComposedField F₀ Θ₀) n (q, t)‖ ≤
        α t * ‖iteratedFDeriv ℝ n (fun y : N04FlowPoint => Θ y.1 t y.2) q -
          iteratedFDeriv ℝ n (fun y : N04FlowPoint => Θ₀ y.1 t y.2) q‖ + M) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ n (fun y : N04FlowPoint => Θ y.1 t y.2 - Θ₀ y.1 t y.2) q‖ ≤
        M * Real.exp Λ := by
  have hu := (n04Flow_spatialJet_continuousOn hF hperiod hΘ n).comp
    (continuousOn_const.prodMk continuousOn_id) (fun t ht => ⟨mem_univ q, ht⟩)
  have hu₀ := (n04Flow_spatialJet_continuousOn hF₀ hperiod₀ hΘ₀ n).comp
    (continuousOn_const.prodMk continuousOn_id) (fun t ht => ⟨mem_univ q, ht⟩)
  have hsource := (n04FlowComposedField_spatialJet_continuousOn hF hperiod hΘ n).comp
    (continuousOn_const.prodMk continuousOn_id) (fun t ht => ⟨mem_univ q, ht⟩)
  have hsource₀ := (n04FlowComposedField_spatialJet_continuousOn hF₀ hperiod₀ hΘ₀ n).comp
    (continuousOn_const.prodMk continuousOn_id) (fun t ht => ⟨mem_univ q, ht⟩)
  have hb := flowJet_difference_norm_le_of_integral_equations
    hu hu₀ hsource hsource₀ hα hα0 hM hΛ
    (fun t ht => n04Flow_spatialJet_integral_eq hF hperiod hΘ n q ht)
    (fun t ht => n04Flow_spatialJet_integral_eq hF₀ hperiod₀ hΘ₀ n q ht) hbound
  intro t ht
  have hs : ContDiffAt ℝ ∞ (fun y : N04FlowPoint => Θ y.1 t y.2) q :=
    (n04Flow_contDiff_slice hF hperiod hΘ ht).contDiffAt
  have hs₀ : ContDiffAt ℝ ∞ (fun y : N04FlowPoint => Θ₀ y.1 t y.2) q :=
    (n04Flow_contDiff_slice hF₀ hperiod₀ hΘ₀ ht).contDiffAt
  change ‖iteratedFDeriv ℝ n
    ((fun y : N04FlowPoint => Θ y.1 t y.2) -
      (fun y : N04FlowPoint => Θ₀ y.1 t y.2)) q‖ ≤ M * Real.exp Λ
  rw [iteratedFDeriv_sub_apply
    (hs.of_le (by simp : (n : ℕ∞ω) ≤ ∞))
    (hs₀.of_le (by simp : (n : ℕ∞ω) ≤ ∞))]
  simpa only [parametricSpatialJet, Function.comp_apply, id_eq] using hb t ht

/-- Actual value stability depends on the original field difference
and the angular derivative of just the first field. -/
theorem n04Flow_difference_abs_le
    {F F₀ : ℝ × N04FlowPoint → ℝ}
    {Θ Θ₀ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hF₀ : ContDiff ℝ ∞ F₀)
    (hΘ : N04FlowEquations F Θ) (hΘ₀ : N04FlowEquations F₀ Θ₀)
    {M Λ : ℝ} (hM : 0 ≤ M) (hangular : N04FlowAngularControl F Λ)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v ∈ n04FlowParameterBox, ∀ θ,
      |F (t, (v, θ)) - F₀ (t, (v, θ))| ≤ M)
    {v : ℝ × ℝ} (hv : v ∈ n04FlowParameterBox) (θ : ℝ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |Θ v t θ - Θ₀ v t θ| ≤ M * Real.exp Λ := by
  obtain ⟨α, hα, hα0, hαbound, hΛ⟩ := hangular
  have hu := n04Flow_time_continuousOn hΘ v θ
  have hu₀ := n04Flow_time_continuousOn hΘ₀ v θ
  have hsource : ContinuousOn
      (fun r => n04FlowComposedField F Θ ((v, θ), r)) (Icc (0 : ℝ) 1) :=
    hF.continuous.comp_continuousOn
      (continuousOn_id.prodMk (continuousOn_const.prodMk hu))
  have hsource₀ : ContinuousOn
      (fun r => n04FlowComposedField F₀ Θ₀ ((v, θ), r)) (Icc (0 : ℝ) 1) :=
    hF₀.continuous.comp_continuousOn
      (continuousOn_id.prodMk (continuousOn_const.prodMk hu₀))
  have hforcing (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      ‖n04FlowComposedField F Θ ((v, θ), r) -
        n04FlowComposedField F₀ Θ₀ ((v, θ), r)‖ ≤
        α r * ‖Θ v r θ - Θ₀ v r θ‖ + M := by
    have hs : ContDiff ℝ ∞ (fun η : ℝ => F (r, (v, η))) :=
      hF.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))
    have hLip : |F (r, (v, Θ v r θ)) - F (r, (v, Θ₀ v r θ))| ≤
        α r * |Θ v r θ - Θ₀ v r θ| := by
      simpa only [Real.norm_eq_abs] using
        (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
          (fun η _ => hs.differentiable (by simp) η)
          (fun η _ => by simpa only [Real.norm_eq_abs] using hαbound r hr v hv η)
          (mem_univ (Θ₀ v r θ)) (mem_univ (Θ v r θ))
    change |F (r, (v, Θ v r θ)) - F₀ (r, (v, Θ₀ v r θ))| ≤
      α r * |Θ v r θ - Θ₀ v r θ| + M
    exact (abs_sub_le (F (r, (v, Θ v r θ))) (F (r, (v, Θ₀ v r θ)))
      (F₀ (r, (v, Θ₀ v r θ)))).trans
        (add_le_add hLip (hbound r hr v hv (Θ₀ v r θ)))
  have hb := flowJet_difference_norm_le_of_integral_equations
    hu hu₀ hsource hsource₀ hα hα0 hM hΛ
    (fun r hr => n04Flow_integral_eq hF hΘ (v, θ) hr)
    (fun r hr => n04Flow_integral_eq hF₀ hΘ₀ (v, θ) hr) hforcing t ht
  simpa only [Real.norm_eq_abs] using hb

/-- Root regularization is linear in the original drift and factored
speed, for the same fixed collar scale. -/
theorem rootRescaledField_sub (d c d₀ c₀ : PolarPoint → ℝ) (δ : ℝ) :
    rootRescaledField (fun p => d p - d₀ p) (fun p => c p - c₀ p) δ =
      fun q => rootRescaledField d c δ q - rootRescaledField d₀ c₀ δ q := by
  funext q
  simp only [rootRescaledField, rootRegularizedField]
  ring

/-- Every genuine mixed spatial derivative of the regularized field
difference retains the coefficient difference bound linearly. -/
theorem rootRescaledField_difference_jet_le
    {d c d₀ c₀ : PolarPoint → ℝ}
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hd₀ : ContDiff ℝ ∞ d₀) (hc₀ : ContDiff ℝ ∞ c₀)
    {δ M : ℝ} (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hM : 0 ≤ M)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {q : N04FlowPoint} (hq : q.1 ∈ n04FlowParameterBox) (n : ℕ)
    (hdb : ∀ k : ℕ, k ≤ n →
      ‖iteratedFDeriv ℝ k (fun p => d p - d₀ p) (δ * q.1.1 * t ^ 2, q.2)‖ ≤ M)
    (hcb : ∀ k : ℕ, k ≤ n →
      ‖iteratedFDeriv ℝ k (fun p => c p - c₀ p) (δ * q.1.1 * t ^ 2, q.2)‖ ≤ M) :
    ‖iteratedFDeriv ℝ n (fun y : N04FlowPoint =>
      rootRescaledField d c δ (t, y) - rootRescaledField d₀ c₀ δ (t, y)) q‖ ≤
      (4 * linearWeightedCompositionJetConstant n) * M := by
  have he : (fun y : N04FlowPoint =>
      rootRescaledField d c δ (t, y) - rootRescaledField d₀ c₀ δ (t, y)) =
      fun y => rootRescaledField (fun p => d p - d₀ p) (fun p => c p - c₀ p) δ (t, y) :=
    funext (fun y => (congrFun (rootRescaledField_sub d c d₀ c₀ δ) (t, y)).symm)
  rw [he]
  exact rootRescaledField_jet_le (hd.sub hd₀) (hc.sub hc₀) hδ hδone hM ht hq n hdb hcb

/-- The sharp coefficient difference controls the rescaled field
uniformly at every point of the closed root collar. -/
theorem rootRescaledField_difference_abs_le
    {d c d₀ c₀ : PolarPoint → ℝ}
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hd₀ : ContDiff ℝ ∞ d₀) (hc₀ : ContDiff ℝ ∞ c₀)
    {δ M : ℝ} (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hM : 0 ≤ M)
    (hdb : ∀ r, |r| ≤ δ → ∀ θ, |d (r, θ) - d₀ (r, θ)| ≤ M)
    (hcb : ∀ r, |r| ≤ δ → ∀ θ, |c (r, θ) - c₀ (r, θ)| ≤ M)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {v : ℝ × ℝ} (hv : v ∈ n04FlowParameterBox) (θ : ℝ) :
    |rootRescaledField d c δ (t, (v, θ)) -
      rootRescaledField d₀ c₀ δ (t, (v, θ))| ≤ 4 * M := by
  have ht2 : t ^ 2 ≤ 1 := by
    simpa only [pow_two, one_mul] using mul_le_mul ht.2 ht.2 ht.1 zero_le_one
  have hv1 : |v.1| ≤ 1 := abs_le.mpr hv.1
  have hr : |δ * v.1 * t ^ 2| ≤ δ := by
    rw [abs_mul, abs_mul, abs_of_nonneg hδ, abs_of_nonneg (sq_nonneg t)]
    calc
      _ ≤ (δ * 1) * 1 := mul_le_mul
        (mul_le_mul_of_nonneg_left hv1 hδ) ht2 (sq_nonneg t) (by positivity)
      _ = δ := by ring
  have hb := rootRescaledField_difference_jet_le hd hc hd₀ hc₀ hδ hδone hM
    ht (q := (v, θ)) hv 0
    (fun k hk => by
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hdb _ hr θ)
    (fun k hk => by
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hcb _ hr θ)
  simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs,
    linearWeightedCompositionJetConstant] using hb

/-- The collar is chosen from one low angular bound before the entire
state family and before either actual solution. Every state's external
difference weight remains a linear factor on that same collar. -/
theorem exists_rootRescaledFlow_common_difference_collar
    {Z : Type} {U : Set Z} (d c : Z → PolarPoint → ℝ)
    (d₀ c₀ : PolarPoint → ℝ) (M : Z → ℝ)
    {ρ L Λ : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L) (hΛ : 0 < Λ)
    (hd : ∀ z ∈ U, ContDiff ℝ ∞ (d z))
    (hc : ∀ z ∈ U, ContDiff ℝ ∞ (c z))
    (hd₀ : ContDiff ℝ ∞ d₀) (hc₀ : ContDiff ℝ ∞ c₀)
    (hM : ∀ z ∈ U, 0 ≤ M z)
    (hdangle : ∀ z ∈ U, ∀ r, |r| ≤ ρ → ∀ θ,
      |deriv (fun η => d z (r, η)) θ| ≤ L)
    (hcangle : ∀ z ∈ U, ∀ r, |r| ≤ ρ → ∀ θ,
      |deriv (fun η => c z (r, η)) θ| ≤ L)
    (hdb : ∀ z ∈ U, ∀ r, |r| ≤ ρ → ∀ θ,
      |d z (r, θ) - d₀ (r, θ)| ≤ M z)
    (hcb : ∀ z ∈ U, ∀ r, |r| ≤ ρ → ∀ θ,
      |c z (r, θ) - c₀ (r, θ)| ≤ M z) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ δ ≤ 1 ∧
      ∀ z ∈ U, ∀ Θ Θ₀ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
        N04FlowEquations (rootRescaledField (d z) (c z) δ) Θ →
        N04FlowEquations (rootRescaledField d₀ c₀ δ) Θ₀ →
        ∀ v ∈ n04FlowParameterBox, ∀ θ t, t ∈ Icc (0 : ℝ) 1 →
          |Θ v t θ - Θ₀ v t θ| ≤ (4 * Real.exp Λ) * M z := by
  obtain ⟨δ, hδ, hδρ, hδone, hcontrol⟩ :=
    exists_rootRescaledField_angularControl d c hρ hL hΛ hd hc hdangle hcangle
  refine ⟨δ, hδ, hδρ, hδone, ?_⟩
  intro z hz Θ Θ₀ hΘ hΘ₀ v hv θ t ht
  have hb := n04Flow_difference_abs_le
    (contDiff_rootRescaledField (hd z hz) (hc z hz) δ)
    (contDiff_rootRescaledField hd₀ hc₀ δ) hΘ hΘ₀
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (hM z hz)) (hcontrol z hz)
    (fun r hr w hw η => rootRescaledField_difference_abs_le
      (hd z hz) (hc z hz) hd₀ hc₀ hδ.le hδone (hM z hz)
      (fun x hx => hdb z hz x (hx.trans hδρ))
      (fun x hx => hcb z hz x (hx.trans hδρ)) hr hw η) hv θ ht
  exact hb.trans_eq (by ring)

/-- Time reversal preserves the raw field-difference cost. The same
value estimate therefore applies to actual inverse endpoint flows. -/
theorem n04Flow_inverse_difference_abs_le
    {F F₀ : ℝ × N04FlowPoint → ℝ}
    {Ψ Ψ₀ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hF₀ : ContDiff ℝ ∞ F₀)
    (hΨ : N04FlowEquations (n04FlowReverseField F) Ψ)
    (hΨ₀ : N04FlowEquations (n04FlowReverseField F₀) Ψ₀)
    {M Λ : ℝ} (hM : 0 ≤ M) (hangular : N04FlowAngularControl F Λ)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v ∈ n04FlowParameterBox, ∀ θ,
      |F (t, (v, θ)) - F₀ (t, (v, θ))| ≤ M)
    {v : ℝ × ℝ} (hv : v ∈ n04FlowParameterBox) (θ : ℝ) :
    |Ψ v 1 θ - Ψ₀ v 1 θ| ≤ M * Real.exp Λ := by
  apply n04Flow_difference_abs_le (n04FlowReverseField_contDiff hF)
    (n04FlowReverseField_contDiff hF₀) hΨ hΨ₀ hM
    (n04FlowReverseField_angularControl hangular) ?_ hv θ ⟨zero_le_one, le_rfl⟩
  intro t ht w hw η
  have htime : 1 - t ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  simpa only [n04FlowReverseField, neg_sub_neg, abs_sub_comm] using
    hbound (1 - t) htime w hw η

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04Flow_spatialJet_difference_norm_le_of_composed_bound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04Flow_spatialJet_difference_norm_le_of_composed_bound

/-- info: 'ContinuousFlexibility.Analysis.n04Flow_inverse_difference_abs_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04Flow_inverse_difference_abs_le

/-- info: 'ContinuousFlexibility.Analysis.exists_rootRescaledFlow_common_difference_collar'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.exists_rootRescaledFlow_common_difference_collar
