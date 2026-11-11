import ContinuousFlexibility.Statements.ScalarWeighted

/-!
# The actual common low-order scalar neighbourhood

All four state coordinates are controlled by the one seminorm ball appearing
in the frozen scalar statements.  The topology and bounds below use that ball
itself, including its arbitrary fixed height centre.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

theorem scalarStateGrading_apply (S : PhysicalSpacesData) (s : ℕ)
    (x : ScalarWeightedState S) :
    scalarStateGrading S s x =
      scalarHeightGrading S s x.1.1.1 + scalarHeightGrading S s x.1.1.2 +
        ‖x.1.2‖ + ‖x.2‖ := by
  simp only [scalarStateGrading, pairGrading, realGrading, add_apply,
    Seminorm.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, coe_normSeminorm]

theorem scalarHeightGrading_monotone (S : PhysicalSpacesData) :
    Monotone (scalarHeightGrading S) :=
  gradedSeminorm_monotone (fun s => (S.height scalarBeta).level s)
    (S.height scalarBeta).bond

theorem scalarStateGrading_monotone (S : PhysicalSpacesData) :
    Monotone (scalarStateGrading S) := by
  intro s t hst x
  rw [scalarStateGrading_apply, scalarStateGrading_apply]
  have h₁ := scalarHeightGrading_monotone S hst x.1.1.1
  have h₂ := scalarHeightGrading_monotone S hst x.1.1.2
  linarith only [h₁, h₂]

theorem continuous_scalarHeightGrading (S : PhysicalSpacesData) (s : ℕ) :
    Continuous (scalarHeightGrading S s) :=
  continuous_gradedSeminorm (fun s => (S.height scalarBeta).level s)
    (S.height scalarBeta).bond s

theorem continuous_scalarStateGrading (S : PhysicalSpacesData) (s : ℕ) :
    Continuous (scalarStateGrading S s) := by
  have h := continuous_scalarHeightGrading S s
  have he : (fun x : ScalarWeightedState S => scalarStateGrading S s x) = fun x =>
      scalarHeightGrading S s x.1.1.1 + scalarHeightGrading S s x.1.1.2 +
        ‖x.1.2‖ + ‖x.2‖ := funext (scalarStateGrading_apply S s)
  change Continuous (fun x : ScalarWeightedState S => scalarStateGrading S s x)
  rw [he]
  exact (((h.comp continuous_fst.fst.fst).add (h.comp continuous_fst.fst.snd)).add
    continuous_fst.snd.norm).add continuous_snd.norm

theorem isOpen_scalarStateBall (S : PhysicalSpacesData) (v₀ : ScalarHeightSpace S)
    (base : ℕ) (ε : ℝ) : IsOpen (scalarStateBall S v₀ base ε) :=
  isOpen_lt ((continuous_scalarStateGrading S base).comp
    (continuous_id.sub continuous_const)) continuous_const

theorem scalarStateCenter_mem_ball (S : PhysicalSpacesData) (v₀ : ScalarHeightSpace S)
    (base : ℕ) {ε : ℝ} (hε : 0 < ε) :
    scalarStateCenter S v₀ ∈ scalarStateBall S v₀ base ε := by
  change scalarStateGrading S base (scalarStateCenter S v₀ - scalarStateCenter S v₀) < ε
  rw [sub_self]
  calc
    scalarStateGrading S base 0 = 0 := (scalarStateGrading S base).map_zero'
    _ < ε := hε

theorem scalarStateGrading_sub_center (S : PhysicalSpacesData)
    (v₀ : ScalarHeightSpace S) (base : ℕ) (x : ScalarWeightedState S) :
    scalarStateGrading S base (x - scalarStateCenter S v₀) =
      scalarHeightGrading S base x.1.1.1 +
        scalarHeightGrading S base (x.1.1.2 - v₀) + ‖x.1.2‖ + ‖x.2‖ := by
  rw [scalarStateGrading_apply]
  simp only [scalarStateCenter, Prod.fst_sub, Prod.snd_sub, sub_zero]

/-- The common ball bounds the profile perturbation, height displacement,
left constant, and independent parameter at the same order. -/
theorem scalarStateBall_coordinate_bounds {S : PhysicalSpacesData}
    {v₀ : ScalarHeightSpace S} {base : ℕ} {ε : ℝ} {x : ScalarWeightedState S}
    (hx : x ∈ scalarStateBall S v₀ base ε) :
    scalarHeightGrading S base x.1.1.1 < ε ∧
      scalarHeightGrading S base (x.1.1.2 - v₀) < ε ∧ ‖x.1.2‖ < ε ∧ ‖x.2‖ < ε := by
  change scalarStateGrading S base (x - scalarStateCenter S v₀) < ε at hx
  rw [scalarStateGrading_sub_center] at hx
  have h₁ := apply_nonneg (scalarHeightGrading S base) x.1.1.1
  have h₂ := apply_nonneg (scalarHeightGrading S base) (x.1.1.2 - v₀)
  have h₃ := norm_nonneg x.1.2
  have h₄ := norm_nonneg x.2
  constructor
  · linarith only [hx, h₂, h₃, h₄]
  constructor
  · linarith only [hx, h₁, h₃, h₄]
  constructor
  · linarith only [hx, h₁, h₂, h₄]
  · linarith only [hx, h₁, h₂, h₃]

theorem scalarStateBall_height_bound {S : PhysicalSpacesData}
    {v₀ : ScalarHeightSpace S} {base : ℕ} {ε : ℝ} {x : ScalarWeightedState S}
    (hx : x ∈ scalarStateBall S v₀ base ε) :
    scalarHeightGrading S base x.1.1.2 < ε + scalarHeightGrading S base v₀ := by
  have hb := (scalarStateBall_coordinate_bounds hx).2.1
  calc
    _ = scalarHeightGrading S base ((x.1.1.2 - v₀) + v₀) := by rw [sub_add_cancel]
    _ ≤ scalarHeightGrading S base (x.1.1.2 - v₀) + scalarHeightGrading S base v₀ :=
      map_add_le_add (scalarHeightGrading S base) (x.1.1.2 - v₀) v₀
    _ < _ := by linarith only [hb]

theorem scalarStateBall_mono {S : PhysicalSpacesData} {v₀ : ScalarHeightSpace S}
    {base base' : ℕ} {ε ε' : ℝ} (hb : base ≤ base') (hε : ε' ≤ ε) :
    scalarStateBall S v₀ base' ε' ⊆ scalarStateBall S v₀ base ε := by
  intro x hx
  exact lt_of_le_of_lt (scalarStateGrading_monotone S hb (x - scalarStateCenter S v₀))
    (lt_of_lt_of_le hx hε)

end ContinuousFlexibility.Statements
