import ContinuousFlexibility.Analysis.N04PrincipalNegativeReciprocalDifference
import ContinuousFlexibility.Analysis.N04PrincipalFullTower

/-!
# The frozen current-data clause for reciprocals

The neighborhood on which denominators are nonzero is supplied once.
The full reciprocal tower is unweighted, while the exact difference
identity restores one complete sampled height weight. A final fixed
restriction provides the value clause of the frozen interface.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

theorem CurrentJetDataOn.n04PrincipalNegative_reference_zero
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
    {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}
    (h : CurrentJetDataOn S T cell P base ε f f₀) (hε : 0 < ε)
    (m : ℕ) (hm : P m) : EqOn (f 0 m) (f₀ m) unitStrip := by
  have hz : (0 : Parameter S) ∈ sectorNeighborhood S base ε ε := by
    constructor
    · change sectorGrading S base 0 < ε
      exact (sectorGrading S base).map_zero'.trans_lt hε
    · change |(0 : ℝ)| < ε
      simpa only [abs_zero] using hε
  have hv := h.2.choose_spec.1
  have hb := (hv.choose_spec 0).choose_spec.2
  intro q hq
  have hh := hb 0 hz m hm ⟨q, hq⟩ 0 0 (by omega)
  have hpzero : parameterGrading S hv.choose (0 : Parameter S) = 0 :=
    (parameterGrading S hv.choose).map_zero'
  have hh' : |f 0 m q - f₀ m q| ≤ 0 := by
    simp only [spaces_mixedDerivative_zero, Nat.zero_add] at hh
    rw [hpzero, mul_zero] at hh
    exact hh
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hh' (abs_nonneg _)))

/-- Reciprocal closure of the exact all-pieces current-data interface.
The low order is chosen once, before every output derivative order. -/
theorem CurrentJetDataOn.n04PrincipalNegative_inv
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {base : ℕ} {ε : ℝ}
    {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}
    (h : CurrentJetDataOn S T cell (fun _ => True) base ε f f₀)
    (hε : 0 < ε) (hI : HasInterpolation (parameterGrading S))
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 < T.H (T.sample (cell m)))
    {RH : ℝ} (hRH : 0 ≤ RH)
    (hheight : ∀ m, T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) ≤ RH)
    (href : ∀ m, ContDiffOn ℝ ∞ (f₀ m) unitStrip)
    (hrefb : ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m,
      ∀ (q : unitStrip) (a b : ℕ), a + b ≤ s →
        |mixedDerivative a b (f₀ m) q.val| ≤ B * T.E0 (T.sample (cell m)) ^ B)
    (hrefib : ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m,
      ∀ (q : unitStrip) (a b : ℕ), a + b ≤ s →
        |mixedDerivative a b (fun y => (f₀ m y)⁻¹) q.val| ≤
          B * T.E0 (T.sample (cell m)) ^ B)
    (hnonzero : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m,
      ∀ q ∈ unitStrip, f z m q ≠ 0)
    (hinverse : ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m, ∀ q ∈ unitStrip,
        |(f z m q)⁻¹| ≤ B * T.E0 (T.sample (cell m)) ^ B) :
    ∃ newBase : ℕ, base ≤ newBase ∧
      CurrentJetDataOn S T cell (fun _ => True) newBase (min ε (1 / 2))
        (fun z m q => (f z m q)⁻¹) (fun m q => (f₀ m q)⁻¹) := by
  classical
  let U : Set (Parameter S) := sectorNeighborhood S base ε ε
  let ι : Type := {m : ℕ // True}
  let E : ι → ℝ := fun m => T.E0 (T.sample (cell m.val))
  let W : ι → ℝ := fun m => T.H (T.sample (cell m.val)) ^ (3 / 4 : ℝ)
  have hU : IsOpen U := isOpen_sectorNeighborhood S base ε ε
  have hΩ : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  have hp : Monotone (parameterGrading S) := n07aParameterGrading_monotone S
  have hz : (0 : Parameter S) ∈ U := by
    constructor
    · change sectorGrading S base 0 < ε
      exact (sectorGrading S base).map_zero'.trans_lt hε
    · change |(0 : ℝ)| < ε
      simpa only [abs_zero] using hε
  have hzero := h.n04PrincipalNegative_reference_zero hε
  have hrefne (m : ℕ) (q : PolarPoint) (hq : q ∈ unitStrip) : f₀ m q ≠ 0 := by
    rw [← hzero m trivial hq]
    exact hnonzero 0 hz m q hq
  have hrefi (m : ℕ) : ContDiffOn ℝ ∞ (fun q => (f₀ m q)⁻¹) unitStrip :=
    (href m).inv (hrefne m)
  let RFall (m : ℕ) : MixedJetRegularity U unitStrip (fun z => f z m) :=
    h.n04Principal_familyRegularity (fun m _ => href m) m trivial
  let RIall (m : ℕ) : MixedJetRegularity U unitStrip (fun z q => (f z m q)⁻¹) :=
    (RFall m).n04PrincipalNegative_inv hU hΩ (fun z hz q hq => hnonzero z hz m q hq)
  let RI₀all (m : ℕ) : MixedJetRegularity U unitStrip (fun _ q => (f₀ m q)⁻¹) :=
    n04Realization_mixedJetRegularity_fixedSpatial hU (hrefi m)
  let RN₀all (m : ℕ) : MixedJetRegularity U unitStrip (fun _ q => -(f₀ m q)⁻¹) :=
    (RI₀all m).scalarComp hU hΩ isOpen_univ contDiff_neg.contDiffOn
      (fun _ _ _ _ => mem_univ _)
  let RDIall (m : ℕ) : MixedJetRegularity U unitStrip
      (fun z q => (f z m q)⁻¹ - (f₀ m q)⁻¹) := by
    simpa only [sub_eq_add_neg] using (RIall m).add (RN₀all m) hU hΩ
  let RD : ∀ m : ι, MixedJetRegularity U unitStrip
      (fun z q => f z m.val q - f₀ m.val q) :=
    fun m => h.n04Principal_differenceRegularity (fun m _ => href m) m.val m.property
  let RF : ∀ m : ι, MixedJetRegularity U unitStrip (fun z => f z m.val) :=
    fun m => RFall m.val
  let RI : ∀ m : ι, MixedJetRegularity U unitStrip (fun z q => (f z m.val q)⁻¹) :=
    fun m => RIall m.val
  let RI₀ : ∀ m : ι, MixedJetRegularity U unitStrip (fun _ q => (f₀ m.val q)⁻¹) :=
    fun m => RI₀all m.val
  let RDI : ∀ m : ι, MixedJetRegularity U unitStrip
      (fun z q => (f z m.val q)⁻¹ - (f₀ m.val q)⁻¹) := fun m => RDIall m.val
  have hfull : N04PrincipalWeightedTowerBounds (parameterGrading S) base E
      (fun _ => 1) RF := h.n04Principal_fullWeighted (fun m _ => href m)
    (fun s => ⟨(hrefb s).choose, (hrefb s).choose_spec.1,
      fun m _ => (hrefb s).choose_spec.2 m⟩)
    hE (fun m => (hH m).le) hRH hheight
  have hrecip := n04PrincipalNegative_reciprocal_weightedTower
    (parameterGrading S) hp hI base base E (fun m => hE m.val) hU hΩ
    (fun m z => f z m.val) RF RI hfull
    (fun m z hz q hq => hnonzero z hz m.val q hq)
    ⟨hinverse.choose, hinverse.choose_spec.1,
      fun m z hz q hq => hinverse.choose_spec.2 z hz m.val q hq⟩
  let bi : ℕ := hrecip.choose
  have hbi : base ≤ bi := (le_max_left _ _).trans hrecip.choose_spec.1
  have hRD : N04PrincipalWeightedTowerBounds (parameterGrading S) bi E W RD :=
    n04Principal_weightedTower_monoBase (parameterGrading S) hp E W
      (fun m => hE m.val) (fun m => Real.rpow_nonneg (hH m.val).le _) hbi RD
      (h.n04Principal_weightedDifference (fun m _ => href m))
  have hRI₀ : N04PrincipalWeightedTowerBounds (parameterGrading S) bi E (fun _ => 1) RI₀ := by
    apply n04Principal_weightedTower_fixedSpatial (parameterGrading S) bi E
      (fun m => hE m.val) (fun m q => (f₀ m.val q)⁻¹) RI₀
    intro s
    refine ⟨(hrefib s).choose, (hrefib s).choose, ?_⟩
    intro m a b hab q hq
    exact (Real.norm_eq_abs _).trans_le
      ((hrefib s).choose_spec.2 m.val ⟨q, hq⟩ a b hab)
  have hdifference := n04PrincipalNegative_reciprocalDifference_weightedTower
    (parameterGrading S) hp hI bi bi hU hΩ E W (fun m => hE m.val)
    (fun m => Real.rpow_pos_of_pos (hH m.val) _)
    (fun m z => f z m.val) (fun m => f₀ m.val) RD RI RI₀ RDI
    hRD hrecip.choose_spec.2 hRI₀
    (fun m z hz q hq => hnonzero z hz m.val q hq)
    (fun m q hq => hrefne m.val q hq)
  let newBase : ℕ := hdifference.choose
  have hbase : base ≤ newBase := hbi.trans
    ((le_max_left _ _).trans hdifference.choose_spec.1)
  refine ⟨newBase, hbase, ?_⟩
  apply n04Principal_data_of_weightedDifference hbase
    (lt_min hε (by norm_num)) (min_le_left _ _) (min_le_right _ _)
    hE (fun m => (hH m).le) ?_ ?_
    (fun m a b q => (RDIall m).parameter a b q.val q.property) RDI
    hdifference.choose_spec.2
  · intro z hz m _
    refine ⟨(h.1 z hz m trivial).1.inv (fun q hq => hnonzero z hz m q hq), ?_⟩
    intro q hq
    exact congrArg (fun t : ℝ => t⁻¹) ((h.1 z hz m trivial).2 q hq)
  · intro m _ q hq
    exact congrArg (fun t : ℝ => t⁻¹) (hzero m trivial hq)

end ContinuousFlexibility.Analysis
