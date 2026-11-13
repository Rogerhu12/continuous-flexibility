import ContinuousFlexibility.Analysis.N04NegativeHeightDomains
import ContinuousFlexibility.Analysis.N04NegativeGeometryDataCollector
import ContinuousFlexibility.Analysis.N04SourceColumnsScalarFamily

/-!
# Scalar composition on one fixed compact range

The parameter base is chosen from the full input tower before its order.
Every positive derivative of the scalar composite retains the sampled
height factor.  The first derivative then controls the reference
difference, on one smaller convex sector neighborhood.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff BigOperators

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

private theorem height_compact_outer_jets
    {V K : Set ℝ} (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V)
    {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g V) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ K, ∀ a b : ℕ, a + b ≤ N →
      ‖iteratedFDeriv ℝ a (iteratedDeriv b g) t‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := compact_iteratedFDeriv_bound hK
    (fun t ht => (hg t (hKV ht)).contDiffAt (hV.mem_nhds (hKV ht))) N
  refine ⟨C, hC, fun t ht a b hab => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    n04SourceColumns_iteratedDeriv_add]
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hb (a + b) hab t ht

/-- Pack the compact scalar bound before introducing any concrete
parameter space or current-data certificate. -/
private theorem height_compact_outer_envelope
    {X I : Type*} {U : Set X} {Ω : Set PolarPoint} {V K : Set ℝ}
    (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V)
    {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g V)
    (E : I → ℝ) (hE : ∀ t, 1 ≤ E t) (f : I → X → PolarPoint → ℝ)
    (hrange : ∀ t q, q ∈ Ω → ∀ z ∈ U, f t z q ∈ K) :
    ∀ N : ℕ, ∃ A : ℝ, 0 < A ∧
      ∀ t q, q ∈ Ω → ∀ z ∈ U, ∀ a b : ℕ, a + b ≤ N →
        ‖iteratedFDeriv ℝ a (iteratedDeriv b g) (f t z q)‖ ≤ A * E t ^ A := by
  intro N
  have h := height_compact_outer_jets hV hK hKV hg N
  refine ⟨h.choose, h.choose_spec.1, fun t q hq z hz a b hab => ?_⟩
  exact (h.choose_spec.2 (f t z q) (hrange t q hq z hz) a b hab).trans
    (le_mul_of_one_le_right h.choose_spec.1.le
      (Real.one_le_rpow (hE t) h.choose_spec.1.le))

private theorem height_zero_coefficient_bound {x E R : ℝ}
    (h : x * E ^ (0 : ℝ) ≤ R) : x ≤ R := by
  simpa only [Real.rpow_zero, mul_one] using h

variable {S : PhysicalSpacesData} {T : MaterialData} {D : ReferenceData}
  {cell : ℕ → ℕ} {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
  {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}

/-- Smooth scalar kernels on a fixed compact range preserve the actual
current-data estimate, including the positive parameter height factor. -/
theorem CurrentJetDataOn.height_scalarComp
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hI : HasInterpolation (parameterGrading S))
    (hε : 0 < ε) (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (h : CurrentJetDataOn S T cell P base ε f f₀)
    (h₀ : N04HeightReferenceDataOn T cell P f₀)
    (hzero : ∀ m, P m → ∀ q ∈ unitStrip, f 0 m q = f₀ m q)
    {V : Set ℝ} (hV : IsOpen V) {K : Set ℝ} (hK : IsCompact K) (hKV : K ⊆ V)
    (g : ℝ → ℝ) (hg : ContDiffOn ℝ ∞ g V)
    (hrange : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m, P m →
      ∀ q ∈ unitStrip, f z m q ∈ K) :
    ∃ b' : ℕ, ∃ ε' : ℝ, base ≤ b' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      CurrentJetDataOn S T cell P b' ε'
        (fun z m q => g (f z m q)) (fun m q => g (f₀ m q)) := by
  classical
  let U := sectorNeighborhood S base ε ε
  have hU : IsOpen U := isOpen_sectorNeighborhood S base ε ε
  have hΩ : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  have hp : Monotone (parameterGrading S) :=
    tamePairGrading_monotone (sectorGrading_monotone S) (fun _ _ _ => le_rfl)
  let RF : ∀ m, P m → MixedJetRegularity U unitStrip (fun z => f z m) :=
    fun m hm => h.height_regularity h₀ m hm
  let RG : ∀ m, P m → MixedJetRegularity U unitStrip (fun z q => g (f z m q)) :=
    fun m hm => (RF m hm).scalarComp hU hΩ hV hg
      (fun z hz q hq => hKV (hrange z hz m hm q hq))
  have hz₀ : (0 : Parameter S) ∈ U := by
    exact ⟨(sectorGrading S base).map_zero'.trans_lt hε,
      (abs_zero : |(0 : ℝ)| = 0).trans_lt hε⟩
  have hH (m : ℕ) : 0 ≤ T.H (T.sample (cell m)) :=
    (hT.2.1 _ (materialSample_mem_interval hD hT (cell m))).2.1.le
  have hheight := material_sample_height_coefficient_power_bounded hD hT cell 0
    (by norm_num : (0 : ℝ) < 3 / 4)
  let RH : ℝ := hheight.choose
  have hHR (m : ℕ) : T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) ≤ RH :=
    height_zero_coefficient_bound (hheight.choose_spec.2 m)
  have ht := h.height_fullTower hD hT h₀ hE
  let L : ℕ → ℕ := fun k => (ht k).choose
  have hbound : ∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ t : {m // P m}, ∀ q (hq : q ∈ unitStrip) a b, a + b ≤ s →
      ∀ z ∈ U, ∀ v : Fin k → Parameter S,
        |((RF t.val t.property).parameter a b q hq).D k z v| ≤
          B * T.E0 (T.sample (cell t.val)) ^ B *
            parameterHeightWeight (T.H (T.sample (cell t.val)) ^ (3 / 4 : ℝ)) k *
              oneHighVariationWeight (parameterGrading S) base (s + L k) z v := by
    intro k s
    exact ⟨((ht k).choose_spec s).choose, ((ht k).choose_spec s).choose_spec.1,
      fun t q hq a b hab z hz v =>
        ((ht k).choose_spec s).choose_spec.2 t.val t.property q hq a b hab
          ((RF t.val t.property).parameter a b q hq) z hz v⟩
  have houter := height_compact_outer_envelope (U := U) (Ω := unitStrip) hV hK hKV hg
    (fun t : {m // P m} => T.E0 (T.sample (cell t.val))) (fun t => hE t.val)
    (fun t z => f z t.val) (fun t q hq z hz => hrange z hz t.val t.property q hq)
  have hcomposite := n04SourceColumns_scalarFamily_oneHigh
    (parameterGrading S) hp hI base L hU hΩ hV
    (fun t : {m // P m} => T.E0 (T.sample (cell t.val)))
    (fun t => T.H (T.sample (cell t.val)) ^ (3 / 4 : ℝ)) RH
    (fun t => hE t.val) (fun t => ⟨Real.rpow_nonneg (hH t.val) _, hHR t.val⟩)
    (fun t z => f z t.val) g (fun t => RF t.val t.property) hg
    (fun t z hz q hq => hKV (hrange z hz t.val t.property q hq)) hbound houter
  let b' : ℕ := hcomposite.choose
  have hb' : base ≤ b' := hcomposite.choose_spec.1
  let ε' : ℝ := min ε (1 / 2)
  let U' := sectorNeighborhood S b' ε' ε'
  have hε' : 0 < ε' := lt_min hε (by norm_num)
  have hεε : ε' ≤ ε := min_le_left _ _
  have hU' : IsOpen U' := isOpen_sectorNeighborhood S b' ε' ε'
  have hsub : U' ⊆ U := sectorNeighborhood_mono S hb' hεε hεε
  let R' : ∀ m, P m → MixedJetRegularity U' unitStrip (fun z q => g (f z m q)) :=
    fun m hm => (RG m hm).height_restrict hU' hsub
  have hlow : ∀ z ∈ U', parameterGrading S b' z ≤ 1 :=
    fun z hz => n04NegativeHeight_parameterGrading_le_one (min_le_right ε (1 / 2)) hz
  refine ⟨b', ε', hb', hε', hεε, CurrentJetDataOn.of_positive_towers hε' hE hH R'
    (fun z hz m hm q hq => congrArg g ((h.1 z (hsub hz) m hm).2 q hq))
    (fun m hm => ?_) (fun m hm q hq => congrArg g (hzero m hm q hq)) hlow ?_⟩
  · exact hg.comp (h₀.1 m hm).1 (fun q hq =>
      Eq.mp (congrArg (fun t : ℝ => t ∈ V) (hzero m hm q hq))
        (hKV (hrange 0 hz₀ m hm q hq)))
  · intro k hk
    have hkbound := hcomposite.choose_spec.2 k hk
    refine ⟨hkbound.choose, fun s => ?_⟩
    have hs := hkbound.choose_spec s
    refine ⟨hs.choose, hs.choose_spec.1, ?_⟩
    intro m hm q hq a b hab z hz v
    exact hs.choose_spec.2 ⟨m, hm⟩ q hq a b hab
      ((RG m hm).parameter a b q hq) z (hsub hz) (hlow z hz) v

end ContinuousFlexibility.Analysis
