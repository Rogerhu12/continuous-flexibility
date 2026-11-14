module

public import ContinuousFlexibility.Radial.CentralRadialHilbert
public import ContinuousFlexibility.Radial.CentralRadialWeightedInverse

/-!
# The actual normalized central radial weak graph

The tests are genuine smooth compact functions. The source is arbitrary
Lebesgue L² data: multiplication of the source by `nu` is not a domain
assumption. The inverse weight is a bounded actual multiplier, justified
by the global lower bound from the constructed radius.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

set_option backward.isDefEq.respectTransparency false

private theorem centralEvenFrequency_pos (n : ℕ) (hn : 2 ≤ n) :
    (0 : ℝ) < 2 * (n : ℝ) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem centralRadialInverseWeight_abs_le (x : ℝ) :
    |(centralRadiusLogDerivative x)⁻¹| ≤ centralRadiusA⁻¹ := by
  rw [abs_inv, abs_of_pos (centralRadiusLogDerivative_pos x)]
  simpa only [one_div] using
    one_div_le_one_div_of_le centralRadiusA_pos (centralRadiusLogDerivative_gt x).le

def centralRadialInverseWeight : HermiteL2 →L[ℝ] HermiteL2 :=
  boundedScalarMultiplier (fun x => (centralRadiusLogDerivative x)⁻¹)
    contDiff_centralRadiusLogDerivative.continuous.measurable.inv
    centralRadiusA⁻¹ centralRadialInverseWeight_abs_le

theorem centralRadialInverseWeight_ae (h : HermiteL2) :
    (centralRadialInverseWeight h : ℝ → ℝ) =ᵐ[volume]
      (fun x => (centralRadiusLogDerivative x)⁻¹ * h x) :=
  boundedScalarMultiplier_ae _ _ _ _ h

theorem centralRadialInverseWeight_norm_le :
    ‖centralRadialInverseWeight‖ ≤ centralRadiusA⁻¹ :=
  boundedScalarMultiplier_norm_le _ _ _ (inv_nonneg.mpr centralRadiusA_pos.le) _

theorem centralRadialInverseWeight_inner_swap (f g : HermiteL2) :
    ⟪centralRadialInverseWeight f, g⟫_ℝ = ⟪f, centralRadialInverseWeight g⟫_ℝ :=
  boundedScalarMultiplier_inner_swap _ _ _ _ f g

theorem centralRadialInverseWeight_hasWeight (h : HermiteL2) :
    HasCentralRadialWeightL2 (centralRadialInverseWeight h) h := by
  filter_upwards [centralRadialInverseWeight_ae h] with x hx
  rw [hx]
  field_simp [(centralRadiusLogDerivative_pos x).ne']

theorem centralRadialInverseWeight_weighted {f wf : HermiteL2}
    (hw : HasCentralRadialWeightL2 f wf) : centralRadialInverseWeight wf = f := by
  apply Lp.ext
  filter_upwards [centralRadialInverseWeight_ae wf, hw] with x hq hwx
  rw [hq, hwx]
  exact inv_mul_cancel_left₀ (centralRadiusLogDerivative_pos x).ne' _

theorem centralRadialInverseWeight_injective : Function.Injective centralRadialInverseWeight := by
  intro f g h
  have hf := centralRadialInverseWeight_hasWeight f
  rw [h] at hf
  exact hf.unique (centralRadialInverseWeight_hasWeight g)

def centralRadialTestWeight (φ : ℝ → ℝ) (hs : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) : HermiteL2 :=
  (memLp_centralRadialWeight (compactSmooth_energyDomain hs hc).2.1
    (compactSmooth_energyDomain hs hc).2.2.2).toLp
      (fun x => centralRadiusLogDerivative x * φ x)

theorem centralRadialTestWeight_ae (φ : ℝ → ℝ) (hs : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    (centralRadialTestWeight φ hs hc : ℝ → ℝ) =ᵐ[volume]
      (fun x => centralRadiusLogDerivative x * φ x) := MemLp.coeFn_toLp _

theorem centralRadialTestWeight_hasWeight (φ : ℝ → ℝ) (hs : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    HasCentralRadialWeightL2 ((compactSmooth_energyDomain hs hc).2.1.toLp φ)
      (centralRadialTestWeight φ hs hc) := by
  filter_upwards [centralRadialTestWeight_ae φ hs hc,
    (compactSmooth_energyDomain hs hc).2.1.coeFn_toLp] with x hw hφ
  rw [hw, hφ]

theorem centralRadialInverseWeight_testWeight (φ : ℝ → ℝ) (hs : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    centralRadialInverseWeight (centralRadialTestWeight φ hs hc) =
      (compactSmooth_energyDomain hs hc).2.1.toLp φ :=
  centralRadialInverseWeight_weighted (centralRadialTestWeight_hasWeight φ hs hc)

def CentralRadialCompactWeakEquation (j : ℝ) (h F : HermiteL2) : Prop :=
  ∀ (φ : ℝ → ℝ) (hs : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
    ⟪centralRadialInverseWeight h,
      (compactSmooth_centralImage_memLp hs hc j).toLp
        (liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot φ)⟫_ℝ =
      12 * ⟪F, centralRadialTestWeight φ hs hc⟫_ℝ

def centralRadialClosedGraph (j : ℝ) : Submodule ℝ (HermiteL2 × HermiteL2) where
  carrier := {p | CentralRadialCompactWeakEquation j p.1 p.2}
  zero_mem' := by
    intro φ hs hc
    change ⟪centralRadialInverseWeight (0 : HermiteL2), _⟫_ℝ =
      12 * ⟪(0 : HermiteL2), _⟫_ℝ
    rw [map_zero, inner_zero_left, inner_zero_left]
    ring
  add_mem' := by
    intro p q hp hq φ hs hc
    change ⟪centralRadialInverseWeight (p.1 + q.1), _⟫_ℝ =
      12 * ⟪p.2 + q.2, _⟫_ℝ
    rw [map_add, inner_add_left, inner_add_left, hp φ hs hc, hq φ hs hc]
    ring
  smul_mem' := by
    intro a p hp φ hs hc
    change ⟪centralRadialInverseWeight (a • p.1), _⟫_ℝ = 12 * ⟪a • p.2, _⟫_ℝ
    rw [map_smul, real_inner_smul_left, real_inner_smul_left, hp φ hs hc]
    ring

theorem mem_centralRadialClosedGraph (j : ℝ) (h F : HermiteL2) :
    (h, F) ∈ centralRadialClosedGraph j ↔ CentralRadialCompactWeakEquation j h F := Iff.rfl

theorem centralRadialClosedGraph_isClosed (j : ℝ) :
    IsClosed (centralRadialClosedGraph j : Set (HermiteL2 × HermiteL2)) := by
  change IsClosed {p : HermiteL2 × HermiteL2 | ∀ (φ : ℝ → ℝ)
    (hs : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
      ⟪centralRadialInverseWeight p.1, (compactSmooth_centralImage_memLp hs hc j).toLp
        (liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot φ)⟫_ℝ =
        12 * ⟪p.2, centralRadialTestWeight φ hs hc⟫_ℝ}
  simp only [ofPred_forall]
  refine isClosed_iInter fun φ => isClosed_iInter fun hs => isClosed_iInter fun hc => ?_
  exact isClosed_eq
    ((centralRadialInverseWeight.continuous.comp continuous_fst).inner continuous_const)
    (continuous_const.mul (continuous_snd.inner continuous_const))

theorem centralRadialClosedGraph_completeSpace (j : ℝ) :
    CompleteSpace (centralRadialClosedGraph j) :=
  (centralRadialClosedGraph_isClosed j).isComplete.completeSpace_coe

private theorem radial_inner_toLp (u : HermiteL2) {φ : ℝ → ℝ}
    (hφ : MemLp φ 2 volume) :
    ⟪u, hφ.toLp φ⟫_ℝ = ∫ x, u x * φ x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hφ.coeFn_toLp] with x hx
  rw [hx]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

theorem centralRadialLeftInverse_testImage (n : ℕ) (hn : 2 ≤ n)
    (φ : ℝ → ℝ) (hs : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    centralRadialLeftInverse n hn
      ((compactSmooth_centralImage_memLp hs hc (2 * (n : ℝ))).toLp
        (liouvilleSchrodinger ((2 * (n : ℝ)) ^ 2) centralRadius centralDensityRoot φ)) =
      centralRadialTestWeight φ hs hc := by
  have hg := centralHilbertInverse_left n hn _ _
    (central_smooth_energy_graph (centralEvenFrequency_pos n hn)
      (compactSmooth_energyDomain hs hc) (compactSmooth_centralImage_memLp hs hc _))
  have hw := centralRadialLeftInverse_ae n hn
    ((compactSmooth_centralImage_memLp hs hc (2 * (n : ℝ))).toLp _)
  rw [hg] at hw
  exact hw.unique (centralRadialTestWeight_hasWeight φ hs hc)

theorem centralRadialInverseWeight_doubleInverse (n : ℕ) (hn : 2 ≤ n) (F : HermiteL2) :
    centralRadialInverseWeight (centralRadialDoubleInverse n hn F) =
      centralRadialRightInverse n hn F :=
  centralRadialInverseWeight_weighted (centralRadialDoubleInverse_ae n hn F)

/-- The bounded four-piece inverse solves the actual compact-test equation
for every L² source. -/
theorem centralRadialDoubleInverse_graph (n : ℕ) (hn : 2 ≤ n) (F : HermiteL2) :
    ((12 : ℝ) • centralRadialDoubleInverse n hn F, F) ∈
      centralRadialClosedGraph (2 * (n : ℝ)) := by
  intro φ hs hc
  rw [map_smul, centralRadialInverseWeight_doubleInverse, real_inner_smul_left,
    centralRadialRightInverse_inner_swap, centralRadialLeftInverse_testImage n hn φ hs hc]

private theorem radial_homogeneous_to_central {j : ℝ} (hj : 0 < j) (h : HermiteL2)
    (hw : (h, 0) ∈ centralRadialClosedGraph j) :
    (centralRadialInverseWeight h, 0) ∈ centralClosedGraph hj := by
  apply (centralClosedGraph_iff_compact_weak hj _ _).mpr
  intro φ hs hc
  rw [← radial_inner_toLp (0 : HermiteL2) (compactSmooth_energyDomain hs hc).2.1,
    ← radial_inner_toLp (centralRadialInverseWeight h) (compactSmooth_centralImage_memLp hs hc j)]
  have hz := hw φ hs hc
  simpa only [inner_zero_left, mul_zero] using hz.symm

theorem centralRadialClosedGraph_even_kernel_iff (n : ℕ) (hn : 2 ≤ n) (h : HermiteL2) :
    (h, 0) ∈ centralRadialClosedGraph (2 * (n : ℝ)) ↔ h = 0 := by
  constructor
  · intro hw
    have hq := (centralClosedGraph_even_kernel_iff n hn _).mp
      (radial_homogeneous_to_central (centralEvenFrequency_pos n hn) h hw)
    apply centralRadialInverseWeight_injective
    simpa only [map_zero] using hq
  · rintro rfl
    exact (centralRadialClosedGraph _).zero_mem

theorem mem_centralRadialClosedGraph_even_iff (n : ℕ) (hn : 2 ≤ n) (h F : HermiteL2) :
    (h, F) ∈ centralRadialClosedGraph (2 * (n : ℝ)) ↔
      h = (12 : ℝ) • centralRadialDoubleInverse n hn F := by
  constructor
  · intro hw
    have hz := (centralRadialClosedGraph (2 * (n : ℝ))).sub_mem hw
      (centralRadialDoubleInverse_graph n hn F)
    change (h - (12 : ℝ) • centralRadialDoubleInverse n hn F, F - F) ∈ _ at hz
    rw [sub_self] at hz
    exact sub_eq_zero.mp ((centralRadialClosedGraph_even_kernel_iff n hn _).mp hz)
  · rintro rfl
    exact centralRadialDoubleInverse_graph n hn F

private theorem compact_tests_total (F : HermiteL2)
    (hF : ∀ (φ : ℝ → ℝ) (hs : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
      ⟪F, (compactSmooth_energyDomain hs hc).2.1.toLp φ⟫_ℝ = 0) : F = 0 := by
  have hj : (0 : ℝ) < 1 := by norm_num
  have hn (n : ℕ) : ⟪F, hermiteL2Vector hj n⟫_ℝ = 0 := by
    have hl := ((innerSL ℝ F).continuous.tendsto (hermiteL2Vector hj n)).comp
      (compactHermiteFunction_tendsto_L2 hj n)
    have hz : Tendsto (fun N : ℕ =>
        ⟪F, (compactHermiteFunction_memLp 1 n N).toLp (compactHermiteFunction 1 n N)⟫_ℝ)
        atTop (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      exact Eventually.of_forall (fun N =>
        (hF _ (contDiff_compactHermiteFunction 1 n N)
          (compactHermiteFunction_hasCompactSupport 1 n N)).symm)
    exact tendsto_nhds_unique hl hz
  apply (hermiteCoefficientTransform hj).injective
  apply lp.ext
  funext n
  simp only [hermiteCoefficientTransform_apply]
  rw [← inner_hermiteL2Vector_right hj, ← inner_hermiteL2Vector_right hj, hn n,
    inner_zero_left]

theorem centralRadialClosedGraph_source_zero (j : ℝ) (F : HermiteL2)
    (hF : (0, F) ∈ centralRadialClosedGraph j) : F = 0 := by
  apply compact_tests_total F
  intro χ hs hc
  let φ : ℝ → ℝ := fun x => (centralRadiusLogDerivative x)⁻¹ * χ x
  have hφs : ContDiff ℝ ∞ φ :=
    (contDiff_centralRadiusLogDerivative.inv (fun x => (centralRadiusLogDerivative_pos x).ne')).mul hs
  have hφc : HasCompactSupport φ := hc.mul_left
  have hw : centralRadialTestWeight φ hφs hφc =
      (compactSmooth_energyDomain hs hc).2.1.toLp χ := by
    apply Lp.ext
    filter_upwards [centralRadialTestWeight_ae φ hφs hφc,
      (compactSmooth_energyDomain hs hc).2.1.coeFn_toLp] with x hw hx
    rw [hw, hx]
    dsimp [φ]
    field_simp [(centralRadiusLogDerivative_pos x).ne']
  have hh := hF φ hφs hφc
  rw [map_zero, inner_zero_left, hw] at hh
  linarith

theorem centralRadialClosedGraph_unique (j : ℝ) (h F G : HermiteL2)
    (hF : (h, F) ∈ centralRadialClosedGraph j)
    (hG : (h, G) ∈ centralRadialClosedGraph j) : F = G := by
  have hz := (centralRadialClosedGraph j).sub_mem hF hG
  change (h - h, F - G) ∈ centralRadialClosedGraph j at hz
  rw [sub_self] at hz
  exact sub_eq_zero.mp (centralRadialClosedGraph_source_zero j _ hz)

/-- Actual strong differential pairs map into the weak radial graph. This
is an implication, not a definition of the full radial domain. -/
theorem centralRadialClosedGraph_of_central {j : ℝ} (hj : 0 < j)
    (u v h : HermiteL2) (huv : (u, v) ∈ centralClosedGraph hj)
    (hw : HasCentralRadialWeightL2 u h) :
    (h, (1 / 12 : ℝ) • centralRadialInverseWeight v) ∈ centralRadialClosedGraph j := by
  intro φ hs hc
  rw [centralRadialInverseWeight_weighted hw, real_inner_smul_left,
    centralRadialInverseWeight_inner_swap, centralRadialInverseWeight_testWeight]
  have hp := central_smooth_energy_graph hj (compactSmooth_energyDomain hs hc)
    (compactSmooth_centralImage_memLp hs hc j)
  have he := centralClosedGraph_symmetric hj u v _ _ huv hp
  linarith

def centralRadialStrongGraphMap (n : ℕ) (hn : 2 ≤ n) :
    (HermiteL2 × HermiteL2) →L[ℝ] (HermiteL2 × HermiteL2) :=
  ((centralRadialLeftInverse n hn).comp (ContinuousLinearMap.snd ℝ HermiteL2 HermiteL2)).prod
    (((1 / 12 : ℝ) • centralRadialInverseWeight).comp
      (ContinuousLinearMap.snd ℝ HermiteL2 HermiteL2))

theorem centralRadialStrongGraphMap_apply (n : ℕ) (hn : 2 ≤ n) (p : HermiteL2 × HermiteL2) :
    centralRadialStrongGraphMap n hn p =
      (centralRadialLeftInverse n hn p.2, (1 / 12 : ℝ) • centralRadialInverseWeight p.2) := rfl

theorem centralRadialStrongGraphMap_test (n : ℕ) (hn : 2 ≤ n)
    (φ : ℝ → ℝ) (hs : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    centralRadialStrongGraphMap n hn
      ((compactSmooth_energyDomain hs hc).2.1.toLp φ,
        (compactSmooth_centralImage_memLp hs hc (2 * (n : ℝ))).toLp
          (liouvilleSchrodinger ((2 * (n : ℝ)) ^ 2) centralRadius centralDensityRoot φ)) =
      (centralRadialTestWeight φ hs hc, (1 / 12 : ℝ) • centralRadialInverseWeight
        ((compactSmooth_centralImage_memLp hs hc (2 * (n : ℝ))).toLp
          (liouvilleSchrodinger ((2 * (n : ℝ)) ^ 2) centralRadius centralDensityRoot φ))) := by
  rw [centralRadialStrongGraphMap_apply, centralRadialLeftInverse_testImage n hn φ hs hc]

/-- Its carrier is proved below to be precisely the graph of actual smooth
compact functions, with normalized input `nu*φ` and output `Hφ/(12*nu)`. -/
def centralRadialCompactSmoothGraph (n : ℕ) (hn : 2 ≤ n) :
    Submodule ℝ (HermiteL2 × HermiteL2) :=
  (centralCompactSmoothGraph (2 * (n : ℝ))).map (centralRadialStrongGraphMap n hn).toLinearMap

theorem mem_centralRadialCompactSmoothGraph (n : ℕ) (hn : 2 ≤ n) (p : HermiteL2 × HermiteL2) :
    p ∈ centralRadialCompactSmoothGraph n hn ↔
      ∃ (φ : ℝ → ℝ) (hs : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
        p = (centralRadialTestWeight φ hs hc, (1 / 12 : ℝ) • centralRadialInverseWeight
          ((compactSmooth_centralImage_memLp hs hc (2 * (n : ℝ))).toLp
            (liouvilleSchrodinger ((2 * (n : ℝ)) ^ 2) centralRadius centralDensityRoot φ))) := by
  constructor
  · rintro ⟨q, hq, hp⟩
    rcases (mem_centralCompactSmoothGraph _ q).mp hq with ⟨φ, hs, hc, rfl⟩
    change centralRadialStrongGraphMap n hn _ = p at hp
    rw [centralRadialStrongGraphMap_test n hn φ hs hc] at hp
    exact ⟨φ, hs, hc, hp.symm⟩
  · rintro ⟨φ, hs, hc, rfl⟩
    exact ⟨_, (mem_centralCompactSmoothGraph _ _).mpr ⟨φ, hs, hc, rfl⟩,
      centralRadialStrongGraphMap_test n hn φ hs hc⟩

theorem centralRadialCompactSmoothGraph_le (n : ℕ) (hn : 2 ≤ n) :
    centralRadialCompactSmoothGraph n hn ≤ centralRadialClosedGraph (2 * (n : ℝ)) := by
  intro p hp
  rcases (mem_centralRadialCompactSmoothGraph n hn p).mp hp with ⟨φ, hs, hc, rfl⟩
  exact centralRadialClosedGraph_of_central (centralEvenFrequency_pos n hn) _ _ _
    (central_smooth_energy_graph (centralEvenFrequency_pos n hn)
      (compactSmooth_energyDomain hs hc) (compactSmooth_centralImage_memLp hs hc _))
    (centralRadialTestWeight_hasWeight φ hs hc)

theorem centralRadialStrongGraphMap_mem_closure (n : ℕ) (hn : 2 ≤ n)
    (p : HermiteL2 × HermiteL2)
    (hp : p ∈ centralClosedGraph (centralEvenFrequency_pos n hn)) :
    centralRadialStrongGraphMap n hn p ∈ (centralRadialCompactSmoothGraph n hn).topologicalClosure := by
  have hm := (centralCompactSmoothGraph (2 * (n : ℝ))).topologicalClosure_map
    (centralRadialStrongGraphMap n hn)
  rw [centralCompactSmoothGraph_closure (centralEvenFrequency_pos n hn)] at hm
  exact hm ⟨p, hp, rfl⟩

private theorem centralRadial_core_basis (n : ℕ) (hn : 2 ≤ n) (m : ℕ) :
    ((12 : ℝ) • centralRadialDoubleInverse n hn (hermiteL2Vector (centralEvenFrequency_pos n hn) m),
      hermiteL2Vector (centralEvenFrequency_pos n hn) m) ∈
        (centralRadialCompactSmoothGraph n hn).topologicalClosure := by
  let e := hermiteL2Vector (centralEvenFrequency_pos n hn) m
  let xe := centralHermitePositionVector (centralEvenFrequency_pos n hn) m
  let we := centralRadialBMultiplier e + centralRadialCMultiplier xe
  have hw : HasCentralRadialWeightL2 e we :=
    centralRadialWeight_of_position e xe (centralHermitePositionVector_ae _ m)
  have hL : centralRadialLeftInverse n hn we = centralRadialDoubleInverse n hn e :=
    (centralRadialLeftInverse_ae n hn we).unique (centralRadialDoubleInverse_weighted n hn e we hw)
  have hp := centralRadialStrongGraphMap_mem_closure n hn
    (centralHilbertInverse n hn we, we) (centralHilbertInverse_graph n hn we)
  rw [centralRadialStrongGraphMap_apply] at hp
  have ht := (centralRadialCompactSmoothGraph n hn).topologicalClosure.smul_mem (12 : ℝ) hp
  simpa only [Prod.smul_mk, hL, centralRadialInverseWeight_weighted hw, smul_smul,
    show (12 : ℝ) * (1 / 12) = 1 by norm_num, one_smul] using ht

/-- Genuine compact smooth differential pairs are a core of the full
normalized weak graph, including all L² sources. -/
theorem centralRadialCompactSmoothGraph_closure (n : ℕ) (hn : 2 ≤ n) :
    (centralRadialCompactSmoothGraph n hn).topologicalClosure =
      centralRadialClosedGraph (2 * (n : ℝ)) := by
  apply le_antisymm
  · exact (centralRadialCompactSmoothGraph n hn).topologicalClosure_minimal
      (centralRadialCompactSmoothGraph_le n hn) (centralRadialClosedGraph_isClosed _)
  · let J : HermiteL2 →L[ℝ] (HermiteL2 × HermiteL2) :=
      ((12 : ℝ) • centralRadialDoubleInverse n hn).prod (ContinuousLinearMap.id ℝ HermiteL2)
    let S : Submodule ℝ HermiteL2 :=
      (centralRadialCompactSmoothGraph n hn).topologicalClosure.comap J.toLinearMap
    have hS : IsClosed (S : Set HermiteL2) :=
      (centralRadialCompactSmoothGraph n hn).isClosed_topologicalClosure.preimage J.continuous
    have hs : Submodule.span ℝ (Set.range (hermiteL2Vector (centralEvenFrequency_pos n hn))) ≤ S := by
      apply Submodule.span_le.mpr
      rintro _ ⟨m, rfl⟩
      exact centralRadial_core_basis n hn m
    have htop : (⊤ : Submodule ℝ HermiteL2) ≤ S := by
      rw [← hermiteL2Vector_dense_span (centralEvenFrequency_pos n hn)]
      exact (Submodule.span ℝ (Set.range (hermiteL2Vector (centralEvenFrequency_pos n hn)))).topologicalClosure_minimal hs hS
    rintro ⟨h, F⟩ hp
    have hh := (mem_centralRadialClosedGraph_even_iff n hn h F).mp hp
    have hf := htop (show F ∈ (⊤ : Submodule ℝ HermiteL2) from trivial)
    change ((12 : ℝ) • centralRadialDoubleInverse n hn F, F) ∈
      (centralRadialCompactSmoothGraph n hn).topologicalClosure at hf
    simpa only [hh] using hf

def centralRadialHilbertInverse (n : ℕ) (hn : 2 ≤ n) : HermiteL2 →L[ℝ] HermiteL2 :=
  (12 : ℝ) • centralRadialDoubleInverse n hn

theorem centralRadialHilbertInverse_norm_le (n : ℕ) (hn : 2 ≤ n) :
    ‖centralRadialHilbertInverse n hn‖ ≤ 12 * centralRadialDoubleConstant := by
  rw [centralRadialHilbertInverse, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 12)]
  exact mul_le_mul_of_nonneg_left (centralRadialDoubleInverse_norm_le n hn) (by norm_num)

def centralRadialGroundVector : HermiteL2 := hermiteL2Vector (by norm_num : (0 : ℝ) < 2) 0

def centralRadialKernelVector : HermiteL2 :=
  centralRadialBMultiplier centralRadialGroundVector +
    centralRadialCMultiplier (centralHermitePositionVector (by norm_num : (0 : ℝ) < 2) 0)

def centralRadialKernelDual : HermiteL2 := centralRadialInverseWeight centralRadialGroundVector

theorem centralRadialKernelVector_hasWeight :
    HasCentralRadialWeightL2 centralRadialGroundVector centralRadialKernelVector :=
  centralRadialWeight_of_position _ _ (centralHermitePositionVector_ae (by norm_num) 0)

theorem centralRadialInverseWeight_kernel :
    centralRadialInverseWeight centralRadialKernelVector = centralRadialGroundVector :=
  centralRadialInverseWeight_weighted centralRadialKernelVector_hasWeight

theorem centralRadialKernel_pairing :
    ⟪centralRadialKernelDual, centralRadialKernelVector⟫_ℝ = 1 := by
  rw [centralRadialKernelDual, centralRadialInverseWeight_inner_swap,
    centralRadialInverseWeight_kernel]
  exact hermiteL2Vector_inner (by norm_num) 0 0

private theorem centralRadial_ground_graph :
    (centralRadialGroundVector, 0) ∈ centralClosedGraph (by norm_num : (0 : ℝ) < 2) := by
  have h := centralClosedGraph_eigenpair (by norm_num : (0 : ℝ) < 2) 0
  simpa only [centralRadialGroundVector, centralSpectralLevel_two, Nat.cast_zero, mul_zero, zero_smul] using h

theorem centralRadialKernelVector_graph :
    (centralRadialKernelVector, 0) ∈ centralRadialClosedGraph 2 := by
  have h := centralRadialClosedGraph_of_central (by norm_num : (0 : ℝ) < 2)
    _ _ _ centralRadial_ground_graph centralRadialKernelVector_hasWeight
  simpa only [map_zero, smul_zero] using h

theorem centralRadialClosedGraph_two_kernel_iff (h : HermiteL2) :
    (h, 0) ∈ centralRadialClosedGraph 2 ↔
      ∃ c : ℝ, h = c • centralRadialKernelVector := by
  constructor
  · intro hw
    rcases (centralClosedGraph_two_kernel_iff _).mp
      (radial_homogeneous_to_central (by norm_num : (0 : ℝ) < 2) h hw) with ⟨c, hc⟩
    refine ⟨c, centralRadialInverseWeight_injective ?_⟩
    rw [map_smul, centralRadialInverseWeight_kernel]
    exact hc
  · rintro ⟨c, rfl⟩
    simpa only [Prod.smul_mk, smul_zero] using
      (centralRadialClosedGraph 2).smul_mem c centralRadialKernelVector_graph

theorem centralRadialReducedLeftInverse_testImage
    (φ : ℝ → ℝ) (hs : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    centralRadialReducedLeftInverse ((compactSmooth_centralImage_memLp hs hc 2).toLp
        (liouvilleSchrodinger (2 ^ 2) centralRadius centralDensityRoot φ)) =
      centralRadialTestWeight φ hs hc -
        ⟪(compactSmooth_energyDomain hs hc).2.1.toLp φ, centralRadialGroundVector⟫_ℝ •
          centralRadialKernelVector := by
  apply centralRadialInverseWeight_injective
  rw [centralRadialInverseWeight_weighted (centralRadialReducedLeftInverse_ae _),
    map_sub, map_smul, centralRadialInverseWeight_testWeight, centralRadialInverseWeight_kernel]
  rw [centralReducedHilbertInverse_left_projected _ _
    (central_smooth_energy_graph (by norm_num : (0 : ℝ) < 2)
      (compactSmooth_energyDomain hs hc) (compactSmooth_centralImage_memLp hs hc 2)),
    centralGroundProjection_apply]
  rw [show centralRadialGroundVector = hermiteL2Vector (by norm_num : (0 : ℝ) < 2) 0 from rfl,
    inner_hermiteL2Vector_right]

def centralRadialTwoGraphWeight : (HermiteL2 × HermiteL2) →L[ℝ] HermiteL2 :=
  centralRadialReducedLeftInverse.comp (ContinuousLinearMap.snd ℝ HermiteL2 HermiteL2) +
    ((hermiteCoefficientCLM (by norm_num : (0 : ℝ) < 2) 0).smulRight
      centralRadialKernelVector).comp (ContinuousLinearMap.fst ℝ HermiteL2 HermiteL2)

theorem centralRadialTwoGraphWeight_apply (p : HermiteL2 × HermiteL2) :
    centralRadialTwoGraphWeight p = centralRadialReducedLeftInverse p.2 +
      hermiteCoefficient 2 p.1 0 • centralRadialKernelVector := by
  change centralRadialReducedLeftInverse p.2 +
    hermiteCoefficientCLM (by norm_num : (0 : ℝ) < 2) 0 p.1 • centralRadialKernelVector = _
  rw [hermiteCoefficientCLM_apply]

theorem centralRadialTwoGraphWeight_test
    (φ : ℝ → ℝ) (hs : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    centralRadialTwoGraphWeight ((compactSmooth_energyDomain hs hc).2.1.toLp φ,
      (compactSmooth_centralImage_memLp hs hc 2).toLp
        (liouvilleSchrodinger (2 ^ 2) centralRadius centralDensityRoot φ)) =
      centralRadialTestWeight φ hs hc := by
  rw [centralRadialTwoGraphWeight_apply, centralRadialReducedLeftInverse_testImage φ hs hc]
  rw [show centralRadialGroundVector = hermiteL2Vector (by norm_num : (0 : ℝ) < 2) 0 from rfl,
    inner_hermiteL2Vector_right]
  abel

theorem centralRadialTwoGraphWeight_ground :
    centralRadialTwoGraphWeight (centralRadialGroundVector, 0) = centralRadialKernelVector := by
  rw [centralRadialTwoGraphWeight_apply, map_zero]
  simp only [centralRadialGroundVector, hermiteCoefficient_hermiteL2Vector, ite_true, one_smul, zero_add]

theorem centralRadialClosedGraph_two_compat (h F : HermiteL2)
    (hw : (h, F) ∈ centralRadialClosedGraph 2) : ⟪F, centralRadialKernelVector⟫_ℝ = 0 := by
  let L : (HermiteL2 × HermiteL2) →L[ℝ] ℝ :=
    (innerSL ℝ (centralRadialInverseWeight h)).comp (ContinuousLinearMap.snd ℝ HermiteL2 HermiteL2) -
      (12 : ℝ) • (innerSL ℝ F).comp centralRadialTwoGraphWeight
  have hcore : centralCompactSmoothGraph 2 ≤ L.ker := by
    intro p hp
    rcases (mem_centralCompactSmoothGraph 2 p).mp hp with ⟨φ, hs, hc, rfl⟩
    change ⟪centralRadialInverseWeight h, _⟫_ℝ - 12 * ⟪F, centralRadialTwoGraphWeight _⟫_ℝ = 0
    rw [centralRadialTwoGraphWeight_test φ hs hc]
    exact sub_eq_zero.mpr (hw φ hs hc)
  have hclosed := (centralCompactSmoothGraph 2).topologicalClosure_minimal hcore L.isClosed_ker
  rw [centralCompactSmoothGraph_closure (by norm_num : (0 : ℝ) < 2)] at hclosed
  have hg := hclosed centralRadial_ground_graph
  change ⟪centralRadialInverseWeight h, (0 : HermiteL2)⟫_ℝ -
    12 * ⟪F, centralRadialTwoGraphWeight (centralRadialGroundVector, 0)⟫_ℝ = 0 at hg
  rw [inner_zero_right, centralRadialTwoGraphWeight_ground] at hg
  linarith

/-- This is the actual oblique source correction. Its complementary kernel
direction is `Q e0`, not the radial orthogonal projection onto `nu e0`. -/
def centralRadialObliqueSource : HermiteL2 →L[ℝ] HermiteL2 :=
  ContinuousLinearMap.id ℝ HermiteL2 -
    (innerSL ℝ centralRadialKernelVector).smulRight centralRadialKernelDual

theorem centralRadialObliqueSource_apply (F : HermiteL2) :
    centralRadialObliqueSource F = F - ⟪F, centralRadialKernelVector⟫_ℝ • centralRadialKernelDual := by
  change F - ⟪centralRadialKernelVector, F⟫_ℝ • centralRadialKernelDual = _
  rw [real_inner_comm]

theorem centralRadialObliqueSource_compat (F : HermiteL2) :
    ⟪centralRadialObliqueSource F, centralRadialKernelVector⟫_ℝ = 0 := by
  rw [centralRadialObliqueSource_apply, inner_sub_left, real_inner_smul_left,
    centralRadialKernel_pairing]
  ring

def centralRadialReducedHilbertInverse : HermiteL2 →L[ℝ] HermiteL2 :=
  (12 : ℝ) • centralRadialReducedDoubleInverse

theorem centralRadialReducedHilbertInverse_graph (F : HermiteL2) :
    (centralRadialReducedHilbertInverse F, centralRadialObliqueSource F) ∈ centralRadialClosedGraph 2 := by
  intro φ hs hc
  change ⟪centralRadialInverseWeight ((12 : ℝ) • centralRadialReducedDoubleInverse F), _⟫_ℝ = _
  rw [map_smul, centralRadialInverseWeight_weighted (centralRadialReducedDoubleInverse_ae F),
    real_inner_smul_left, centralRadialReducedRightInverse_inner_swap,
    centralRadialReducedLeftInverse_testImage φ hs hc, centralRadialObliqueSource_apply,
    inner_sub_right, real_inner_smul_right, inner_sub_left, real_inner_smul_left]
  rw [centralRadialKernelDual, centralRadialInverseWeight_inner_swap,
    centralRadialInverseWeight_testWeight, real_inner_comm centralRadialGroundVector]
  ring

theorem centralRadialReducedHilbertInverse_graph_compatible (F : HermiteL2)
    (hF : ⟪F, centralRadialKernelVector⟫_ℝ = 0) :
    (centralRadialReducedHilbertInverse F, F) ∈ centralRadialClosedGraph 2 := by
  have h := centralRadialReducedHilbertInverse_graph F
  simpa only [centralRadialObliqueSource_apply, hF, zero_smul, sub_zero] using h

theorem mem_centralRadialClosedGraph_two_iff (h F : HermiteL2) :
    (h, F) ∈ centralRadialClosedGraph 2 ↔
      ⟪F, centralRadialKernelVector⟫_ℝ = 0 ∧
        ∃ c : ℝ, h = centralRadialReducedHilbertInverse F + c • centralRadialKernelVector := by
  constructor
  · intro hw
    have hF := centralRadialClosedGraph_two_compat h F hw
    have hz := (centralRadialClosedGraph 2).sub_mem hw
      (centralRadialReducedHilbertInverse_graph_compatible F hF)
    change (h - centralRadialReducedHilbertInverse F, F - F) ∈ centralRadialClosedGraph 2 at hz
    rw [sub_self] at hz
    rcases (centralRadialClosedGraph_two_kernel_iff _).mp hz with ⟨c, hc⟩
    refine ⟨hF, c, ?_⟩
    exact sub_eq_iff_eq_add'.mp hc
  · rintro ⟨hF, c, rfl⟩
    have h := (centralRadialClosedGraph 2).add_mem
      (centralRadialReducedHilbertInverse_graph_compatible F hF)
      ((centralRadialClosedGraph_two_kernel_iff _).mpr ⟨c, rfl⟩)
    simpa only [Prod.add_def, add_zero] using h

theorem centralRadialInverseWeight_twoGraphWeight (p : HermiteL2 × HermiteL2)
    (hp : p ∈ centralClosedGraph (by norm_num : (0 : ℝ) < 2)) :
    centralRadialInverseWeight (centralRadialTwoGraphWeight p) = p.1 := by
  rw [centralRadialTwoGraphWeight_apply, map_add, map_smul,
    centralRadialInverseWeight_weighted (centralRadialReducedLeftInverse_ae _),
    centralRadialInverseWeight_kernel, centralReducedHilbertInverse_left_projected _ _ hp,
    centralGroundProjection_apply, centralRadialGroundVector]
  abel

def centralRadialTwoStrongGraphMap : (HermiteL2 × HermiteL2) →L[ℝ] (HermiteL2 × HermiteL2) :=
  centralRadialTwoGraphWeight.prod
    (((1 / 12 : ℝ) • centralRadialInverseWeight).comp (ContinuousLinearMap.snd ℝ HermiteL2 HermiteL2))

def centralRadialTwoCompactSmoothGraph : Submodule ℝ (HermiteL2 × HermiteL2) :=
  (centralCompactSmoothGraph 2).map centralRadialTwoStrongGraphMap.toLinearMap

theorem mem_centralRadialTwoCompactSmoothGraph (p : HermiteL2 × HermiteL2) :
    p ∈ centralRadialTwoCompactSmoothGraph ↔
      ∃ (φ : ℝ → ℝ) (hs : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
        p = (centralRadialTestWeight φ hs hc, (1 / 12 : ℝ) • centralRadialInverseWeight
          ((compactSmooth_centralImage_memLp hs hc 2).toLp
            (liouvilleSchrodinger (2 ^ 2) centralRadius centralDensityRoot φ))) := by
  constructor
  · rintro ⟨q, hq, hp⟩
    rcases (mem_centralCompactSmoothGraph 2 q).mp hq with ⟨φ, hs, hc, rfl⟩
    change (centralRadialTwoGraphWeight _, _) = p at hp
    rw [centralRadialTwoGraphWeight_test φ hs hc] at hp
    exact ⟨φ, hs, hc, hp.symm⟩
  · rintro ⟨φ, hs, hc, rfl⟩
    refine ⟨_, (mem_centralCompactSmoothGraph 2 _).mpr ⟨φ, hs, hc, rfl⟩, ?_⟩
    apply Prod.ext
    · exact centralRadialTwoGraphWeight_test φ hs hc
    · rfl

private theorem radial_two_strong_mem_closure (p : HermiteL2 × HermiteL2)
    (hp : p ∈ centralClosedGraph (by norm_num : (0 : ℝ) < 2)) :
    centralRadialTwoStrongGraphMap p ∈ centralRadialTwoCompactSmoothGraph.topologicalClosure := by
  have hm := (centralCompactSmoothGraph 2).topologicalClosure_map centralRadialTwoStrongGraphMap
  rw [centralCompactSmoothGraph_closure (by norm_num : (0 : ℝ) < 2)] at hm
  exact hm ⟨p, hp, rfl⟩

private theorem radial_two_core_weighted (F wf : HermiteL2)
    (hw : HasCentralRadialWeightL2 F wf) (hF : ⟪F, centralRadialKernelVector⟫_ℝ = 0) :
    (centralRadialReducedHilbertInverse F, F) ∈ centralRadialTwoCompactSmoothGraph.topologicalClosure := by
  have hc : hermiteCoefficient 2 wf 0 = 0 := by
    rw [← inner_hermiteL2Vector_right (by norm_num : (0 : ℝ) < 2)]
    change ⟪wf, centralRadialGroundVector⟫_ℝ = 0
    rw [← centralRadialInverseWeight_kernel, ← centralRadialInverseWeight_inner_swap,
      centralRadialInverseWeight_weighted hw]
    exact hF
  have hp := radial_two_strong_mem_closure (centralReducedHilbertInverse wf, wf)
    (centralReducedHilbertInverse_graph wf hc)
  change (centralRadialTwoGraphWeight (centralReducedHilbertInverse wf, wf),
    (1 / 12 : ℝ) • centralRadialInverseWeight wf) ∈ _ at hp
  rw [centralRadialTwoGraphWeight_apply, centralReducedHilbertInverse_zero_coefficient,
    zero_smul, add_zero, centralRadialInverseWeight_weighted hw] at hp
  have hL : centralRadialReducedLeftInverse wf = centralRadialReducedDoubleInverse F :=
    (centralRadialReducedLeftInverse_ae wf).unique (centralRadialReducedDoubleInverse_weighted F wf hw)
  have ht := centralRadialTwoCompactSmoothGraph.topologicalClosure.smul_mem (12 : ℝ) hp
  simpa only [Prod.smul_mk, hL, smul_smul, show (12 : ℝ) * (1 / 12) = 1 by norm_num,
    one_smul, centralRadialReducedHilbertInverse, smul_apply] using ht

/-- The genuine compact smooth graph is a core also in mode two. The
source correction is oblique, and the kernel component is retained. -/
theorem centralRadialTwoCompactSmoothGraph_closure :
    centralRadialTwoCompactSmoothGraph.topologicalClosure = centralRadialClosedGraph 2 := by
  apply le_antisymm
  · apply centralRadialTwoCompactSmoothGraph.topologicalClosure_minimal _ (centralRadialClosedGraph_isClosed 2)
    intro p hp
    rcases (mem_centralRadialTwoCompactSmoothGraph p).mp hp with ⟨φ, hs, hc, rfl⟩
    exact centralRadialClosedGraph_of_central (by norm_num : (0 : ℝ) < 2) _ _ _
      (central_smooth_energy_graph (by norm_num : (0 : ℝ) < 2)
        (compactSmooth_energyDomain hs hc) (compactSmooth_centralImage_memLp hs hc 2))
      (centralRadialTestWeight_hasWeight φ hs hc)
  · let J : HermiteL2 →L[ℝ] (HermiteL2 × HermiteL2) :=
      centralRadialReducedHilbertInverse.prod (ContinuousLinearMap.id ℝ HermiteL2)
    let S : Submodule ℝ HermiteL2 := centralRadialTwoCompactSmoothGraph.topologicalClosure.comap
      (J.comp centralRadialObliqueSource).toLinearMap
    have hS : IsClosed (S : Set HermiteL2) :=
      centralRadialTwoCompactSmoothGraph.isClosed_topologicalClosure.preimage
        (J.comp centralRadialObliqueSource).continuous
    have hs : Submodule.span ℝ (Set.range (hermiteL2Vector (by norm_num : (0 : ℝ) < 2))) ≤ S := by
      apply Submodule.span_le.mpr
      rintro _ ⟨m, rfl⟩
      let e := hermiteL2Vector (by norm_num : (0 : ℝ) < 2) m
      let we := centralRadialBMultiplier e +
        centralRadialCMultiplier (centralHermitePositionVector (by norm_num : (0 : ℝ) < 2) m)
      have hw : HasCentralRadialWeightL2 e we :=
        centralRadialWeight_of_position _ _ (centralHermitePositionVector_ae (by norm_num) m)
      let wf := we - ⟪e, centralRadialKernelVector⟫_ℝ • centralRadialGroundVector
      have hq : centralRadialInverseWeight wf = centralRadialObliqueSource e := by
        rw [map_sub, map_smul, centralRadialInverseWeight_weighted hw,
          centralRadialObliqueSource_apply]
        simp only [centralRadialKernelDual]
      have hwe := centralRadialInverseWeight_hasWeight wf
      rw [hq] at hwe
      exact radial_two_core_weighted _ _ hwe (centralRadialObliqueSource_compat e)
    have htop : (⊤ : Submodule ℝ HermiteL2) ≤ S := by
      rw [← hermiteL2Vector_dense_span (by norm_num : (0 : ℝ) < 2)]
      exact (Submodule.span ℝ (Set.range (hermiteL2Vector (by norm_num : (0 : ℝ) < 2)))).topologicalClosure_minimal hs hS
    have hk := radial_two_strong_mem_closure _ centralRadial_ground_graph
    change (centralRadialTwoGraphWeight (centralRadialGroundVector, 0),
      (1 / 12 : ℝ) • centralRadialInverseWeight 0) ∈ _ at hk
    rw [centralRadialTwoGraphWeight_ground, map_zero, smul_zero] at hk
    rintro ⟨h, F⟩ hp
    rcases (mem_centralRadialClosedGraph_two_iff h F).mp hp with ⟨hF, c, rfl⟩
    have hf := htop (show F ∈ (⊤ : Submodule ℝ HermiteL2) from trivial)
    simp only [S, Submodule.mem_comap, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      J, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply] at hf
    rw [centralRadialObliqueSource_apply, hF, zero_smul, sub_zero] at hf
    simpa only [Prod.add_def, Prod.smul_mk, smul_zero, add_zero] using
      centralRadialTwoCompactSmoothGraph.topologicalClosure.add_mem hf
        (centralRadialTwoCompactSmoothGraph.topologicalClosure.smul_mem c hk)

private theorem centralRadialReducedLeftInverse_ground :
    centralRadialReducedLeftInverse centralRadialGroundVector = 0 := by
  have hg : centralReducedHilbertInverse centralRadialGroundVector = 0 := by
    apply ext_inner_right ℝ
    intro g
    rw [inner_zero_left, centralReducedHilbertInverse_inner_swap,
      real_inner_comm (centralReducedHilbertInverse g) centralRadialGroundVector]
    change ⟪centralReducedHilbertInverse g, hermiteL2Vector (by norm_num : (0 : ℝ) < 2) 0⟫_ℝ = 0
    rw [inner_hermiteL2Vector_right]
    exact centralReducedHilbertInverse_zero_coefficient g
  apply centralRadialInverseWeight_injective
  rw [centralRadialInverseWeight_weighted (centralRadialReducedLeftInverse_ae _), hg, map_zero]

/-- The reduced output has its actual oblique row fixed. This row is not
the orthogonality row against the radial kernel `nu*e0`. -/
theorem centralRadialReducedHilbertInverse_row (F : HermiteL2) :
    ⟪centralRadialReducedHilbertInverse F, centralRadialKernelDual⟫_ℝ = 0 := by
  change ⟪(12 : ℝ) • centralRadialReducedDoubleInverse F,
    centralRadialInverseWeight centralRadialGroundVector⟫_ℝ = 0
  rw [← centralRadialInverseWeight_inner_swap, map_smul,
    centralRadialInverseWeight_weighted (centralRadialReducedDoubleInverse_ae F),
    real_inner_smul_left, centralRadialReducedRightInverse_inner_swap,
    centralRadialReducedLeftInverse_ground, inner_zero_right, mul_zero]

theorem centralRadialReducedHilbertInverse_unique (h F : HermiteL2)
    (hw : (h, F) ∈ centralRadialClosedGraph 2)
    (hr : ⟪h, centralRadialKernelDual⟫_ℝ = 0) : h = centralRadialReducedHilbertInverse F := by
  rcases (mem_centralRadialClosedGraph_two_iff h F).mp hw with ⟨_, c, rfl⟩
  rw [inner_add_left, real_inner_smul_left, centralRadialReducedHilbertInverse_row,
    real_inner_comm centralRadialKernelDual centralRadialKernelVector, centralRadialKernel_pairing] at hr
  have hc : c = 0 := by linarith
  rw [hc, zero_smul, add_zero]

end ContinuousFlexibility.Radial
