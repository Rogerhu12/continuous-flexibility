module

public import ContinuousFlexibility.Radial.OscillatorWeakEnergy
public import ContinuousFlexibility.Radial.OscillatorPhysicalFormBasis
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# The operator associated with the actual closed physical energy form

The form domain is the proved complete Hilbert subspace of genuine weak
energy triples. Its associated equation quantifies over every element of
that physical space. Riesz representation is then applied to its actual
bounded source functional. The association is not defined by a spectral
graph or by the image of an inverse.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace InnerProductSpace

set_option backward.isDefEq.respectTransparency false

def physicalFormFunctional (j : ℝ) (f : HermiteL2) :
    StrongDual ℝ (PhysicalEnergySpace j) :=
  (innerSL ℝ f).comp (physicalEnergyBase j)

def physicalFormRepresentative (j : ℝ) (f : HermiteL2) : PhysicalEnergySpace j :=
  (InnerProductSpace.toDual ℝ (PhysicalEnergySpace j)).symm (physicalFormFunctional j f)

theorem physicalFormRepresentative_pairing (j : ℝ) (f : HermiteL2)
    (V : PhysicalEnergySpace j) :
    ⟪physicalFormRepresentative j f, V⟫_ℝ = ⟪f, physicalEnergyBase j V⟫_ℝ :=
  InnerProductSpace.toDual_symm_apply

theorem physicalFormRepresentative_unique (j : ℝ) (f : HermiteL2)
    (Z : PhysicalEnergySpace j)
    (hZ : ∀ V : PhysicalEnergySpace j, ⟪Z, V⟫_ℝ = ⟪f, physicalEnergyBase j V⟫_ℝ) :
    Z = physicalFormRepresentative j f := by
  apply (InnerProductSpace.toDual ℝ (PhysicalEnergySpace j)).injective
  ext V
  change ⟪Z, V⟫_ℝ = ⟪physicalFormRepresentative j f, V⟫_ℝ
  rw [hZ V, physicalFormRepresentative_pairing]

theorem physicalEnergyBase_opNorm_le (j : ℝ) : ‖physicalEnergyBase j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro Z
  simpa only [physicalEnergyBase, one_mul] using physicalEnergyCoordinate_norm_le j 0 Z

theorem physicalFormFunctional_norm_le (j : ℝ) (f : HermiteL2) :
    ‖physicalFormFunctional j f‖ ≤ ‖f‖ := by
  calc
    _ ≤ ‖innerSL ℝ f‖ * ‖physicalEnergyBase j‖ :=
      (innerSL ℝ f).opNorm_comp_le (physicalEnergyBase j)
    _ ≤ ‖f‖ * 1 := by
      rw [innerSL_apply_norm]
      exact mul_le_mul_of_nonneg_left (physicalEnergyBase_opNorm_le j) (norm_nonneg f)
    _ = ‖f‖ := mul_one _

theorem physicalFormRepresentative_norm_le (j : ℝ) (f : HermiteL2) :
    ‖physicalFormRepresentative j f‖ ≤ ‖f‖ := by
  change ‖(InnerProductSpace.toDual ℝ (PhysicalEnergySpace j)).symm
    (physicalFormFunctional j f)‖ ≤ _
  rw [(InnerProductSpace.toDual ℝ (PhysicalEnergySpace j)).symm.norm_map]
  exact physicalFormFunctional_norm_le j f

theorem physicalFormRepresentative_base_norm_le (j : ℝ) (f : HermiteL2) :
    ‖physicalEnergyBase j (physicalFormRepresentative j f)‖ ≤ ‖f‖ :=
  (physicalEnergyCoordinate_norm_le j 0 _).trans (physicalFormRepresentative_norm_le j f)

/-- The actual variational equation for the central differential operator,
with its explicit positive shift removed from the source. -/
def PhysicalClosedFormEquation (j : ℝ) (u v : HermiteL2) : Prop :=
  ∃ Z : PhysicalEnergySpace j,
    physicalEnergyBase j Z = u ∧
      ∀ V : PhysicalEnergySpace j,
        ⟪Z, V⟫_ℝ = ⟪v + centralEnergyShift j • u, physicalEnergyBase j V⟫_ℝ

def physicalClosedFormGraph (j : ℝ) : Submodule ℝ (HermiteL2 × HermiteL2) where
  carrier := {p | PhysicalClosedFormEquation j p.1 p.2}
  zero_mem' := by
    refine ⟨0, by simp, ?_⟩
    intro V
    simp
  add_mem' := by
    intro p q hp hq
    rcases hp with ⟨Z, hZu, hZ⟩
    rcases hq with ⟨W, hWu, hW⟩
    refine ⟨Z + W, ?_, ?_⟩
    · change physicalEnergyBase j (Z + W) = p.1 + q.1
      rw [map_add, hZu, hWu]
    · intro V
      change ⟪Z + W, V⟫_ℝ =
        ⟪p.2 + q.2 + centralEnergyShift j • (p.1 + q.1), physicalEnergyBase j V⟫_ℝ
      have hsum : p.2 + q.2 + centralEnergyShift j • (p.1 + q.1) =
          (p.2 + centralEnergyShift j • p.1) + (q.2 + centralEnergyShift j • q.1) := by
        simp only [smul_add, add_assoc, add_left_comm]
      rw [hsum, inner_add_left, inner_add_left, hZ V, hW V]
  smul_mem' := by
    intro a p hp
    rcases hp with ⟨Z, hZu, hZ⟩
    refine ⟨a • Z, ?_, ?_⟩
    · change physicalEnergyBase j (a • Z) = a • p.1
      rw [map_smul, hZu]
    · intro V
      change ⟪a • Z, V⟫_ℝ =
        ⟪a • p.2 + centralEnergyShift j • (a • p.1), physicalEnergyBase j V⟫_ℝ
      have hsmul : a • p.2 + centralEnergyShift j • (a • p.1) =
          a • (p.2 + centralEnergyShift j • p.1) := by
        rw [smul_add, smul_comm (centralEnergyShift j) a p.1]
      rw [hsmul, real_inner_smul_left, real_inner_smul_left, hZ V]

theorem mem_physicalClosedFormGraph_iff (j : ℝ) (u v : HermiteL2) :
    (u, v) ∈ physicalClosedFormGraph j ↔ PhysicalClosedFormEquation j u v := Iff.rfl

/-- The Riesz representative gives an equivalent criterion only after the
association has been defined by its genuine variational identity. -/
theorem physicalClosedFormEquation_iff_representative (j : ℝ) (u v : HermiteL2) :
    PhysicalClosedFormEquation j u v ↔
      physicalEnergyBase j (physicalFormRepresentative j (v + centralEnergyShift j • u)) = u := by
  constructor
  · rintro ⟨Z, hbase, hZ⟩
    rw [← physicalFormRepresentative_unique j _ Z hZ]
    exact hbase
  · intro hbase
    refine ⟨physicalFormRepresentative j (v + centralEnergyShift j • u), hbase, ?_⟩
    intro V
    exact physicalFormRepresentative_pairing j _ V


private theorem closedForm_inner_toLp_right (u : HermiteL2)
    {φ : ℝ → ℝ} (hφ : MemLp φ 2 volume) :
    ⟪u, hφ.toLp φ⟫_ℝ = ∫ x : ℝ, u x * φ x :=
  (real_inner_comm _ _).trans (physicalTestPairing_apply φ hφ u)

theorem PhysicalClosedFormEquation.mem_centralClosedGraph
    {j : ℝ} (hj : 0 < j) {u v : HermiteL2}
    (h : PhysicalClosedFormEquation j u v) :
    (u, v) ∈ centralClosedGraph hj := by
  rcases h with ⟨Z, hbase, hform⟩
  apply (centralClosedGraph_iff_compact_weak hj u v).mpr
  intro φ hs hc
  have hh := hform (physicalEnergyLift j (compactSmooth_energyDomain hs hc))
  rw [physicalEnergy_inner_compact_operator j Z φ hs hc, physicalEnergyLift_base,
    inner_add_left, real_inner_smul_left, hbase] at hh
  have heq :
      ⟪v, (compactSmooth_energyDomain hs hc).2.1.toLp φ⟫_ℝ =
        ⟪u, (compactSmooth_centralImage_memLp hs hc j).toLp
          (liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot φ)⟫_ℝ :=
    (add_right_cancel hh).symm
  rw [closedForm_inner_toLp_right, closedForm_inner_toLp_right] at heq
  exact heq

theorem physicalClosedFormEquation_of_mem_centralClosedGraph
    {j : ℝ} (hj : 0 < j) (u v : HermiteL2)
    (huv : (u, v) ∈ centralClosedGraph hj) :
    PhysicalClosedFormEquation j u v := by
  let Z := physicalFormRepresentative j (v + centralEnergyShift j • u)
  have hgraph := (mem_centralClosedGraph_iff hj u v).mp huv
  have hcoeff : ∀ n : ℕ,
      hermiteCoefficient j (physicalEnergyBase j Z) n = hermiteCoefficient j u n := by
    intro n
    have hh := physicalFormRepresentative_pairing j (v + centralEnergyShift j • u)
      (physicalHermiteLift hj n)
    rw [physicalEnergy_inner_hermite, physicalHermiteLift_base, inner_add_left,
      real_inner_smul_left, inner_hermiteL2Vector_right,
      inner_hermiteL2Vector_right, hgraph n] at hh
    have hw : centralSpectralLevel j n + centralEnergyShift j =
        physicalHermiteWeight j n := centralEnergyShift_level j n
    rw [← add_mul, hw] at hh
    exact mul_left_cancel₀ (physicalHermiteWeight_pos hj n).ne' hh
  have hbase : physicalEnergyBase j Z = u := by
    apply (hermiteCoefficientTransform hj).injective
    apply lp.ext
    funext n
    rw [hermiteCoefficientTransform_apply, hermiteCoefficientTransform_apply]
    exact hcoeff n
  refine ⟨Z, hbase, ?_⟩
  intro V
  exact physicalFormRepresentative_pairing j _ V

theorem physicalClosedFormEquation_iff_centralClosedGraph
    {j : ℝ} (hj : 0 < j) (u v : HermiteL2) :
    PhysicalClosedFormEquation j u v ↔ (u, v) ∈ centralClosedGraph hj :=
  ⟨fun h => h.mem_centralClosedGraph hj,
    physicalClosedFormEquation_of_mem_centralClosedGraph hj u v⟩

theorem physicalClosedFormGraph_eq_centralClosedGraph {j : ℝ} (hj : 0 < j) :
    physicalClosedFormGraph j = centralClosedGraph hj := by
  apply Submodule.ext
  rintro ⟨u, v⟩
  exact physicalClosedFormEquation_iff_centralClosedGraph hj u v

theorem physicalClosedFormGraph_isClosed {j : ℝ} (hj : 0 < j) :
    IsClosed (physicalClosedFormGraph j : Set (HermiteL2 × HermiteL2)) := by
  rw [physicalClosedFormGraph_eq_centralClosedGraph hj]
  exact centralClosedGraph_isClosed hj

theorem physicalClosedFormEquation_unique {j : ℝ} (hj : 0 < j)
    (u v w : HermiteL2) (hv : PhysicalClosedFormEquation j u v)
    (hw : PhysicalClosedFormEquation j u w) : v = w :=
  centralClosedGraph_unique hj u v w (hv.mem_centralClosedGraph hj)
    (hw.mem_centralClosedGraph hj)

theorem physicalClosedFormEquation_domain_iff {j : ℝ} (hj : 0 < j) (u : HermiteL2) :
    (∃ v : HermiteL2, PhysicalClosedFormEquation j u v) ↔
      Memℓp (fun n : ℕ => centralSpectralLevel j n * hermiteCoefficient j u n) 2 := by
  simpa only [physicalClosedFormEquation_iff_centralClosedGraph hj] using
    centralClosedGraph_domain_iff hj u

end ContinuousFlexibility.Radial
