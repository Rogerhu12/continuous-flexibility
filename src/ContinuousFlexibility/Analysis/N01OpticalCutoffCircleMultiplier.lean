module

public import ContinuousFlexibility.Analysis.CircleComponentMultiplier
public import ContinuousFlexibility.Analysis.N01ControlIndexBound
public import ContinuousFlexibility.Analysis.MaterialSampleRadialLoss

/-!
# The actual optical cutoff jets cost one fixed circle weight

Each fixed radial jet of the selected cutoff grows by a fixed power of
its actual containing-cell radial weight. N01 controls that cell index
by the original control label. One material sample weight therefore
absorbs the entire radial cost, independently of the radial jet order
and of the selected radii.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.opticalCutoff_iteratedDeriv_le_sample_M
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (χ : ℕ → ℝ → ℝ)
    (hcutoff : ∀ k : ℕ, ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m r,
      |iteratedDeriv k (χ m) r| ≤ A * radialE (D.cellIndex (j m)) ^ P) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m r,
      |iteratedDeriv k (χ m) r| ≤ K * T.M (T.sample m) := by
  obtain ⟨A, P, hA, hP, hbound⟩ := hcutoff k
  obtain ⟨B, hB, hindex⟩ := hN.control_actual_cell_index_bound hS hT
  obtain ⟨L, hL, hradial⟩ :=
    materialSample_radialE_rpow_le_M_of_index_bound hT hN.1.1 hB hP
  refine ⟨A * L, mul_nonneg hA hL.le, fun m r => ?_⟩
  calc
    _ ≤ A * radialE (D.cellIndex (j m)) ^ P := hbound m r
    _ ≤ A * (L * T.M (T.sample m)) :=
      mul_le_mul_of_nonneg_left
        (hradial m (D.cellIndex (j m)) (hindex m (j m) (hcell m))) hA
    _ = _ := by ring

def N01Properties.opticalCutoffJetCircleLinear
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (χ : ℕ → ℝ → ℝ)
    (hcutoff : ∀ k : ℕ, ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m r,
      |iteratedDeriv k (χ m) r| ≤ A * radialE (D.cellIndex (j m)) ^ P)
    (k : ℕ) (rsel : ℕ → ℝ) : CircleSpace S →ₗ[ℝ] CircleSpace S :=
  let h := hN.opticalCutoff_iteratedDeriv_le_sample_M hS hT j hcell χ hcutoff k
  circleComponentMultiplierLinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1
    (fun m => iteratedDeriv k (χ m) (rsel m)) 1 h.choose h.choose_spec.1
    (fun m => by simpa only [pow_one] using h.choose_spec.2 m (rsel m))

theorem N01Properties.opticalCutoffJetCircleLinear_decode
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (χ : ℕ → ℝ → ℝ)
    (hcutoff : ∀ k : ℕ, ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m r,
      |iteratedDeriv k (χ m) r| ≤ A * radialE (D.cellIndex (j m)) ^ P)
    (k : ℕ) (rsel : ℕ → ℝ) (u : CircleSpace S) :
    (S.circle (3 / 4 : ℝ)).decode
        (hN.opticalCutoffJetCircleLinear hS hT j hcell χ hcutoff k rsel u) =
      fun m θ => iteratedDeriv k (χ m) (rsel m) * (S.circle (3 / 4 : ℝ)).decode u m θ := by
  unfold N01Properties.opticalCutoffJetCircleLinear
  exact circleComponentMultiplierLinear_decode _ _ _ _ _ _ _ _ u

theorem N01Properties.opticalCutoffJetCircleLinear_uniform_bound
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (χ : ℕ → ℝ → ℝ)
    (hcutoff : ∀ k : ℕ, ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m r,
      |iteratedDeriv k (χ m) r| ≤ A * radialE (D.cellIndex (j m)) ^ P)
    (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ rsel s u,
      (S.circle (3 / 4 : ℝ)).grading s
        (hN.opticalCutoffJetCircleLinear hS hT j hcell χ hcutoff k rsel u) ≤
      K * (S.circle (3 / 4 : ℝ)).grading (s + 1) u := by
  let h := hN.opticalCutoff_iteratedDeriv_le_sample_M hS hT j hcell χ hcutoff k
  refine ⟨h.choose, h.choose_spec.1, fun rsel s u => ?_⟩
  exact circleComponentMultiplierLinear_grading_le
    (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1
    (fun m => iteratedDeriv k (χ m) (rsel m)) 1 h.choose h.choose_spec.1
    (fun m => by simpa only [pow_one] using h.choose_spec.2 m (rsel m)) s u

theorem N01Properties.smoothTameOn_opticalCutoffJetCircleLinear
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (χ : ℕ → ℝ → ℝ)
    (hcutoff : ∀ k : ℕ, ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m r,
      |iteratedDeriv k (χ m) r| ≤ A * radialE (D.cellIndex (j m)) ^ P)
    (k : ℕ) (rsel : ℕ → ℝ) :
    SmoothTameOn (S.circle (3 / 4 : ℝ)).grading (S.circle (3 / 4 : ℝ)).grading univ
      (hN.opticalCutoffJetCircleLinear hS hT j hcell χ hcutoff k rsel) := by
  unfold N01Properties.opticalCutoffJetCircleLinear
  exact smoothTameOn_circleComponentMultiplierLinear _ _ _ _ _ _ _ _

end ContinuousFlexibility.Statements
