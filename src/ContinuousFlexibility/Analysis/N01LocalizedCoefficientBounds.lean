module

public import ContinuousFlexibility.Analysis.N01CoefficientValueJets
public import ContinuousFlexibility.Analysis.OneHighCircleFlowLocalization
public import ContinuousFlexibility.Analysis.PhysicalTransmissionTrace
public import ContinuousFlexibility.Analysis.SpacesCylinderEvenJets
public import ContinuousFlexibility.Analysis.SolveReturnEquations

/-!
# Uniform actual coefficient jets on one physical cell strip

The radial clamp is fixed before the state. Reference jets are bounded
on a compact interval and are angularly constant. The actual N01
coefficient-difference estimate then bounds all selected coefficient
jets on the inner strip. Constants may depend on the fixed cell and
spatial order; the state base and loss remain exactly those of N01.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem mixedDerivative_angle_independent {f : PolarPoint → ℝ}
    (hf : ∀ r θ : ℝ, f (r, θ) = f (r, 0)) (a b : ℕ) (r θ : ℝ) :
    mixedDerivative a b f (r, θ) = mixedDerivative a b f (r, 0) := by
  have hs (x : ℝ) : (fun η : ℝ => f (x, η)) = fun _ : ℝ => f (x, 0) :=
    funext (hf x)
  unfold mixedDerivative
  simp_rw [hs]
  simp only [iteratedDeriv_const]

private theorem exists_reference_coefficient_jet_bound
    (K : Fin 3 → PolarPoint → ℝ)
    (hK : ∀ i, ContDiff ℝ ∞ (K i))
    (hangle : ∀ i r θ, K i (r, θ) = K i (r, 0))
    (l u : ℝ) (s : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i : Fin 3, ∀ a b : ℕ, a + b ≤ s →
      ∀ q : PolarPoint, q.1 ∈ Icc l u → |mixedDerivative a b (K i) q| ≤ M := by
  let J : ℝ → ℝ := fun r =>
    ∑ i : Fin 3, ∑ a : Fin (s + 1), ∑ b : Fin (s + 1),
      |mixedDerivative a b (K i) (r, 0)|
  have hJ : Continuous J :=
    continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun a _ =>
      continuous_finsetSum _ (fun b _ =>
        (((contDiff_mixedDerivative (hK i) a b).continuous).comp
          (continuous_id.prodMk continuous_const)).abs)))
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc l u)).exists_bound_of_continuousOn
    hJ.continuousOn
  refine ⟨|M|, abs_nonneg _, ?_⟩
  intro i a b hab q hq
  have ha : a < s + 1 := by omega
  have hb : b < s + 1 := by omega
  have ht : |mixedDerivative a b (K i) (q.1, 0)| ≤ J q.1 := by
    calc
      _ ≤ ∑ j : Fin (s + 1), |mixedDerivative a j (K i) (q.1, 0)| := by
        exact Finset.single_le_sum
          (f := fun j : Fin (s + 1) => |mixedDerivative a j (K i) (q.1, 0)|)
          (fun j _ => abs_nonneg _)
          (Finset.mem_univ (⟨b, hb⟩ : Fin (s + 1)))
      _ ≤ ∑ k : Fin (s + 1), ∑ j : Fin (s + 1),
          |mixedDerivative k j (K i) (q.1, 0)| := by
        exact Finset.single_le_sum
          (f := fun k : Fin (s + 1) => ∑ j : Fin (s + 1),
            |mixedDerivative k j (K i) (q.1, 0)|)
          (fun k _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
          (Finset.mem_univ (⟨a, ha⟩ : Fin (s + 1)))
      _ ≤ J q.1 := by
        exact Finset.single_le_sum
          (f := fun k : Fin 3 => ∑ a : Fin (s + 1), ∑ b : Fin (s + 1),
            |mixedDerivative a b (K k) (q.1, 0)|)
          (fun k _ => Finset.sum_nonneg (fun a _ =>
            Finset.sum_nonneg (fun b _ => abs_nonneg _))) (Finset.mem_univ i)
  have hr : |mixedDerivative a b (K i) q| =
      |mixedDerivative a b (K i) (q.1, 0)| :=
    congrArg abs (mixedDerivative_angle_independent (hangle i) a b q.1 q.2)
  have hJM : J q.1 ≤ M := (le_abs_self _).trans
    (by simpa only [Real.norm_eq_abs] using hM q.1 hq)
  exact hr.trans_le (ht.trans (hJM.trans (le_abs_self M)))

/-- Add the reference jets to a genuine difference estimate over an
abstract state type. The reference compactness constant is selected before
the state, and no projective-space instance is unfolded in the algebra. -/
private theorem exists_coefficient_jet_bound_of_difference
    {E : Type*} (K : E → Fin 3 → PolarPoint → ℝ) (zref : E)
    (U : Set E) (P : E → Prop) (w : E → ℝ) (l u : ℝ) (s : ℕ) (B : ℝ)
    (hw : ∀ z, 0 ≤ w z)
    (hK : ∀ z ∈ U, P z → ∀ i, ContDiff ℝ ∞ (K z i))
    (hKref : ∀ i, ContDiff ℝ ∞ (K zref i))
    (hangle : ∀ i r θ, K zref i (r, θ) = K zref i (r, 0))
    (hdifference : ∀ z ∈ U, P z → ∀ i : Fin 3, ∀ a b : ℕ, a + b ≤ s →
      ∀ q ∈ Ioo l u ×ˢ (univ : Set ℝ),
        |mixedDerivative a b (fun x => K z i x - K zref i x) q| ≤
          B * (1 + w z)) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ z ∈ U, P z → ∀ i : Fin 3,
      ∀ a b : ℕ, a + b ≤ s → ∀ q ∈ Ioo l u ×ˢ (univ : Set ℝ),
        |mixedDerivative a b (K z i) q| ≤ A * (1 + w z) := by
  obtain ⟨M, hM, hreference⟩ := exists_reference_coefficient_jet_bound
    (K zref) hKref hangle l u s
  refine ⟨1 + M + |B|, by linarith [abs_nonneg B], ?_⟩
  intro z hz hP i a b hab q hq
  have hH : 1 ≤ 1 + w z := le_add_of_nonneg_right (hw z)
  have hH0 : 0 ≤ 1 + w z := zero_le_one.trans hH
  have hdiff : |mixedDerivative a b (fun x => K z i x - K zref i x) q| ≤
      |B| * (1 + w z) :=
    (hdifference z hz hP i a b hab q hq).trans
      (mul_le_mul_of_nonneg_right (le_abs_self B) hH0)
  have href : |mixedDerivative a b (K zref i) q| ≤ M * (1 + w z) :=
    (hreference i a b hab q ⟨hq.1.1.le, hq.1.2.le⟩).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hH hM)
  have he : (fun x => (K z i x - K zref i x) + K zref i x) = K z i := by
    funext x
    ring
  have hsum := spaces_mixedDerivative_add
    ((hK z hz hP i).sub (hKref i)) (hKref i) a b q
  rw [he] at hsum
  calc
    |mixedDerivative a b (K z i) q| ≤
        |mixedDerivative a b (fun x => K z i x - K zref i x) q| +
          |mixedDerivative a b (K zref i) q| := by
      rw [hsum]
      exact abs_add_le _ _
    _ ≤ |B| * (1 + w z) + M * (1 + w z) := add_le_add hdiff href
    _ ≤ (1 + M + |B|) * (1 + w z) := by nlinarith only [hH0]

/-- A concrete globally smooth extension obtained with the same radial
clamp for every state and each of the three actual coefficients. -/
def localizedOriginalCoefficient (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) {l u ρ : ℝ} (hlu : l ≤ u) (hρ : 0 < ρ)
    (z : AnnularState S × ℝ) (i : Fin 3) : PolarPoint → ℝ :=
  circleFlowLocalizedSpeed (canonicalCoefficientComponent i (originalCoefficients D S C z))
    hlu hρ

theorem contDiff_localizedOriginalCoefficient
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    {l u ρ : ℝ} (hlu : l ≤ u) (hρ : 0 < ρ)
    (hphysical : Ioo (l - ρ) (u + ρ) ⊆ Ioo D.a D.b)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (i : Fin 3) :
    ContDiff ℝ ∞ (localizedOriginalCoefficient D S C hlu hρ z i) :=
  contDiff_circleFlowLocalizedSpeed hlu hρ
    ((contDiffOn_originalCoefficientComponent_of_n01 hS hT hN hz hsector i).mono
      (fun _ hq => ⟨hphysical hq.1, hq.2⟩))

theorem localizedOriginalCoefficient_eqOn
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    {l u ρ : ℝ} (hlu : l ≤ u) (hρ : 0 < ρ)
    (z : AnnularState S × ℝ) (i : Fin 3) :
    EqOn (localizedOriginalCoefficient D S C hlu hρ z i)
      (canonicalCoefficientComponent i (originalCoefficients D S C z))
      (Ioo l u ×ˢ (univ : Set ℝ)) := by
  intro q hq
  exact circleFlowLocalizedSpeed_eq hlu hρ ⟨hq.1.1.le, hq.1.2.le⟩ q.2

/-- The clamp is the identity on the inner strip. Thus its actual
difference jets are exactly the frozen coefficient-family jets. The
component selector is normalized explicitly before identifying them. -/
private theorem localizedOriginalCoefficient_difference_jet
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    {l u ρ : ℝ} (hlu : l ≤ u) (hρ : 0 < ρ)
    (z : AnnularState S × ℝ) (i : Fin 3) (a b : ℕ) {q : PolarPoint}
    (hq : q ∈ Ioo l u ×ˢ (univ : Set ℝ)) :
    mixedDerivative a b
      (fun x => localizedOriginalCoefficient D S C hlu hρ z i x -
        localizedOriginalCoefficient D S C hlu hρ (C.referenceState, 0) i x) q =
      coefficientFamily D S C i a b q z := by
  have hmatch : EqOn
      (fun x => localizedOriginalCoefficient D S C hlu hρ z i x -
        localizedOriginalCoefficient D S C hlu hρ (C.referenceState, 0) i x)
      (fun x => canonicalCoefficientComponent i (originalCoefficients D S C z) x -
        canonicalCoefficientComponent i
          (originalCoefficients D S C (C.referenceState, 0)) x)
      (Ioo l u ×ˢ (univ : Set ℝ)) := by
    intro x hx
    change localizedOriginalCoefficient D S C hlu hρ z i x -
        localizedOriginalCoefficient D S C hlu hρ (C.referenceState, 0) i x =
      canonicalCoefficientComponent i (originalCoefficients D S C z) x -
        canonicalCoefficientComponent i
          (originalCoefficients D S C (C.referenceState, 0)) x
    rw [localizedOriginalCoefficient_eqOn D S C hlu hρ z i hx,
      localizedOriginalCoefficient_eqOn D S C hlu hρ (C.referenceState, 0) i hx]
  calc
    _ = mixedDerivative a b
        (fun x => canonicalCoefficientComponent i (originalCoefficients D S C z) x -
          canonicalCoefficientComponent i
            (originalCoefficients D S C (C.referenceState, 0)) x) q :=
      mixedDerivative_eqOn_of_isOpen (isOpen_Ioo.prod isOpen_univ) hmatch a b hq
    _ = _ := by
      unfold coefficientFamily canonicalCoefficientComponent
      split_ifs <;> rfl

/-- One fixed-order coefficient estimate, with the complete state body
named before existential elimination. This is exactly the estimate used
by the public fixed-loss theorem below. -/
def LocalizedOriginalCoefficientBoundAtOrder
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base loss : ℕ) (ε : ℝ) {l u ρ : ℝ} (hlu : l ≤ u) (hρ : 0 < ρ)
    (s : ℕ) (A : ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε,
    stateSector S z.1 → ∀ i : Fin 3, ∀ a b : ℕ, a + b ≤ s →
    ∀ q ∈ Ioo l u ×ˢ (univ : Set ℝ),
      |mixedDerivative a b (localizedOriginalCoefficient D S C hlu hρ z i) q| ≤
        A * (1 + pairGrading (stateGrading S) realGrading (s + loss)
          (z - (C.referenceState, 0)))

private theorem localizedOriginalCoefficient_reference_smooth
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    {l u ρ : ℝ} (hlu : l ≤ u) (hρ : 0 < ρ)
    (hphysical : Ioo (l - ρ) (u + ρ) ⊆ Ioo D.a D.b)
    (i : Fin 3) :
    ContDiff ℝ ∞
      (localizedOriginalCoefficient D S C hlu hρ (C.referenceState, 0) i) :=
  contDiff_localizedOriginalCoefficient hS hT hN hlu hρ hphysical
    (reference_mem_stateNeighborhood S C base hN.2.1) hN.2.2.1.stateSector i

private theorem localizedOriginalCoefficient_reference_angle
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    {l u ρ : ℝ} (hlu : l ≤ u) (hρ : 0 < ρ)
    (i : Fin 3) (r θ : ℝ) :
    localizedOriginalCoefficient D S C hlu hρ (C.referenceState, 0) i (r, θ) =
      localizedOriginalCoefficient D S C hlu hρ (C.referenceState, 0) i (r, 0) := by
  change canonicalCoefficientComponent i
      (originalCoefficients D S C (C.referenceState, 0))
      (circleFlowSmoothTimeClamp l u ρ hlu hρ r, θ) =
    canonicalCoefficientComponent i
      (originalCoefficients D S C (C.referenceState, 0))
      (circleFlowSmoothTimeClamp l u ρ hlu hρ r, 0)
  exact originalCoefficientComponent_zeroParameter_angle_invariant D S C C.referenceState i
    (circleFlowSmoothTimeClamp l u ρ hlu hρ r) θ 0

private theorem localizedOriginalCoefficient_difference_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    {l u ρ : ℝ} (hlu : l ≤ u) (hρ : 0 < ρ)
    (m : ℕ) (hcell : Ioo l u ⊆ D.cells m) (s : ℕ) (B : ℝ)
    (hbound : N01CoefficientValueBoundAtOrder D T S C base loss ε s B)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (i : Fin 3) (a b : ℕ) (hab : a + b ≤ s) {q : PolarPoint}
    (hq : q ∈ Ioo l u ×ˢ (univ : Set ℝ)) :
    |mixedDerivative a b
      (fun x => localizedOriginalCoefficient D S C hlu hρ z i x -
        localizedOriginalCoefficient D S C hlu hρ (C.referenceState, 0) i x) q| ≤
      (B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B) *
        (1 + pairGrading (stateGrading S) realGrading (s + loss)
          (z - (C.referenceState, 0))) :=
  (congrArg abs
    (localizedOriginalCoefficient_difference_jet D S C hlu hρ z i a b hq)).trans_le
      (hbound m i a b q hab (hcell hq.1) z hz)

private theorem localizedOriginalCoefficient_bound_of_value_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    {l u ρ : ℝ} (hlu : l ≤ u) (hρ : 0 < ρ)
    (hphysical : Ioo (l - ρ) (u + ρ) ⊆ Ioo D.a D.b)
    (m : ℕ) (hcell : Ioo l u ⊆ D.cells m) (s : ℕ) (B : ℝ)
    (hbound : N01CoefficientValueBoundAtOrder D T S C base loss ε s B) :
    ∃ A : ℝ, 1 ≤ A ∧
      LocalizedOriginalCoefficientBoundAtOrder D S C base loss ε hlu hρ s A := by
  exact exists_coefficient_jet_bound_of_difference
    (E := AnnularState S × ℝ)
    (localizedOriginalCoefficient D S C hlu hρ) (C.referenceState, 0)
    (stateNeighborhood S C base ε) (fun z => stateSector S z.1)
    (fun z => pairGrading (stateGrading S) realGrading (s + loss)
      (z - (C.referenceState, 0)))
    l u s (B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B)
    (fun z => apply_nonneg _ _)
    (fun z hz hs i => contDiff_localizedOriginalCoefficient
      hS hT hN hlu hρ hphysical hz hs i)
    (localizedOriginalCoefficient_reference_smooth hS hT hN hlu hρ hphysical)
    (localizedOriginalCoefficient_reference_angle D S C hlu hρ)
    (fun z hz _ i a b hab q hq =>
      localizedOriginalCoefficient_difference_bound hlu hρ m hcell s B hbound hz i a b hab hq)

/-- The common N01 loss controls actual total coefficient jets on any
fixed inner strip lying in one actual radial cell. The constant is
selected before the state, component selector, derivative split, and
point. It may depend on this cell and strip; no component-uniform
reference constant is asserted. -/
theorem localizedOriginalCoefficient_fixed_loss_bound_of_n01
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    {l u ρ : ℝ} (hlu : l ≤ u) (hρ : 0 < ρ)
    (hphysical : Ioo (l - ρ) (u + ρ) ⊆ Ioo D.a D.b)
    (m : ℕ) (hcell : Ioo l u ⊆ D.cells m) (s : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧
      LocalizedOriginalCoefficientBoundAtOrder D S C base loss ε hlu hρ s A := by
  obtain ⟨B, _hB, hbound⟩ := coefficientFamily_value_bound_of_n01 hN s
  exact localizedOriginalCoefficient_bound_of_value_bound
    hS hT hN hlu hρ hphysical m hcell s B hbound

end ContinuousFlexibility.Analysis
