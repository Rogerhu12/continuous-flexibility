import ContinuousFlexibility.Analysis.N01ReturnLinearOperators
import ContinuousFlexibility.Analysis.N02ChartIncrement
import ContinuousFlexibility.Analysis.N02ChartError
import ContinuousFlexibility.Analysis.N02ProjectiveChartVariation
import ContinuousFlexibility.Analysis.ReturnChartIdentities

/-!
# Assembly of the actual N02 return equation

A circle-valued realization of the actual residual and its genuine
smooth tame tower determine all remaining fields of the frozen return
equation. The Fourier inverse has the fixed loss already proved from
N01, and the variation identity holds in the full projective topology.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

theorem N01Properties.exists_returnEquation_of_smoothTame_residual
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (f : AnnularState S × ℝ → CircleSpace S)
    (hdecode : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ m θ,
      (S.circle (3 / 4 : ℝ)).decode (f z) m θ = returnResidualField S C z m θ)
    (htame : SmoothTameOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun z => f (liftSectorParameter S C z))) :
    ∃ R : ReturnEquationData S, R.residual = f ∧ N02Properties D T S C R base ε := by
  obtain ⟨L, J, hL, hright, hleft, hJ⟩ := hN.returnLinearOperators hS hT
  rcases htame with ⟨K, hK⟩
  let R : ReturnEquationData S :=
    { residual := f
      linearPart := L
      inverse := J
      chartIncrement := actualChartIncrement hS hT hN.1.1
      error := fun z => actualChartError hS hT hN.1.1 C (f z) }
  refine ⟨R, rfl, ?_⟩
  refine ⟨?_, hdecode, ?_, hL, ?_, ?_, ?_, hright, hleft, ⟨4, 0, hJ⟩, ⟨K, hK⟩⟩
  · intro z hz hs m θ
    have hi := hN.2.2.2.2.2.2.2.2.1 z hz hs m θ
    exact ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2,
      N01Properties.rightChart_deriv_pos S C z m hN hz hs θ⟩
  · intro z hz hs
    exact N01Properties.residual_eq_zero_iff_returns S C z hN hS R hz hs
      (hdecode z hz hs)
  · intro z hz hs r v m θ
    exact actualChartError_decode hS hT hN.1.1 C z (f z)
      (by funext i t; exact hdecode z hz hs i t) r v m θ
  · intro z hz hs v m θ
    exact actualChartIncrement_decode hS hT hN.1.1 z v m θ
  · intro z hz hs v hv
    apply hN.hasProjectiveLineDerivAt_returnResidual_chartDirection hS hT f K hdecode
      hz hs (R.chartIncrement z v) v (R.linearPart v + R.error z (R.residual z) v) hv
    · intro m θ
      exact actualChartIncrement_decode hS hT hN.1.1 z v m θ
    · intro m θ
      change (S.circle (3 / 4 : ℝ)).decode
        (L v + actualChartError hS hT hN.1.1 C (f z) (f z) v) m θ = _
      rw [map_add]
      simp only [Pi.add_apply]
      rw [hL v m θ, actualChartError_decode hS hT hN.1.1 C z (f z)
        (by funext i t; exact hdecode z hz hs i t)]

end ContinuousFlexibility.Statements
