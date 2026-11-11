import ContinuousFlexibility.Scalar.WeightedDecodedProductMap

/-! # The literal two-factor decoder, without finite-product elaboration -/

noncomputable section

namespace ContinuousFlexibility.Statements.SobolevModelData

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

theorem decode_decodedProductMap_two
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 ≤ γ)
    (u : Fin 2 → A.Space) :
    A.decode (decodedProductMap hT hA hinterp hγ 1 u) =
      fun p => A.decode (u 0) p * A.decode (u 1) p := by
  apply (decode_decodedProductMap hT hA hinterp hγ 1 u).trans
  funext p
  exact Fin.prod_univ_two (fun i : Fin 2 => A.decode (u i) p)

end ContinuousFlexibility.Statements.SobolevModelData
