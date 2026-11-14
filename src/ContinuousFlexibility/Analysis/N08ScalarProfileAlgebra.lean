module

public import ContinuousFlexibility.Analysis.N08MixedWeightProduct
public import ContinuousFlexibility.Analysis.N08ScalarFormula
public import ContinuousFlexibility.Scalar.WeightedScalarCandidates

/-!
# The scalar residual with a weaker profile weight

The profile perturbation may have any nonnegative physical weight. Each
term of the residual also contains a height jet of weight `3/4`, so the
mixed product retains the required source weight. The construction uses
the existing height derivatives, including the cutoff constant, and the
actual odd-jet products.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData} {γ : ℝ}
variable (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
  (hS : IsPhysicalSpaces D T S) (hγ : 0 ≤ γ)

def n08ProfileWAct (m : (S.height γ).Space) (u : ScalarHeightSpace S) :
    ScalarHeightSpace S :=
  scalarReferenceWCLM hD hT hS (u + n08MixedWeightAction hT hS hγ scalarBeta m u)

def n08ProfileEnergyAct (m : (S.height γ).Space) (u : ScalarHeightSpace S) :
    ScalarHeightSpace S :=
  u + n08ProfileWAct hD hT hS hγ m (n08ProfileWAct hD hT hS hγ m u)

def n08ProfileWDerivAct (m : (S.height γ).Space) (u : ScalarHeightSpace S) :
    ScalarHeightSpace S :=
  scalarReferenceWDerivCLM hD hT hS (u + n08MixedWeightAction hT hS hγ scalarBeta m u) +
    scalarReferenceWCLM hD hT hS (n08MixedWeightAction hT hS hγ scalarBeta
      (SobolevModelData.radialCLM hT (hS.1 γ) m) u)

def n08ProfileDiscriminant (m : (S.height γ).Space) (x : ScalarWeightedState S) :
    ScalarHeightSpace S :=
  (-2 : ℝ) • n08ProfileWAct hD hT hS hγ m (scalarStateRadialHeight hD hT hS x) -
    scalarHeightMul hT hS (scalarStateRadialHeight hD hT hS x)
      (scalarStateRadialHeight hD hT hS x) -
    n08ProfileEnergyAct hD hT hS hγ m (scalarStateAngularSquare hD hT hS x)

def n08ProfileNumerator (m : (S.height γ).Space) (x : ScalarWeightedState S) :
    ScalarHeightSpace S :=
  let a := scalarStateRadialCLM hD hT hS x
  let b := scalarStateRadialSecondCLM hD hT hS x
  let c := scalarStateAngularPrimitiveCLM hD hT hS x
  let d := scalarStateAngularRadialPrimitiveCLM hD hT hS x
  let e := scalarStateAngularSecondCLM hD hT hS x
  n08ProfileWDerivAct hD hT hS hγ m (a + e) + n08ProfileWAct hD hT hS hγ m b +
    x.2 • (scalarHeightMul hT hS (a + n08ProfileEnergyAct hD hT hS hγ m e) b -
      scalarReferenceRadiusCLM hD hT hS
        (n08ProfileEnergyAct hD hT hS hγ m (scalarHeightAngularMul hT hS d d)) +
      n08ProfileWAct hD hT hS hγ m (n08ProfileWDerivAct hD hT hS hγ m
        (scalarHeightAngularMul hT hS c c - scalarHeightMul hT hS a e)))

def n08ProfileResidual (m : (S.height γ).Space) (x : ScalarWeightedState S) :
    ScalarHeightSpace S :=
  scalarHeightUnitalAct hT hS
    (scalarHeightPower hT hS (-(3 / 2) : ℝ) (n08ProfileDiscriminant hD hT hS hγ m x))
    (n08ProfileNumerator hD hT hS hγ m x)

theorem n08ProfileWAct_decode (m : (S.height γ).Space) (u : ScalarHeightSpace S)
    (p : PolarPoint) {w : ℝ}
    (hw : D.w p.1 * (1 + (S.height γ).decode m p) = w) :
    (S.height scalarBeta).decode (n08ProfileWAct hD hT hS hγ m u) p =
      w * (S.height scalarBeta).decode u p := by
  simp only [n08ProfileWAct, decode_scalarReferenceWCLM, map_add, Pi.add_apply,
    n08MixedWeightAction_decode]
  rw [← hw]
  ring

theorem n08ProfileEnergyAct_decode (m : (S.height γ).Space) (u : ScalarHeightSpace S)
    (p : PolarPoint) {w : ℝ}
    (hw : D.w p.1 * (1 + (S.height γ).decode m p) = w) :
    (S.height scalarBeta).decode (n08ProfileEnergyAct hD hT hS hγ m u) p =
      (1 + w ^ 2) * (S.height scalarBeta).decode u p := by
  simp only [n08ProfileEnergyAct, map_add, Pi.add_apply,
    n08ProfileWAct_decode hD hT hS hγ m _ p hw]
  ring

theorem n08ProfileWDerivAct_decode (m : (S.height γ).Space) (u : ScalarHeightSpace S)
    (p : PolarPoint) {w' : ℝ}
    (hw' : deriv D.w p.1 * (1 + (S.height γ).decode m p) +
      D.w p.1 * radialPartial ((S.height γ).decode m) p = w') :
    (S.height scalarBeta).decode (n08ProfileWDerivAct hD hT hS hγ m u) p =
      w' * (S.height scalarBeta).decode u p := by
  simp only [n08ProfileWDerivAct, map_add, Pi.add_apply,
    decode_scalarReferenceWDerivCLM, decode_scalarReferenceWCLM,
    n08MixedWeightAction_decode, SobolevModelData.decode_radialCLM]
  rw [← hw']
  ring

theorem n08ProfileDiscriminant_decode (m : (S.height γ).Space)
    (x : ScalarWeightedState S) (p : PolarPoint) {w : ℝ}
    (hw : D.w p.1 * (1 + (S.height γ).decode m p) = w) :
    1 + (S.height scalarBeta).decode (n08ProfileDiscriminant hD hT hS hγ m x) p =
      (1 + w ^ 2) * (1 - (x.2 * heightAngular (scalarStateIncrement S x) p) ^ 2) -
        (w + x.2 * radialPartial (scalarStateIncrement S x) p) ^ 2 := by
  simp only [n08ProfileDiscriminant, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, n08ProfileWAct_decode hD hT hS hγ m _ p hw,
    n08ProfileEnergyAct_decode hD hT hS hγ m _ p hw, decode_scalarHeightMul,
    decode_scalarStateRadialHeight, decode_scalarStateAngularSquare]
  ring

theorem n08ProfileNumerator_decode (m : (S.height γ).Space)
    (x : ScalarWeightedState S) (p : PolarPoint) {w w' : ℝ}
    (hw : D.w p.1 * (1 + (S.height γ).decode m p) = w)
    (hw' : deriv D.w p.1 * (1 + (S.height γ).decode m p) +
      D.w p.1 * radialPartial ((S.height γ).decode m) p = w') :
    (S.height scalarBeta).decode (n08ProfileNumerator hD hT hS hγ m x) p =
      let u := scalarStateIncrement S x
      let a := radialPartial u p
      let b := radialPartial (radialPartial u) p
      let c := heightAngular u p
      let d := radialPartial (heightAngular u) p
      let e := angularPartial (heightAngular u) p
      w' * (a + e) + w * b + x.2 *
        ((a + (1 + w ^ 2) * e) * b - (1 + w ^ 2) * p.1 * d ^ 2 +
          w * w' * (c ^ 2 - a * e)) := by
  simp only [n08ProfileNumerator, map_add, map_sub, map_smul, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    n08ProfileWAct_decode hD hT hS hγ m _ p hw,
    n08ProfileWDerivAct_decode hD hT hS hγ m _ p hw',
    n08ProfileEnergyAct_decode hD hT hS hγ m _ p hw,
    decode_scalarHeightMul, decode_scalarHeightAngularMul, decode_scalarReferenceRadiusCLM,
    decode_scalarStateRadialCLM, decode_scalarStateRadialSecondCLM,
    decode_scalarStateAngularSecondCLM, angularPartial_decode_scalarStateAngularPrimitiveCLM,
    angularPartial_decode_scalarStateAngularRadialPrimitiveCLM]
  ring

theorem n08ProfileResidual_decode (m : (S.height γ).Space)
    (x : ScalarWeightedState S) (p : PolarPoint) (w : ℝ → ℝ)
    (hw : D.w p.1 * (1 + (S.height γ).decode m p) = w p.1)
    (hw' : deriv D.w p.1 * (1 + (S.height γ).decode m p) +
      D.w p.1 * radialPartial ((S.height γ).decode m) p = deriv w p.1)
    (hsmall : |(S.height scalarBeta).decode (n08ProfileDiscriminant hD hT hS hγ m x) p|
      ≤ 1 / 2) :
    (S.height scalarBeta).decode (n08ProfileResidual hD hT hS hγ m x) p =
      n08ScalarFiniteFormula w (scalarStateIncrement S x) x.2 p := by
  rw [n08ProfileResidual, decode_scalarHeightUnitalAct,
    decode_scalarHeightPower_neg_three_halves hT hS _ hsmall,
    n08ProfileDiscriminant_decode hD hT hS hγ m x p hw,
    n08ProfileNumerator_decode hD hT hS hγ m x p hw hw']
  dsimp only [n08ScalarFiniteFormula]
  ring

end ContinuousFlexibility.Statements
