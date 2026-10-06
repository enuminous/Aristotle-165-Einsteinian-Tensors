import Mathlib

namespace FieldSpace

/-- Generic local scalar residual used only to formalize the source grammar algebraically.
    `base` stands for the kinetic/mass/curvature part; the other arguments
    represent two pair terms and one three-way term. -/
def scalarTripletResidual
    (base lij lik lijk phij phik : ℝ) : ℝ :=
  base + lij * phij + lik * phik + lijk * phij * phik

/-- Removing the third field kills both terms that require that field. -/
theorem restrict_third_zero
    (base lij lik lijk phij : ℝ) :
    scalarTripletResidual base lij lik lijk phij 0 =
      base + lij * phij := by
  simp [scalarTripletResidual]

/-- Removing the second field gives the symmetric reduction. -/
theorem restrict_second_zero
    (base lij lik lijk phik : ℝ) :
    scalarTripletResidual base lij lik lijk 0 phik =
      base + lik * phik := by
  simp [scalarTripletResidual]

/-- A genuinely mixed trilinear contribution is invisible on either null slice. -/
theorem trilinear_null_slice_left (l x : ℝ) :
    l * x * 0 = 0 := by
  ring

theorem trilinear_null_slice_right (l y : ℝ) :
    l * 0 * y = 0 := by
  ring

/-- Two triplet charts that share the same base term and i-j pair coefficient
    glue exactly on the slice where their respective third fields vanish. -/
theorem shared_pair_overlap_consistency
    (base lij lik lijk lil lijl phij : ℝ) :
    scalarTripletResidual base lij lik lijk phij 0 =
    scalarTripletResidual base lij lil lijl phij 0 := by
  simp [scalarTripletResidual]

/-- Triple-term ablation is exact subtraction of that term. -/
theorem triple_ablation_difference
    (base lij lik lijk phij phik : ℝ) :
    scalarTripletResidual base lij lik lijk phij phik -
      scalarTripletResidual base lij lik 0 phij phik =
      lijk * phij * phik := by
  unfold scalarTripletResidual
  ring

end FieldSpace
