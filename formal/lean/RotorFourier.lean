import RotorEnclosure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open scoped BigOperators
open IncrementCycles RotorEnclosure RotorRational

namespace RotorFourier
noncomputable section

def moment (z : ℂ) (k : Fin 6 → ℝ) : ℂ := ∑ d : Fin 6, (k d : ℂ) * z^d.val

theorem shift_char_forward (z : ℂ) (hz : z^6 = 1) (d : Fin 6) :
    z^(d+1).val = z^d.val*z := by
  fin_cases d <;> first | rfl | (change z^0 = z^5*z; rw [← pow_succ,hz,pow_zero])

theorem shift_char_backward (z : ℂ) (hz : z^6 = 1) (d : Fin 6) :
    z^(d-1).val = z^d.val*z^5 := by
  fin_cases d <;> rw [← pow_add]
  · rfl
  · change z^0 = z^6
    rw [pow_zero,hz]
  · change z^1 = z^(6+1)
    rw [pow_add,hz,one_mul]
  · change z^2 = z^(6+2)
    rw [pow_add,hz,one_mul]
  · change z^3 = z^(6+3)
    rw [pow_add,hz,one_mul]
  · change z^4 = z^(6+4)
    rw [pow_add,hz,one_mul]

theorem walk_moment (z : ℂ) (hz : z^6 = 1) (a : ℝ) (n : ℕ) :
    moment z (walk a n) = ((forward a : ℂ)*z + (backward a : ℂ)*z^5)^n := by
  induction n with
  | zero =>
    unfold moment
    simp [walk,apply_ite]
  | succ n ih =>
    unfold moment at ih ⊢
    have left := (Equiv.sum_comp (Equiv.addRight (1 : Fin 6))
      (fun d => ((walk a n (d-1) : ℝ) : ℂ) * (forward a : ℂ) * z^d.val)).symm
    have right := (Equiv.sum_comp (Equiv.addRight (-1 : Fin 6))
      (fun d => ((walk a n (d+1) : ℝ) : ℂ) * (backward a : ℂ) * z^d.val)).symm
    change (∑ d : Fin 6, (walk a n (d-1) : ℂ) * (forward a : ℂ) * z^d.val) =
      ∑ d : Fin 6, (walk a n ((d+1)-1) : ℂ) * (forward a : ℂ) * z^(d+1).val at left
    change (∑ d : Fin 6, (walk a n (d+1) : ℂ) * (backward a : ℂ) * z^d.val) =
      ∑ d : Fin 6, (walk a n ((d+(-1))+1) : ℂ) * (backward a : ℂ) * z^(d+(-1)).val at right
    simp only [add_sub_cancel_right,shift_char_forward z hz] at left
    simp only [← sub_eq_add_neg,sub_add_cancel,shift_char_backward z hz] at right
    have left' :
        (∑ d : Fin 6, (walk a n (d-1) : ℂ) * (forward a : ℂ) * z^d.val) =
        (∑ d : Fin 6, (walk a n d : ℂ) * z^d.val) * ((forward a : ℂ)*z) := by
      rw [left,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    have right' :
        (∑ d : Fin 6, (walk a n (d+1) : ℂ) * (backward a : ℂ) * z^d.val) =
        (∑ d : Fin 6, (walk a n d : ℂ) * z^d.val) * ((backward a : ℂ)*z^5) := by
      rw [right,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    simp only [walk,Complex.ofReal_add,Complex.ofReal_mul,add_mul,Finset.sum_add_distrib]
    rw [left',right',ih,pow_succ]
    ring

theorem poisson_characteristic (z : ℂ) (hz : z^6 = 1) (u a : ℝ) (hu : 0 ≤ u)
    (ha : -1 ≤ a ∧ a ≤ 1) :
    moment z (kernel u a) =
      Complex.exp ((u : ℂ)*((forward a : ℂ)*z + (backward a : ℂ)*z^5-1)) := by
  let m : ℂ := (forward a : ℂ)*z + (backward a : ℂ)*z^5
  have H (d : Fin 6) : Summable (fun n : ℕ =>
      (↑(poissonWeight u n * walk a n d) : ℂ) * z^d.val) :=
    ((kernel_series_summable hu ha d).mapL Complex.ofRealCLM).mul_right _
  have hseries :
      (∑ d : Fin 6, (↑(∑' n, poissonWeight u n * walk a n d) : ℂ) * z^d.val) =
      Complex.exp ((u : ℂ)*m) := by
    simp only [Complex.ofReal_tsum, ← tsum_mul_right]
    rw [← Summable.tsum_finsetSum (fun d _ => H d)]
    rw [Complex.exp_eq_exp_ℂ,NormedSpace.exp_eq_tsum_div]
    refine tsum_congr fun n => ?_
    simp only [Complex.ofReal_mul, mul_assoc, ← Finset.mul_sum]
    change (poissonWeight u n : ℂ) * moment z (walk a n) = _
    rw [walk_moment z hz]
    simp only [poissonWeight,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast,mul_pow]
    dsimp only [m]
    ring
  unfold moment kernel
  trans (∑ d : Fin 6, (↑(∑' n, poissonWeight u n * walk a n d) : ℂ) * z^d.val) /
      ((Real.exp u : ℝ) : ℂ)
  · simp only [div_eq_mul_inv,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    push_cast
    ring
  · rw [hseries, Complex.ofReal_exp, ← Complex.exp_sub]
    congr 1
    dsimp [m]
    ring


-- Sixth roots are defined through the complex exponential on the imaginary axis.
def root (n : ℕ) : ℂ := Complex.exp (((n : ℝ) * Real.pi / 3 : ℝ) * Complex.I)

theorem root_pow (n k : ℕ) : root n ^ k = root (n*k) := by
  rw [root,← Complex.exp_nat_mul,root]
  congr 1
  push_cast
  ring

theorem root_one_pow (k : ℕ) : root 1 ^ k = root k := by rw [root_pow,one_mul]

theorem root_six (n : ℕ) : root n ^ 6 = 1 := by
  rw [root_pow]
  have h : (((↑(n*6) : ℝ)*Real.pi/3 : ℝ) : ℂ)*Complex.I =
      (n : ℂ)*(2*(Real.pi : ℂ)*Complex.I) := by push_cast; ring
  rw [root,h,Complex.exp_nat_mul,Complex.exp_two_pi_mul_I,one_pow]

theorem root_mod (n : ℕ) : root n = root (n % 6) := by
  rw [← root_one_pow n,← root_one_pow (n%6)]
  conv_lhs => rw [← Nat.mod_add_div n 6]
  rw [pow_add,pow_mul,root_six,one_pow,mul_one]

theorem root_re (n : ℕ) : (root n).re = Real.cos ((n : ℝ)*Real.pi/3) := by
  simp [root,Complex.exp_re,Complex.mul_re,Complex.mul_im]

theorem root_im (n : ℕ) : (root n).im = Real.sin ((n : ℝ)*Real.pi/3) := by
  simp [root,Complex.exp_im,Complex.mul_re,Complex.mul_im]

theorem cosine120 : Real.cos (2*Real.pi/3) = -(1/2) := by
  rw [show 2*Real.pi/3 = Real.pi-Real.pi/3 by ring,Real.cos_pi_sub,Real.cos_pi_div_three]

theorem sine120 : Real.sin (2*Real.pi/3) = Real.sqrt 3/2 := by
  rw [show 2*Real.pi/3 = Real.pi-Real.pi/3 by ring,Real.sin_pi_sub,Real.sin_pi_div_three]

theorem roots_re_computed :
    (root 0).re = 1 ∧ (root 1).re = 1/2 ∧ (root 2).re = -(1/2) ∧
    (root 3).re = -1 ∧ (root 4).re = -(1/2) ∧ (root 5).re = 1/2 := by
  simp only [root_re, Nat.cast_ofNat,Nat.cast_one,Nat.cast_zero,zero_mul,zero_div,Real.cos_zero,one_mul]
  rw [Real.cos_pi_div_three,cosine120,
    show 3*Real.pi/3=Real.pi by ring, Real.cos_pi,
    show 4*Real.pi/3=2*Real.pi-2*Real.pi/3 by ring, Real.cos_two_pi_sub,cosine120,
    show 5*Real.pi/3=2*Real.pi-Real.pi/3 by ring, Real.cos_two_pi_sub,Real.cos_pi_div_three]
  simp

theorem roots_im_computed :
    (root 1).im = Real.sqrt 3/2 ∧ (root 2).im = Real.sqrt 3/2 ∧
    (root 3).im = 0 ∧ (root 4).im = -(Real.sqrt 3/2) ∧ (root 5).im = -(Real.sqrt 3/2) := by
  simp only [root_im,Nat.cast_ofNat,Nat.cast_one,one_mul]
  rw [Real.sin_pi_div_three,sine120,
    show 3*Real.pi/3=Real.pi by ring,Real.sin_pi,
    show 4*Real.pi/3=2*Real.pi-2*Real.pi/3 by ring,Real.sin_two_pi_sub,sine120,
    show 5*Real.pi/3=2*Real.pi-Real.pi/3 by ring,Real.sin_two_pi_sub,Real.sin_pi_div_three]
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem root_five_reduced (n : ℕ) : root n ^ 5 = root ((n*5)%6) := by rw [root_pow,root_mod]

theorem modes_one (a u : ℝ) (ha : -1 ≤ a ∧ a ≤ 1) (hu : 0 ≤ u) :
    (moment (root 1) (kernel u a)).re =
      Real.exp (-u/2) * Real.cos (Real.sqrt 3 * a * u/2) := by
  rw [poisson_characteristic _ (root_six 1) _ _ hu ha, root_five_reduced, Complex.exp_re]
  rcases roots_re_computed with ⟨_,h1,_,_,_,h5⟩
  rcases roots_im_computed with ⟨i1,_,_,_,i5⟩
  simp [Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
    h1,h5,i1,i5,forward,backward]
  congr 1
  · ring_nf
  · congr 1
    ring

theorem modes_two (a u : ℝ) (ha : -1 ≤ a ∧ a ≤ 1) (hu : 0 ≤ u) :
    (moment (root 2) (kernel u a)).re =
      Real.exp (-3*u/2) * Real.cos (Real.sqrt 3 * a * u/2) := by
  rw [poisson_characteristic _ (root_six 2) _ _ hu ha, root_five_reduced, Complex.exp_re]
  rcases roots_re_computed with ⟨_,_,h2,_,h4,_⟩
  rcases roots_im_computed with ⟨_,i2,_,i4,_⟩
  simp [Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
    h2,h4,i2,i4,forward,backward]
  congr 1
  · ring_nf
  · congr 1
    ring

theorem modes_three (a u : ℝ) (ha : -1 ≤ a ∧ a ≤ 1) (hu : 0 ≤ u) :
    (moment (root 3) (kernel u a)).re = Real.exp (-2*u) := by
  rw [poisson_characteristic _ (root_six 3) _ _ hu ha, root_five_reduced, Complex.exp_re]
  rcases roots_re_computed with ⟨_,_,_,h3,_,_⟩
  rcases roots_im_computed with ⟨_,_,i3,_,_⟩
  simp [Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
    h3,i3,forward,backward]
  ring

theorem list_sites_sum (f : Fin 6 → ℝ) : listVal sites f = ∑ d : Fin 6, f d := by
  simp [sites,listVal,Fin.sum_univ_succ]

theorem correlation_modes (k : Fin 6 → ℝ) :
    corr k = 2/9 * (moment (root 1) k).re +
      2/3 * (moment (root 2) k).re + 1/9 * (moment (root 3) k).re := by
  have weight (d : Fin 6) : (rWeight d : ℝ) =
      2/9 * ((root 1)^d.val).re + 2/3 * ((root 2)^d.val).re + 1/9 * ((root 3)^d.val).re := by
    rw [root_pow,root_pow,root_pow,root_mod (1*d.val),root_mod (2*d.val),root_mod (3*d.val)]
    rcases roots_re_computed with ⟨h0,h1,h2,h3,h4,h5⟩
    fin_cases d <;> norm_num [rWeight,h0,h1,h2,h3,h4,h5]
  unfold corr moment
  rw [list_sites_sum]
  simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    Finset.mul_sum,← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [weight d]
  ring

theorem autocorrelation_eq14 (u a : ℝ) (hu : 0 ≤ u) (ha : -1 ≤ a ∧ a ≤ 1) :
    corr (kernel u a) = rotorR a u := by
  rw [correlation_modes,modes_one a u ha hu,modes_two a u ha hu,modes_three a u ha hu]
  unfold rotorR
  ring

theorem char_add (z : ℂ) (hz : z^6=1) (i j : Fin 6) :
    z^(i+j).val = z^i.val * z^j.val := by
  rw [← pow_add]
  change z^((i.val+j.val)%6) = z^(i.val+j.val)
  have h := Nat.mod_add_div (i.val+j.val) 6
  conv_rhs => rw [← h,pow_add,pow_mul,hz,one_pow,mul_one]

theorem moment_conv (z : ℂ) (hz : z^6=1) (k : Fin 6 → ℝ) :
    moment z (conv k) = moment z k * moment z k := by
  unfold moment conv
  simp only [list_sites_sum,Complex.ofReal_sum,Complex.ofReal_mul,Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h := (Equiv.sum_comp (Equiv.addRight i)
      (fun d : Fin 6 => (k i : ℂ) * (k (d-i) : ℂ) * z^d.val)).symm
  change (∑ d : Fin 6, (k i : ℂ) * (k (d-i) : ℂ) * z^d.val) =
    ∑ d : Fin 6, (k i : ℂ) * (k ((d+i)-i) : ℂ) * z^(d+i).val at h
  rw [h,Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [add_sub_cancel_right,char_add z hz]
  ring

theorem conv_moment_time_two (z : ℂ) (hz : z^6=1) (a : ℝ) (ha : -1 ≤ a ∧ a ≤ 1) :
    moment z (conv (kernel 1 a)) = moment z (kernel 2 a) := by
  rw [moment_conv z hz,poisson_characteristic z hz 1 a (by norm_num) ha,
    poisson_characteristic z hz 2 a (by norm_num) ha, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem gap_eq14 (a : ℝ) (ha : -1 ≤ a ∧ a ≤ 1) :
    liveGap a = rotorGap a := by
  unfold liveGap rotorGap liveCorr
  rw [autocorrelation_eq14 1 a (by norm_num) ha]
  have h2 : corr (conv (kernel 1 a)) = corr (kernel 2 a) := by
    rw [correlation_modes,correlation_modes (kernel 2 a),
      conv_moment_time_two _ (root_six 1) a ha,conv_moment_time_two _ (root_six 2) a ha,
      conv_moment_time_two _ (root_six 3) a ha]
  rw [h2,autocorrelation_eq14 2 a (by norm_num) ha]

/-- The manuscript's analytic equality and a positive witness hold at the same parameter. -/
theorem eq14_same_root :
    ∃ a ∈ Set.Icc (RotorRational.low : ℝ) (RotorRational.high : ℝ),
      rotorR a 2 = (rotorR a 1)^2 ∧ (2436/1000000 : ℝ) < liveContrast a ∧
      0 < rotorR a 1 ∧ rotorR a 1 < 1 := by
  obtain ⟨a,ha,hzero,hD,hpos,hlt⟩ := rotor_matched_positive
  have hab : -1 ≤ a ∧ a ≤ 1 :=
    ⟨(show (-1 : ℝ) ≤ RotorRational.low by norm_num [RotorRational.low]).trans ha.1,
     ha.2.trans (show (RotorRational.high : ℝ) ≤ 1 by norm_num [RotorRational.high])⟩
  rw [gap_eq14 a hab] at hzero
  have h := autocorrelation_eq14 1 a (by norm_num) hab
  exact ⟨a,ha,sub_eq_zero.mp hzero,hD,h ▸ hpos,h ▸ hlt⟩

end
end RotorFourier
