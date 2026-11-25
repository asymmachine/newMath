import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# 施瓦茨导数（Schwarzian Derivative）与费根鲍姆重整化的分析地基

本模块形式化一维动力系统与重整化理论的核心不变量——**施瓦茨导数**（目前 Mathlib 空白）：
1. **施瓦茨导数的代数与分析定义** `schwarzianVal` / `schwarzian`。
2. **核心定理：施瓦茨导数的复合链式法则（Cocycle 性质）**：
   $$S(f \circ g)(x) = S(f)(g(x)) \cdot (g'(x))^2 + S(g)(x)$$
3. **推论 1（负施瓦茨导数在复合下封闭）**：
   若 $Sf(g(x)) < 0$ 且 $Sg(x) < 0$，则 $S(f \circ g)(x) < 0$。
4. **推论 2（仿射变换的施瓦茨导数为零）**：
   $S(x \mapsto a x + b) = 0$，从而费根鲍姆重整化算子 $\mathcal{R}_\alpha f(x) = -\alpha f(f(-x/\alpha))$
   保持负施瓦茨导数不变。
5. **具体例子**：逻辑斯蒂映射 $f_\mu(x) = \mu x(1 - x)$ 在所有非临界点处施瓦茨导数严格为负
   $S(f_\mu)(x) = -6 / (1 - 2x)^2 < 0$。
-/

namespace Mathmatica.Schwarzian

/-- 由 1、2、3 阶导数值给出的施瓦茨导数公式：`f''' / f' - (3 / 2) * (f'' / f')²`。 -/
noncomputable def schwarzianVal (d1 d2 d3 : ℝ) : ℝ :=
  d3 / d1 - (3 / 2 : ℝ) * (d2 / d1) ^ 2

/-- 函数 `f` 在点 `x` 处的施瓦茨导数。 -/
noncomputable def schwarzian (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  schwarzianVal (deriv f x) (deriv (deriv f) x) (deriv (deriv (deriv f)) x)

/-- **核心代数恒等式（施瓦茨导数链式法则）**：
给定 `f` 在 `g(x)` 处的 1、2、3 阶导数 `(f1, f2, f3)` 与 `g` 在 `x` 处的 1、2、3 阶导数 `(g1, g2, g3)`，
复合函数 `f ∘ g` 的 1、2、3 阶导数为：
- `h1 = f1 * g1`
- `h2 = f2 * g1² + f1 * g2`
- `h3 = f3 * g1³ + 3 * f2 * g1 * g2 + f1 * g3`
则严格满足 Cocycle 链式法则：`S(f ∘ g) = S(f) * g1² + S(g)`。 -/
theorem schwarzianVal_comp {f1 f2 f3 g1 g2 g3 : ℝ} (hf1 : f1 ≠ 0) (hg1 : g1 ≠ 0) :
    schwarzianVal
      (f1 * g1)
      (f2 * g1 ^ 2 + f1 * g2)
      (f3 * g1 ^ 3 + 3 * f2 * g1 * g2 + f1 * g3) =
    schwarzianVal f1 f2 f3 * g1 ^ 2 + schwarzianVal g1 g2 g3 := by
  unfold schwarzianVal
  field_simp [hf1, hg1]
  ring

/-- **定理 1（分析版施瓦茨导数链式法则）**：
若 `f` 在 `g x` 处、`g` 在 `x` 处分别具有 1、2、3 阶导数（且一阶导数非零），
则 `schwarzian (f ∘ g) x = schwarzian f (g x) * (deriv g x) ^ 2 + schwarzian g x`。 -/
theorem schwarzian_comp {f g : ℝ → ℝ} {x : ℝ}
    (hg1 : HasDerivAt g (deriv g x) x)
    (hg2 : HasDerivAt (deriv g) (deriv (deriv g) x) x)
    (hg3 : HasDerivAt (deriv (deriv g)) (deriv (deriv (deriv g)) x) x)
    (hf1 : HasDerivAt f (deriv f (g x)) (g x))
    (hf2 : HasDerivAt (deriv f) (deriv (deriv f) (g x)) (g x))
    (hf3 : HasDerivAt (deriv (deriv f)) (deriv (deriv (deriv f)) (g x)) (g x))
    (h_d1_eq : ∀ᶠ y in nhds x, deriv (f ∘ g) y = deriv f (g y) * deriv g y)
    (h_d2_eq : ∀ᶠ y in nhds x,
      deriv (deriv (f ∘ g)) y = deriv (deriv f) (g y) * (deriv g y) ^ 2 + deriv f (g y) * deriv (deriv g) y)
    (hf1_ne : deriv f (g x) ≠ 0) (hg1_ne : deriv g x ≠ 0) :
    schwarzian (f ∘ g) x = schwarzian f (g x) * (deriv g x) ^ 2 + schwarzian g x := by
  have hd1 : deriv (f ∘ g) x = deriv f (g x) * deriv g x :=
    (hf1.comp x hg1).deriv
  have hd2_has : HasDerivAt (fun y => deriv f (g y) * deriv g y)
      (deriv (deriv f) (g x) * (deriv g x) ^ 2 + deriv f (g x) * deriv (deriv g) x) x := by
    have h := (hf2.comp x hg1).mul hg2
    convert h using 1
    · funext y; rfl
    · simp only [Function.comp_apply]; ring
  have hd2 : deriv (deriv (f ∘ g)) x =
      deriv (deriv f) (g x) * (deriv g x) ^ 2 + deriv f (g x) * deriv (deriv g) x := by
    rw [Filter.EventuallyEq.deriv_eq h_d1_eq]
    exact hd2_has.deriv
  have hd3_has : HasDerivAt
      (fun y => deriv (deriv f) (g y) * (deriv g y) ^ 2 + deriv f (g y) * deriv (deriv g) y)
      (deriv (deriv (deriv f)) (g x) * (deriv g x) ^ 3 +
        3 * deriv (deriv f) (g x) * deriv g x * deriv (deriv g) x +
        deriv f (g x) * deriv (deriv (deriv g)) x) x := by
    have hpow : HasDerivAt (fun y => (deriv g y) ^ 2) (2 * deriv g x ^ (2 - 1) * deriv (deriv g) x) x :=
      hg2.pow 2
    have hterm1 := (hf3.comp x hg1).mul hpow
    have hterm2 := (hf2.comp x hg1).mul hg3
    have hsum := hterm1.add hterm2
    convert hsum using 1
    · funext y; rfl
    · simp only [Function.comp_apply]; ring
  have hd3 : deriv (deriv (deriv (f ∘ g))) x =
      deriv (deriv (deriv f)) (g x) * (deriv g x) ^ 3 +
      3 * deriv (deriv f) (g x) * deriv g x * deriv (deriv g) x +
      deriv f (g x) * deriv (deriv (deriv g)) x := by
    rw [Filter.EventuallyEq.deriv_eq h_d2_eq]
    exact hd3_has.deriv
  unfold schwarzian
  rw [hd1, hd2, hd3]
  exact schwarzianVal_comp hf1_ne hg1_ne

/-- **定理 2（负施瓦茨导数在函数复合下封闭）**：
这是费根鲍姆重整化算子保持负施瓦茨导数类的核心原因。 -/
theorem schwarzianVal_comp_neg {f1 f2 f3 g1 g2 g3 : ℝ}
    (hf1 : f1 ≠ 0) (hg1 : g1 ≠ 0)
    (hSf : schwarzianVal f1 f2 f3 < 0)
    (hSg : schwarzianVal g1 g2 g3 < 0) :
    schwarzianVal
      (f1 * g1)
      (f2 * g1 ^ 2 + f1 * g2)
      (f3 * g1 ^ 3 + 3 * f2 * g1 * g2 + f1 * g3) < 0 := by
  rw [schwarzianVal_comp hf1 hg1]
  have hsq : 0 < g1 ^ 2 := sq_pos_of_ne_zero hg1
  nlinarith

/-- **定理 3（仿射变换的施瓦茨导数恒为零）**：
仿射缩放 `L(x) = a * x + b` 的二阶、三阶导数均为 0，故 `schwarzianVal a 0 0 = 0`。
推论：重整化算子中的缩放变换 `x ↦ -x / α` 与 `y ↦ -α * y` 不改变负施瓦茨导数的符号。 -/
theorem schwarzianVal_affine (a : ℝ) : schwarzianVal a 0 0 = 0 := by
  unfold schwarzianVal
  simp

/-- **定理 4（逻辑斯蒂映射 `f_μ(x) = μ x (1 - x)` 的施瓦茨导数恒为负）**：
对任意非零参数 `μ` 和非临界点 `x ≠ 1/2`，
逻辑斯蒂映射的一阶、二阶、三阶导数为 `(μ(1 - 2x), -2μ, 0)`，
其施瓦茨导数严格等于 `-6 / (1 - 2x)² < 0`。 -/
theorem logistic_schwarzian_neg {μ x : ℝ} (hμ : μ ≠ 0) (hx : 1 - 2 * x ≠ 0) :
    schwarzianVal (μ * (1 - 2 * x)) (-2 * μ) 0 = -6 / (1 - 2 * x) ^ 2 ∧
    schwarzianVal (μ * (1 - 2 * x)) (-2 * μ) 0 < 0 := by
  have hd1 : μ * (1 - 2 * x) ≠ 0 := mul_ne_zero hμ hx
  have heq : schwarzianVal (μ * (1 - 2 * x)) (-2 * μ) 0 = -6 / (1 - 2 * x) ^ 2 := by
    unfold schwarzianVal
    field_simp [hμ, hx]
    ring
  refine ⟨heq, ?_⟩
  rw [heq]
  have hpos : 0 < (1 - 2 * x) ^ 2 := sq_pos_of_ne_zero hx
  exact div_neg_of_neg_of_pos (by norm_num) hpos

end Mathmatica.Schwarzian
