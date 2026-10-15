[English](README.md) | [简体中文](README_zh.md)

# Lean 4 中的 Artin 原根定理（无穷性部分）

除 −1 和完全平方数以外的每个整数，都是无穷多个素数的原根。

- **作者：** Yao Xu ([@cadamcat](https://github.com/cadamcat))；见[作者与署名说明](AUTHORS.md)。
- **数学结果：** OpenAI，[*Primitive roots for every admissible integer base*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf)。
- 本项目在 AI 协助下开发；所有证明均由 Lean 4 内核验证。

## 主要结果

| 定理 | 陈述 |
| --- | --- |
| `ArtinPrimitiveRootsConjecture.artin_primitive_roots_infinite` | 对任意满足 `a ≠ -1` 且 `¬ IsSquare a` 的 `a : ℤ`，集合 `S a = {p : ℕ \| p.Prime ∧ orderOf (a : ZMod p) = (p-1 : ℕ)}` 是无限集。 |

证明见 [ArtinPrimitiveRoots/Target.lean](ArtinPrimitiveRoots/Target.lean)。只用 Mathlib 定义写成的挑战陈述见 [Challenge.lean](Challenge.lean)；[comparator.json](comparator.json) 配置 Comparator 比较这两个陈述。`S` 的定义逐字取自 Formal Conjectures 中的 `ArtinPrimitiveRootsConjecture.S`（`FormalConjectures/Wikipedia/ArtinPrimitiveRootsConjecture.lean`，提交 `9d259649abe0b02d7a25f7589b872db679b35e21`）；该文件只陈述了猜想的密度形式。

`orderOf` 是 `ZMod p` 中的乘法阶。若 `p` 整除 `a`，则 `0` 的阶为 `0`，所以这样的素数不属于 `S a`。当 `a` 为奇数时，素数 2 属于 `S a`，因为 1 的阶是 `1 = 2 - 1`；这最多多出一个素数，不影响无穷性。

## 证明结构

形式化证明按照 OpenAI 的论文进行。论文的定理 1.1 断言：对每个满足条件的 `a`，存在常数 `c > 0` 和 `X ≥ 2`，使得当 `x ≥ X` 时，区间 `(x, 2x)` 中至少有 `c x / (log x)²` 个不整除 `a`、且以 `a` 为原根的素数 `p`。这就是 [ArtinPrimitiveRoots/Reduction.lean](ArtinPrimitiveRoots/Reduction.lean) 中的 `ArtinPrimitiveRoots.thm_main`；取 `x` 大于任一有限素数集合中的所有元素，即得主定理。

`a` 不是模 `p` 的原根，当且仅当某个素数 `q` 整除指数 `(p − 1)/ord_p(a)`。证明构造一类素数，使这样的 `q` 只能落在很大的范围或一个中间范围内，再分别排除。证明分为三部分，每部分在 Lean 中是一个独立的定理：

1. **前驱受控的素数**（`ArtinPrimitiveRoots.prop_controlled`，[Controlled.lean](ArtinPrimitiveRoots/Controlled.lean)）。在一个固定的剩余类中，`(x, 2x)` 内有 `≫ x/(log x)²` 个素数 `p` 满足 `p − 1 = c r Q`，其中 `c ∈ {2, 4}`，`Q > x^0.9` 是素数，`r` 的每个素因子都在 `exp((log x)^0.1)` 与 `exp((log x)^0.3)` 之间。所选剩余类使 `a` 成为模 `p` 的二次非剩余，从而排除 `q = 2`。这部分用到筛法、OpenAI 关于 Poisson–Dirichlet 分布的论文中的带标记双线性（Type II）估计、Bombieri–Vinogradov 定理和 Buchstab 恒等式。
2. **一致的完全分裂估计**（`ArtinPrimitiveRoots.prop_splitting`，[Splitting.lean](ArtinPrimitiveRoots/Splitting.lean)）。对素数 `q ≤ exp((log x)^0.3)`，`(x, 2x]` 中在 `ℚ(μ_q, a^{1/q})` 里完全分裂的素数个数为 `O(x/(q(q−1) log x) + x^{1−10⁻⁶})`，常数与 `q` 无关。Lean 陈述计数的是满足 `q ∣ p − 1` 且在 `ZMod p` 中 `a^{(p−1)/q} = 1` 的素数 `p`。
3. **固定宽度的 Hecke 无零点区域**（`ArtinPrimitiveRoots.HeckeBoundary.thm_hecke_zero_free`，[Hecke/Boundary.lean](ArtinPrimitiveRoots/Hecke/Boundary.lean)）。对 `12 ∣ n` 的分圆域 `F = ℚ(μ_n)` 及其任一射线类群上的特征，Hecke L 函数可亚纯延拓到 `Re s > 1 − 10⁻⁶`，且在该区域内无零点。宽度与 `F` 和特征无关，第 2 部分依赖这一点。证明对六次 Kummer 扭曲下三次 theta 系数的同一个加性平均作两种计算，一种用系数反射，一种用 Poisson 求和；这部分按照论文的无零点区域各节，以及其附录中对 Kazhdan–Patterson theta 规范化的验证。

对第 1 部分得到的素数，指数的素因子 `q ≠ 2` 要么等于 `Q`，要么整除 `r`。若 `q = Q`，则 `a` 的阶整除 `c r < 2x^0.1`，于是 `p` 整除某个指数 `j` 很小的 `a^j − 1`，这样的素数很少。整除 `r` 的 `q` 落在第 2 部分的范围内，对这一范围求和后排除的素数少于第 1 部分提供的素数。

## 构建与验证

环境要求：Git、Python 3 和 [elan](https://github.com/leanprover/elan)，并确保 `lake` 在 `PATH` 中。在全新检出的仓库根目录运行：

```sh
lake update
scripts/apply-oai-patches.sh
lake exe cache get
lake build
```

OpenAI 的 `lake update` hook 会在解析依赖并写入 `lake-manifest.json` 之后报错，错误以 `iut: Lake resolved an unexpected checkout at …` 开头。接着运行补丁脚本：它把 OpenAI 的 Lean 4.34.1 兼容补丁应用到已下载的依赖包上，再次运行 `lake update` 后也可重新运行。`lake exe cache get` 下载 Mathlib 的编译结果；其他依赖由 `lake build` 从源码编译。

若要检查陈述和最终定理的公理，运行 `LEAN_NUM_THREADS=4 ./scripts/verify.sh`。它检查 [ArtinPrimitiveRoots/Target.lean](ArtinPrimitiveRoots/Target.lean) 与 [Challenge.lean](Challenge.lean) 的陈述文本相同，在 Lean 中把两者分别与同一个展示出的陈述比较，并打印 `ArtinPrimitiveRootsConjecture.artin_primitive_roots_infinite` 依赖的公理；允许的公理只有 `propext`、`Classical.choice` 和 `Quot.sound`。详见[验证说明](docs/verification.md)。

## 固定依赖

- Lean `v4.34.1`，由 [lean-toolchain](lean-toolchain) 选定。
- [Mathlib](https://github.com/leanprover-community/mathlib4)，提交 `d13f23b723b8a846827a245b89c10fc7d3f11612`。
- OpenAI 的 [`openai/math`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean)，提交 `adc7f1241b42e322a6451854ab7e4b4c146bf78a`，以及它固定版本的依赖包。本项目从其中的 [ClassFieldTheory](https://github.com/n-yamaguchi-0729/ClassFieldTheory)（`2eb22d6`，包括其 `ValuedFieldTheory` 和 `GaloisCohomology` 库）、[TauCeti](https://github.com/TauCetiProject/TauCeti)（`3bed7e3`）、[AINTLIB](https://github.com/CBirkbeck/AINTLIB)（`160e446`，其 `DedekindResidue` 库）、[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)（`c39a751`）和 [rellich-kondrachov](https://github.com/abenenson/rellich-kondrachov)（`70f85d4`）导入模块。
- 所有版本都固定在 [lake-manifest.json](lake-manifest.json) 中。

## 数学参考文献

- OpenAI，[*Primitive roots for every admissible integer base*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf)。
- OpenAI，[*The Poisson–Dirichlet law for prime predecessors*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/paper.pdf)，定理 3.1（第 1 部分使用的带标记素数估计）。
- C. Hooley，*On Artin's conjecture*，J. reine angew. Math. 225 (1967)，209–220。
- D. A. Kazhdan 和 S. J. Patterson，*Metaplectic forms*，Publ. Math. IHÉS 59 (1984)，35–142。

代码署名见 [THIRD_PARTY.md](THIRD_PARTY.md)，项目许可证见 [LICENSE](LICENSE)。
